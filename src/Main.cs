// This is a pretty straightforward port of the C++ test harness.

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using Newtonsoft.Json.Linq;
using W65C02S;

class AllDone : Exception {}

class Range {
    private ushort beg, end;
    public Range() { beg = 65535; end = 0; }
    public Range(ushort beg, ushort end) { this.beg = beg; this.end = end;}
    public bool contains(ushort addr) {
        return addr >= beg && addr <= end;
    }
}

enum OutFormat {
    NONE, BASE64, UTF8
}

class Flip {
    private uint underlying;
    public Flip() { underlying = 0; }
    public Flip(uint underlying) { this.underlying = underlying; }
    public uint getCycle() {
      return underlying & 0xFFFFFF;
    }
    bool getState() {
      return (underlying & 0x80000000) != 0;
    }
    uint getPin() {
      return (underlying >> 24) & 0x7F;
    }
    public void apply(CPU cpu) {
      bool state = getState();
      switch(getPin()) {
      case 1:
          cpu.SetP((byte)(cpu.GetP() | CPU.P_V));
          break;
      case 2: cpu.SetNMI(state); break;
      case 3: cpu.SetIRQ(state); break;
      }
    }
}

namespace W65C02S {
    public class MainClass {
        private static byte[] sram = new byte[65536];
        private const byte TERMINATE_ON_BRK = 0x01;
        private const byte TERMINATE_ON_INFINITE = 0x02;
        private const byte TERMINATE_ON_ZERO = 0x04;
        private const byte TERMINATE_ON_STACK = 0x08;
        private const byte TERMINATE_ON_VECTOR = 0x10;
        private const byte TERMINATE_ON_BAD_WRITE = 0x20;
        private const byte TERMINATE_ON_UNUSED_FLAGS = 0xC0;
        private static List<Range> ranges = new List<Range>();
        private static ushort serial_in_addr, serial_out_addr;
        private static Queue<byte> serial_in = new Queue<byte>();
        private const int MAX_SERIAL_OUT = 131072;
        private static Queue<byte> serial_out = new Queue<byte>();
        private static OutFormat serial_out_fmt = OutFormat.NONE;
        private static bool serial_in_enabled = false,
            serial_out_enabled = false, last_pc_valid = false,
            vector_has_been_pulled = false;
        private static ushort last_pc;
        private static uint cycles_to_report = 0, cycles_to_run = 10000000,
            num_cycles = 5;
        private static List<uint> cycles = new List<uint>(50000);
        private static byte terminate_on
            = (byte)(~TERMINATE_ON_UNUSED_FLAGS & 0xFF);
        private static byte termination_cause = 0;
        private static Queue<Flip> flips;
        private static CPU cpu = new CPU();
        private sealed class UsBus : Bus {
            private const byte LOCKED_WRITE = 2;
            private const byte LOCKED_READ = 3;
            private const byte VECTOR_READ = 5;
            private const byte NORMAL_WRITE = 6;
            private const byte NORMAL_READ = 7;
            private const byte OPCODE_READ = 15;
            public override byte Read(CPU cpu, ushort addr)
                => PerformRead(cpu, NORMAL_READ, addr);
            public override byte ReadLocked(CPU cpu, ushort addr)
                => PerformRead(cpu, LOCKED_READ, addr);
            public override byte ReadOpcode(CPU cpu, ushort addr) {
                byte ret = PerformRead(cpu, OPCODE_READ, addr);
                if(vector_has_been_pulled) {
                    if(last_pc_valid && addr == last_pc) {
                        if((terminate_on & TERMINATE_ON_INFINITE) != 0) {
                            termination_cause = 2;
                            throw new AllDone();
                        }
                    }
                    last_pc_valid = true;
                    last_pc = addr;
                    if((terminate_on & TERMINATE_ON_ZERO) != 0
                       && addr < 0x0100) {
                        termination_cause = 3;
                        throw new AllDone();
                    }
                    if((terminate_on & TERMINATE_ON_STACK) != 0
                       && addr >= 0x0100 && addr < 0x0200) {
                        termination_cause = 4;
                        throw new AllDone();
                    }
                    if((terminate_on & TERMINATE_ON_ZERO) != 0
                       && addr >= 0xfffa) {
                        termination_cause = 5;
                        throw new AllDone();
                    }
                    if((terminate_on & TERMINATE_ON_BRK) != 0
                       && ret == 0) {
                        termination_cause = 1;
                        throw new AllDone();
                    }
                }
                return ret;
            }
            public override byte ReadVector(CPU cpu, ushort addr) {
                vector_has_been_pulled = true;
                return PerformRead(cpu, VECTOR_READ, addr);
            }
            public override void Write(CPU cpu, ushort addr, byte val)
                => PerformWrite(cpu, NORMAL_WRITE, addr, val);
            public override void WriteLocked(CPU cpu, ushort addr, byte val)
                => PerformWrite(cpu, LOCKED_WRITE, addr, val);
            private byte PerformRead(CPU cpu, byte type, ushort addr) {
                byte ret = HandleRead(cpu, addr);
                if(vector_has_been_pulled) {
                    report_cycle(type, addr, ret);
                }
                return ret;
            }
            private void PerformWrite(CPU cpu, byte type, ushort addr,
                                      byte val) {
                if(vector_has_been_pulled) {
                    report_cycle(type, addr, val);
                }
                HandleWrite(cpu, addr, val);
            }
            private byte HandleRead(CPU cpu, ushort addr) {
                if(serial_in_enabled && addr == serial_in_addr) {
                    if(serial_in.Count == 0) {
                        cpu.SetP((byte)(cpu.GetP() | CPU.P_V));
                        return 0;
                    }
                    else return serial_in.Dequeue();
                }
                return sram[addr];
            }
            private void HandleWrite(CPU cpu, ushort addr, byte val) {
                if(serial_out_enabled && addr == serial_out_addr) {
                    if(serial_out.Count >= MAX_SERIAL_OUT)
                        cpu.SetP((byte)(cpu.GetP() | CPU.P_V));
                    else
                        serial_out.Enqueue(val);
                    return;
                }
                bool valid = false;
                foreach(Range range in ranges) {
                    if(range.contains(addr)) {
                        valid = true;
                        break;
                    }
                }
                if(valid) sram[addr] = val;
                else if((terminate_on & TERMINATE_ON_BAD_WRITE) != 0) {
                    termination_cause = 6;
                    throw new AllDone();
                }
            }
        }
        private static UsBus bus = new UsBus();
        private static void report_cycle(byte cycle_type, ushort addr,
                                         byte data) {
            if(cycles_to_report > 0) {
                cycles.Add(((uint)(cycle_type) << 24)
                           | ((uint)(addr) << 8)
                           | (uint)data);
                --cycles_to_report;
            }
            ++num_cycles;
            if(num_cycles == cycles_to_run) throw new AllDone();
            while(flips.Count != 0
                  && flips.Peek().getCycle() <= num_cycles) {
                Flip flip = flips.Dequeue();
                flip.apply(cpu);
            }
        }
        private static void write_init_records(JArray records) {
            for(int n = 0; n < records.Count; ++n) {
                JObject record = (JObject)records[n];
                ushort i = (ushort)record["base"];
                byte[] data = data_decode((string)record["data"]);
                if(data.Length == 0) {
                    throw new Exception("Empty init record");
                }
                int j = 0;
                uint rem;
                if(record.ContainsKey("size")) rem = (uint)record["size"];
                else rem = (uint)data.Length;
                while(rem-- > 0) {
                    sram[i++] = data[j++];
                    if(j >= data.Length) j = 0;
                }
            }
        }
        private static byte[] data_decode(string source) {
            if(source.StartsWith("utf8:")) {
                return Encoding.UTF8.GetBytes(source.Substring(5));
            }
            else if(source.StartsWith("base64:")) {
                return Convert.FromBase64String(source.Substring(7));
            }
            else {
                throw new Exception("Unknown data format");
            }
        }
        private static void add_flips(List<Flip> flip_list,
                                      JArray src, uint flip_type) {
            bool state = false;
            uint[] v = new uint[src.Count];
            for(int n = 0; n < src.Count; ++n) v[n] = (uint)src[n];
            Array.Sort(v);
            flip_type <<= 24;
            for(int n = 0; n < v.Length; ++n) {
                state = !state;
                flip_list.Add(new Flip((state ? 0x80000000 : 0)
                                       | flip_type
                                       | v[n]));
            }
        }
        public static int Main(string[] args) {
            if(args.Length != 1) {
                Console.Error.WriteLine("Usage: w65c02s-dotnet-test job.json > report.json");
                return 1;
            }
            JObject job = JObject.Parse(File.ReadAllText(args[0]));
            sram[0xFFFD] = 0x02;
            if(job.ContainsKey("init")) {
                // um... it *better* contain "init"
                write_init_records((JArray)job["init"]);
            }
            else throw new Exception("no init records, what a pointless test");
            if(job.ContainsKey("rwmap")) {
                JArray rwmap = (JArray)job["rwmap"];
                for(int n = 0; n < rwmap.Count; ++n) {
                    JArray r = (JArray)rwmap[n];
                    ranges.Add(new Range((ushort)r[0], (ushort)r[1]));
                }
            }
            else {
                ranges.Add(new Range(0x0000, 0x01FF));
            }
            if(job.ContainsKey("serial_in_addr")) {
                serial_in_addr = (ushort)job["serial_in_addr"];
                serial_in_enabled = true;
                if(job.ContainsKey("serial_in_data")) {
                    serial_in = new Queue<byte>(data_decode((string)job["serial_in_data"]));
                }
            }
            if(job.ContainsKey("serial_out_addr")) {
                serial_out_addr = (ushort)job["serial_out_addr"];
                serial_out_enabled = true;
            }
            if(job.ContainsKey("serial_out_fmt")) {
                switch((string)job["serial_out_fmt"]) {
                    case "utf8": serial_out_fmt = OutFormat.UTF8; break;
                    case "base64": serial_out_fmt = OutFormat.BASE64; break;
                    default: throw new Exception("unknown serial_out_fmt");
                }
            }
            if(job.ContainsKey("show_cycles") && (bool)job["show_cycles"]) {
                cycles_to_report = 1000;
            }
            if(job.ContainsKey("max_cycles")) {
                cycles_to_run = (uint)job["max_cycles"];
            }
            if(job.ContainsKey("terminate_on_brk") && !(bool)job["terminate_on_brk"]) {
                terminate_on &= (byte)(~TERMINATE_ON_BRK & 0xFF);
            }
            if(job.ContainsKey("terminate_on_infinite_loop") && !(bool)job["terminate_on_infinite_loop"]) {
                terminate_on &= (byte)(~TERMINATE_ON_INFINITE & 0xFF);
            }
            if(job.ContainsKey("terminate_on_zero_fetch") && !(bool)job["terminate_on_zero_fetch"]) {
                terminate_on &= (byte)(~TERMINATE_ON_ZERO & 0xFF);
            }
            if(job.ContainsKey("terminate_on_stack_fetch") && !(bool)job["terminate_on_stack_fetch"]) {
                terminate_on &= (byte)(~TERMINATE_ON_STACK & 0xFF);
            }
            if(job.ContainsKey("terminate_on_vector_fetch") && !(bool)job["terminate_on_vector_fetch"]) {
                terminate_on &= (byte)(~TERMINATE_ON_VECTOR & 0xFF);
            }
            if(job.ContainsKey("terminate_on_bad_write") && !(bool)job["terminate_on_bad_write"]) {
                terminate_on &= (byte)(~TERMINATE_ON_BAD_WRITE & 0xFF);
            }
            if(job.ContainsKey("rdy"))
                throw new Exception("this test harness does not support the RDY signal");
            if(job.ContainsKey("res"))
                throw new Exception("this test harness does not support the reset signal");
            List<Flip> flip_list = new List<Flip>();
            if(job.ContainsKey("so"))
                add_flips(flip_list, (JArray)job["so"], 1);
            if(job.ContainsKey("nmi"))
                add_flips(flip_list, (JArray)job["nmi"], 2);
            if(job.ContainsKey("irq"))
                add_flips(flip_list, (JArray)job["irq"], 3);
            flip_list.Sort((Flip a, Flip b) =>
                (int)a.getCycle() - (int)b.getCycle());
            flips = new Queue<Flip>(flip_list);
            cpu.reset();
            try {
                while(num_cycles < cycles_to_run && termination_cause == 0) {
                    cpu.Step(bus);
                }
            }
            catch(AllDone) {}
            JObject result = new JObject();
            if(last_pc_valid) result["last_pc"] = last_pc;
            result["num_cycles"] = num_cycles;
            switch(termination_cause) {
                case 0: result["termination_cause"] = "limit"; break;
                case 1: result["termination_cause"] = "brk"; break;
                case 2: result["termination_cause"] = "infinite_loop"; break;
                case 3: result["termination_cause"] = "zero_fetch"; break;
                case 4: result["termination_cause"] = "stack_fetch"; break;
                case 5: result["termination_cause"] = "vector_fetch"; break;
                case 6: result["termination_cause"] = "bad_write"; break;
                default: result["termination_cause"] = "unknown"; break;
            }
            if(cycles.Count != 0) {
                JArray result_cycles = new JArray();
                foreach(uint cycle in cycles) {
                    result_cycles.Add(cycle.ToString("X7"));
                }
                result["cycles"] = result_cycles;
            }
            switch(serial_out_fmt) {
                case OutFormat.NONE: break;
                case OutFormat.UTF8:
                    result["serial_out_data"] = "utf8:"
                        + Encoding.UTF8.GetString(serial_out.ToArray());
                    break;
                case OutFormat.BASE64:
                    result["serial_out_data"] = "base64:"
                        + Convert.ToBase64String(serial_out.ToArray());
                    break;
            }
            Console.WriteLine(result.ToString());
            return 0;
        }
    }
}

