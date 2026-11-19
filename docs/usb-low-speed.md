# USB low-speed descriptor read

The opt-in depth-two target is `tt_um_pinwheel_usb_low_speed_d2`. It uses the existing quad load, START, exchange, and RELEASE commands. The host loads three images for SETUP, IN, and status. The request reads eight bytes of the device descriptor at address zero, endpoint zero.

The IN image ends with the 64-bit word `5`. The core takes this instruction with a START count of 64, a released idle pin configuration, and empty queues. The receiver samples both line states, resynchronizes at J/K transitions, decodes NRZI and bit stuffing, and checks SYNC, DATA1, length, CRC16, and EOP. It holds the two RX words unpublished until it has driven the complete ACK. A rejected reply retains a fault with zero readable words. The host uses its owner tag to acknowledge the exported range before RELEASE.

The digital model uses a 24 MHz core clock, rational peer timing, an ideal two-stage sampler, and a directly connected peer that drives through one J symbol after SE0. The receiver handles peer bit periods from 15.76 to 16.24 core clocks. The public-pin harness connects the two output pads to their corresponding sense inputs and detects overlapping strong drive. These assumptions apply to the generated RTL and generic synthesis netlist replay.

## Reproduce

Run from the repository root with Lean, Python, Icarus Verilog, and Yosys on the path.

```sh
lake --no-cache build Pinwheel.Hardware.USB.Proof Pinwheel.Hardware.USB.Emit \
  Pinwheel.Hardware.USB.IN Pinwheel.Program.USB.Custody
lake env lean -DwarningAsError=true --run test/USBEmit.lean build/usb
python3 -B scripts/usb_low_speed_replay.py build/usb --prepare

(
  cd build/usb
  iverilog -g2012 -s streaming_quad_host_bridge -o rtl.vvp core.sv frontend.sv package.sv tt.sv bridge.sv
  yosys -l synth.log -p 'read_verilog -sv core.sv frontend.sv package.sv tt.sv; synth -top tt_um_pinwheel_usb_low_speed_d2 -flatten; check -assert; write_verilog -noattr gate.v'
  iverilog -g2012 -s streaming_quad_host_bridge -o gate.vvp gate.v bridge.sv
)

python3 -B scripts/usb_low_speed_replay.py build/usb --backend rtl
python3 -B scripts/usb_low_speed_replay.py build/usb --backend gate
```

The reports record the exact image words, source and netlist hashes, payload bytes, and clock edges. The peer decodes outgoing packets from the public pins before advancing to the next control-transfer stage. During a START the harness keeps the quad bus idle until BUSY clears, then reads the receipt and drains the retained data.
