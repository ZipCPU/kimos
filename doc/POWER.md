# Board power supplies and jumper settings

Baseboard adjustable voltages
- `VCC_OUT_A`	(Set by daughter board to 2.5V)
- `VCC_OUT_B`	(Set by daughter board to 1.8V)
- `VCC_IO_A`	-- Sets the daughter board voltage, `VCC_CFG_B14`
  - Controls Xilinx startup voltage, Bank 14, flash, ehternet,
    I2C level shifter, FTDI status level shifter(s)
  - Supports 1.8V or 2.5-3.3V according to schematic sheet
  - XDC file has this set at 1.8V
  - Controls BTN0#, BTN1#, Anios IO #0
  - Via lvl shift: POR#, SRST#, FTDI to flash, FTDI to UART, FTDI to JTAG, VCC_OSC100, Micro SD card detect, MIPI, `I2C_S??_FPGA`, FPGA to 3.3V SD, FPGA to 3.3V DP, HDMI hotplug, 
- `VCC_IO_B`	-- Sets the daughter board voltage, `VCC_IO_B16` and `VCC_IO_B15`
  - Schematic says `VCC_IO_B16` can be anywhere from 1.8v-3.3v, controls FPGA Bank 16
  - Schematic says `VCC_IO_B15` can be anywhere from 1.0v-3.3v, controls bank 15
  - Controls `VCC_FMC_ADJ`
- `VCC_IO_C`	-- Sets daughter voltage `VCC_IO_B13`
  - Supports anything from 1.0v-3.3v according to schematic
  - Controls ANIOS IO #1

Daughter-board voltages

- `VCC_INT` = 1.0V
- `VCC_1V2` = 1.2V
- `VCC_DDR3` is adjustable
- `VCC_1V8` = 1.8V
- `VCC_2V0` = 2.0V
- `VCC_2V5` = 2.5V
- `VCC_3V3` = 3.3V

- `PWR_EN` (low=disabled, floating/3.3=enabled)
- `PWR_GOOD` (0=not okay, 3.3V = okay)


FMC Drive (SATA) board voltages
- C37=12V, driven by `VCC_MAIN` on baseboard
- C39=3.3V
- D32=3P3AUX
- D36,38,40 = V3.3
- D1=V3.3 = Power Good
- G39,H40 = VADJ
- C30,C31: I2C is pulled to 3.3V (Yes, driven from `VCC_IO_A`, level shifted to 3.3V)
- J40, K40 ? (No connect on FMC drive board, so ... `VCCC_FMC_VIOB` has no effect
- `VCC_FMC_ADJ` is driven by `VCC_IO_B`


## Jumper settings

First, let's pick the voltage choices we can pick:

- `VCC_OUT_A`	(Set by daughter board to 2.5V)
- `VCC_OUT_B`	(Set by daughter board to 1.8V)
- `VCC_IO_A` should be set to 1.8V (as per XDC)
- `VCC_IO_B` can be set to ... anything above 1.8V.  We'll set it to 1.8V
- `VCC_IO_C` can be set to ... anything between 1.0v and 3.3v.  We'll set
  it to 1.2V, simply because we don't really have any other choices left.

From here, we can select the following jumper settings

- 5-6 will connect `VCC_IO_A` to `VCC_OUT_B` (i.e. 1.8V)
  - CHECK
- 9-10 will set `VCC_IO_B` to `VCC_OUT_B` (1.8V)
  - CHECK (This is a change to my original setup ...)
- 11-13 will connect `VCC_1.2` to `VCC_IO_C`
  - At this point, there don't seem to be any other choices ...

<!-- - 12-14 will connect `VCC_IO_C` to `VCC_FMC_VIOB`	(Unused) -->
<!-- 12-10 will set `VCC_IO_B` to `VCC_IO_C`, and thus to 1.2V (Unacceptable)-->

