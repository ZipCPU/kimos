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


## Cross-board voltages

### A

- `VCC_IO_B12` (A38, A41) = `VCC_IO_A`
- `VCC_CFG_B14` (A74, A77) = `VCC_IO_A`: QSPI Flash, Eth IO, `I2C_LS` (not 3.3V), JTAG

Has B12, B14, and CFG pins
- All `IO_B14` pins connect here

### B

- `VCC_IO_B15` (B64, B88, B140, B143) = `VCC_IO_B`
- `VCC_IO_B16` (B67, B95) = `VCC_IO_B`

Has MGT, B16, B15, and `VMON_DDR3` (B8)

- `IO_B15` pins connect here and in C (where they are NC on the FMC daughter board)
- `IO_B16` pins connect here and in C (where they are NC on the FMC daughter board)

(`VMON_1V2`?)
### C

Has pins from banks B13, B14, B15, and B16

- `VCC_IO_B13` (C76, C116, C158) = `VCC_IO_C`
  - LED2 (`VCC_LED`)
  - LED3 (`VCC_LED`)
- `VCC_OUT_C` = `VCC_2V5`

- All `IO_B13` pins connect here

- Why are the B15 pins associated with either 3.3V or the B13 power supply?
  - These should all be on B's voltage, or 1.8V as we've chosen above
  - `IO_B15_K15`, C72, `FMC_HA12_P`, NC
  - `IO_B15_M16`, C74, `FMC_HA12_N`, NC
  - `IO_B15_L8_AD3_G15_P`, C78, `FM_HA10_P`, NC
  - `IO_B15_L8_AD3_F15_N`, C80, `FM_HA10_N`, NC
  - `IO_B15_L9_AD11_J15_P`, C82, `FMC_HA08_P`, NC
  - `IO_B15_L9_AD11_J16_N`, C84, `FMC_HA08_N`, NC
  - `IO_B15_L12_MRCC_AD5_F17_P`, C88, `FMC_HA00_CC_P`, NC
  - `IO_B15_L12_MRCC_AD5_E17_N`, C90, `FMC_HA00_CC_N`, NC
  - `IO_B15_L10_AD4_E15_P`, C92, `FMC_HA06_P`, NC
  - `IO_B15_L10_AD4_E16_N`, C94, `FMC_HA06_N`, NC
  - `IO_B15_L7_AD10_H16_P`, C98, `FMC_HA05_P`, NC
  - `IO_B15_L7_AD10_G16_N`, C100, `FMC_HA05_N`, NC
  - `IO_B15_L6_D15_P`, C102, `FMC_HA03_P`, NC
  - `IO_B15_L6_VREF_D16_N`, C104, `FMC_HA03_N`, NC

- Why are the B16 pins associated with either 3.3V or 2.5V power supply?
  - These should all be on B's voltage, or 1.8V as we've chosen above
  - `IO_B16_J8`, C69, `FMC_HA13_P`, NC
  - `IO_B16_J14`, C71, `FMC_HA13_N`, NC
  - `IO_B16_L9_A9_P`, C75, `FMC_HA11_P`, NC
  - `IO_B16_L9_A8_N`, C77, `FMC_HA11_N`, NC
  - `IO_B16_L10_C9_P`, C79, `FMC_HA09_P`, NC
  - `IO_B16_L10_B9_N`, C81, `FMC_HA09_N`, NC
  - `IO_B16_L8_D9_P`, C85, `FMC_HA07_P`, NC
  - `IO_B16_L8_D8_N`, C87, `FMC_HA07_N`, NC
  - `IO_B16_L12_MRCC_E10_P`, C87, `FMC_HA01_CC_P`, NC
  - `IO_B16_L12_MRCC_D10_N`, C91, `FMC_HA01_CC_N`, NC
  - `IO_B16_L7_F9_P`, C95, `FMC_HA04_P`, NC
  - `IO_B16_L7_F8_N`, C97, `FMC_HA04_N`, NC
  - `IO_B16_L1_H9_P`, C99, `FMC_HA02_P`, NC
  - `IO_B16_L1_H8_N`, C101, `FMC_HA02_N`, NC

# Differences

- Should clk200 be LVDS?
- Serial at 1.5V?
- CKE
- CS
