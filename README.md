# Project Goals

- Demonstrate an open source DDR3 SDRAM controller on a Kintex-7 board
- Repeat the demonstration using an open source synthesis tool, followed by an
  open source place and route tool

# Key hardware components

- UART/Debug bus/Console
  - ExBUS
  - WBConsole
- (6?) 4x+4x LEDs
- (3?) 2x BTN
- (1?) Switch
- DDR3
- QSPI flash
- GbE
- SD Card (DDR I/O)
  - Max clock = 50MHz
  - TXS02612RTWR, only one SD card connected
  - GPIO: SD Reset, SD card reset, Clock locked

Once these have been implemented, we'll have success.  The following
additional peripherals may also be implemented if time is available.

- I2C
  - RTC: ISL12020MIRZ
  - Secure EEPROM: ATSHA204A or DS28CN01U
  - Si5338 ? PCI3, Ethernet, GbE, broadcast audio, ???
  - Si570: 10MHz->1.4GHz I2C Programmable XO/VCXO
  - I2C Multiplexers: NLASB3157DFT2G--is a silicon switch (?)
- SPI?
- SATA
- (2nd GbE)
- (Display Port?)
- (HDMI: Doesn't work)
