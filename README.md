# Project Goals

- Demonstrate an open source DDR3 SDRAM controller on a Kintex-7 board
- Repeat the demonstration using Yosys, an open source synthesis tool,
  followed by an open source place and route tool

# Key hardware components

- UART/Debug bus/Console
  - ExBUS
  - WBConsole
- (6?) 4x+4x LEDs
- (3?) 2x BTN
- (1?) Switch
- QSPI flash
- DDR3
- GbE
- SD Card (DDR I/O)
  - Max clock = 50MHz
  - TXS02612RTWR, only one SD card connected
  - GPIO: SD Reset, SD card reset, Clock locked

Once these have been implemented, the project will be a success.  The following
additional peripherals may also be implemented as time and necessity allow.

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
- (HDMI: Not connected)

# Test priority and order

1. EXBUS

   Required to load programs for the CPU

2. LED/Switch

   Used as a test of the EXBUS

3. Flash

   Load a design, configure design from flash.

   First CPU loads come from flash.

4. CPU

   CPU check will be the first program

5. DDR3 SDRAM memory

   Memory test (requires memory, duh!)

6. SDIO

   Requires both the CPU and memory

7. Ping

   Includes automatic ARP responses.
   Can be done with only the ability to load the FPGA.

8. RDMA

   Requires ping to work.
   Requires updating exbus protocol to work over the net.  (Need ready/busy
   lines.)

# Current project status

The project is currently being assembled.  It does not yet build, not even in
a simulator.
