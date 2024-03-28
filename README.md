# Project Goals

This is a project in development.  It's basic goals are:

- Demonstrate an [open source DDR3 SDRAM
  controller](https://github.com/AngeloJacobo/DDR3_Controller) on a Kintex-7
  board

- Repeat the demonstration using Yosys, an open source synthesis tool,
  followed by an open source place and route tool

# Key hardware components

I'll be building this project on an [Enclustra KX2 daughter
board](https://www.enclustra.com/en/products/fpga-modules/mercury-kx2/),
mounted on their [Mercury+ ST1
Baseboards](https://www.enclustra.com/en/products/base-boards/mercury-st1/).
Key peripherals in this setup include:

- UART/Debug bus/Console
  - [ExBUS](rtl/exbus/exbuswb.v)
  - [WBConsole](rtl/exbus/wbconsole.v)
- [4x+4x LEDs, 2x BTNs, and no switches](rtl/spio.v)
- [QSPI flash](https://github.com/ZipCPU/qspiflash)
- [DDR3](https://github.com/AngeloJacobo/DDR3_Controller)
- [GbE](rtl/net/enetstream.v)
- [SD Card (DDR I/O)](https://github.com/ZipCPU/sdspi)
  - Max clock = 50MHz
  - TXS02612RTWR, only one SD card connected
  - GPIO wires include: SD Reset, SD card reset, Clock locked

Once these have been implemented, the project will be a success.  The following
additional peripherals may also be implemented as time and necessity allow.

- [I2C](https://github.com/ZipCPU/wbi2c)
  - RTC: ISL12020MIRZ
  - Secure EEPROM: ATSHA204A or DS28CN01U
  - Si5338 ? PCI3, Ethernet, GbE, broadcast audio, ???
  - Si570: 10MHz->1.4GHz I2C Programmable XO/VCXO
  - I2C Multiplexers: NLASB3157DFT2G--is a silicon switch (?)
- SPI?
- [SATA](https://github.com/ZipCPU/wbsata).  My SATA project isn't (currently)
  in a usable state.  Until it gets there, we won't have SATA control on this
  board.  Still, this board is a key piece of test hardware for testing the
  [SATA](https://github.com/ZipCPU/wbsata) controller.

  No, the Enclustra board doesn't come with a SATA capability.  However, I have
  an [FPGADrive](https://www.fpgadrive.com/) FMC board attached, which should
  allow SATA development.

- (2nd GbE)  This board has two Gb Ethernet ports on it.  At present, I have
  no plans for the second port.  I'm open to ideas, however.

- (Display Port?)  I've never touched the display port protocol before.
  Whether or not I can do anything with it, or even whether or not I have
  the time and priority to do so remains to be determined.

- (HDMI: Not connected).  Don't ask me why, but Enclustra never connected the
  HDMI port.  (I think they ran out of high speed IO or some such.  I'm not
  certain.)

# Test priority and order

1. [EXBUS](rtl/exbus/exwb.v)

   Required to load programs for the CPU

2. [LED/Switch](rtl/spio.v)

   Used as a test of the EXBUS

3. [Flash](rtl/qflexpress.v)

   Load a design, configure design from flash.

   First CPU loads come from flash.

4. [CPU](https://github.com/ZipCPU/zipcpu)

   CPU check will be the first program

5. DDR3 SDRAM memory

   Memory test (requires memory, duh!)

   This test will first run with Xilinx's DDR3 memory controller.  If and when
   that test passes, we'll move on to testing the [open source DDR3 memory
   controller]().

6. [SDIO](rtl/sdspi/sdio.v)

   Requires both the CPU and memory

7. [Ping](rtl/proto/icmpecho.v)

   Includes [automatic ARP](rtl/proto/arp.v) handling.
   Can be done with only the ability to load the FPGA.

8. [Remote/network DMA](rtl/proto/netdebug.v)

   This will test whether or not memory can be read and/or written from an
   external host, via [specially crafted UDP/IP
   packets](https://zipcpu.com/blog/2022/08/24/protocol-design.html).
   This network packet protocol blows the doors off of the UART alternative,
   although it is a bit harder to setup and get working initially.  For
   example, both [ARP](rtl/proto/arp.v) and [ICMP](rtl/proto/icmpecho.v)
   handling have to work automatically and without CPU involvement first.

   This will also require updating the [(new) exbus](rtl/exbus) protocol so
   that it can work over the net.  This will primarily involve adding
   ready/busy handshaking signals throughout--signals that aren't really
   needed with UART.  (The UART version only checks valid on incoming bytes.)
   It'll also need signals to know when a packet is complete, and so can be
   sent out.

# Current project status

The current project status is maintained pictorially [here, in the doc/
directory](doc/kimos-busblocks.png).  The project has been assembled, and
several of the key tests already pass--in simulation only.  The project can
also be synthesized/implemented, and timing passes.  The next step in this
project will be to place it onto the board itself, to see if it still works.

(At present, the design is configured to use Xilinx's MIG controller.  Using
this controller, the design synthesizes, but fails to load ...  If I remove the
SDRAM component--controller and all, then the design loads and the DONE LED
goes high.  Like I said, this project is a work in progress.)
