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

   STATUS: Sort of working.  There remain some latent bugs in the interface
   that still need to be chased down.

2. [LED/Switch](rtl/spio.v)

   Used as a test of the EXBUS

   STATUS: PASS

3. [Flash](rtl/qflexpress.v)

   Load a design, configure design from flash.
   First CPU loads come from flash.

   STATUS: PASS.  However, loading a 6MB design into the flash is horribly
   slow.

4. [ICAPE Controller](https://github.com/ZipCPU/wbicapetwo)

   Status: Mostly working

   I've demonstrated the ability to read and write configuration registers.
   I haven't (yet) demonstrated the ability to restart the FPGA from a flash
   image.  This may have more to do with a broken image, however, than with
   the [ICAPE controller](rtl/wbicapetwo.v).

5. [CPU](https://github.com/ZipCPU/zipcpu)

   [CPU check](sw/board/cputest.c) will be the first program.  Other
   programs have included [Hello World](sw/board/hello.c), and an
   [MDIO register check](sw/board/mdio.c).

   Status: PASS

6. [MDIO Dump](sw/board/mdio.c)

   Can the management registers be read from the Ethernet PHY?  Do these
   registers make sense?

   STATUS: PASS.

   Given that there are two Ethernet ports on this board, and further that
   the design only connects one of these ports to logic, accessing the MDIO
   registers is an important part of knowing whether or not the ethernet
   cable is plugged into the correct port.

7. [Ping](rtl/proto/icmpecho.v)

   Can the board be "pinged"?  This includes a test of the [automatic
   ARP](rtl/proto/arp.v) handling.  The test depends upon the ability to
   load an FPGA design, but does not depend on the CPU.

   STATUS: PASS

8. DDR3 SDRAM memory

   This test will first verify that the onboard memory works with Xilinx's
   DDR3 memory controller, commonly known as "the MIG".

   Once hooked up, the MIG will be subjected to a memory test.  [Portions
   of the test have been drafted already](sw/board/memtest.c).

   Status: FAIL.  Any attempt (at present) to load the design with the
   SDRAM controller enabled within it will fail to configure the FPGA.

9. OpenSource DDR3 SDRAM memory

   If and when the MIG DDR3 SDRAM test passes, we'll move on to testing
   the [open source DDR3 memory controller](https://github.com/AngeloJacobo/DDR3_Controller).

   STATUS: Pending MIG controller success.

10. Open source place and route

    Can the design be built using all open-source tools, instead of via Vivado?

11. [SDIO](rtl/sdspi/sdio.v) _(Optional test)_

    Requires both the CPU and memory

    STATUS: Not yet tested.  (Waiting on memory.)

12. [Network debugging protocol](rtl/proto/netdebug.v) _(Optional test)_

    This will test whether or not memory can be read and/or written from an
    external host, via [specially crafted UDP/IP
    packets](https://zipcpu.com/blog/2022/08/24/protocol-design.html).
    This network packet protocol blows the doors off of the UART alternative,
    although it is a bit harder to setup and get working initially.  For
    example, both [ARP](rtl/proto/arp.v) and [ICMP](rtl/proto/icmpecho.v)
    handling have to work automatically and without CPU involvement first.

    STATUS: Not yet tested.  Pending on a software driver.

13. Network CPU Access _(Optional test)_

    Can the CPU send and receive packets?

    STATUS: Not yet tested.  Pending on a software driver.

# Current project status

This project is a work in progress.

The current project status is maintained pictorially [here, in the doc/
directory](doc/kimos-busblocks.png).  The project has been assembled, and
several of the initial component tests already pass--as noted above and [in
the diagram](doc/kimos-busblocks.png).

At present, the design is configured to use Xilinx's MIG controller.  Using
this controller, the design synthesizes, but fails to load ...  If I remove the
[SDRAM component--controller and all](autodata/sdram.txt), then the design
loads fine and the DONE LED goes high.

