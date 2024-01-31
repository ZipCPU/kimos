################################################################################
################################################################################
set_property CFGBVS GND [current_design]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 22 [current_design]
set_property BITSTREAM.CONFIG.OVERTEMPPOWERDOWN ENABLE [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN PULLNONE [current_design]

# set_property -dict {PACKAGE_PIN AD24  IOSTANDARD LVCMOS18  } [get_ports {CLK_100_CAL}]
set_property DCI_CASCADE {32} [get_iobanks 34]
set_property INTERNAL_VREF 0.675 [get_iobanks 33]
set_property INTERNAL_VREF 0.750 [get_iobanks 33]

## Clocks
## {{{
# 100MHz single ended input clock
set_property -dict {PACKAGE_PIN AA4 IOSTANDARD SSTL15  } [get_ports {i_clk}];
create_clock -name i_clk -period 10.000 [get_ports i_clk];

## set_property DIFF_TERM FALSE [get_ports CLK200_N];
## set_property DIFF_TERM FALSE [get_ports CLK200_P];
## set_property -dict {PACKAGE_PIN AC11  IOSTANDARD DIFF_SSTL15} [get_ports {CLK200_N}];
## set_property -dict {PACKAGE_PIN AB11  IOSTANDARD DIFF_SSTL15} [get_ports {CLK200_P}];
## }}}

## LEDs
## {{{
## set_property SLEW SLOW [get_ports LED0_N];
## set_property SLEW SLOW [get_ports LED1_N];
## set_property SLEW SLOW [get_ports LED2_N];
## set_property SLEW SLOW [get_ports LED3_N];
set_property -dict {SLEW SLOW PACKAGE_PIN U9  IOSTANDARD SSTL15 } [get_ports {o_led[0]}]; # LED0_N
set_property -dict {SLEW SLOW PACKAGE_PIN V12 IOSTANDARD SSTL15 } [get_ports {o_led[1]}]; # LED1_N
set_property -dict {SLEW SLOW PACKAGE_PIN V13 IOSTANDARD SSTL15 } [get_ports {o_led[2]}]; # LED2_N
set_property -dict {SLEW SLOW PACKAGE_PIN W13 IOSTANDARD SSTL15 } [get_ports {o_led[3]}]; # LED3_N

## Baseboard LEDs
set_property -dict {SLEW SLOW PACKAGE_PIN F22   IOSTANDARD LVCMOS18  } [get_ports { o_led[4] }]; # GPIO0_LED0_N
set_property -dict {SLEW SLOW PACKAGE_PIN E23   IOSTANDARD LVCMOS18  } [get_ports { o_led[5] }]; # GPIO1_LED1_N

## C142 LED2 (ST1)
## C144 LED3 (ST1)
## }}}

## UART
## {{{
set_property -dict {PACKAGE_PIN B20   IOSTANDARD LVCMOS18  } [get_ports {i_wbu_uart_rx}]; # UART_RX
set_property -dict {PACKAGE_PIN A20   IOSTANDARD LVCMOS18  } [get_ports {o_wbu_uart_tx}]; # UART_TX
## }}}

## Buttons
## {{{
set_property -dict {PACKAGE_PIN C22   IOSTANDARD LVCMOS18    } [get_ports {i_btn}]; # (Not in TCL)
## # set_property -dict {PACKAGE_PIN AD23  IOSTANDARD LVCMOS18    } [get_ports {i_btn[1]}]; # (Not in TCL)
## IO B14 L7  C22  N / A100 / BTN0#
## IO B12 L16 AD23 P / A58  / BTN1#

## Reset button
# set_property -dict {PACKAGE_PIN AD9   IOSTANDARD SSTL15    } [get_ports {i_reset_btn}]; # Rst_N
## }}}

## I2C
## {{{
## I2C #1: I2C_SCL and I2C_SDA
## {{{
## Connects to FTDI, Si53388B, AniosIO #1, HDMI Redriver
# set_property SLEW SLOW [get_ports I2C_INT_N_LS];
# set_property SLEW SLOW [get_ports io_sda];
# set_property SLEW SLOW [get_ports io_scl];
# set_property -dict {PACKAGE_PIN AC18  IOSTANDARD SSTL15    } [get_ports {I2C_INT_N_LS}];
# set_property -dict {PACKAGE_PIN L23   IOSTANDARD LVCMOS18  } [get_ports {io_scl}];
# set_property -dict {PACKAGE_PIN C24   IOSTANDARD LVCMOS18  } [get_ports {io_sda}];
## }}}
## I2C #2: I2C_SCL_FPGA and I2C_SDA_FPGA
## {{{
## Connects to FMC, AniosIO #2, Reference oscillator control, HDMI, MIPI, SFP+
# set_property -dict {PACKAGE_PIN W25   IOSTANDARD LVCMOS18  } [get_ports {io_i2c_fpga_scl}];	## IO Bank B12, A55
# set_property -dict {PACKAGE_PIN W26   IOSTANDARD LVCMOS18  } [get_ports {io_i2c_fpga_sda}];	## IO Bank B12, A57
## }}}

## }}}

## HDMI (Not supported.  The KX2 wires aren't connected)
## {{{
# set_property -dict {PACKAGE_PIN U26   IOSTANDARD LVCMOS18  } [get_ports {HDMI_HPD}];
# set_property -dict {PACKAGE_PIN R20   IOSTANDARD LVCMOS18  } [get_ports {HDMI_CLK_N}];
# set_property -dict {PACKAGE_PIN T20   IOSTANDARD LVCMOS18  } [get_ports {HDMI_CLK_P}];
## IO B12 L4 U26 P / A61 / HDMI_HPD  (ST1)

## C45, C47, C51, C53, C57, and C59 don't appear to connect to the FPGA.  Is this correct?
## C45 / HDMI_D0_P (ST1)
## C47 / HDMI_D0_N (ST1)
## C51 / HDMI_D1_P (ST1)
## C53 / HDMI_D1_N (ST1)
## C57 / HDMI_D2_P (ST1)
## C59 / HDMI_D2_N (ST1)
## }}}

## Display port
## {{{
## Four lanes, an AUX channel, and an HPD channel
## Bank 115, 1.2V
# set_property -dict {PACKAGE_PIN P2  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_p[0]}];
# set_property -dict {PACKAGE_PIN P1  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_n[0]}];
# set_property -dict {PACKAGE_PIN M2  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_p[1]}];
# set_property -dict {PACKAGE_PIN M1  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_n[1]}];
##
# set_property -dict {PACKAGE_PIN P2  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_p[2]}];
# set_property -dict {PACKAGE_PIN P1  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_n[2]}];
# set_property -dict {PACKAGE_PIN M2  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_p[3]}];
# set_property -dict {PACKAGE_PIN M1  IOSTANDARD DIFF_SSTL12  } [get_ports { o_dp_n[3]}];
##
## Bank 14, VCCO=VCC_CFG_B14=1.8v, Same as FLASH, Eth0,Eth1
# set_property -dict { PACKAGE_PIN D23   IOSTANDARD LVCMOS18  } [get_ports {i_dp_aux}];
# set_property -dict { PACKAGE_PIN D24   IOSTANDARD LVCMOS18  } [get_ports {o_dp_aux}];
# set_property -dict { PACKAGE_PIN E21   IOSTANDARD LVCMOS18  } [get_ports {o_dp_aux_oe}];
# set_property -dict { PACKAGE_PIN E22   IOSTANDARD LVCMOS18  } [get_ports {i_dp_hpd}];
## }}}

## Gyro SPI Controller
## {{{
## 600ms reset recovery time
## Reset must be low for 10us (minimum) to ensure proper reset
# set_property -dict {PACKAGE_PIN K20   IOSTANDARD LVCMOS18  } [get_ports {o_gyro_reset_n}];
# set_property -dict {PACKAGE_PIN M17   IOSTANDARD LVCMOS18  } [get_ports {o_gyro_csn  }];
# set_property -dict {PACKAGE_PIN L18   IOSTANDARD LVCMOS18  } [get_ports {o_gyro_sck   }];
# set_property -dict {PACKAGE_PIN L17   IOSTANDARD LVCMOS18  } [get_ports {i_gyro_miso  }];
# set_property -dict {PACKAGE_PIN K18   IOSTANDARD LVCMOS18  } [get_ports {o_gyro_mosi  }];
##
## GPIO Digital I/O pins
# set_property -dict {PACKAGE_PIN K16   IOSTANDARD LVCMOS18  } [get_ports {io_gyro_dio[0]}];	# These should be output by default
# set_property -dict {PACKAGE_PIN K17   IOSTANDARD LVCMOS18  } [get_ports {io_gyro_dio[1]}];
# set_property -dict {PACKAGE_PIN J18   IOSTANDARD LVCMOS18  } [get_ports {io_gyro_dio[2]}];
# set_property -dict {PACKAGE_PIN J19   IOSTANDARD LVCMOS18  } [get_ports {io_gyro_dio[3]}];
## }}}

## PSU A/D SPI controller
## {{{
# set_property -dict {PACKAGE_PIN H19   IOSTANDARD LVCMOS18  } [get_ports {o_psu_csn }];
# set_property -dict {PACKAGE_PIN G20   IOSTANDARD LVCMOS18  } [get_ports {o_psu_sck }];
# set_property -dict {PACKAGE_PIN D19   IOSTANDARD LVCMOS18  } [get_ports {i_psu_miso}];
# set_property -dict {PACKAGE_PIN D20   IOSTANDARD LVCMOS18  } [get_ports {o_psu_mosi}];
##
# set_property -dict {PACKAGE_PIN G17   IOSTANDARD LVCMOS18  } [get_ports {o_psu_reset_n}];
## }}}

## TC (Thermocouple) SPI controller
## {{{
# set_property -dict {PACKAGE_PIN B16   IOSTANDARD LVCMOS18  } [get_ports { o_tc_sck   }];
# set_property -dict {PACKAGE_PIN B17   IOSTANDARD LVCMOS18  } [get_ports { o_tc_mosi  }];
# set_property -dict {PACKAGE_PIN A17   IOSTANDARD LVCMOS18  } [get_ports { i_tc_miso  }];
# set_property -dict {PACKAGE_PIN E18   IOSTANDARD LVCMOS18  } [get_ports { o_tc_csn[0]}];		## IO Bank B15
# set_property -dict {PACKAGE_PIN D18   IOSTANDARD LVCMOS18  } [get_ports { o_tc_csn[1]}];		## IO Bank B15
# set_property -dict {PACKAGE_PIN C19   IOSTANDARD LVCMOS18  } [get_ports { o_tc_csn[2]}];
# set_property -dict {PACKAGE_PIN B19   IOSTANDARD LVCMOS18  } [get_ports { o_tc_csn[3]}];
# set_property -dict {PACKAGE_PIN A18   IOSTANDARD LVCMOS18  } [get_ports { o_tc_csn[4]}];
# set_property -dict {PACKAGE_PIN A19   IOSTANDARD LVCMOS18  } [get_ports { o_tc_csn[5]}];
## }}}

## KX2 IO Bank #0
## {{{
# set_property -dict {PACKAGE_PIN V23   IOSTANDARD LVCMOS18  } [get_ports {i_ltc_clkout}];
# set_property -dict {PACKAGE_PIN V24   IOSTANDARD LVCMOS18  } [get_ports {o_ltc_pll}]; ## IO_B12_L3_V24_N
# set_property -dict {PACKAGE_PIN Y21   IOSTANDARD LVCMOS18  } [get_ports {IO0_D15_N}];
# set_property -dict {PACKAGE_PIN AD21  IOSTANDARD LVCMOS18  } [get_ports {IO0_D16_P}];
# set_property -dict {PACKAGE_PIN AE21  IOSTANDARD LVCMOS18  } [get_ports {IO0_D17_N}];
# set_property -dict {PACKAGE_PIN AE22  IOSTANDARD LVCMOS18  } [get_ports { o_en_20v  }];
# set_property -dict {PACKAGE_PIN AF22  IOSTANDARD LVCMOS18  } [get_ports { o_en_6p5v }];
# set_property -dict {PACKAGE_PIN V21   IOSTANDARD LVCMOS18  } [get_ports {IO0_D20_P}];
# set_property -dict {PACKAGE_PIN W21   IOSTANDARD LVCMOS18  } [get_ports {IO0_D21_N}];
set_property -dict {PACKAGE_PIN U24   IOSTANDARD LVCMOS18  } [get_ports {i_water_ingress}];	# IO_B12_L2_U24_P
set_property -dict {PACKAGE_PIN U25   IOSTANDARD LVCMOS18  } [get_ports {i_housing_interlock}];	# IO_B12_L2_U25_N
# set_property -dict {PACKAGE_PIN AC24  IOSTANDARD LVCMOS18  } [get_ports {IO0_CLK1_N}];
# set_property -dict {PACKAGE_PIN AC23  IOSTANDARD LVCMOS18  } [get_ports {IO0_CLK0_P}];
## }}}

## KX2 IO Bank #1
## {{{
# set_property -dict {PACKAGE_PIN P23   IOSTANDARD LVCMOS18  } [get_ports {IO1_D0_P}];
# set_property -dict {PACKAGE_PIN N23   IOSTANDARD LVCMOS18  } [get_ports {IO1_D1_N}];
# set_property -dict {PACKAGE_PIN T18   IOSTANDARD LVCMOS18  } [get_ports {IO1_D2_P}];
# set_property -dict {PACKAGE_PIN T19   IOSTANDARD LVCMOS18  } [get_ports {IO1_D3_N}];
# set_property -dict {PACKAGE_PIN N19   IOSTANDARD LVCMOS18  } [get_ports {IO1_D4_P}];
# set_property -dict {PACKAGE_PIN M20   IOSTANDARD LVCMOS18  } [get_ports {IO1_D5_N}];
# set_property -dict {PACKAGE_PIN T24   IOSTANDARD LVCMOS18  } [get_ports {IO1_D6_P}];
# set_property -dict {PACKAGE_PIN T25   IOSTANDARD LVCMOS18  } [get_ports {IO1_D7_N}];
# set_property -dict {PACKAGE_PIN R16   IOSTANDARD LVCMOS18  } [get_ports {IO1_D8_P}];
# set_property -dict {PACKAGE_PIN R17   IOSTANDARD LVCMOS18  } [get_ports {IO1_D9_N}];
# set_property -dict {PACKAGE_PIN N18   IOSTANDARD LVCMOS18  } [get_ports {IO1_D10_P}];
# set_property -dict {PACKAGE_PIN M19   IOSTANDARD LVCMOS18  } [get_ports {IO1_D11_N}];
# set_property -dict {PACKAGE_PIN T22   IOSTANDARD LVCMOS18  } [get_ports {IO1_D12_P}];
# set_property -dict {PACKAGE_PIN T23   IOSTANDARD LVCMOS18  } [get_ports {IO1_D13_N}];
# set_property -dict {PACKAGE_PIN P19   IOSTANDARD LVCMOS18  } [get_ports {IO1_D14_P}];
# set_property -dict {PACKAGE_PIN P20   IOSTANDARD LVCMOS18  } [get_ports {IO1_D15_N}];
# set_property -dict {PACKAGE_PIN P24   IOSTANDARD LVCMOS18  } [get_ports {IO1_D16_P}];
# set_property -dict {PACKAGE_PIN N24   IOSTANDARD LVCMOS18  } [get_ports {IO1_D17_N}];
# set_property -dict {PACKAGE_PIN R18   IOSTANDARD LVCMOS18  } [get_ports {IO1_D18_P}];
# set_property -dict {PACKAGE_PIN P18   IOSTANDARD LVCMOS18  } [get_ports {IO1_D19_N}];
# set_property -dict {PACKAGE_PIN U17   IOSTANDARD LVCMOS18  } [get_ports {IO1_D20_P}];
# set_property -dict {PACKAGE_PIN T17   IOSTANDARD LVCMOS18  } [get_ports {IO1_D21_N}];
# set_property -dict {PACKAGE_PIN P16   IOSTANDARD LVCMOS18  } [get_ports {IO1_D22_P}];
# set_property -dict {PACKAGE_PIN N17   IOSTANDARD LVCMOS18  } [get_ports {IO1_D23_N}];
# set_property -dict {PACKAGE_PIN R23   IOSTANDARD LVCMOS18  } [get_ports {IO1_CLK1_N}];
# set_property -dict {PACKAGE_PIN R22   IOSTANDARD LVCMOS18  } [get_ports {IO1_CLK0_P}];
## }}}

## FMC (IO Bank #2?)
## {{{
# set_property -dict {PACKAGE_PIN G4    IOSTANDARD LVCMOS18  } [get_ports {i_sata_p}];		## IO Bank MGT
# set_property -dict {PACKAGE_PIN G3    IOSTANDARD LVCMOS18  } [get_ports {i_sata_n}];		## IO Bank MGT
# set_property -dict {PACKAGE_PIN F2    IOSTANDARD LVCMOS18  } [get_ports {o_sata_p}];		## IO Bank MGT
# set_property -dict {PACKAGE_PIN F1    IOSTANDARD LVCMOS18  } [get_ports {o_sata_n}];		## IO Bank MGT
# set_property -dict {PACKAGE_PIN D19   IOSTANDARD LVCMOS18  } [get_ports {o_disable_ssdb}];	## IO Bank B15
# set_property -dict {PACKAGE_PIN K6    IOSTANDARD LVCMOS18  } [get_ports {i_fmc_refclk_p}];	## IO Bank MGT
# set_property -dict {PACKAGE_PIN K5    IOSTANDARD LVCMOS18  } [get_ports {i_fmc_refclk_n}];	## IO Bank MGT

# set_property -dict {PACKAGE_PIN H8    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA02_N}];
# set_property -dict {PACKAGE_PIN H9    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA02_P}];
# set_property -dict {PACKAGE_PIN D16   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA03_N}];
# set_property -dict {PACKAGE_PIN D15   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA03_P}];
# set_property -dict {PACKAGE_PIN F8    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA04_N}];
# set_property -dict {PACKAGE_PIN F9    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA04_P}];
# set_property -dict {PACKAGE_PIN G16   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA05_N}];
# set_property -dict {PACKAGE_PIN H16   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA05_P}];
# set_property -dict {PACKAGE_PIN E16   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA06_N}];
# set_property -dict {PACKAGE_PIN E15   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA06_P}];
# set_property -dict {PACKAGE_PIN D8    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA07_N}];
# set_property -dict {PACKAGE_PIN D9    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA07_P}];
# set_property -dict {PACKAGE_PIN J16   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA08_N}];
# set_property -dict {PACKAGE_PIN J15   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA08_P}];
# set_property -dict {PACKAGE_PIN B9    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA09_N}];
# set_property -dict {PACKAGE_PIN C9    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA09_P}];
# set_property -dict {PACKAGE_PIN F15   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA10_N}];
# set_property -dict {PACKAGE_PIN G15   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA10_P}];
# set_property -dict {PACKAGE_PIN A8    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA11_N}];
# set_property -dict {PACKAGE_PIN A9    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA11_P}];
# set_property -dict {PACKAGE_PIN M16   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA12_N}];
# set_property -dict {PACKAGE_PIN K15   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA12_P}];
# set_property -dict {PACKAGE_PIN J14   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA13_N}];
# set_property -dict {PACKAGE_PIN J8    IOSTANDARD LVCMOS18  } [get_ports {FMC_HA13_P}];
# set_property -dict {PACKAGE_PIN C16   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA05_P}];
# set_property -dict {PACKAGE_PIN C18   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA06_N}];
# set_property -dict {PACKAGE_PIN C17   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA06_P}];
# set_property -dict {PACKAGE_PIN J20   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA13_N}];
# set_property -dict {PACKAGE_PIN L20   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA14_N}];
# set_property -dict {PACKAGE_PIN L19   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA14_P}];
# set_property -dict {PACKAGE_PIN F20   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA15_N}];
# set_property -dict {PACKAGE_PIN G19   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA15_P}];
# set_property -dict {PACKAGE_PIN E20   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA16_N}];
# set_property -dict {PACKAGE_PIN F19   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA16_P}];
# set_property -dict {PACKAGE_PIN H12   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA26_P}];
# set_property -dict {PACKAGE_PIN H11   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA27_N}];
# set_property -dict {PACKAGE_PIN E17   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA00_CC_N}];
# set_property -dict {PACKAGE_PIN F17   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA00_CC_P}];
# set_property -dict {PACKAGE_PIN D10   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA01_CC_N}];
# set_property -dict {PACKAGE_PIN E10   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA01_CC_P}];
# set_property -dict {PACKAGE_PIN U20   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA17_N}];
# set_property -dict {PACKAGE_PIN U19   IOSTANDARD LVCMOS18  } [get_ports {FMC_HA17_P}];
# set_property -dict {PACKAGE_PIN F18   IOSTANDARD LVCMOS18  } [get_ports {FMC_LA01_CC_N}];
# set_property -dict {PACKAGE_PIN H18   IOSTANDARD LVCMOS18  } [get_ports {FMC_CLK0_M2C_N}];
# set_property -dict {PACKAGE_PIN H17   IOSTANDARD LVCMOS18  } [get_ports {FMC_CLK0_M2C_P}];
## }}}

# set_property -dict {PACKAGE_PIN W20   IOSTANDARD LVCMOS18  } [get_ports {i_ltc_pgood}];

## KX2 IO Bank #3
## {{{
# set_property -dict {PACKAGE_PIN Y23   IOSTANDARD LVCMOS18  } [get_ports {IO3_D0_P}];
# set_property -dict {PACKAGE_PIN AA24  IOSTANDARD LVCMOS18  } [get_ports {IO3_D1_N}];
# set_property -dict {PACKAGE_PIN AB26  IOSTANDARD LVCMOS18  } [get_ports {IO3_D2_P}];
# set_property -dict {PACKAGE_PIN AC26  IOSTANDARD LVCMOS18  } [get_ports {IO3_D3_N}];
# set_property -dict {PACKAGE_PIN AA25  IOSTANDARD LVCMOS18  } [get_ports {IO3_D4_P}];
# set_property -dict {PACKAGE_PIN AB25  IOSTANDARD LVCMOS18  } [get_ports {IO3_D5_N}];
# set_property -dict {PACKAGE_PIN U21   IOSTANDARD LVCMOS18  } [get_ports {IO3_D6_P}];
# set_property -dict {PACKAGE_PIN Y20   IOSTANDARD LVCMOS18  } [get_ports {IO3_D7_N}];
## }}}

## KX2 IO Bank #4
## {{{
# set_property -dict {PACKAGE_PIN Y25   IOSTANDARD LVCMOS18  } [get_ports {IO4_D0_P}];
# set_property -dict {PACKAGE_PIN Y26   IOSTANDARD LVCMOS18  } [get_ports {IO4_D1_N}];
## }}}

## MIPI
## {{{
# set_property -dict {PACKAGE_PIN P25   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_D0_N}];
# set_property -dict {PACKAGE_PIN R25   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_D0_P}];
# set_property -dict {PACKAGE_PIN L24   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_D1_N}];
# set_property -dict {PACKAGE_PIN M24   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_D1_P}];
# set_property -dict {PACKAGE_PIN P21   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_CLK_N}];
# set_property -dict {PACKAGE_PIN R21   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_CLK_P}];
# set_property -dict {PACKAGE_PIN L25   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_CLK_D0LP_N}];
# set_property -dict {PACKAGE_PIN M25   IOSTANDARD LVCMOS18  } [get_ports {MIPI0_CLK_D0LP_P}];
# set_property -dict {PACKAGE_PIN M26   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_D0_N}];
# set_property -dict {PACKAGE_PIN N26   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_D0_P}];
# set_property -dict {PACKAGE_PIN M22   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_D1_N}];
# set_property -dict {PACKAGE_PIN M21   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_D1_P}];
# set_property -dict {PACKAGE_PIN N22   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_CLK_N}];
# set_property -dict {PACKAGE_PIN N21   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_CLK_P}];
# set_property -dict {PACKAGE_PIN P26   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_CLK_D0LP_N}];
# set_property -dict {PACKAGE_PIN R26   IOSTANDARD LVCMOS18  } [get_ports {MIPI1_CLK_D0LP_P}];
## }}}

## DDR3 MEMORY
## {{{
# set_property SLEW SLOW [get_ports DDR3_VSEL]
# set_property -dict {PACKAGE_PIN AD11  IOSTANDARD SSTL15    } [get_ports {DDR3_BA[0]}];
# set_property -dict {PACKAGE_PIN AA10  IOSTANDARD SSTL15    } [get_ports {DDR3_BA[1]}];
# set_property -dict {PACKAGE_PIN AF12  IOSTANDARD SSTL15    } [get_ports {DDR3_BA[2]}];
# set_property -dict {PACKAGE_PIN AA2   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[0]}];
# set_property -dict {PACKAGE_PIN Y2    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[1]}];
# set_property -dict {PACKAGE_PIN AB2   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[2]}];
# set_property -dict {PACKAGE_PIN V1    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[3]}];
# set_property -dict {PACKAGE_PIN Y1    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[4]}];
# set_property -dict {PACKAGE_PIN W1    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[5]}];
# set_property -dict {PACKAGE_PIN AC2   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[6]}];
# set_property -dict {PACKAGE_PIN V2    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[7]}];
# set_property -dict {PACKAGE_PIN W3    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[8]}];
# set_property -dict {PACKAGE_PIN V3    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[9]}];
# set_property -dict {PACKAGE_PIN AE11  IOSTANDARD SSTL15    } [get_ports {DDR3_A[0]}];
# set_property -dict {PACKAGE_PIN AF9   IOSTANDARD SSTL15    } [get_ports {DDR3_A[1]}];
# set_property -dict {PACKAGE_PIN AD10  IOSTANDARD SSTL15    } [get_ports {DDR3_A[2]}];
# set_property -dict {PACKAGE_PIN AB10  IOSTANDARD SSTL15    } [get_ports {DDR3_A[3]}];
# set_property -dict {PACKAGE_PIN AA9   IOSTANDARD SSTL15    } [get_ports {DDR3_A[4]}];
# set_property -dict {PACKAGE_PIN AB9   IOSTANDARD SSTL15    } [get_ports {DDR3_A[5]}];
# set_property -dict {PACKAGE_PIN AA8   IOSTANDARD SSTL15    } [get_ports {DDR3_A[6]}];
# set_property -dict {PACKAGE_PIN AC8   IOSTANDARD SSTL15    } [get_ports {DDR3_A[7]}];
# set_property -dict {PACKAGE_PIN AA7   IOSTANDARD SSTL15    } [get_ports {DDR3_A[8]}];
# set_property -dict {PACKAGE_PIN AE8   IOSTANDARD SSTL15    } [get_ports {DDR3_A[9]}];
# set_property -dict {PACKAGE_PIN AA13  IOSTANDARD SSTL15    } [get_ports {DDR3_CKE[0]}];
# set_property -dict {PACKAGE_PIN AC12  IOSTANDARD DIFF_SSTL15} [get_ports {DDR3_CK_N[0]}];
# set_property -dict {PACKAGE_PIN AB12  IOSTANDARD DIFF_SSTL15} [get_ports {DDR3_CK_P[0]}];
# set_property -dict {PACKAGE_PIN U1    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[10]}];
# set_property -dict {PACKAGE_PIN U7    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[11]}];
# set_property -dict {PACKAGE_PIN U6    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[12]}];
# set_property -dict {PACKAGE_PIN V4    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[13]}];
# set_property -dict {PACKAGE_PIN V6    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[14]}];
# set_property -dict {PACKAGE_PIN U2    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[15]}];
# set_property -dict {PACKAGE_PIN AE3   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[16]}];
# set_property -dict {PACKAGE_PIN AE6   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[17]}];
# set_property -dict {PACKAGE_PIN AF3   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[18]}];
# set_property -dict {PACKAGE_PIN AD1   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[19]}];
# set_property -dict {PACKAGE_PIN AE1   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[20]}];
# set_property -dict {PACKAGE_PIN AE2   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[21]}];
# set_property -dict {PACKAGE_PIN AF2   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[22]}];
# set_property -dict {PACKAGE_PIN AE5   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[23]}];
# set_property -dict {PACKAGE_PIN AD5   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[24]}];
# set_property -dict {PACKAGE_PIN Y5    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[25]}];
# set_property -dict {PACKAGE_PIN AC6   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[26]}];
# set_property -dict {PACKAGE_PIN Y6    IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[27]}];
# set_property -dict {PACKAGE_PIN AB4   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[28]}];
# set_property -dict {PACKAGE_PIN AD6   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[29]}];
# set_property -dict {PACKAGE_PIN AB6   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[30]}];
# set_property -dict {PACKAGE_PIN AC3   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[31]}];
# set_property -dict {PACKAGE_PIN AD16  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[32]}];
# set_property -dict {PACKAGE_PIN AE17  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[33]}];
# set_property -dict {PACKAGE_PIN AF15  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[34]}];
# set_property -dict {PACKAGE_PIN AF20  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[35]}];
# set_property -dict {PACKAGE_PIN AD15  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[36]}];
# set_property -dict {PACKAGE_PIN AF14  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[37]}];
# set_property -dict {PACKAGE_PIN AE15  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[38]}];
# set_property -dict {PACKAGE_PIN AF17  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[39]}];
# set_property -dict {PACKAGE_PIN AA14  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[40]}];
# set_property -dict {PACKAGE_PIN AA15  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[41]}];
# set_property -dict {PACKAGE_PIN AC14  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[42]}];
# set_property -dict {PACKAGE_PIN AD14  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[43]}];
# set_property -dict {PACKAGE_PIN AB14  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[44]}];
# set_property -dict {PACKAGE_PIN AB15  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[45]}];
# set_property -dict {PACKAGE_PIN AA17  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[46]}];
# set_property -dict {PACKAGE_PIN AA18  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[47]}];
# set_property -dict {PACKAGE_PIN AB20  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[48]}];
# set_property -dict {PACKAGE_PIN AD19  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[49]}];
# set_property -dict {PACKAGE_PIN AC19  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[50]}];
# set_property -dict {PACKAGE_PIN AA20  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[51]}];
# set_property -dict {PACKAGE_PIN AA19  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[52]}];
# set_property -dict {PACKAGE_PIN AC17  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[53]}];
# set_property -dict {PACKAGE_PIN AD18  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[54]}];
# set_property -dict {PACKAGE_PIN AB17  IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[55]}];
# set_property -dict {PACKAGE_PIN W15   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[56]}];
# set_property -dict {PACKAGE_PIN W16   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[57]}];
# set_property -dict {PACKAGE_PIN W14   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[58]}];
# set_property -dict {PACKAGE_PIN V16   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[59]}];
# set_property -dict {PACKAGE_PIN V19   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[60]}];
# set_property -dict {PACKAGE_PIN V17   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[61]}];
# set_property -dict {PACKAGE_PIN V18   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[62]}];
# set_property -dict {PACKAGE_PIN Y17   IOSTANDARD SSTL15_T_DCI} [get_ports {DDR3_DQ[63]}];
# set_property -dict {PACKAGE_PIN AD13  IOSTANDARD SSTL15    } [get_ports {DDR3_ODT[0]}];
# set_property -dict {PACKAGE_PIN AA3   IOSTANDARD SSTL15    } [get_ports {DDR3_VSEL}];
# set_property -dict {PACKAGE_PIN AA12  IOSTANDARD SSTL15    } [get_ports {DDR3_WE_N}];
# set_property -dict {PACKAGE_PIN AF10  IOSTANDARD SSTL15    } [get_ports {DDR3_A[10]}];
# set_property -dict {PACKAGE_PIN AD8   IOSTANDARD SSTL15    } [get_ports {DDR3_A[11]}];
# set_property -dict {PACKAGE_PIN AE10  IOSTANDARD SSTL15    } [get_ports {DDR3_A[12]}];
# set_property -dict {PACKAGE_PIN AF8   IOSTANDARD SSTL15    } [get_ports {DDR3_A[13]}];
# set_property -dict {PACKAGE_PIN AC7   IOSTANDARD SSTL15    } [get_ports {DDR3_A[14]}];
# set_property -dict {PACKAGE_PIN AE12  IOSTANDARD SSTL15    } [get_ports {DDR3_CAS_N}];
# set_property -dict {PACKAGE_PIN Y12   IOSTANDARD SSTL15    } [get_ports {DDR3_CS_N[0]}];
# set_property -dict {PACKAGE_PIN Y3    IOSTANDARD SSTL15    } [get_ports {DDR3_DM[0]}];
# set_property -dict {PACKAGE_PIN U5    IOSTANDARD SSTL15    } [get_ports {DDR3_DM[1]}];
# set_property -dict {PACKAGE_PIN AD4   IOSTANDARD SSTL15    } [get_ports {DDR3_DM[2]}];
# set_property -dict {PACKAGE_PIN AC4   IOSTANDARD SSTL15    } [get_ports {DDR3_DM[3]}];
# set_property -dict {PACKAGE_PIN AF19  IOSTANDARD SSTL15    } [get_ports {DDR3_DM[4]}];
# set_property -dict {PACKAGE_PIN AC16  IOSTANDARD SSTL15    } [get_ports {DDR3_DM[5]}];
# set_property -dict {PACKAGE_PIN AB19  IOSTANDARD SSTL15    } [get_ports {DDR3_DM[6]}];
# set_property -dict {PACKAGE_PIN V14   IOSTANDARD SSTL15    } [get_ports {DDR3_DM[7]}];
# set_property -dict {PACKAGE_PIN AE13  IOSTANDARD SSTL15    } [get_ports {DDR3_RAS_N}]
# set_property -dict {PACKAGE_PIN AC1   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[0]}];
# set_property -dict {PACKAGE_PIN W5    IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[1]}];
# set_property -dict {PACKAGE_PIN AF5   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[2]}];
# set_property -dict {PACKAGE_PIN AF4   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[2]}];
# set_property -dict {PACKAGE_PIN AA5   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[3]}];
# set_property -dict {PACKAGE_PIN AB5   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[3]}];
# set_property -dict {PACKAGE_PIN AE18  IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[4]}];
# set_property -dict {PACKAGE_PIN AF18  IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[4]}];
# set_property -dict {PACKAGE_PIN Y15   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[5]}];
# set_property -dict {PACKAGE_PIN Y16   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[5]}];
# set_property -dict {PACKAGE_PIN AD20  IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[6]}];
# set_property -dict {PACKAGE_PIN AE20  IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[6]}];
# set_property -dict {PACKAGE_PIN W18   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[7]}];
# set_property -dict {PACKAGE_PIN W19   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_N[7]}];
# set_property -dict {PACKAGE_PIN AB1   IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[0]}];
# set_property -dict {PACKAGE_PIN W6    IOSTANDARD DIFF_SSTL15_T_DCI} [get_ports {DDR3_DQS_P[1]}];
# set_property -dict {PACKAGE_PIN AB7   IOSTANDARD SSTL15    } [get_ports {DDR3_RST_N}];
## }}}

## Ethernet MDIO
## {{{
## Should these be o_eth_mdclk and io_eth_mdio?
##
# set_property -dict {PACKAGE_PIN B25   IOSTANDARD LVCMOS18  } [get_ports {o_eth_mdclk}]; # FPGA_MDC_PUDC_N
# set_property -dict {PACKAGE_PIN B26   IOSTANDARD LVCMOS18  } [get_ports {io_eth_mdio}]; # FPGA_MDIO_EMCCLK
## }}}

## Ethernet #0
## {{{
# set_property -dict {PACKAGE_PIN H23   IOSTANDARD LVCMOS18  } [get_ports {i_eth0_rxd[0]}]; # ETH0_RX_D[0]
# set_property -dict {PACKAGE_PIN H24   IOSTANDARD LVCMOS18  } [get_ports {i_eth0_rxd[1]}]; # ETH0_RX_D[1]
# set_property -dict {PACKAGE_PIN J21   IOSTANDARD LVCMOS18  } [get_ports {i_eth0_rxd[2]}]; # ETH0_RX_D[2]
# set_property -dict {PACKAGE_PIN H22   IOSTANDARD LVCMOS18  } [get_ports {i_eth0_rxd[3]}]; # ETH0_RX_D[3]
# set_property -dict {PACKAGE_PIN G22   IOSTANDARD LVCMOS18  } [get_ports {i_eth0_rx_clk}]; # ETH0_RX_CLK
# set_property -dict {PACKAGE_PIN F23   IOSTANDARD LVCMOS18  } [get_ports {i_eth0_rx_ctl}]; # ETH0_RX_CTL
# set_property -dict {SLEW FAST PACKAGE_PIN J24 IOSTANDARD LVCMOS18 } [get_ports { o_eth0_txd[0] }]; # ETH0_TX_D[0]
# set_property -dict {SLEW FAST PACKAGE_PIN J25 IOSTANDARD LVCMOS18 } [get_ports { o_eth0_txd[1] }]; # ETH0_TX_D[1]
# set_property -dict {SLEW FAST PACKAGE_PIN L22 IOSTANDARD LVCMOS18 } [get_ports { o_eth0_txd[2] }]; # ETH0_TX_D[2]
# set_property -dict {SLEW FAST PACKAGE_PIN K22 IOSTANDARD LVCMOS18 } [get_ports { o_eth0_txd[3] }]; # ETH0_TX_D[3]
# set_property -dict {SLEW FAST PACKAGE_PIN K23 IOSTANDARD LVCMOS18 } [get_ports { o_eth0_tx_clk }]; # ETH0_TX_CLK
# set_property -dict {SLEW FAST PACKAGE_PIN J23 IOSTANDARD LVCMOS18 } [get_ports { o_eth0_tx_ctl }]; # ETH0_TX_CTL
## }}}

## Ethernet #1
## {{{
# set_property -dict {PACKAGE_PIN G25   IOSTANDARD LVCMOS18  } [get_ports {i_eth1_rxd[0]}];
# set_property -dict {PACKAGE_PIN G26   IOSTANDARD LVCMOS18  } [get_ports {i_eth1_rxd[1]}];
# set_property -dict {PACKAGE_PIN F25   IOSTANDARD LVCMOS18  } [get_ports {i_eth1_rxd[2]}];
# set_property -dict {PACKAGE_PIN E26   IOSTANDARD LVCMOS18  } [get_ports {i_eth1_rxd[3]}];
# set_property -dict {PACKAGE_PIN G24   IOSTANDARD LVCMOS18  } [get_ports {i_eth1_rx_clk}];
# set_property -dict {PACKAGE_PIN F24   IOSTANDARD LVCMOS18  } [get_ports {i_eth1_rx_ctl}];
#
# set_property -dict {SLEW FAST PACKAGE_PIN J26 IOSTANDARD LVCMOS18 } [get_ports {o_eth1_txd[0]}]; # ETH1_TX_D[0]
# set_property -dict {SLEW FAST PACKAGE_PIN H26 IOSTANDARD LVCMOS18 } [get_ports {o_eth1_txd[1]}]; # ETH1_TX_D[1]
# set_property -dict {SLEW FAST PACKAGE_PIN H21 IOSTANDARD LVCMOS18 } [get_ports {o_eth1_txd[2]}]; # ETH1_TX_D[2]
# set_property -dict {SLEW FAST PACKAGE_PIN G21 IOSTANDARD LVCMOS18 } [get_ports {o_eth1_txd[3]}]; # ETH1_TX_D[3]
# set_property -dict {SLEW FAST PACKAGE_PIN E25 IOSTANDARD LVCMOS18 } [get_ports {o_eth1_tx_clk}]; # ETH1_TX_CLK
# set_property -dict {SLEW FAST PACKAGE_PIN D25 IOSTANDARD LVCMOS18 } [get_ports {o_eth1_tx_ctl}]; # ETH1_TX_CTL
## }}}

## Flash
## {{{
# set_property -dict {SLEW SLOW PACKAGE_PIN K21   IOSTANDARD LVCMOS18  } [get_ports {o_qspi_sck}];  # FPGA_CCLK
set_property -dict {SLEW SLOW PACKAGE_PIN C23   IOSTANDARD LVCMOS18  } [get_ports {o_qspi_cs_n}]; # FLASH_CS_N
set_property -dict {SLEW SLOW PACKAGE_PIN B24   IOSTANDARD LVCMOS18  } [get_ports {io_qspi_dat[0]}]; # FLASH_DI
set_property -dict {SLEW SLOW PACKAGE_PIN A25   IOSTANDARD LVCMOS18  } [get_ports {io_qspi_dat[1]}]; # FLASH_DO
set_property -dict {SLEW SLOW PACKAGE_PIN B22   IOSTANDARD LVCMOS18  } [get_ports {io_qspi_dat[2]}]; # FLASH_WP_N
set_property -dict {SLEW SLOW PACKAGE_PIN A22   IOSTANDARD LVCMOS18  } [get_ports {io_qspi_dat[3]}]; # FLASH_HOLD_N
## }}}

## FTDI
## {{{
# set_property -dict {PACKAGE_PIN W10   IOSTANDARD SSTL15    } [get_ports {FTDI_D0}];
# set_property -dict {PACKAGE_PIN W9    IOSTANDARD SSTL15    } [get_ports {FTDI_D1}];
# set_property -dict {PACKAGE_PIN Y8    IOSTANDARD SSTL15    } [get_ports {FTDI_D2}];
# set_property -dict {PACKAGE_PIN Y7    IOSTANDARD SSTL15    } [get_ports {FTDI_D3}];
# set_property -dict {PACKAGE_PIN Y11   IOSTANDARD SSTL15    } [get_ports {FTDI_D4}];
# set_property -dict {PACKAGE_PIN Y10   IOSTANDARD SSTL15    } [get_ports {FTDI_D5}];
# set_property -dict {PACKAGE_PIN V9    IOSTANDARD SSTL15    } [get_ports {FTDI_D6}];
# set_property -dict {PACKAGE_PIN W8    IOSTANDARD SSTL15    } [get_ports {FTDI_D7}];
# set_property -dict {PACKAGE_PIN AB16  IOSTANDARD SSTL15    } [get_ports {FTDI_UART_RX}];
# set_property -dict {PACKAGE_PIN W11   IOSTANDARD SSTL15    } [get_ports {FTDI_UART_TX}];
# set_property -dict {PACKAGE_PIN V11   IOSTANDARD SSTL15    } [get_ports {FTDI_OE_N}];
# set_property -dict {PACKAGE_PIN V8    IOSTANDARD SSTL15    } [get_ports {FTDI_RD_N}];
# set_property -dict {PACKAGE_PIN V7    IOSTANDARD SSTL15    } [get_ports {FTDI_WR_N}];
# set_property -dict {PACKAGE_PIN AF7   IOSTANDARD SSTL15    } [get_ports {FTDI_RXF_N}];
# set_property -dict {PACKAGE_PIN AE7   IOSTANDARD SSTL15    } [get_ports {FTDI_TXE_N}];
# set_property -dict {PACKAGE_PIN AC9   IOSTANDARD SSTL15    } [get_ports {FTDI_CLKOUT}];
## }}}

## SDCARD
## {{{
# set_property -dict {PACKAGE_PIN C21   IOSTANDARD LVCMOS18  } [get_ports {o_sd_sck}];  # SDIO_CLK
# set_property -dict {PACKAGE_PIN B21   IOSTANDARD LVCMOS18  } [get_ports {io_sd_cmd}]; # SDIO_CLK
# set_property -dict {PACKAGE_PIN D26   IOSTANDARD LVCMOS18  } [get_ports {io_sd[0]}];  # SDIO_D0
# set_property -dict {PACKAGE_PIN C26   IOSTANDARD LVCMOS18  } [get_ports {io_sd[1]}];  # SDIO_D1
# set_property -dict {PACKAGE_PIN A23   IOSTANDARD LVCMOS18  } [get_ports {io_sd[2]}];  # SDIO_D2
# set_property -dict {PACKAGE_PIN A24   IOSTANDARD LVCMOS18  } [get_ports {io_sd[3]}];  # SDIO_D3

# set_property -dict {PACKAGE_PIN D21   IOSTANDARD LVCMOS18  } [get_ports {i_sd_cd_n}];  # SDCARD_CD#

## IO B14 L10 C21 P / A91 / SDIO_CLK
## IO B14 L10 B21 N / A93 / SDIO_CMD
## IO B14 L5  D26 P / A95 / SDIO_D0
## IO B14 L5  C26 N / A97 / SDIO_D1

## IO B14 L4  A23 P / A101 / SDIO_D1
## IO B14 L4  A24 N / A103 / SDIO_D3

## IO B14 L7  D21 P / A98  / SDCARD_CD#
## }}}

## Adding in any XDC_INSERT tags

## No XDC.INSERT tag in mem_bkram_only
## No XDC.INSERT tag in mem_flash_sdram
## No XDC.INSERT tag in mem_flash_bkram
## No XDC.INSERT tag in XDC
## No XDC.INSERT tag in zip
## No XDC.INSERT tag in zip_jiffies
## No XDC.INSERT tag in zip_dmac
## No XDC.INSERT tag in zip_tmc
## No XDC.INSERT tag in zip_tmb
## No XDC.INSERT tag in zip_alt_utc
## No XDC.INSERT tag in zip_alt_moc
## From sdio
set_property -dict { PULLTYPE PULLUP } [get_ports io_sdcard_cmd]
## No XDC.INSERT tag in zip_alt_mic
## No XDC.INSERT tag in syspic
## No XDC.INSERT tag in sdram
## No XDC.INSERT tag in flashcfg
## No XDC.INSERT tag in crossflash
## No XDC.INSERT tag in bkram
## No XDC.INSERT tag in altpic
## No XDC.INSERT tag in SIM
## No XDC.INSERT tag in wb32
## No XDC.INSERT tag in mem_sdram_only
## No XDC.INSERT tag in flash
## No XDC.INSERT tag in DEFAULT
## No XDC.INSERT tag in ck_pps
## No XDC.INSERT tag in zip_alt_mtc
## No XDC.INSERT tag in REGDEFS
## From rxeth0ck
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *clkrxeth0ckctr/avgs*}]       -to [ get_cells -hier -filter {NAME =~*clkrxeth0ckctr/q_v*}]   8.0
## No XDC.INSERT tag in zip_alt_upc
## No XDC.INSERT tag in zip_alt_uoc
## No XDC.INSERT tag in iclock
## From txclk
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *clktxclkctr/avgs*}]       -to [ get_cells -hier -filter {NAME =~*clktxclkctr/q_v*}]   8.0
## No XDC.INSERT tag in KEYS
## No XDC.INSERT tag in masterclk
## From adcclk
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *clkadcclkctr/avgs*}]       -to [ get_cells -hier -filter {NAME =~*clkadcclkctr/q_v*}]   8.0
## No XDC.INSERT tag in uart
## No XDC.INSERT tag in RESET_ADDRESS
## No XDC.INSERT tag in version
## No XDC.INSERT tag in wbu
## No XDC.INSERT tag in zip_alt_mpc
## No XDC.INSERT tag in crossbus
## No XDC.INSERT tag in REGISTER
## No XDC.INSERT tag in buspic
## No XDC.INSERT tag in cfg
## No XDC.INSERT tag in buildtime
## No XDC.INSERT tag in alt
## No XDC.INSERT tag in pwrcount
## No XDC.INSERT tag in TMA
## No XDC.INSERT tag in rtccount
## No XDC.INSERT tag in spio
## No XDC.INSERT tag in zip_alt_uic
## No XDC.INSERT tag in wbu_arbiter
