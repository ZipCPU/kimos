#!bin/bash

./exregs flashcfg 0x0001100	# Activate config mode
./exregs flashcfg 0x00010ff	# Send 16(*4) bits of ones, break the mode
./exregs flashcfg 0x00010ff
./exregs flashcfg 0x00010ff
./exregs flashcfg 0x0001100	# Inactivate the port

# Reset the SCOPE
./exregs flashscope 0x0c07ffff
# echo READ-ID
./exregs flashcfg 0x000109f	# Issue the read ID command
./exregs flashcfg 0x0001000	# Read the ID
./exregs flashcfg
./exregs flashcfg 0x0001000	#
./exregs flashcfg
./exregs flashcfg 0x0001000	#
./exregs flashcfg
./exregs flashcfg 0x0001000	#
./exregs flashcfg
./exregs flashcfg 0x0001100	# End the command

echo Return to QSPI
./exregs flashcfg 0x00010ec	# Return us to QSPI mode, via QIO_READ4 cmd
./exregs flashcfg 0x0001a00	# dummy address
./exregs flashcfg 0x0001a00	# dummy address
./exregs flashcfg 0x0001a00	# dummy address
./exregs flashcfg 0x0001a00	# dummy address
./exregs flashcfg 0x0001aa0	# mode byte
./exregs flashcfg 0x0001800	# empty byte, switching directions
./exregs flashcfg 0x0001800	# Read a byte of data
./exregs flashcfg
./exregs flashcfg 0x0001800	# Read a byte of data
./exregs flashcfg
./exregs flashcfg 0x0001800	# Read a byte of data
./exregs flashcfg
./exregs flashcfg 0x0001800	# Read a byte of data
./exregs flashcfg
./exregs flashcfg 0x0001800	# Read a byte of data
./exregs flashcfg
./exregs flashcfg 0x0001800	# Read a byte of data
./exregs flashcfg
./exregs flashcfg 0x0001800	# Read a byte of data
./exregs flashcfg
./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001800	# Read a byte of data
# ./exregs flashcfg
# ./exregs flashcfg 0x0001900	# Raise (deactivate) CS_n
# ./exregs flashcfg 0x0000100	# Return to user mode
# 
# ./exregs 0x06000000
# ./exregs 0x06000004
# ./exregs 0x06000008
# ./exregs 0x0600000c
# ./exregs 0x06000010
# ./exregs 0x06000014
# ./exregs 0x06000018
# ./exregs 0x0600001c
# ./exregs 0x06000020
# ./exregs 0x06000024
# ./exregs 0x06000028
# ./exregs 0x0600002c
