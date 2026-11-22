# ============================================================================
# hardware/build_tang_nano_9k.tcl
# Automated Gowin EDA / gw_sh Bitstream Synthesis Script for Sipeed Tang Nano 9K
#   Target Device : GW1NR-LV9QN88PC6/I5 (GW1NR-9C)
#   Top Module    : tang_nano_9k_uart_board_top
#   RTL Source    : hardware/cuboctahedron_carrier_asic.v
#   Pin CST       : hardware/tang_nano_9k.cst
#   Usage         : gw_sh build_tang_nano_9k.tcl
# ============================================================================

set_device -name GW1NR-9C GW1NR-LV9QN88PC6/I5

add_file -type verilog "cuboctahedron_carrier_asic.v"
add_file -type cst     "tang_nano_9k.cst"

set_option -top_module tang_nano_9k_uart_board_top
set_option -verilog_std sysv2017
set_option -use_sspi_as_gpio 1
set_option -use_mspi_as_gpio 1
set_option -output_base_name cuboctahedron_tang_nano_9k

run all
