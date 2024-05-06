
################################################################################
##
## Filename:	Makefile
## {{{
## Project:	KIMOS, a Mercury KX2 demonstration project
##
## Purpose:	A master project makefile.  It tries to build all targets
##		within the project, mostly by directing subdirectory makes.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2024, Gisselquist Technology, LLC
## {{{
## This file is part of the KIMOS project.
##
## The KIMOS project is free software and gateware: you can redistribute it
## and/or modify it under the terms of the GNU General Public License as
## published by the Free Software Foundation, either version 3 of the License,
## or (at your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory, run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
.PHONY: all
all: excompress exdecompress exdeword exmkword exidle exwb netdbgrx

.PHONY: excompress
## {{{
excompress: excompress_prf/PASS excompress_cvr/PASS
excompress_prf/PASS: excompress.sby ../../rtl/exbus/excompress.v
	-sby -f excompress.sby prf
excompress_cvr/PASS: excompress.sby ../../rtl/exbus/excompress.v
	sby -f excompress.sby cvr
## }}}

.PHONY: exdecompress
## {{{
exdecompress: exdecompress_prf/PASS exdecompress_cvr/PASS
exdecompress_prf/PASS: exdecompress.sby ../../rtl/exbus/exdecompress.v
	-sby -f exdecompress.sby prf
exdecompress_cvr/PASS: exdecompress.sby ../../rtl/exbus/exdecompress.v
	sby -f exdecompress.sby cvr
## }}}

.PHONY: exmkword
## {{{
exmkword: exmkword_prf/PASS exmkword_cvr/PASS
exmkword_prf/PASS: exmkword.sby ../../rtl/exbus/exmkword.v
	-sby -f exmkword.sby prf
exmkword_cvr/PASS: exmkword.sby ../../rtl/exbus/exmkword.v
	sby -f exmkword.sby cvr
## }}}

.PHONY: exdeword
## {{{
exdeword: exdeword_prf/PASS exdeword_cvr/PASS
exdeword_prf/PASS: exdeword.sby ../../rtl/exbus/exdeword.v
	-sby -f exdeword.sby prf
exdeword_cvr/PASS: exdeword.sby ../../rtl/exbus/exdeword.v
	sby -f exdeword.sby cvr
## }}}

.PHONY: exidle
## {{{
exidle: exidle_prf/PASS exidle_cvr/PASS
exidle_prf/PASS: exidle.sby ../../rtl/exbus/exidle.v
	-sby -f exidle.sby prf
exidle_cvr/PASS: exdeword.sby ../../rtl/exbus/exidle.v
	sby -f exidle.sby cvr
## }}}

.PHONY: exwb
## {{{
exwb: exwb_prf/PASS exwb_cvr/PASS
exwb: exwb_prfp/PASS exwb_cvrp/PASS
exwb: exwb_prflp/PASS exwb_prflpp/PASS

exwb_prf/PASS: exwb.sby fwb_master.v ../../rtl/exbus/exwb.v
	-sby -f exwb.sby prf
exwb_prfp/PASS: exwb.sby fwb_master.v ../../rtl/exbus/exwb.v
	-sby -f exwb.sby prfp
exwb_prflp/PASS: exwb.sby fwb_master.v ../../rtl/exbus/exwb.v
	-sby -f exwb.sby prflp
exwb_prflpp/PASS: exwb.sby fwb_master.v ../../rtl/exbus/exwb.v
	-sby -f exwb.sby prflpp
exwb_cvr/PASS: exwb.sby fwb_master.v ../../rtl/exbus/exwb.v
	sby -f exwb.sby cvr
exwb_cvrp/PASS: exwb.sby fwb_master.v ../../rtl/exbus/exwb.v
	sby -f exwb.sby cvrp
## }}}

.PHONY: netdbgrx
## {{{
netdbgrx: netdbgrx_prf/PASS netdbgrx_cvr/PASS
netdbgrx_prf/PASS: netdbgrx.sby ../../rtl/proto/netdbgrx.v
	-sby -f netdbgrx.sby prf
netdbgrx_cvr/PASS: exdeword.sby ../../rtl/proto/netdbgrx.v
	sby -f netdbgrx.sby cvr
## }}}


.PHONY: clean
## {{{
clean:
	rm -rf excompress_*/ exdecompress_*/
	rm -rf exmkword_*/ exdeword_*/
	rm -rf exwb_*/ exidle_*/
## }}}
