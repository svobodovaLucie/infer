; Copyright (c) Facebook, Inc. and its affiliates.
;
; This source code is licensed under the MIT license found in the
; LICENSE file in the root directory of this source tree.

(-noautolink
 -cclib -Wl,-Bstatic
 -cclib -lzarith -cclib -lgmp -cclib -lsqlite3_stubs -cclib -lsqlite3
 -cclib -Wl,-Bdynamic
 -cclib -lCStubs_stubs -cclib -lcamlzip -cclib -lz -cclib -lpthread -cclib -lparmap_stubs
 -cclib -lmtime_clock_stubs -cclib -lrt -cclib -lcamlstr -cclib -lANSITerminal_stubs
 -cclib -lcore_stubs -cclib -lspawn_stubs -cclib -lversion_util_stubs
 -cclib -lerror_checking_mutex_stubs -cclib -lthreadsnat -cclib -lpthread -cclib -lcore_kernel_stubs
 -cclib -lbase_bigstring_stubs -cclib -lexpect_test_collector_stubs -cclib -lbin_prot_stubs -cclib -lunix
 -cclib -ltime_now_stubs -cclib -lbase_stubs -cclib -lbase_internalhash_types_stubs
 )
