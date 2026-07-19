#!/usr/bin/env bash
# Minimal repro of tactus-core's dominant lean obligation (~48s alone):
#   _tactus_postcondition_wp_stm_sound_at_lib_3687_13_53
# Needs LEAN_PATH = <prelude cache>:<an out dir holding TactusDefs_lib_exec
# + TactusStmts_lib_exec__lib__wp_stm_sound oleans from a tactus-core run>.
time lean "$(dirname "$0")/wp53_repro.lean"
