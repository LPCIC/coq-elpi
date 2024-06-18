open Elpi_plugin

let time_tc_bench = ref false

let set_time_tc_bench = (:=) time_tc_bench
let get_time_tc_bench () = !time_tc_bench

let () = Goptions.declare_bool_option { optstage = Summary.Stage.Interp;
        optdepr  = None;
        optkey   = ["Time";"TC";"Bench"];
        optread  = get_time_tc_bench;
        optwrite = set_time_tc_bench; }

let time_all b =
  CDebug.set_flag Coq_elpi_utils.elpitime_flag b;
  set_time_tc_bench b