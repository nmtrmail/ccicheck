(******************************************************************************)
(* PipeCheck: Specifying and Verifying Microarchitectural                     *)
(* Enforcement of Memory Consistency Models                                   *)
(*                                                                            *)
(* Copyright (c) 2015 Daniel Lustig & Yatin Manerkar, Princeton University    *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(*                                                                            *)
(* You should have received a copy of the GNU Lesser General Public           *)
(* License along with this library; if not, write to the Free Software        *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  *)
(* USA                                                                        *)
(******************************************************************************)

open Printf
open Unix
open Arg
open PipeGraph
open HerdGraph

(* FIXME works in OCaml v4.00 - 4.01 only!
   <  v4.00: no iteri
   >= v4.02: strings no longer mutable *)
let rec stringOfString s =
  let s' = String.make (length s) '-' in
  List.iteri (fun n c -> String.set s' n c) s;
  s'

let rec printString oc s =
  match s with
  | h::t -> fprintf oc "%s" (stringOfString h); printString oc t
  | [] -> ();;

let rec printStrings oc s =
  match s with
  | h::t -> printString oc h; printStrings oc t
  | [] -> ();;

let input_filename = ref ""
let output_filename = ref ""
let procname = ref "FiveStagePrivL1L2_CCL2_Processor"
let graphstyle = ref "compressed"
let do_reduction = ref true
let model = ref "x86tso.cat"
let keep_pruned = ref 1
let fast_mode = ref false

let update_input_filename s = input_filename := s
let update_output_filename s = output_filename := s
let update_procname s = procname := s
let update_graphstyle s = graphstyle := s
let unknown_argument s = raise (Arg.Bad ("Unknown argument: " ^ s))
let update_model s = model := s
let update_keep_pruned s = keep_pruned := int_of_string s

let parse_anon s =
  if (String.length !input_filename = 0)
  then input_filename := s
  else if (String.length !output_filename = 0)
  then output_filename := s
  else unknown_argument s

let speclist = [
  ("-i", Arg.String update_input_filename, "Input litmus test file");
  ("-o", Arg.String update_output_filename, "Output file");
  ("-p", Arg.String update_procname, "Processor");
  ("-g", Arg.String update_graphstyle, "Graph Style");
  ("-m", Arg.String update_model, "herd model to use (default x86tso.cat)");
  ("-r", Arg.Clear  do_reduction, "Don't perform transitive reduction");
  ("-k", Arg.String update_keep_pruned, "Keep pruned (-k 1)/invalid (-k 2) graphs");
  ("-f", Arg.Set    fast_mode, "Fast mode: print only the first observable outcome")];;

Arg.parse speclist parse_anon "PipeGraph";;

let _ = if (String.length !input_filename = 0)
  then (Arg.usage speclist "PipeGraph";
    raise (Arg.Bad "No input file specified"))
  else if (String.length !output_filename = 0)
  then (Arg.usage speclist "PipeGraph";
    raise (Arg.Bad "No output file specified"))
  else ();;

let (allowed, final_memory_values, programs) =
  execute_herd "herd" !input_filename !model;;

let processors = [
  PipeGraph.fiveStagePrivL1L2_CCL2_Processor (length (List.hd programs));
  PipeGraph.fiveStageSharedL1OnlyProcessor (length (List.hd programs));
  PipeGraph.fiveStagePrivL1SharedL2_CCL1_Processor (length (List.hd programs));
  PipeGraph.fiveStagePrivL1L2_CCL1L2_Processor (length (List.hd programs));
  PipeGraph.fiveStageL1OnlyProcessor (length (List.hd programs));
  PipeGraph.fiveStagePeekabooProcessor (length (List.hd programs));
  PipeGraph.fiveStageTSOCC_Processor (length (List.hd programs));
  PipeGraph.fiveStageTSOCC_OoO_Processor (length (List.hd programs));
  PipeGraph.fiveStageGPUProcessor (length (List.hd programs))
  ]

let processor =
  let processors_list =
    List.map (fun p -> stringOfString (PipeGraph.procName p)) processors in
  (try
    List.find (fun p -> stringOfString (PipeGraph.procName p) = !procname)
    processors
  with
  | Not_found ->
      Printf.printf "Unknown processor name\n";
      Printf.printf "Known processor names are:\n";
      List.iter (Printf.printf "\t%s\n") processors_list;
      raise (Arg.Bad "Unknown processor"));;

let all_graphs progs =
  let program_graphs = map (PipeGraph.programGraphs !keep_pruned final_memory_values processor) progs in

  Printf.printf "%d architecture-level graphs\n" (List.length program_graphs);

  let rec print_num_uarch_graphs l n count =
    match l with
    | h::t ->
        let lh = List.length h in
        Printf.printf "Graph %d: %d microarchitecture-level graphs\n" n lh;
        print_num_uarch_graphs t (n+1) (count + lh)
    | [] -> count
    in

  let total_count = print_num_uarch_graphs program_graphs 0 0 in

  let outputs = if !graphstyle = "compressed"
  then map (PipeGraph.compressedGraphsOfExecutions processor !do_reduction) program_graphs
  else if !graphstyle = "original"
  then map (PipeGraph.graphsOfExecutions processor) program_graphs
  else raise (Arg.Bad "Illegal graphstyle specified") in

  let oc = open_out !output_filename in
  List.iter (printStrings oc) outputs;
  close_out oc;

  let observable = fold_left (||) (map PipeGraph.isObservable program_graphs) false in

  let result_string =
    match (allowed, observable) with
    | (true, true) -> "Allowed/Observable"
    | (true, false) -> "Allowed/Not Observable (Stricter than necessary)"
    | (false, true) -> "Forbidden/Observable (BUG!)"
    | (false, false) -> "Forbidden/Not observable" in

  Printf.printf "Input %s: %s\n" !input_filename result_string;

  Printf.printf "Total Graphs: %d\n" total_count

let program_length p = fold_left (+) (map List.length p) 0

let first_observable_graph progs =
  let Pair (counts, graph) = PipeGraph.programGraphsFindAnyObservableOutcome
    !keep_pruned {numInsts = program_length (List.hd progs);
       numCyclic = 0; numAcyclic = 0; numPruned = []; numInvalid = [];
       numIterations = []}
    final_memory_values processor progs in

  Printf.printf "Input %s %s\n" !input_filename
    (stringOfString (PipeGraph.stringOfGraphCounts counts));

  let observable =
    match PipeGraph.compressedGraphOfOneOutcome processor !do_reduction graph with
    | PipeGraph.Some s ->
      let oc = open_out !output_filename in
      printString oc s;
      close_out oc;
      true
    | PipeGraph.None -> false
  in

  let result_string =
    match (allowed, observable) with
    | (true, true) -> "Allowed/Observable"
    | (true, false) -> "Allowed/Not Observable (Stricter than necessary)"
    | (false, true) -> "Forbidden/Observable (BUG!)"
    | (false, false) -> "Forbidden/Not observable"
  in

  Printf.printf "Input %s: %s\n" !input_filename result_string

let _ = if !fast_mode then first_observable_graph programs else all_graphs programs;

print_string "Done!\n"

