(******************************************************************************)
(* Copyright (c) 2015 Daniel Lustig & Yatin Manerkar, Princeton University    *)
(*                                                                            *)
(* Permission is hereby granted, free of charge, to any person obtaining a    *)
(* copy of this software and associated documentation files (the "Software"), *)
(* to deal in the Software without restriction, including without limitation  *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense,   *)
(* and/or sell copies of the Software, and to permit persons to whom the      *)
(* Software is furnished to do so, subject to the following conditions:       *)
(*                                                                            *)
(* The above copyright notice and this permission notice shall be included in *)
(* all copies or substantial portions of the Software.                        *)
(*                                                                            *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *)
(* DEALINGS IN THE SOFTWARE.                                                  *)
(******************************************************************************)

Require Import Arith.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Processor.
Require Import PipeGraph.Graph.
Require Import PipeGraph.Graphviz.
Require Import PipeGraph.GraphvizCompressed.
Require Import PipeGraph.FiveStagePrivL1L2_CCL2.
Require Import PipeGraph.FiveStageL1Only.
Require Import PipeGraph.FiveStageSharedL1Only.
Require Import PipeGraph.FiveStagePrivL1L2_CCL1L2.
Require Import PipeGraph.FiveStagePrivL1SharedL2_CCL1.
Require Import PipeGraph.FiveStagePeekaboo.
Require Import PipeGraph.FiveStageTSOCC.
Require Import PipeGraph.FiveStageTSOCC_OoO.
Require Import PipeGraph.FiveStageGPU.

Import ListNotations.

Definition GraphsOfExecutions
  (proc : Processor)
  (graphs : list (NumberedAdjacencyList * MicroopPathMap))
  : list (list string) :=
  let f x := GraphvizGraph proc (snd x) (fst x) in
  let g x := (EdgesFromAdjacencyList (snd (fst x)), snd x) in
  Map f (Map g graphs).

Definition CompressedGraphsOfExecutions
  (proc : Processor)
  (do_reduction : bool)
  (graphs : list (NumberedAdjacencyList * MicroopPathMap))
  : list (list string) :=
  let f x := GraphvizCompressedGraph proc (snd x) (EdgesFromAdjacencyList (snd (fst x))) (fst (fst x)) do_reduction in
  Map f graphs.

Definition i0 := mkMicroop 0 0 0 (Write 0 1).
Definition i1 := mkMicroop 1 0 0 (Write 1 1).
Definition i2 := mkMicroop 2 1 0 (Read  1 1).
Definition i3 := mkMicroop 3 1 0 (Read  0 0).

Definition myProgram := [[i0; i1]; [i2; i3]].

Extraction Language Ocaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "(fun x -> x + 1)" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Extract Inductive string => "char list" [ "[]" "(::)" ].

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant beq_nat => "( fun (a:int) (b:int) -> a=b )".

Extract Constant Printf => "(fun x -> fun y -> let implode l = let res = String.create (List.length l) in let rec imp i = function | [] -> res | c :: l -> res.[i] <- c; imp (i + 1) l in imp 0 l in try let _ = Sys.getenv (implode ['P'; 'I'; 'P'; 'E'; 'G'; 'R'; 'A'; 'P'; 'H'; '_'; 'D'; 'E'; 'B'; 'U'; 'G']) in let rec print_chars l = match l with | h::t -> (print_char h; print_chars t) | [] -> (flush stdout; x) in print_chars y with Not_found -> x)".

Extract Constant MessageHelper => "(fun x -> fun y -> let rec print_chars l = match l with | h::t -> (print_char h; print_chars t) | [] -> (flush stdout; x) in print_chars y)".

Extraction "PipeGraph.ml" ProgramGraphs ProgramGraphsFindAnyObservableOutcome
  GraphsOfExecutions IsObservable
  CompressedGraphOfOneOutcome CompressedGraphsOfExecutions
  FiveStagePrivL1L2_CCL2_Processor FiveStageL1OnlyProcessor
  FiveStageSharedL1OnlyProcessor FiveStagePrivL1SharedL2_CCL1_Processor
  FiveStagePrivL1L2_CCL1L2_Processor FiveStagePeekabooProcessor
  FiveStageTSOCC_Processor FiveStageTSOCC_OoO_Processor FiveStageGPUProcessor
  myProgram.

