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

Require Import List.
Require Import Arith.
Require Import String.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Processor.
Require Import PipeGraph.Graph.
Require Import PipeGraph.Helpers.

Import ListNotations.
Open Scope string_scope.

Definition FiveStagePeekabooPipelineStages := [
  (*  0 *) "Fetch";
  (*  1 *) "Decode";
  (*  2 *) "Execute";
  (*  3 *) "MemoryStage";
  (*  4 *) "Writeback";
  (*  5 *) "StoreBufferOnly";
  (*  6 *) "Completed";
  (*  7 *) "L1 ViCL Request";
  (*  8 *) "L1 ViCL Create";
  (*  9 *) "L1 ViCL Recv Inv";
  (* 10 *) "L1 ViCL Expire"].

Definition FiveStagePeekabooPropagations (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [AlwaysPropagate ((n, 0), (n, 0)) ((n, 1), (n, 1));  (* Fetch -> Decode *)
   AlwaysPropagate ((n, 1), (n, 1)) ((n, 2), (n, 2));  (* Decode -> Execute *)
   AlwaysPropagate ((n, 2), (n, 2)) ((n, 3), (n, 3));  (* Execute -> Memory *)
   AlwaysPropagate ((n, 3), (n, 3)) ((n, 4), (n, 4));  (* Memory -> Writeback *)
   AlwaysPropagate ((n, 4), (n, 4)) ((n, 5), (n, 5));  (* Writeback -> StoreBuffer *)
   AlwaysPropagate ((n, 5), (n, 5)) ((n, 6), (n, 5))   (* StoreBuffer one at a time to L1 *)
  ].

Definition FiveStagePeekabooMicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [
     mkMicroopPath "ReadFromStoreBuffer"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "STBFwd" (ReadsBetween (n, 3) (n, 3) (n, 8))]
         []
         [];
     mkMicroopPath "UsesViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (n, 8) (n, 3) (n, 9));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3))]
         []
         [];
     mkMicroopPath "HasViCLReadL1"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [8; 3; 10])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 8 (n, 8))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 8) (n, 10))]
         [OtherViCL (n, 8) (n, 8) (n, 10) (n, 10)];
     mkMicroopPath "HasViCLReadInitial"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [8; 3; 10])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ReadsZero" ReadsZero]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (n, 8));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 8) (n, 10))]
         [OtherViCL (n, 8) (n, 8) (n, 10) (n, 10)];
     mkMicroopPath "HasViCLPeekabooL1"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 9; 8; 3; 10])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 8 (n, 8));
          MultiChoiceConstraint "Peekaboo" (FlushAllAddresses (n, 3) (n, 7));
          MultiChoiceConstraint "Peekaboo" (FlushAllAddresses (n, 6) (n, 7))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 8) (n, 9))]
         [OtherViCL (n, 7) (n, 8) (n, 9) (n, 10)];
     mkMicroopPath "HasViCLPeekabooInitial"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 9; 8; 3; 10])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ReadsZero" ReadsZero;
          MultiChoiceConstraint "Peekaboo" (FlushAllAddresses (n, 3) (n, 7));
          MultiChoiceConstraint "Peekaboo" (FlushAllAddresses (n, 6) (n, 7))]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (n, 8));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 8) (n, 9))]
         [OtherViCL (n, 7) (n, 8) (n, 9) (n, 10)]
     ]
 | Write _ _ => [
     mkMicroopPath "WriteL1"
       (StraightLine n [0; 1; 2; 3; 4; 5; 8; 10] ++ StraightLine n [8; 6])
       (FiveStagePeekabooPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 8) (n, 10))]
       [SWViCL (n, 8) (n, 8) (n, 10) (n, 10)]
     ]
 | Fence _   => [
     mkMicroopPath "Fence"
       (StraightLine n [0; 1; 2; 3; 4])
       (FiveStagePeekabooPropagations n)
       [MultiChoiceConstraint "FlushSTB" (FlushAllAddresses (n, 6) (n, 3))]
       []
       []
     ]
 | RMWRead _ _ => [
     mkMicroopPath "UsesViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (n, 8) (n, 5) (n, 9));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 8) (n, 10));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 5))]
         [AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 5) (n, 8))]
         [];
     mkMicroopPath "HasViCLReadL1"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [8; 5; 10])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 5));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 8 (n, 8));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 8) (n, 10))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 8) (n, 10));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 8) (n, 8))]
         [OtherViCL (n, 8) (n, 8) (n, 10) (n, 10)];
     mkMicroopPath "HasViCLReadInitial"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [8; 5; 10])
         (FiveStagePeekabooPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 5));
          MultiChoiceConstraint "ReadsZero" ReadsZero;
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 8) (n, 10))]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (n, 8));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 8) (n, 10));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 8) (n, 8))]
         [OtherViCL (n, 8) (n, 8) (n, 10) (n, 10)]
     ]
 | RMWWrite _ _ => [
     mkMicroopPath "WriteL1"
       (StraightLine n [0; 1; 2; 3; 4; 5; 8; 10] ++ StraightLine n [8; 6])
       (FiveStagePeekabooPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 8) (n, 10))]
       [SWViCL (n, 8) (n, 8) (n, 10) (n, 10)]
     ]
 end.

Definition FiveStagePeekabooProcessor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "FiveStagePeekabooPipeline" n
    (FiveStagePeekabooMicroopPaths n) FiveStagePeekabooPipelineStages in
  mkProcessor "FiveStagePeekabooProcessor" (Map p (Range num_cores)).

