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

Definition FiveStagePrivL1SharedL2_CCL1PipelineStages := [
  (*  0 *) "Fetch";
  (*  1 *) "Decode";
  (*  2 *) "Execute";
  (*  3 *) "MemoryStage";
  (*  4 *) "Writeback";
  (*  5 *) "StoreBufferOnly";
  (*  6 *) "Completed";
  (*  7 *) "L1 ViCL Create";
  (*  8 *) "L1 ViCL Invalidate";
  (*  9 *) "L2 ViCL Create";
  (* 10 *) "L2 ViCL Invalidate"].

Definition FiveStagePrivL1SharedL2_CCL1Propagations (n : PipeID) :=
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

Definition FiveStagePrivL1SharedL2_CCL1MicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [

     (** The L1-accessing paths *)
     mkMicroopPath "ReadFromStoreBuffer"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBFwd" (ReadsBetween (n, 3) (n, 3) (n, 7))]
         []
         [];
     mkMicroopPath "UsesViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (n, 7) (n, 3) (n, 8));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3))]
         []
         [];
     mkMicroopPath "HasViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 3; 8])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 7 (n, 7))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8)];
     mkMicroopPath "HasViCL_L1UsesL2"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 3; 8])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "SharesViCL" (SourcedFrom (0, 9) (n, 7))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8)];
     mkMicroopPath "HasViCL_L1L2"
         (StraightLine n [0; 1; 2; 3; 4] ++ [((0, 9), (n, 7))] ++ StraightLine n [7; 3; 8] ++
          StraightLine 0 [9; 10])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 9 (0, 9))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8);
          OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];
     mkMicroopPath "HasViCL_L1L2Initial"
         (StraightLine n [0; 1; 2; 3; 4] ++ [((0, 9), (n, 7))] ++ StraightLine n [7; 3; 8] ++
          StraightLine 0 [9; 10])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ReadsZero" ReadsZero]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (0, 9));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8);
          OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];

     (** The L1-bypassing paths *)
     mkMicroopPath "UsesViCL_L2"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (0, 9) (n, 3) (0, 10));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3))]
         []
         [];
     mkMicroopPath "HasViCLReadL2"
         (StraightLine n [0; 1; 2; 3; 4] ++ [((0, 9), (n, 3)); ((n, 3), (0, 10))])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 9 (0, 9))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10))]
         [OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];
     mkMicroopPath "HasViCL_L2Initial"
         (StraightLine n [0; 1; 2; 3; 4] ++ [((0, 9), (n, 3)); ((n, 3), (0, 10))])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ReadsZero" ReadsZero]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (0, 9));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10))]
         [OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)]
     ]
 | Write _ _ => [
     mkMicroopPath "WriteL1L2"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8] ++
         [((n, 7), (0, 9)); ((0, 9), (0, 10))])
       (FiveStagePrivL1SharedL2_CCL1Propagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8));
        AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 8);
        OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];
     mkMicroopPath "WriteL1Only"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8])
       (FiveStagePrivL1SharedL2_CCL1Propagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 8)];
     mkMicroopPath "WriteL2"
       (StraightLine n [0; 1; 2; 3; 4; 5] ++ [((n, 5), (0, 9)); ((0, 9), (n, 6))] ++ StraightLine 0 [9; 10])
       (FiveStagePrivL1SharedL2_CCL1Propagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (0, 9) (0, 10))]
       [SWViCL (0, 9) (0, 9) (0, 10) (0, 10)]
     ]
 | Fence _   => [
     mkMicroopPath "Fence"
       (StraightLine n [0; 1; 2; 3; 4])
       (FiveStagePrivL1SharedL2_CCL1Propagations n)
       [MultiChoiceConstraint "FlushSTB" (FlushAllAddresses (n, 6) (n, 3))]
       []
       []
     ]
 | RMWRead _ _ => [

     (** The L1-accessing paths *)
     mkMicroopPath "UsesViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (n, 7) (n, 5) (n, 8));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 8))]
         [AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 5) (n, 7))]
         [];
     mkMicroopPath "HasViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [7; 5; 8])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 7 (n, 7));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 8))]
         [AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8)];
     mkMicroopPath "HasViCL_L1UsesL2"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [7; 5; 8])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "SharesViCL" (SourcedFrom (0, 9) (n, 7));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 8))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8)];
     mkMicroopPath "HasViCL_L1L2"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ [((0, 9), (n, 7))] ++ StraightLine n [7; 5; 8] ++
          StraightLine 0 [9; 10])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 9 (0, 9));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 8))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8);
          OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];
     mkMicroopPath "HasViCL_L1L2Initial"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ [((0, 9), (n, 7))] ++ StraightLine n [7; 5; 8] ++
          StraightLine 0 [9; 10])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ReadsZero" ReadsZero;
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 8))]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (0, 9));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (n, 7) (n, 8));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 8) (n, 8);
          OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];

     (** The L1-bypassing paths *)
     mkMicroopPath "UsesViCL_L2"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (0, 9) (n, 5) (0, 10));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (0, 9) (0, 10))]
         [AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 9) (0, 9))]
         [];
     mkMicroopPath "HasViCLReadL2"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ [((0, 9), (n, 5)); ((n, 5), (0, 10))])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 9 (0, 9));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (0, 9) (0, 10))]
         [AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 9) (0, 9))]
         [OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];
     mkMicroopPath "HasViCL_L2Initial"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ [((0, 9), (n, 5)); ((n, 5), (0, 10))])
         (FiveStagePrivL1SharedL2_CCL1Propagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ReadsZero" ReadsZero;
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (0, 9) (0, 10))]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (0, 9));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 9) (0, 9))]
         [OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)]
     ]
 | RMWWrite _ _ => [
     mkMicroopPath "WriteL1L2"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8] ++
         [((n, 7), (0, 9))] ++ StraightLine 0 [9; 10])
       (FiveStagePrivL1SharedL2_CCL1Propagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8));
        AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 9) (0, 10))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 8);
        OtherViCL (0, 9) (0, 9) (0, 10) (0, 10)];
     mkMicroopPath "WriteL1Only"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8])
       (FiveStagePrivL1SharedL2_CCL1Propagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 8)];
     mkMicroopPath "WriteL2"
       (StraightLine n [0; 1; 2; 3; 4; 5] ++ [((n, 5), (0, 9)); ((0, 9), (n, 6))] ++ StraightLine 0 [9; 10])
       (FiveStagePrivL1SharedL2_CCL1Propagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (0, 9) (0, 10))]
       [SWViCL (0, 9) (0, 9) (0, 10) (0, 10)]
     ]
 end.

Definition FiveStagePrivL1SharedL2_CCL1_Processor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "FiveStagePrivL1SharedL2_CCL1_Pipeline" n
    (FiveStagePrivL1SharedL2_CCL1MicroopPaths n) FiveStagePrivL1SharedL2_CCL1PipelineStages in
  mkProcessor "FiveStagePrivL1SharedL2_CCL1_Processor" (Map p (Range num_cores)).
