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

Definition FiveStageTSOCCPipelineStages := [
  (*  0 *) "Fetch";
  (*  1 *) "Decode";
  (*  2 *) "Execute";
  (*  3 *) "MemoryStage";
  (*  4 *) "Writeback";
  (*  5 *) "StoreBufferOnly";
  (*  6 *) "Completed";
  (*  7 *) "L1 ViCL Create";
  (*  8 *) "L1 ViCL Downgrade";
  (*  9 *) "L1 ViCL Invalidate";
  (* 10 *) "L2 ViCL Create";
  (* 11 *) "L2 ViCL Invalidate"].

Definition FiveStageTSOCCPropagations (n : PipeID) :=
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

Definition FiveStageTSOCCMicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [
     mkMicroopPath "ReadFromStoreBuffer"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBFwd" (ReadsBetween (n, 3) (n, 3) (n, 7))]
         []
         [];
     mkMicroopPath "UsesViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (n, 7) (n, 3) (n, 9));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3))]
         []
         [];
     mkMicroopPath "HasViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 3; 9])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
         (* The order of the [8;7] matters here: the first stage (downgrade) is chosen if it exists,
            otherwise the second is chosen. *)
          MultiChoiceConstraint "ViCLSourcing" (SourceAtAndInvIfNotLastOwner (n, 7) (n, 9) [8;7] (n, 7))]
         [AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9)];
     mkMicroopPath "HasViCL_L1UsesL2"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 3; 9])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "SharesViCL" (SourceFromAndInvIfNotLastOwner (n, 7) (n, 9) (0, 10) (n, 7))]
         [AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9)];
     mkMicroopPath "HasViCL_L1L2"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 3; 9] ++
          [((0, 10), (n, 7))] ++ StraightLine 0 [10; 11])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 10 (0, 10));
          MultiChoiceConstraint "InvCache" (InvalidateCache (n, 7) (n, 9))]
         [AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9);
          OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)];
     mkMicroopPath "HasViCL_L1L2Initial"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [7; 3; 9] ++
          [((0, 10), (n, 7))] ++ StraightLine 0 [10; 11])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "InvCache" (InvalidateCache (n, 7) (n, 9));
          MultiChoiceConstraint "ReadsZero" ReadsZero]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (n, 9));
          AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9);
          OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)]
     ]
 | Write _ _ => [
     mkMicroopPath "WriteL1L2Downgrade"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8; 9] ++
         [((n, 8), (0, 10))] ++ StraightLine 0 [10; 11])
       (FiveStageTSOCCPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8));
        AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 9);
        OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)];
     mkMicroopPath "WriteL1OnlyDowngrade"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8; 9])
       (FiveStageTSOCCPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 9)];
     mkMicroopPath "WriteL1L2NoDowngrade"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 9] ++
         [((n, 7), (0, 10))] ++ StraightLine 0 [10; 11])
       (FiveStageTSOCCPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 9));
        AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11))]
       [SWViCL (n, 7) (n, 7) (n, 9) (n, 9);
        OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)]
     ]
 | Fence _   => [
     mkMicroopPath "Fence"
       (StraightLine n [0; 1; 2; 3; 4])
       (FiveStageTSOCCPropagations n)
       [MultiChoiceConstraint "FlushSTB" (FlushAllAddresses (n, 6) (n, 3));
        MultiChoiceConstraint "InvCache" (CreateAllSubsequentAfter (n, 3) (n, 7));
        MultiChoiceConstraint "InvCache" (InvalidateCacheForPriorInsts (n, 3) (n, 3) (n, 7))]
       []
       []
     ]
 | RMWRead _ _ => [
     mkMicroopPath "UsesViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "SharesViCL" (ReadsBetween (n, 7) (n, 5) (n, 9));
          MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 9))]
         [AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 5) (n, 7))]
         [];
     mkMicroopPath "HasViCL_L1"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [7; 5; 9])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
         (* The order of the [8;7] matters here: the first stage (downgrade) is chosen if it exists,
            otherwise the second is chosen. *)
          MultiChoiceConstraint "ViCLSourcing" (SourceAtAndInvIfNotLastOwner (n, 7) (n, 9) [8;7] (n, 7));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 9))]
         [AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9)];
     mkMicroopPath "HasViCL_L1UsesL2"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [7; 5; 9])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 9));
          MultiChoiceConstraint "SharesViCL" (SourceFromAndInvIfNotLastOwner (n, 7) (n, 9) (0, 10) (n, 7))]
         [AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9)];
     mkMicroopPath "HasViCL_L1L2"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [7; 5; 9] ++
          [((0, 10), (n, 7))] ++ StraightLine 0 [10; 11])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "ViCLSourcing" (SourcedAtLevel 10 (0, 10));
          MultiChoiceConstraint "InvCache" (InvalidateCache (n, 7) (n, 9));
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 9))]
         [AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9);
          OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)];
     mkMicroopPath "HasViCL_L1L2Initial"
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [7; 5; 9] ++
          [((0, 10), (n, 7))] ++ StraightLine 0 [10; 11])
         (FiveStageTSOCCPropagations n)
         [MultiChoiceConstraint "STBEmpty" (FlushSameAddress (n, 6) (n, 3));
          MultiChoiceConstraint "InvCache" (InvalidateCache (n, 7) (n, 9));
          MultiChoiceConstraint "ReadsZero" ReadsZero;
          MultiChoiceConstraint "InternalAtomicity" (AtomicityEdges (n, 5) (n, 7) (n, 9))]
         [AddEdgesConstraint "ReadsBeforeAll" (ReadsBeforeAll (n, 9));
          AddEdgesConstraint "InvSharers" (SourceOtherViCLBeforeNextWriters (n, 7));
          AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11));
          AddEdgesConstraint "ExternalAtomicity" (AtomicBeforeAfter (n, 7) (n, 7))]
         [OtherViCL (n, 7) (n, 7) (n, 9) (n, 9);
          OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)]
     ]
 | RMWWrite _ _ => [
     mkMicroopPath "WriteL1L2Downgrade"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8; 9] ++
         [((n, 8), (0, 10))] ++ StraightLine 0 [10; 11])
       (FiveStageTSOCCPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8));
        AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 9);
        OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)];
     mkMicroopPath "WriteL1OnlyDowngrade"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 8; 9])
       (FiveStageTSOCCPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 8))]
       [SWViCL (n, 7) (n, 7) (n, 8) (n, 9)];
     mkMicroopPath "WriteL1L2NoDowngrade"
       (StraightLine n [0; 1; 2; 3; 4; 5; 7; 6] ++ StraightLine n [7; 9] ++
         [((n, 7), (0, 10))] ++ StraightLine 0 [10; 11])
       (FiveStageTSOCCPropagations n)
       []
       [AddEdgesConstraint "InvSharers" (InvalidateSWViCLBeforeNextWriters (n, 7) (n, 9));
        AddEdgesConstraint "InvSharers" (InvalidateOtherViCLBeforeNextWriters (0, 10) (0, 11))]
       [SWViCL (n, 7) (n, 7) (n, 9) (n, 9);
        OtherViCL (0, 10) (0, 10) (0, 11) (0, 11)]
     ]
 end.

Definition FiveStageTSOCC_Processor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "FiveStageTSOCCPipeline" n
    (FiveStageTSOCCMicroopPaths n) FiveStageTSOCCPipelineStages in
  mkProcessor "FiveStageTSOCC_Processor" (Map p (Range num_cores)).
