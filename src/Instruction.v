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

Require Import String.
Require Import Arith.

(** ** Basic Type Definitions *)
Definition InstID := nat.
Definition ThreadID := nat.
Definition IntraInstructionID := nat.
Definition Address := nat.
Definition Data := nat.
Definition FenceType := string.

(** ** Instructions *)

(** *** [MemoryAccess] *)
(** A [MemoryAccess] is the part of the [Microop] data structure representing
interaction with the memory system. *)
Inductive MemoryAccess : Set :=
| Read     : Address -> Data -> MemoryAccess
| Write    : Address -> Data -> MemoryAccess
(* There are (at least) two ways to model RMWs: 1) as two (or more) separate
[Microop]s, with some extra constraints to enforce atomicity, or 2) as a single
[Microop] which performs the RMW all at once.  For the moment, we prefer #1, as
it allows us to model both the read and the write ViCLs.*)
| RMWRead  : Address -> Data -> MemoryAccess
| RMWWrite : Address -> Data -> MemoryAccess
| Fence    : FenceType       -> MemoryAccess
(* LL/SC, etc can be added here for microarchitectures that need them. *).

(** *** [Microop] *)
(** A [Microop] is either an instruction or part of an instruction.  Each
[Microop] has a globally unique ID [globalID], a thread ID [threadID], an
intra-instruction ID [intraInstructionID] (for when a single macroinstruction
has multiple microops), and a [MemoryAccess] [access] describing the memory
semantics. *)
Record Microop : Set := mkMicroop {
  globalID : InstID;
  threadID : ThreadID;
  intraInstructionID : IntraInstructionID;
  access : MemoryAccess
}.

(** *** [SameAddress] *)
Definition SameAddress
  (x y : Microop)
  : bool :=
  let ax :=
    match x with
    | mkMicroop _ _ _ (Read     a _) => Some a
    | mkMicroop _ _ _ (Write    a _) => Some a
    | mkMicroop _ _ _ (RMWRead  a _) => Some a
    | mkMicroop _ _ _ (RMWWrite a _) => Some a
    | _ => None
    end in
  let ay :=
    match y with
    | mkMicroop _ _ _ (Read     a _) => Some a
    | mkMicroop _ _ _ (Write    a _) => Some a
    | mkMicroop _ _ _ (RMWRead  a _) => Some a
    | mkMicroop _ _ _ (RMWWrite a _) => Some a
    | _ => None
    end in
  match (ax, ay) with
  | (Some ax', Some ay') => beq_nat ax' ay'
  | _ => false
  end.

(** *** [beq_uop] *)
(** Boolean equality check for two [Microop]s. *)
Definition beq_uop
  (a b : Microop)
  : bool :=
  beq_nat (globalID a) (globalID b).

(** ** [Thread]s and [Program]s *)
(** A [Thread] is a list of [Microop]s.  A [Program] is a list of [Thread]s. *)
Definition Thread : Set := list Microop.

Definition Program : Set := list Thread.

