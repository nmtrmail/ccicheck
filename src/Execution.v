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
Require Import PipeGraph.Util.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.

Import ListNotations.

Definition beq_nat_pair
  (a b : nat * nat)
  : bool :=
  andb (beq_nat (fst a) (fst b)) (beq_nat (snd a) (snd b)).

Definition WritesList : Set := list ((nat * nat) * (list Microop)).

Definition SortWritesHelper
  (l : WritesList)
  (u : Microop)
  : WritesList :=
  match u with
  | mkMicroop g t n (Write a d) =>
      AppendToMatch (beq_nat_pair (a, d)) l (a, d) u
  | mkMicroop g t n (RMWWrite a d) =>
      AppendToMatch (beq_nat_pair (a, d)) l (a, d) u
  | _ => l
  end.

Fixpoint SortWrites
  (p : list Microop)
  : WritesList :=
  fold_left SortWritesHelper p [].

(** **** [AllPermutationsHelper3] *)
(** Prepend [h] to each of the list in [ts].  If [ts] is empty, create a new
list with only [h]. *)
Definition AllPermutationsHelper3
  {A : Type}
  (h : A)
  (ts : list (list A))
  : list (list A) :=
  match ts with
  | [] => []
  | _ => Map (cons h) ts
  end.

Module AllPermutationsHelper3Example.

Example e1: AllPermutationsHelper3 0 [[1; 2]; [3; 4]] =
  [[0; 1; 2]; [0; 3; 4]].
Proof.
  auto.
Qed.

Example e2: AllPermutationsHelper3 0 [] = [].
Proof.
  auto.
Qed.

End AllPermutationsHelper3Example.

Fixpoint AllPermutationsHelper2
  {A : Type}
  (a b : list A)
  : list (A * list A) :=
  match b with
  | h::t =>
      (** Ultimately: prepend [h] to each permutation of [a ++ t].
      This function returns the set of all [(h, a++t)] pairs *)
      (h, a ++ t) :: AllPermutationsHelper2 (a ++ [h]) t
  | [] => []
  end.

Module AllPermutationsHelper2Example.

Example e1: AllPermutationsHelper2 [0; 1; 2] [3; 4; 5] =
  [(3, [0; 1; 2; 4; 5]); (4, [0; 1; 2; 3; 5]); (5, [0; 1; 2; 3; 4])].
Proof.
  auto.
Qed.

Example e2: AllPermutationsHelper2 [] [0; 1] = [(0, [1]); (1, [0])].
Proof.
  auto.
Qed.

Example e3: AllPermutationsHelper2 [0; 1] [] = [].
Proof.
  auto.
Qed.

End AllPermutationsHelper2Example.

Fixpoint AllPermutationsHelper
  {A : Type}
  (i : nat)
  (l : list A)
  (valid_last_element : A -> bool)
  : list (list A) :=
  match (i, l) with
  | (S i', []) => []
  | (S i', [h]) =>
      if valid_last_element h
      then [[h]]
      else []
  | (S i', _) =>
      let p := AllPermutationsHelper2 [] l in
      let p' :=
        (** For each pairing of (h, others) returned by
        [AllPermutationsHelper2], recursively calculate the set of all
        permutations of "others", and then prepend [h] to each. *)
        Map (fun x => AllPermutationsHelper3 (fst x)
          (AllPermutationsHelper i' (snd x) valid_last_element)) p in
      (** Flatten the list of all permutations *)
      fold_left (app_tail (A:=_)) p' []
  | (O, _) => []
  end.

Definition AllPermutations
  {A : Type}
  (valid_last_element : A -> bool)
  (l : list A)
  : list (list A) :=
  AllPermutationsHelper (length l) l valid_last_element.

Module AllPermutationsExample.

Example e1 : AllPermutations (fun _ => true) [0; 1; 2] =
  [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]].
Proof.
  auto.
Qed.

Example e2 : AllPermutations (beq_nat 2) [0; 1; 2] =
  [[0; 1; 2]; [1; 0; 2]].
Proof.
  auto.
Qed.

End AllPermutationsExample.

Fixpoint WritesByAddressHelper
  (l : list (nat * list (list Microop)))
  (w : WritesList)
  : list (nat * list (list Microop)) :=
  match w with
  | ((a, d), i) :: t =>
      WritesByAddressHelper (AppendToMatch (beq_nat a) l a i) t
  | [] => l
  end.

Definition WritesByAddress
  (w : WritesList)
  : list (list Microop) :=
  let f x := fold_left (app_tail (A:=_)) (snd x) [] in
  Map f (WritesByAddressHelper [] w).

Fixpoint ValidWSScenario
  (last_values : list (Address * Data))
  (uop : Microop)
  : bool :=
  match uop with
  | mkMicroop _ _ _ (Write a d) =>
      match find (fun x => beq_nat a (fst x)) last_values with
      | Some (_, d') => beq_nat d d'
      | None => true (* If no last value was specified, anything is OK *)
      end
  | mkMicroop _ _ _ (RMWWrite a d) =>
      match find (fun x => beq_nat a (fst x)) last_values with
      | Some (_, d') => beq_nat d d'
      | None => true (* If no last value was specified, anything is OK *)
      end
  | _ => false
  end.

Definition WSScenarios
  (w : WritesList)
  (last_values : list (Address * Data))
  : list (list (list Microop)) :=
  CrossProduct (Map (AllPermutations (ValidWSScenario last_values)) (WritesByAddress w)).
Module ExecutionExamples.

Definition e2Microops := [
    mkMicroop 0 0 0 (Write 0 0);
    mkMicroop 1 0 0 (Write 1 1);
    mkMicroop 2 1 0 (Read  0 0)].

Example e2c :
  WSScenarios (SortWrites e2Microops) []
  = [
      [[mkMicroop 0 0 0 (Write 0 0)];
       [mkMicroop 1 0 0 (Write 1 1)]]
    ].
Proof.
auto.
Qed.

Example e2d :
  WSScenarios (SortWrites e2Microops) [(1, 2)]
  = [].
Proof.
auto.
Qed.

Example e3 :
  WSScenarios (SortWrites [
    mkMicroop 0 0 0 (Write 0 1);
    mkMicroop 1 0 0 (Write 1 1);
    mkMicroop 2 1 0 (Write 0 2)]) []
  = [
  [[mkMicroop 2 1 0 (Write 0 2);
    mkMicroop 0 0 0 (Write 0 1)];
   [mkMicroop 1 0 0 (Write 1 1)]];
  [[mkMicroop 0 0 0 (Write 0 1);
    mkMicroop 2 1 0 (Write 0 2)];
   [mkMicroop 1 0 0 (Write 1 1)]]
  ].
Proof.
auto.
Qed.

End ExecutionExamples.
