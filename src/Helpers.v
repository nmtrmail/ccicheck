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
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Processor.
Require Import PipeGraph.Graph.
Require Import PipeGraph.Debug.

Import ListNotations.
Open Scope string_scope.

(** For [SameData], the argument order matters!  If [x] is a [RMW] [Microop],
then look at the written data.  If [y] is a [RMW] [Microop], look at the read
data. *)
Definition SameData
  (x y : Microop)
  : bool :=
  let xd := match x with
  | mkMicroop _ _ _ (Read _ d) => Some d
  | mkMicroop _ _ _ (Write _ d) => Some d
  | mkMicroop _ _ _ (RMWRead _ d) => Some d
  | mkMicroop _ _ _ (RMWWrite _ d) => Some d
  | _ => None
  end in
  let yd := match y with
  | mkMicroop _ _ _ (Read _ d) => Some d
  | mkMicroop _ _ _ (Write _ d) => Some d
  | mkMicroop _ _ _ (RMWRead _ d) => Some d
  | mkMicroop _ _ _ (RMWWrite _ d) => Some d
  | _ => None
  end in
  match (xd, yd) with
  | (Some d1, Some d2) => beq_nat d1 d2
  | _ => false
  end.

Definition ReadsBetweenFilter
  (uop : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  (* the [SameData] order matters: (fst x) is the source, and uop is the dest. *)
  andb
    (andb (beq_loc loc (snd x)) (negb (beq_uop uop (fst x))))
    (andb (SameAddress uop (fst x)) (SameData (fst x) uop)).

Definition ReadsBetween
  (a b c : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  let candidates_a := filter (ReadsBetweenFilter uop a) nodes in
  let candidates_c := filter (ReadsBetweenFilter uop c) nodes in
  let candidates := PairNodesByMicroop candidates_a candidates_c [] in
  let f x := [(fst x, (uop, b), name); ((uop, b), snd x, name)] in
  Some (Map f candidates).

Definition ReadsBetweenSLRFilter
  (a b : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  let valid :=
    andb (beq_loc loc (snd x))
      (andb (blt_nat (globalID a) (globalID (fst x)))
            (blt_nat (globalID (fst x)) (globalID b))) in
  let valid := Println valid ["RBSLRFilter: "; stringOfNat (globalID a);
    " < "; stringOfNat (globalID (fst x)); " < "; stringOfNat (globalID b);
    "?"] in
  match fst x with
  | mkMicroop _ _ _ (Read _ _) => valid
  | mkMicroop _ _ _ (Write _ _) => valid
  | mkMicroop _ _ _ (RMWRead _ _) => valid
  | mkMicroop _ _ _ (RMWWrite _ _) => valid
  | _ => false
  end.

Definition ReadsBetweenSLRHelper
  (a b c : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates_a := filter (ReadsBetweenFilter uop a) nodes in
  let candidates_c := filter (ReadsBetweenFilter uop c) nodes in
  let candidates := PairNodesByMicroop candidates_a candidates_c [] in
  let candidates := Println candidates ["RBSLR: ";
    stringOfNat (List.length candidates); " candidates"] in
  let f x :=
    let nodes_in_between :=
      filter (ReadsBetweenSLRFilter (fst (snd x)) uop b) nodes in
    let nodes_in_between := Println nodes_in_between ["RBSLR: ";
      stringOfNat (List.length nodes_in_between); " nodes in between"] in
    let g y := (y, snd x, name) in
    (fst x, (uop, b), name) :: ((uop, b), snd x, name) ::
      Map g nodes_in_between in
  Some (Map f candidates).

Definition ReadsBetweenSLR
  (a b c : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  ReadsBetweenSLRHelper a b c name nodes uop [].

Definition SourcedFromFilter
  (uop : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  (* the [SameData] order matters: (fst x) is the source, and uop is the dest. *)
  andb
    (andb (beq_loc loc (snd x)) (negb (beq_uop uop (fst x))))
    (andb (SameAddress uop (fst x)) (SameData (fst x) uop)).

Definition SourcedFromHelper
  (a b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates := filter (SourcedFromFilter uop a) nodes in
  let f x := [(x, (uop, b), name)] in
  Some (Map f candidates).

Definition SourcedFrom
  (a b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  SourcedFromHelper a b name nodes uop [].

Definition SourcedAtLevelFilter
  (uop : Microop)
  (stage : nat)
  (x : GraphNode)
  : bool :=
  (* the [SameData] order matters: (fst x) is the source, and uop is the dest. *)
  andb
    (andb (beq_nat stage (snd (snd x))) (negb (beq_uop uop (fst x))))
    (andb (SameAddress uop (fst x)) (SameData (fst x) uop)).

Definition SourcedAtLevelHelper
  (a : nat)
  (b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates := filter (SourcedAtLevelFilter uop a) nodes in
  let f x := [(x, (uop, b), name)] in
  Some (Map f candidates).

Definition SourcedAtLevel
  (a : nat)
  (b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  SourcedAtLevelHelper a b name nodes uop [].

(* A rearrangement of the parameters of SourcedAtLevel for easier partial application. *)
Definition SourcedAtLevel2
  (b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (a : nat)
  : option (list (list GraphEdge)) :=
  SourcedAtLevelHelper a b name nodes uop [].

Fixpoint ConvertToOptList
  (a : list GraphEdge)
  (a' : list (list GraphEdge))
  : option (list (list GraphEdge)) :=
  match a with
  | [] => Some a'
  | h::t => ConvertToOptList t ([h]::a')
  end.

Fixpoint KeepFirstHelper
  (a : list GraphEdge)
  (b : list GraphEdge)
  : list GraphEdge :=
  let f x y := match y with
               | ((uop, loc), n2, str) => beq_uop x uop
               end in
  match a with
  | [] => b
  | h::t => match h with
            | ((uop, _), _, _) => match (find (f uop) b) with
                                  | None => KeepFirstHelper t (h::b)
                                  | _ => KeepFirstHelper t b
                                  end
            end
  end.

Fixpoint KeepFirst
  (a : list (list GraphEdge))
  (b : list GraphEdge)
  : list GraphEdge :=
  match a with
  | [] => b
  | h::t => match h with
            | [] => KeepFirst t b
            | _ => KeepFirst t (KeepFirstHelper h b)
            end
  end.

Definition SourcedAtLevels
  (a : list nat)
  (b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  : list GraphEdge :=
  let le := Map (SourcedAtLevel2 b name nodes uop) a in
  let f x := match x with
             | Some x' => fold_left (app_rev (A:=_)) x' []
             (* This should never happen, as SourcedAtLevel2 always returns Some <list>.*)
             | _ => Warning ([]) ["SourcedAtLevel2 didn't return Some <list>."]
             end in
  let le' := Map f le in
  KeepFirst le' [].

Definition FlushAllAddressesFilter
  (uop : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  let valid :=
    andb (beq_loc loc (snd x)) (blt_nat (globalID (fst x)) (globalID uop)) in
  match fst x with
  | mkMicroop _ _ _ (Read _ _) => valid
  | mkMicroop _ _ _ (Write _ _) => valid
  | mkMicroop _ _ _ (RMWRead _ _) => valid
  | mkMicroop _ _ _ (RMWWrite _ _) => valid
  | _ => false
  end.

Definition FlushAllAddressesHelper
  (a b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates := filter (FlushAllAddressesFilter uop a) nodes in
  let f x := (x, (uop, b), name) in
  match candidates with
  | [] => None
  | _ => Some [(Map f candidates)]
  end.

Definition FlushAllAddresses
  (a b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  FlushAllAddressesHelper a b name nodes uop [].

Definition FlushSameAddressFilter
  (uop : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  andb (andb (beq_loc loc (snd x)) (SameAddress uop (fst x)))
    (blt_nat (globalID (fst x)) (globalID uop)).

Definition FlushSameAddressHelper
  (a b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates := filter (FlushSameAddressFilter uop a) nodes in
  let f x := [(x, (uop, b), name)] in
  match candidates with
  | [] => None
  | _ => Some (Map f candidates)
  end.

Definition FlushSameAddress
  (a b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  FlushSameAddressHelper a b name nodes uop [].

Definition FlushBeforeLaterFilter
  (uop : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  let valid :=
    andb (beq_loc loc (snd x)) (blt_nat (globalID uop) (globalID (fst x))) in
  match fst x with
  | mkMicroop _ _ _ (Read _ _) => valid
  | mkMicroop _ _ _ (Write _ _) => valid
  | mkMicroop _ _ _ (RMWRead _ _) => valid
  | mkMicroop _ _ _ (RMWWrite _ _) => valid
  | _ => false
  end.

Definition FlushBeforeLaterHelper
  (a b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates := filter (FlushBeforeLaterFilter uop b) nodes in
  let f x := ((uop, a), x, name) in
  match candidates with
  | [] => None
  | _ => Some [(Map f candidates)]
  end.

Definition FlushBeforeLater
  (a b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  FlushBeforeLaterHelper a b name nodes uop [].

Fixpoint ReadsBeforeAllHelper
  (vicls : list (Microop * ViCL))
  (node : GraphNode)
  (adj : AdjacencyList)
  : option (list GraphEdge) :=
  match vicls with
  | (h, SWViCL _ c _ _)::t =>
      if andb (SameAddress h (fst node)) (negb (beq_uop h (fst node)))
      then match AdjacencyListFind adj (h, c) node with
      | Some _ => Println (Some []) ["Store "; stringOfNat (globalID h);
          " is visible to instruction "; stringOfNat (globalID (fst node));
          " even though it should read from the initial condition"]
      | None => ReadsBeforeAllHelper t node adj
      end
      else ReadsBeforeAllHelper t node adj
  | _::t => ReadsBeforeAllHelper t node adj
  | [] => None
  end.

Definition ReadsBeforeAll
  (vicl_c : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list GraphEdge) :=
  match TransitiveClosure edges with
  | TC adj => ReadsBeforeAllHelper vicls (uop, vicl_c) adj
  | TCError _ => Println None ["ReadsBeforeAll: already cyclic"]
  end.

Definition ReadsZero
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  match uop with
  | mkMicroop _ _ _ (Read _ 0) => None
  | mkMicroop _ _ _ (RMWRead _ 0) => None
  | _ => Println (Some [])
      ["Read returns non-zero; doesn't read from initial state"]
  end.

Fixpoint LaterSWViCLsForOtherViCL
  (uop : Microop)
  (c : Location)
  (adj : AdjacencyList)
  (vicls : list (Microop * ViCL))
  (latest : option GraphNode)
  (later : list GraphNode)
  : option (list GraphNode) :=
  match vicls with
  | h::t =>
      let h := Println h
        ["LaterSWViCLsForOtherViCL: "; stringOfNat (globalID uop); " @ ";
        stringOfNat (snd c); ", "; stringOfNat (globalID (fst h)); " @ ";
        stringOfNat (snd (ViCLCreate (snd h)))] in
      if andb (SameAddress uop (fst h))
        (orb (negb (beq_uop uop (fst h))) (negb (beq_loc c (ViCLCreate (snd h)))))
      then
        match snd h with
        | SWViCL _ h_c _ _ =>
          let h_c := (fst h, h_c) in
          match AdjacencyListFind adj h_c (uop, c) with
          | Some _ =>
              match latest with
              | Some l =>
                  match AdjacencyListFind adj h_c l with
                  | Some _ =>
                      let uop := Println uop [tab; "earlier than previous latest"] in
                      LaterSWViCLsForOtherViCL uop c adj t latest later
                  | None =>
                      let uop := Println uop [tab; "new latest"] in
                      LaterSWViCLsForOtherViCL uop c adj t (Some h_c) later
                  end
              | None =>
                  let uop := Println uop [tab; "no previous latest; now this is latest"] in
                  LaterSWViCLsForOtherViCL uop c adj t (Some h_c) later
              end
          | None =>
              let uop := Println uop [tab; "not earlier"] in
              LaterSWViCLsForOtherViCL uop c adj t latest (h_c :: later)
          end
        | _ =>
            let uop := Println uop [tab; "Not a SWViCL"] in
            LaterSWViCLsForOtherViCL uop c adj t latest later
        end
      else
        let uop := Println uop [tab; "Different address and/or same ViCL"] in
        LaterSWViCLsForOtherViCL uop c adj t latest later
  | [] =>
      (* Get latest value *)
      match latest with
      | Some l =>
          (* the [SameData] order matters: (fst l) is the source, and uop is
             the dest. *)
          if SameData (fst l) uop
          then Println (Some later) ["Same data"]
          else Println None ["Different data!"]
      | None =>
          match uop with
          | mkMicroop _ _ _ (Read _ 0) => Println (Some later) ["Reads zero"]
          | mkMicroop _ _ _ (RMWRead _ 0) => Println (Some later) ["Reads zero"]
          | _ => Println None ["Doesn't read zero"]
          end
      end
  end.

Definition InvalidateOtherViCLBeforeNextWriters
  (self_c self_i : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list GraphEdge) :=
  match AdjacencyListTransitiveClosure (AdjacencyListFromEdges edges) with
  | TC adj =>
      match LaterSWViCLsForOtherViCL uop self_c adj vicls None [] with
      | Some later_vicls =>
          match later_vicls with
          | [] => None
          | _ => Some (Map (fun x => ((uop, self_i), x, name)) later_vicls)
          end
      | None =>
          Println (Some []) ["Get Latest Value constraint not satisfied"]
      end
  | _ => Println None ["Input to InvalidateBeforeNextWriters is cyclic"]
  end.

Definition SourceOtherViCLBeforeNextWriters
  (self_c : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list GraphEdge) :=
  match AdjacencyListTransitiveClosure (AdjacencyListFromEdges edges) with
  | TC adj =>
      match LaterSWViCLsForOtherViCL uop self_c adj vicls None [] with
      | Some later_vicls =>
          match later_vicls with
          | [] => None
          | _ => Some (Map (fun x => ((uop, self_c), x, name)) later_vicls)
          end
      | None =>
          Println (Some []) ["Get Latest Value constraint not satisfied"]
      end
  | _ => Println None ["Input to SourceOtherViCLBeforeNextWriters is cyclic"]
  end.

Fixpoint LaterSWViCLsForSWViCL
  (uop : Microop)
  (c : Location)
  (adj : AdjacencyList)
  (vicls : list (Microop * ViCL))
  (later : list GraphNode)
  : option (list GraphNode) :=
  match vicls with
  | h::t =>
      match snd h with
      | SWViCL _ h_c _ _ =>
        if andb (SameAddress uop (fst h)) (negb (beq_uop uop (fst h)))
        then
          let h_c := (fst h, h_c) in
          match AdjacencyListFind adj h_c (uop, c) with
          | Some _ => LaterSWViCLsForSWViCL uop c adj t later
          | None => LaterSWViCLsForSWViCL uop c adj t (h_c :: later)
          end
        else LaterSWViCLsForSWViCL uop c adj t later
      | _ => LaterSWViCLsForSWViCL uop c adj t later
      end
  | [] => Some later
  end.

Definition InvalidateSWViCLBeforeNextWriters
  (self_c self_i : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list GraphEdge) :=
  match AdjacencyListTransitiveClosure (AdjacencyListFromEdges edges) with
  | TC adj =>
      match LaterSWViCLsForSWViCL uop self_c adj vicls [] with
      | Some later_vicls =>
          match later_vicls with
          | [] => None
          | _ => Some (Map (fun x => ((uop, self_i), x, name)) later_vicls)
          end
      | None =>
          Println (Some []) ["Get Latest Value constraint not satisfied"]
      end
  | _ => Println None ["Input to InvalidateBeforeNextWriters is cyclic"]
  end.

Definition IsStore
  (uop : Microop)
  : bool :=
  match uop with
  | mkMicroop _ _ _ (Write    _ _) => true
  | mkMicroop _ _ _ (RMWWrite _ _) => true
  | _ => false
  end.

Fixpoint ParallelViCLOptions
  (name : string)
  (uop : Microop)
  (self_c self_i : Location)
  (parallel : list (Microop * ViCL))
  (choices : list (list (list GraphEdge)))
  : option (list (list GraphEdge)) :=
  match parallel with
  | h::t =>
      if IsStore (fst h) then
          (* Either this store ViCL is downgraded (and thus evicted) before the
             fence/missing instr's ViCL, or it's downgraded after the fence/missing
             instr's ViCL. *)
          match ViCLDowngrade (snd h) with
          | None => Warning None ["Store without downgrade in ParallelViCLOptions"]
          | Some d =>
              let new_edges := [[((fst h, ViCLEvict (snd h)), (uop, self_c), name)];
                [((uop, self_c), (fst h, d), name)]] in
              ParallelViCLOptions name uop self_c self_i t (new_edges :: choices)
          end
      else
          let new_edges := [[((fst h, ViCLEvict (snd h)), (uop, self_c), name)];
            [((uop, self_c), (fst h, ViCLCreate (snd h)), name)]] in
          ParallelViCLOptions name uop self_c self_i t (new_edges :: choices)
  | [] =>
     Some (Map (fun x => fold_left (app_rev (A:=_)) x []) (CrossProduct choices))
  end.

Fixpoint SortViCLsBeforeOrAfter
  (name : string)
  (uop : Microop)
  (self_c self_i : Location)
  (adj : AdjacencyList)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (earlier parallel later : list (Microop * ViCL))
  : option (list (list GraphEdge)) :=
  match vicls with
  | h::t =>
      let h_c := ViCLCreate (snd h) in
      let h_i := ViCLEvict (snd h) in
      if andb (beq_loc h_c self_c) (negb (beq_uop uop (fst h)))
      then
        if IsStore (fst h) then
            (* Does the store have a downgrade? *)
            match ViCLDowngrade (snd h) with
            | None => SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                        earlier parallel later (* No DG - immune to invalidation, ignore *)
            | Some d => match (AdjacencyListFind adj (fst h, d) (uop, self_c),
                  AdjacencyListFind adj (uop, self_c) (fst h, d)) with
                        | (Some _, Some _) =>
                            Println
                            (SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                              (h::earlier) parallel later )
                            ["Already cyclic at SortViCLsBeforeOrAfter"]
                        (* DG before missing ViCL created - treat it just like any shared ViCL
                           that was created beforehand *)
                        | (Some _, None) =>
                            SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                              (h::earlier) parallel later
                        | (None, None) => (* Could be downgraded before or after *)
                            SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                              earlier (h::parallel) later
                        (* DG after missing ViCL created - immune to this invalidation, ignore *)
                        | (None, Some _) =>
                            SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                              earlier parallel later
                        end
            end
        else
            let h_c := (fst h, h_c) in
            match (AdjacencyListFind adj h_c (uop, self_c),
              AdjacencyListFind adj (uop, self_c) h_c) with
            | (Some _, Some _) =>
                Println
                (SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                  (h::earlier) parallel later)
                ["Already cyclic at SortViCLsBeforeOrAfter"]
            | (Some _, None) =>
                SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                  (h::earlier) parallel later
            | (None, None) =>
                SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                  earlier (h::parallel) later
            | (None, Some _) =>
                SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes
                  earlier parallel (h::later)
            end
      else SortViCLsBeforeOrAfter name uop self_c self_i adj t nodes earlier parallel later
  | [] =>
      let f_earlier x := ((fst x, ViCLEvict (snd x)), (uop, self_c), name) in
      let f_later x := ((uop, self_c), (fst x, ViCLCreate (snd x)), name) in
      let f_known := app_rev (Map f_earlier earlier) (Map f_later later) in
      let f_known := Println f_known
        ["SortViCLsBeforeOrAfter "; stringOfNat (globalID uop); ": ";
         stringOfNat (List.length earlier); " earlier, ";
         stringOfNat (List.length parallel); " parallel, ";
         stringOfNat (List.length later); " later"] in
      ParallelViCLOptions name uop self_c self_i parallel [[f_known]]
  end.

Fixpoint SortViCLsForFence
  (name : string)
  (uop : Microop)
  (self_c self_i sort_loc : Location)
  (adj : AdjacencyList)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (earlier parallel : list (Microop * ViCL))
  : option (list (list GraphEdge)) :=
  match vicls with
  | h::t =>
      let h_c := ViCLCreate (snd h) in
      let h_i := ViCLEvict (snd h) in
      if (beq_loc h_c sort_loc) then
        if IsStore (fst h) then
            (* Does the store have a downgrade? *)
            match ViCLDowngrade (snd h) with
            | None => SortViCLsForFence name uop self_c self_i sort_loc adj t nodes
                        earlier parallel (* No DG - immune to invalidation, ignore *)
            | Some d => match (AdjacencyListFind adj (fst h, d) (uop, self_c),
                  AdjacencyListFind adj (uop, self_c) (fst h, d)) with
                        | (Some _, Some _) =>
                            Println
                            (SortViCLsForFence name uop self_c self_i sort_loc adj t nodes
                              (h::earlier) parallel)
                            ["Already cyclic at SortViCLsForFence"]
                        (* DG before fence at memory - treat it just like any shared ViCL
                           that was created beforehand *)
                        | (Some _, None) =>
                            SortViCLsForFence name uop self_c self_i sort_loc adj t nodes
                              (h::earlier) parallel
                        | (None, None) => (* Could be downgraded before or after *)
                            SortViCLsForFence name uop self_c self_i sort_loc adj t nodes
                              earlier (h::parallel)
                        (* DG after fence at memory - immune to this invalidation, ignore *)
                        | (None, Some _) =>
                            SortViCLsForFence name uop self_c self_i sort_loc adj t nodes
                              earlier parallel
                        end
            end
        (* All load ViCLs from prior instructions must expire before the fence reaches the memory stage. *)
        else SortViCLsForFence name uop self_c self_i sort_loc adj t nodes (h::earlier) parallel
      (* Not a ViCL we should be ordering here, so skip it. *)
      else SortViCLsForFence name uop self_c self_i sort_loc adj t nodes earlier parallel
  | [] =>
      let f_earlier x := ((fst x, ViCLEvict (snd x)), (uop, self_c), name) in
      let f_known := Map f_earlier earlier in
      ParallelViCLOptions name uop self_c self_i parallel [[f_known]]
  end.

Definition InvalidateCache
  (self_c self_i : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  match AdjacencyListTransitiveClosure (AdjacencyListFromEdges edges) with
  | TC adj =>
      match SortViCLsBeforeOrAfter name uop self_c self_i adj vicls nodes [] [] [] with
      | Some new_edges =>
          match new_edges with
          | [] => None
          | _ => Some new_edges
          end
      | None => Warning (Some []) ["InvalidateCache returned None"]
      end
  | _ => Println (Some []) ["Input to InvalidateCache is cyclic"]
  end.

Definition InvalidateCacheForPriorInsts
  (self_c self_i sort_loc : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  let f x := match x with
  | (u, v) => blt_nat (globalID uop) (globalID u)
  end in
  match AdjacencyListTransitiveClosure (AdjacencyListFromEdges edges) with
  | TC adj =>
      match SortViCLsForFence name uop self_c self_i sort_loc adj (removeb f vicls) nodes [] [] with
      | Some new_edges =>
          match new_edges with
          | [] => None
          | _ => Some new_edges
          end
      | None => Warning (Some []) ["InvalidateCacheForPriorInsts returned None"]
      end
  | _ => Println (Some []) ["Input to InvalidateCacheForPriorInsts is cyclic"]
  end.

Definition InvalidateCacheIfNotLastWriter
  (self_c self_i : Location)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  (src_edge : GraphEdge)
  : list (list GraphEdge) :=
  match src_edge with
  | ((src_uop, (src_proc, st1)), (cur_uop, (cur_proc, st2)), n) =>
  match beq_nat cur_proc src_proc with
  (* The constraint is satisfied: there's no need to inv the cache as we were the last owner *)
  | true => [[src_edge]]
  (* We need to add edges; invalidate the cache as appropriate, and add in the sourcing edge to each possibility. *)
  | false => let new_edges := InvalidateCache self_c self_i "InvCache" vicls nodes edges uop in
                match new_edges with
                | None => [[src_edge]] (* no edges to add *)
                | Some actual_edges => let f x y := (x::y) in
                                        Map (f src_edge) actual_edges
                end
  end
  end.

Definition SourceAtAndInvIfNotLastOwner
  (self_c self_i : Location)
  (a : list nat)
  (b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  let srcs := SourcedAtLevels a b name nodes uop in
  Some (fold_left (app_rev (A:=_)) (Map (InvalidateCacheIfNotLastWriter self_c self_i vicls nodes edges uop) srcs) []).

Definition SourceFromAndInvIfNotLastOwner
  (self_c self_i a b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  let srcs := SourcedFrom a b name vicls nodes edges uop in
  match srcs with
  | None => Warning (Some []) ["No SourceFrom possibilities for this ViCL!"]
  | Some srcs' => let srcs'' := fold_left (app_rev (A:=_)) srcs' [] in
      Some (fold_left (app_rev (A:=_)) (Map (InvalidateCacheIfNotLastWriter self_c self_i vicls nodes edges uop) srcs'') [])
  end.

Fixpoint FindRMWPartner
  (uop_id : nat)
  (vicl_c : Location)
  (vicls : list (Microop * ViCL))
  : option GraphNode :=
  match vicls with
  | h::t =>
      if andb
        (beq_nat uop_id (globalID (fst h)))
        (beq_loc vicl_c (ViCLCreate (snd h)))
      then Some (fst h, ViCLCreate (snd h))
      else FindRMWPartner uop_id vicl_c t
  | [] => Println None ["Could not find write paired with RMWRead!"]
  end.

Fixpoint AtomicBeforeAfterHelper
  (r_c w_c : GraphNode)
  (name : string)
  (vicls : list (Microop * ViCL))
  (adj : AdjacencyList)
  (edges : list GraphEdge)
  : option (list GraphEdge) :=
  match vicls with
  | h::t =>
      let vicl_node := (fst h, ViCLCreate (snd h)) in

      if orb
        (beq_uop (fst vicl_node) (fst r_c))
        (beq_uop (fst vicl_node) (fst w_c))
      then AtomicBeforeAfterHelper r_c w_c name t adj edges
      else

      (* if the ViCL is before the W, it must be before the R too *)
      let edges :=
        if AdjacencyListFind adj vicl_node w_c
        then
          Println ((vicl_node, r_c, name) :: edges)
            ["Found node before W: adding edge to make node before R: ";
              GraphvizShortStringOfGraphNode vicl_node; " --> ";
              GraphvizShortStringOfGraphNode r_c]
        else edges
      in

      (* if the ViCL is after the R, it must be after the W too *)
      let edges :=
        if AdjacencyListFind adj r_c vicl_node
        then Println ((w_c, vicl_node, name) :: edges)
            ["Found node after R: adding edge to make node after W: ";
              GraphvizShortStringOfGraphNode w_c; " --> ";
              GraphvizShortStringOfGraphNode vicl_node]
        else edges
      in

      AtomicBeforeAfterHelper r_c w_c name t adj edges

  | [] => Some edges
  end.

Definition AtomicBeforeAfter
  (r_loc w_loc : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list GraphEdge) :=
  match FindRMWPartner (S (globalID uop)) w_loc vicls with
  | Some w =>
      let a := AdjacencyListFromEdges edges in
      match AdjacencyListTransitiveClosure a with
      | TC adj => AtomicBeforeAfterHelper (uop, r_loc) w name vicls adj []
      | _ => Println None ["AtomicBeforeAfter: already cyclic"]
      end
  | None => Println (Some []) ["AtomicBeforeAfter: Unpaired atomic"]
  end.

Definition AtomicReadsBetweenHelper
  (a b c : Location)
  (w : GraphNode)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates_a := filter (ReadsBetweenFilter uop a) nodes in
  let candidates_c := filter (ReadsBetweenFilter uop c) nodes in
  let candidates := PairNodesByMicroop candidates_a candidates_c [] in
  let f x := [(fst x, (uop, b), name); ((uop, b), snd x, name);
    (* paired with rmw partner *)
    (snd x, w, "RMWPair");
    (* stb: redundant via transitivity, but visually helpful *)
    ((uop, b), w, "RMWStore")
    ] in
  Some (Map f candidates).

Definition AtomicReadsBetween
  (a b c : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  match FindRMWPartner (S (globalID uop)) a vicls with
  | Some w => AtomicReadsBetweenHelper a b c w name nodes uop []
  | None => Println (Some []) ["AtomicReadsBetween: unpaired atomic"]
  end.

Definition AtomicityEdges
  (a b c : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  match FindRMWPartner (S (globalID uop)) b vicls with
  | Some w => Some [[((uop, a), w, name); ((uop, c), w, name)]]
  | None => Println (Some []) ["AtomicityEdges: unpaired atomic"]
  end.

Definition CreateAllSubsequentAfterFilter
  (uop : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  andb (beq_loc loc (snd x)) (blt_nat (globalID uop) (globalID (fst x))).

Definition CreateAllSubsequentAfterHelper
  (a b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  (r : list GraphEdge)
  : option (list (list GraphEdge)) :=
  let candidates := filter (CreateAllSubsequentAfterFilter uop b) nodes in
  let f x := ((uop, a), x, name) in
  match candidates with
  | [] => None
  | _ => Some [(Map f candidates)]
  end.

Definition CreateAllSubsequentAfter
  (a b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  CreateAllSubsequentAfterHelper a b name nodes uop [].

Definition ExecAllSubsequentLoadsAfterFilter
  (uop : Microop)
  (loc : Location)
  (x : GraphNode)
  : bool :=
  let is_ld := match uop, x with
  | mkMicroop _ _ _ (Fence _), (mkMicroop _ _ _ (Read _ _), _) => true
  | mkMicroop _ _ _ (Fence _), (mkMicroop _ _ _ (RMWRead _ _), _) => true
  | _, _ => false
  end in
  andb is_ld (andb (beq_loc loc (snd x)) (blt_nat (globalID uop) (globalID (fst x)))).

Definition ExecAllSubsequentLoadsAfterHelper
  (a b : Location)
  (name : string)
  (nodes : list GraphNode)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  let candidates := filter (ExecAllSubsequentLoadsAfterFilter uop b) nodes in
  let f x := ((uop, a), x, name) in
  match candidates with
  | [] => None
  | _ => Some [(Map f candidates)]
  end.

Definition ExecAllSubsequentLoadsAfter
  (a b : Location)
  (name : string)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  : option (list (list GraphEdge)) :=
  ExecAllSubsequentLoadsAfterHelper a b name nodes uop.
