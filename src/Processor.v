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
Require Import String.
Require Import Arith.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.
Require Import PipeGraph.Execution.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** ** Basic Type Definitions *)

Definition PipeID := nat.

(** *** [PerformEdgeInterpretation] *)
(** Given a high-level RF, WS, or FR edge, interpret in the context of the
given [MicroopPath]. *)
Inductive ViCL : Set :=
| SWViCL : Location -> Location -> Location -> Location -> ViCL
| OtherViCL : Location -> Location -> Location -> Location -> ViCL.

Fixpoint ViCLCreate
  (v : ViCL)
  : Location :=
  match v with
  | SWViCL _ c _ _ => c
  | OtherViCL _ c _ _ => c
  end.

Fixpoint ViCLEvict
  (v : ViCL)
  : Location :=
  match v with
  | SWViCL _ _ _ e => e
  | OtherViCL _ _ _ e => e
  end.

Definition ViCLDowngrade
  (v : ViCL)
  : option Location :=
  match v with
  | SWViCL _ _ d e => if beq_loc d e then None else Some d
  | OtherViCL _ _ d e => if beq_loc d e then None else Some d
  end.

Inductive SinglePassConstraint : Set :=
| MultiChoiceConstraint : string ->
    (string -> list (Microop * ViCL) -> list GraphNode -> list GraphEdge ->
      Microop -> option (list (list GraphEdge))) ->
    SinglePassConstraint.

Inductive IterativeConstraint : Set :=
| AddEdgesConstraint : string ->
    (string -> list (Microop * ViCL) -> list GraphNode -> list GraphEdge ->
      Microop -> option (list GraphEdge)) ->
    IterativeConstraint.

Inductive ViCLSource : Set :=
| InitialState : ViCLSource
| PreSourced : ViCLSource
| SrcViCL : (GraphNode * GraphNode) -> ViCLSource
| CyclicSourcing : ViCLSource.

(** ** Pipeline Definitions *)

(** *** [PropagatedOrdering] *)
(** Orderings propagated from one edge to another edge, i.e., Per-Stage
Reordering Behaviors *)
Inductive PropagatedOrdering : Set :=
| AlwaysPropagate : (Location * Location) -> (Location * Location) ->
    PropagatedOrdering
| PropagateIfSameAddr : (Location * Location) -> (Location * Location) ->
    PropagatedOrdering.

(** *** [MicroopPath] *)
(** A possible path through a pipeline, along with any constraints implied by
that path. *)
Record MicroopPath : Set := mkMicroopPath {
  pathName : string;
  pathEdges : list (Location * Location);
  prop : list PropagatedOrdering;
  singlePassConstraints : list SinglePassConstraint;
  iterativeConstraints : list IterativeConstraint;
  vicls : list ViCL
}.

(** *** [MicroopPathMap] *)
(** Associate a set of [MicroopPath] constraints with a given [Microop]. *)
Definition MicroopPathMap := list (Microop * MicroopPath).

(** *** [Pipeline] *)
(** Primarily, a [Pipeline] is a mapping from a [Microop] to a list of possible
paths that [Microop] can take through the [Pipeline]. *)
Record Pipeline : Set := mkPipeline {
  pipeName : string;
  pipeID : PipeID;
  possiblePaths : Microop -> list MicroopPath;
  stageNames : list string
}.

(** *** [Processor] *)
(** A [Processor] is just a list of the component [Pipeline]s. *)
Inductive Processor : Set := mkProcessor {
  procName : string;
  pipes : list Pipeline
}.

(** ** Pipeline Definition Helper Functions *)

Fixpoint StraightLineHelper
  (p : PipeID)
  (a : option nat)
  (l : list nat)
  : list (Location * Location) :=
  match (a, l) with
  | (Some a', h::t) => ((p, a'), (p, h)) :: StraightLineHelper p (Some h) t
  | (None   , h::t) =>                      StraightLineHelper p (Some h) t
  | _               => []
  end.

Definition StraightLine
  (p : nat)
  (l : list nat)
  : list (Location * Location) :=
  StraightLineHelper p None l.

(** **** [AddEdgeToExistingNodes] *)
(** Add an edge to the given [AdjacencyList], but only if it is touching
[GraphNode]s which already exist.  In other words, don't create new node(s) by
adding this edge.  Return: the new [AdjacencyList], plus a bool indicating
whether this edge was added (or whether edge was added previously, as indicated
by the corresponding bool input. *)
Definition AddEdgeToExistingNodes
  (nodes : list GraphNode)
  (prev : bool * AdjacencyList)
  (e : GraphEdge)
  : bool * AdjacencyList :=
  match e with
  | (s, d, l) =>
      match (find (beq_node s) nodes, find (beq_node d) nodes) with
      | (Some _, Some _) =>
          let (previously_added, previous_graph) := prev in
          match AdjacencyListAddEdge previous_graph e with
          | (newly_added, new_graph) =>
              (orb previously_added newly_added, new_graph)
          end
      | _ => prev
      end
  end.

(** **** [AddEdgeToExistingNodes'] *)
(** Add an edge to the given [AdjacencyList], but only if it is touching
[GraphNode]s which already exist.  In other words, don't create new node(s) by
adding this edge. *)
Definition AddEdgeToExistingNodes'
  (nodes : list GraphNode)
  (previous_graph : AdjacencyList)
  (e : GraphEdge)
  : AdjacencyList :=
  match e with
  | (s, d, l) =>
      match (find (beq_node s) nodes, find (beq_node d) nodes) with
      | (Some _, Some _) =>
          match AdjacencyListAddEdge previous_graph e with
          | (_, new_graph) => new_graph
          end
      | _ => previous_graph
      end
  end.

(** **** [AddEdgesToExistingNodes] *)
(** Add the list of [GraphEdge]s to the given [AdjacencyList], but only add
each edge if it touches [GraphNode]s which already exist.  In other words,
don't create new node(s) by adding these edges.  Return: the new
[AdjacencyList], plus a bool indicating whether any edges were added. *)
Definition AddEdgesToExistingNodes
  (nodes : list GraphNode)
  (g : AdjacencyList)
  (l_e : list GraphEdge)
  : bool * AdjacencyList :=
  fold_left (AddEdgeToExistingNodes nodes) l_e (false, g).

Definition AddEdgesToExistingNodes'
  (nodes : list GraphNode)
  (g : list GraphEdge)
  (l_e : list GraphEdge)
  : list GraphEdge :=
  let f x := match x with
             | (s, d, l) => match (find (beq_node s) nodes, find (beq_node d) nodes) with
                            | (Some _, Some _) => false
                            | _ => true
                            end
             end in
  app_tail g (removeb f l_e).

(** *** [IsCyclic] *)
(** Return [true] if the given graph is cyclic. *)
Definition IsCyclic
  (a : AdjacencyList)
  : bool :=
  match AdjacencyListTopsort a with
  | ReverseTotalOrder _ => false
  | _ => true
  end.

(** *** [IsCyclic'] *)
(** Return [true] if the given graph is cyclic. *)
Definition IsCyclic'
  (a : NumberedAdjacencyList * MicroopPathMap)
  : bool :=
  match a with
  | (((NormalGraph, _), g), _) =>
      match AdjacencyListTopsort g with
      | ReverseTotalOrder _ => false
      | _ => true
      end
  | _ => true
  end.

(** ** Program Order Edges *)

(** **** [ThreadProgramOrderEdges] *)
(** Given a [Thread], return the set of [GraphEdge]s representing program
order: the set of edges from each instruction in the thread to the next,
at stage 0 of the given [Pipeline]. *)
Fixpoint ThreadProgramOrderEdges
  (pipeID : nat)
  (thread : list Microop)
  (edges : list GraphEdge) (* Tail recursion *)
  : list GraphEdge :=
  match thread with
  | h::t =>
      match t with
      | t1::t2 =>
          ThreadProgramOrderEdges pipeID t
            (((h, (pipeID, 0)), (t1, (pipeID, 0)), "PO") :: edges)
      | [] => edges
      end
  | [] => edges
  end.

(** *** [EnumerateProgramOrderEdges] *)
(** Given a [Program], return the set of [GraphEdge]s representing program
order: the set of edges from each instruction in the thread to the next,
at stage 0 of the given [Pipeline]. *)
Fixpoint EnumerateProgramOrderEdges
  (processor : list Pipeline)
  (program : Program)
  (l : list GraphEdge) (* Tail recursion *)
  : list GraphEdge :=
  match (processor, program) with
  | (proc_h :: proc_t, prog_h :: prog_t) =>
      EnumerateProgramOrderEdges proc_t prog_t
        (ThreadProgramOrderEdges (pipeID proc_h) prog_h l)
  | _ => l
  end.

(** ** Path Edges *)

(** **** [MicroopExecutions] *)
(** A [MicroopExecutions] is the list of [MicroopPath]s taken by a list of
[Microop]s in one particular execution. *)
Definition MicroopExecutions := list (Microop * MicroopPath).

(** **** [MicroopPathEdges] *)
(** Calculate the [GraphEdge]s representing the [Microop] following the
specified [MicroopPath] through the [Pipeline]. *)
Fixpoint MicroopPathEdges
  (uop : Microop)
  (path : list (Location * Location))
  (edges : list GraphEdge) (* Tail recursion *)
  : list GraphEdge :=
  match path with
  | (l1, l2) :: t =>
      let new_edge := ((uop, l1), (uop, l2), "path") in
      MicroopPathEdges uop t (new_edge :: edges)
  | [] => edges
  end.

(** **** [ThreadPathExecutions] *)
(** Calculate the set of possible [MicroopExecutions] for a given [Thread] on
a given [Pipeline]. *)
Definition ThreadPathExecutions
  (pipeline : Pipeline)
  (thread : Thread)
  : list MicroopExecutions :=
  let pathFunction := possiblePaths pipeline in 
  let instructionExecutions := Map pathFunction thread in
  let cross_product := CrossProduct instructionExecutions in
  (* Zip: pair microops with their corresponding list of possible executions *)
  Map (Zip thread) cross_product.

(** **** [ProgramPathExecutions] *)
(** Calculate the set of possible [MicroopExecutions] for a given [Program] on
a given [Processor]. *)
Definition ProgramPathExecutions
  (program : Program)
  (processor : list Pipeline)
  : list MicroopExecutions :=
  let TPEUncurry x := ThreadPathExecutions (fst x) (snd x) in
  let thread_executions := Map TPEUncurry (Zip processor program) in
  let program_executions := CrossProduct thread_executions in
  (* fold_left: combine the list of lists of [MicroopExecutions] from each
  [Thread] into a single list of [MicroopExecutions] for the [Program] *)
  Map (fun x => fold_left (app_tail (A:=_)) x []) program_executions.

(** **** [MicroopExecutionEdges] *)
(** Calculate the set of [GraphEdge]s associated with the given [Microop]
and the given [MicroopExecution].  Also, build up a list of taken
[MicroopPath]s so that we can return to them later when the rest of
the graph has been built up. *)
Fixpoint MicroopExecutionEdges
  (edges_cmap : list GraphEdge * MicroopPathMap) (* Tail recursion *)
  (exec : MicroopExecutions)
  : list GraphEdge * MicroopPathMap :=
  let (edges, cmap) := edges_cmap in
  match exec with
  | h::t =>
      match h with
      | (uop, mkMicroopPath _ path_edges _ _ _ _) =>
          let edges' := MicroopPathEdges uop path_edges edges in
          MicroopExecutionEdges (edges', h :: cmap) t
      end
  | [] => (edges, cmap)
  end.

(** *** [EnumeratePathEdges] *)
(** Given a [Processor] and a [Program], enumerate the set of possible path
executions that can be taken by the [Microop]s in the [Program].  Also take
as input a graph from a previous stage, and use that as the starting point
for the newly-added path edges. *)
Definition EnumeratePathEdges
  (program : Program)
  (processor : Processor)
  (edges : list GraphEdge) (* Tail recursion *)
  : list (list GraphEdge * MicroopPathMap) :=
  let executions := ProgramPathExecutions program (pipes processor) in
  Map (MicroopExecutionEdges (edges, [])) executions.

Definition ThreadPathExecutionsDF
  (x : Pipeline * Thread)
  : list (list (list GraphEdge * MicroopPathMap)) :=
  let (pipeline, thread) := x in
  let f i :=
    let paths := possiblePaths pipeline i in
    Map (fun p => (MicroopPathEdges i (pathEdges p) [], [(i, p)])) paths
  in
  Map f thread.

(** **** [ProgramPathExecutions] *)
(** Calculate the set of possible [MicroopExecutions] for a given [Program] on
a given [Processor]. *)
Definition ProgramPathExecutionsDF
  (program : Program)
  (processor : list Pipeline)
  : list (list (list GraphEdge * MicroopPathMap)) :=
  let thread_executions := Map ThreadPathExecutionsDF (Zip processor program) in
  fold_left (app (A:=_)) thread_executions [].

(** **** [MicroopPathMapFind] *)
(** Find the [MicroopPath] constraints associated with the given [Microop] in
the given [MicroopPathMap]. *)
Fixpoint MicroopPathMapFind
  (c : MicroopPathMap)
  (uop : Microop)
  : option MicroopPath :=
  match c with
  | (h1, h2)::t =>
      if beq_uop h1 uop then Some h2 else MicroopPathMapFind t uop
  | [] => None
  end.

(** ** Coherence Protocol Edges *)

Fixpoint AllSWPairsHelper
  (h1 : GraphNode)
  (l2 : list GraphNode)
  (l' : list GraphEdge) (* tail recursion *)
  : list GraphEdge :=
  match l2 with
  | h2::t2 => AllSWPairsHelper h1 t2 ((h1, h2, "SW") :: l')
  | [] => l'
  end.

Fixpoint AllSWPairs
  (l1 l2 : list GraphNode)
  (l' : list GraphEdge) (* tail recursion *)
  : list GraphEdge :=
  match l1 with
  | h1::t1 => AllSWPairs t1 l2 (AllSWPairsHelper h1 l2 l')
  | [] => l'
  end.

Fixpoint SWViCLCs
  (uop : Microop)
  (l : list ViCL)
  (l' : list GraphNode)
  : list GraphNode :=
  match l with
  | SWViCL r c i e :: t => SWViCLCs uop t ((uop, c)::l')
  | _ :: t => SWViCLCs uop t l'
  | _ => l'
  end.

Fixpoint SWViCLIs
  (uop : Microop)
  (l : list ViCL)
  (l' : list GraphNode)
  : list GraphNode :=
  match l with
  | SWViCL r c i e :: t => SWViCLCs uop t ((uop, i)::l')
  | _ :: t => SWViCLCs uop t l'
  | _ => l'
  end.

(** **** [ExecutionPerformEdgesWSFold] *)
(** Given a list of nodes in a total order specified by WS for a given address,
add a WS edge to the graph for the first two nodes in the list, according to
the pipeline's specification of how to interpret that edge for the chosen
[MicroopPath], but only add the edge if it connects two pre-existing nodes;
otherwise, just drop the edge silently.  Then recurse with the next two nodes
in the WS list (overlapping the first). *)
Fixpoint ExecutionPerformEdgesWSFold
  (c : MicroopPathMap)
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (ws : list Microop)
  : list GraphEdge :=
  match ws with
  | h::t =>
      match t with
      | t1::t2 =>
          let w1_nodes := match MicroopPathMapFind c h with
          | Some (mkMicroopPath _ _ _ _ _ vicls) =>
              Some (SWViCLIs h vicls [])
          | None => Warning None ["Didn't find MicroopPathMap"]
          end in
          let w2_nodes := match MicroopPathMapFind c t1 with
          | Some (mkMicroopPath _ _ _ _ _ vicls) =>
              Some (SWViCLCs t1 vicls [])
          | None => Warning None ["Didn't find MicroopPathMap"]
          end in
          let edges' := match (w1_nodes, w2_nodes) with
          | (Some w1list, Some w2list) =>
            AddEdgesToExistingNodes' nodes edges (AllSWPairs w1list w2list [])
          | _ => edges
          end in
          ExecutionPerformEdgesWSFold c nodes edges' t
      | [] => edges
      end
  | [] => edges
  end.

(** **** [ExecutionPerformEdgesWS] *)
(** Given a list of WS total orders per address, add edges to the graph
according to the pipeline's specification of how to interpret those edges for
the chosen [MicroopPath]s, but only add the edges if they connect two
pre-existing nodes; otherwise, just drop them silently. *)
Definition ExecutionPerformEdgesWS
  (c : MicroopPathMap)
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (wss : list (list Microop))
  : list GraphEdge :=
  fold_left (ExecutionPerformEdgesWSFold c nodes) wss edges.

(** ** Propagation of Edges *)

(** **** [PropagateEdgesHelper] *)
(** Given a [PropagatedOrdering] specification, find all edges meeting the
precondition of the propagation, and add the resulting implied edges. *)
Definition PropagateEdgesHelper
  (n : list GraphNode)
  (a : bool * AdjacencyList)
  (p : Microop * PropagatedOrdering)
  : bool * AdjacencyList :=
  match p with
  | (op, AlwaysPropagate ((p0, l0), (p1, l1)) ((p2, l2), (p3, l3))) =>
      (* If there is an edge from ((op0, p0, l0), (op1, p1, l1)), then add an
      * edge ((op0 , p2, l2), (op1, p3, l3)) *)
      let f e :=
        match e with
        | ((ia, (pa, la)), (ib, (pb, lb)), _) =>
            andb (beq_uop ia op) (andb (andb (beq_nat p0 pa) (beq_nat p1 pb))
              (andb (beq_nat l0 la) (beq_nat l1 lb)))
        end in
      (* Find all edges meeting the specified precondition *)
      let srcs := AdjacencyListFilter f (snd a) in
      (* Replace them with the corresponding implied edge *)
      let replace e :=
        match e with
        | ((ia, (pa, la)), (ib, (pb, lb)), _) =>
            ((ia, (p2, l2)), (ib, (p3, l3)), "propagated")
        end in
      let dsts := Map replace srcs in
      (* Add them to the list (if they touch pre-existing nodes only) *)
      fold_left (AddEdgeToExistingNodes n) dsts a
  | (op, PropagateIfSameAddr ((p0, l0), (p1, l1)) ((p2, l2), (p3, l3))) =>
      (* If there is an edge from ((op0, p0, l0), (op1, p1, l1)), then add an
         edge ((op0, p2, l2), (op1, p3, l3)) *)
      let f e :=
        match e with
        | ((ia, (pa, la)), (ib, (pb, lb)), _) =>
            andb (andb (beq_uop ia op) (SameAddress ia ib))
              (andb (andb (beq_nat p0 pa) (beq_nat p1 pb))
              (andb (beq_nat l0 la) (beq_nat l1 lb)))
        end in
      (* Find all edges meeting the specified precondition *)
      let srcs := AdjacencyListFilter f (snd a) in
      (* Replace them with the corresponding implied edge *)
      let replace e :=
        match e with
        | ((ia, (pa, la)), (ib, (pb, lb)), _) =>
            ((ia, (p2, l2)), (ib, (p3, l3)), "propSameAddr")
        end in
      let dsts := Map replace srcs in
      (* Add them to the list (if they touch pre-existing nodes only) *)
      fold_left (AddEdgeToExistingNodes n) dsts a
  end.

Definition GetPropagations
  (c : MicroopPathMap)
  : list (Microop * PropagatedOrdering) :=
  let g y z := (y,z) in
  let f x := Map (g (fst x)) (prop (snd x)) in
  fold_left (app_tail (A:=_)) (Map f c) [].

(** *** [PropagateEdges] *)
(** Find all edges meeting the precondition of the
[PropagatedOrdering]s of each [Microop] in the [Pipeline]s,
and add the resulting implied edges. *)
Definition PropagateEdges
  (a : AdjacencyList)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  let l := GetPropagations c in
  match AdjacencyListTransitiveClosure a with
  | TC a' =>
      let n := NodesFromAdjacencyList a in
      match fold_left (PropagateEdgesHelper n) l (false, a') with
      | (_, l') =>
          match AdjacencyListTransitiveClosure l' with
          | TC _ => [((NormalGraph, l'), c)]
          | _ => [((PrunedGraph, l'), c)]
          end
      end
  | _ => [((PrunedGraph, a), c)]
  end.

(** ** Path Constraints *)

(** **** [FindAndRemoveHelper] *)
(** If we find a node [h] such that [f h = true], then remove [h] and return
the rest of the list.  Otherwise, return [None]. *)
Fixpoint FindAndRemoveHelper
  {A : Type}
  (f : A -> bool)
  (l l' : list A)
  : option (list A * A) :=
  match l with
  | h::t =>
      if f h
      then Some (l' ++ t, h)
      else FindAndRemoveHelper f t (l' ++ [h])
  | [] => None
  end.

(** **** [FindAndRemove] *)
(** If we find a node [h] such that [f h = true], then remove [h] and return
the rest of the list.  Otherwise, return [None]. *)
Fixpoint FindAndRemove
  {A : Type}
  (f : A -> bool)
  (l : list A)
  : option (list A * A) :=
  FindAndRemoveHelper f l [].

(** **** [SameInstAs] *)
(** Return [true] if the two [GraphNode]s represent the same [Microop]. *)
Definition SameInstAs
  (x y : GraphNode)
  : bool :=
  match (x, y) with
  | ((ix, _), (iy, _)) => beq_uop ix iy
  end.

(** **** [PairNodesByMicroop] *)
(** Given a list of [GraphNode]s, return the list of pairs of [GraphNode]s for
the same [Microop], and filter out nodes which don't have a partner.  This is
used to find nodes which satisfy the [ExtraConstraint]s associated with a
path. *)
Fixpoint PairNodesByMicroop
  (l_a l_c : list GraphNode)
  (l_pairs : list (GraphNode * GraphNode))
  : list (GraphNode * GraphNode) :=
  match l_a with
  | h::t =>
      match FindAndRemove (SameInstAs h) l_c with
      | Some (l_c', partner) =>
          PairNodesByMicroop t l_c' ((h, partner) :: l_pairs)
      | None => PairNodesByMicroop t l_c l_pairs
      end
  | [] => l_pairs
  end.

Fixpoint GetViCLsHelper
  (uop : Microop)
  (l : list (Microop * ViCL))
  (vicls : list ViCL)
  : list (Microop * ViCL) :=
  match vicls with
  | h :: t =>
      GetViCLsHelper uop ((uop, h) :: l) t
  | [] => l
  end.

Fixpoint GetViCLs
  (m : MicroopPathMap)
  (l : list (Microop * ViCL))
  : list (Microop * ViCL) :=
  match m with
  | (uop, mkMicroopPath _ _ _ _ _ vicls) :: t =>
      GetViCLs t (GetViCLsHelper uop l vicls)
  | [] => l
  end.

Fixpoint SinglePassConstraintsHelper
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  (l : list SinglePassConstraint)
  (l' : list (list (list GraphEdge))) (* tail recursion *)
  : list (list (list GraphEdge)) :=
  match l with
  | MultiChoiceConstraint name f::t =>
      let name := Println name ["Evaluating single pass constraint "; name;
        " for uop "; stringOfNat (globalID uop)] in
      match f name vicls nodes edges uop with
      | Some [] =>
          Println (SinglePassConstraintsHelper vicls nodes edges uop t ([] :: l'))
            ["No solution to constraint "; name]
      | Some x => SinglePassConstraintsHelper vicls nodes edges uop t (x :: l')
      | None => SinglePassConstraintsHelper vicls nodes edges uop t l'
      end
  | [] => l'
  end.

(** **** [SinglePassConstraintsHelperFold] *)
(** Iterate over the list of [MicroopPath] constraints in a given execution to
make sure they are all satisfied.  [None] means no constraints, [Some x] means
[x] is the list of choices for a particular constraint. *)
Fixpoint SinglePassConstraintsHelperFold
  (m : MicroopPathMap)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (l' : list (list (list GraphEdge))) (* tail recursion *)
  : list (list (list GraphEdge)) :=
  match m with
  | (uop, mkMicroopPath _ _ _ cs _ _)::t =>
      let candidates := SinglePassConstraintsHelper vicls nodes edges
        uop cs [] in
      SinglePassConstraintsHelperFold t vicls nodes edges (app_rev l' candidates)
  | [] => l'
  end.

(** *** [EnumerateSinglePassConstraints] *)
(** Iterate over the list of [MicroopPath] constraints in a given execution to
find the set of satisfying solutions, and return the set of graphs for each
solution. *)
Definition EnumerateSinglePassConstraints
  (g : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let nodes := NodesFromEdges g in
  let vicls := GetViCLs c [] in
  let edge_candidates := SinglePassConstraintsHelperFold c vicls nodes g [] in
  let edge_candidates' := CrossProduct edge_candidates in
  let edge_candidates'' :=
    Map (fun x => fold_left (app_tail (A:=_)) x []) edge_candidates' in
  (* If there were no constraints to be satisfied, return the original list.
     If there were, merge each solution with the input graph and return the
     resulting list of graphs. *)
  match (edge_candidates, edge_candidates'') with
  | ([], _) => [((NormalGraph, g), c)]
  | (_, []) => [((InvalidGraph "No solution to constraints", g), c)]
  | (_, _) => Map
      (fun x => ((NormalGraph, app_tail g x), c))
      edge_candidates''
  end.

Fixpoint EnumerateSinglePassConstraintsDFHelper
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  (cs : list SinglePassConstraint)
  (m : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let edge_candidates :=
    SinglePassConstraintsHelper vicls nodes edges uop cs [] in
  let edge_candidates' := CrossProduct edge_candidates in
  let edge_candidates' := match edge_candidates' with
  | [] => edge_candidates'
  | [_] => edge_candidates'
  | _ => Println edge_candidates' ["Microop "; stringOfNat (globalID uop);
      " edge_candidates' has length ";
      stringOfNat (List.length edge_candidates')]
  end in
  let edge_candidates'' :=
    Map (fun x => fold_left (app_tail (A:=_)) x []) edge_candidates' in
  match (edge_candidates, edge_candidates'') with
  | ([], _) => [((NormalGraph, edges), m)]
  | (_, []) => [((InvalidGraph "No solution to constraints", edges), m)]
  | (_,  _) => Map (fun x => (((NormalGraph, app_tail edges x), m))) edge_candidates''
  end.

Definition EnumerateSinglePassConstraintsDF
  (m : Microop * MicroopPath)
  (edges : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let nodes := NodesFromEdges edges in
  let vicls := GetViCLs c [] in
  match m with
  | (uop, mkMicroopPath _ _ _ cs _ _) =>
    EnumerateSinglePassConstraintsDFHelper vicls nodes edges uop cs c
  end.

Fixpoint AddEdgesIfNotAlreadyPresentHelper
  (g g' : list GraphEdge)
  (e : GraphEdge)
  : bool * list GraphEdge :=
  match e with
  | (e1, e2, el) =>
      match g with
      | (h1, h2, hl)::t =>
          if andb (andb (beq_node e1 h1) (beq_node e2 h2)) (beq_string el hl)
          then (false, app_rev g g') (* slow - need to optimize *)
          else AddEdgesIfNotAlreadyPresentHelper t ((h1, h2, hl)::g') e
      | [] => Println (true, e :: g')
            ["Adding edge "; GraphvizShortStringOfGraphNode e1; " --> ";
            GraphvizShortStringOfGraphNode e2; " ["; el; "]"]
      end
  end.

Fixpoint AddEdgesIfNotAlreadyPresent
  (g : list GraphEdge)
  (l : list GraphEdge)
  (n : nat)
  : (nat * list GraphEdge) :=
  match l with
  | h::t =>
      let h := Println h ["TEMP graph has length "; stringOfNat (List.length g)] in
      match AddEdgesIfNotAlreadyPresentHelper g [] h with
      | (true , g') => AddEdgesIfNotAlreadyPresent g' t (S n)
      | (false, g') => AddEdgesIfNotAlreadyPresent g' t n
      end
  | [] => (n, g)
  end.

Fixpoint IterativeConstraintsIteration
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (uop : Microop)
  (l : list IterativeConstraint)
  (n : nat)
  : nat * option (list GraphEdge) :=
  match l with
  | AddEdgesConstraint name f::t =>
      let name := Println name ["Evaluating iterative constraint "; name;
        " for uop "; stringOfNat (globalID uop)] in
      let new_edges := f name vicls nodes edges uop in
      let (added, edges') := match new_edges with
      | Some [] => (0, [])
      | Some e => AddEdgesIfNotAlreadyPresent edges e 0
      | None => (0, edges)
      end in
      let added := Println added ["Added "; stringOfNat added; " edges"] in
      match new_edges with
      | Some [] => (n, None)
      | _ => IterativeConstraintsIteration vicls nodes edges' uop t (n + added)
      end
  | [] => (n, Some edges)
  end.

Fixpoint IterativeConstraintsOuter
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (c : MicroopPathMap)
  (n : nat)
  : option (nat * list GraphEdge) :=
  match c with
  | (uop, mkMicroopPath _ _ _ _ cs _) :: t =>
      let (added, edges') :=
        IterativeConstraintsIteration vicls nodes edges uop cs 0 in
      match edges' with
      | Some e => IterativeConstraintsOuter vicls nodes e t (n + added)
      | None => None
      end
  | [] => Some (n, edges)
  end.

Fixpoint EnumerateIterativeConstraintsHelper
  (iterations_remaining : nat)
  (vicls : list (Microop * ViCL))
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (c : MicroopPathMap)
  (l : list (GraphGenerationStepResult * MicroopPathMap))
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  match iterations_remaining with
  | S n' =>
      match IterativeConstraintsOuter vicls nodes edges c 0 with
      | Some (0, edges') => Println (((NormalGraph, edges'), c) :: l)
          ["Stopped w/ "; stringOfNat n'; " constraint iterations remaining"]
      | Some (added, edges') =>
          match TransitiveClosure edges' with
          | TC _ => EnumerateIterativeConstraintsHelper n' vicls nodes edges' c
              (((NormalGraph, edges'), c) :: l)
          | _ => Println (((PrunedGraph, edges'), c) :: l)
              ["Pruning w/ "; stringOfNat n'; " constraint iterations remaining"]
          end
      | None => ((InvalidGraph "IterativeConstraints", edges), c) :: l
      end
  | O => Warning
      [((InvalidGraph "Iterative constraints didn't converge", edges), c)]
      ["Exceeded the maximum number of iterations for IterativeConstraints"]
  end.

Definition EnumerateIterativeConstraints
  (g : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let nodes := NodesFromEdges g in
  let vicls := GetViCLs c [] in
  EnumerateIterativeConstraintsHelper 5 vicls nodes g c [].

Fixpoint FilterNodesByAddress
  (p0 : PipeID)
  (a : Address)
  (l : list GraphNode)
  : list GraphNode :=
  match l with
  | h::t =>
      match h with
      | (mkMicroop _ _ _ (Read a' d'), (p', l')) =>
          if andb (beq_nat a a') (beq_nat p' p0)
          then h :: FilterNodesByAddress p0 a t
          else      FilterNodesByAddress p0 a t
      | (mkMicroop _ _ _ (Write a' d'), (p', l')) =>
          if andb (beq_nat a a') (beq_nat p' p0)
          then h :: FilterNodesByAddress p0 a t
          else      FilterNodesByAddress p0 a t
      | (mkMicroop _ _ _ (RMWRead a' d'), (p', l')) =>
          if andb (beq_nat a a') (beq_nat p' p0)
          then h :: FilterNodesByAddress p0 a t
          else      FilterNodesByAddress p0 a t
      | (mkMicroop _ _ _ (RMWWrite a' d'), (p', l')) =>
          if andb (beq_nat a a') (beq_nat p' p0)
          then h :: FilterNodesByAddress p0 a t
          else      FilterNodesByAddress p0 a t
      | _ => FilterNodesByAddress p0 a t
      end
  | [] => []
  end.

(** **** [FilterNodesByLocation] *)
(** Find [GraphNode]s which are passing through a particular
([PipeID], [Location]) point *)
Fixpoint FilterNodesByLocation
  (p0 : PipeID)
  (l0 : nat)
  (l : list GraphNode)
  : list GraphNode :=
  match l with
  | h::t =>
      match h with
      |  (mkMicroop gid _ _ (Read _ _), (p', l')) =>
          if andb (beq_nat p' p0) (beq_nat l' l0)
          then h :: FilterNodesByLocation p0 l0 t
          else      FilterNodesByLocation p0 l0 t
      |  (mkMicroop gid _ _ (RMWRead _ _), (p', l')) =>
          if andb (beq_nat p' p0) (beq_nat l' l0)
          then h :: FilterNodesByLocation p0 l0 t
          else      FilterNodesByLocation p0 l0 t
      | _ => FilterNodesByLocation p0 l0 t
      end
  | [] => []
  end.

Fixpoint GetUniqueAddrs
  (l : list Address)
  : list Address :=
  match l with
  | [] => []
  | h::t => let f x := beq_nat h x in
            let dup := fold_left orb (Map f t) false in
            match dup with
            | true => GetUniqueAddrs t
            | false => h::(GetUniqueAddrs t)
            end
  end.

Fixpoint GetAddrs
  (l : list (option Address))
  : list Address :=
  match l with
  | [] => []
  | h::t => match h with
            | Some a => a :: GetAddrs t
            | None => GetAddrs t
            end
  end.

Definition GetAddressList
  (l : list Microop)
  : list Address :=
  let f x := match x with
             | mkMicroop _ _ _ (Read  a _) => Some a
             | mkMicroop _ _ _ (Write a _) => Some a
             | mkMicroop _ _ _ (RMWRead  a _) => Some a
             | mkMicroop _ _ _ (RMWWrite a _) => Some a
             | _ => None
             end in
  GetUniqueAddrs (GetAddrs (Map f l)).

Fixpoint SortViCLsAdd
  (uop : Microop)
  (v : ViCL)
  (l l' : list (list (Microop * ViCL)))
  : list (list (Microop * ViCL)) :=
  match (v, l) with
  | (SWViCL _ c _ _, h::t) =>
      match hd_error h with
      | Some h' =>
        if andb (SameAddress uop (fst h')) (beq_loc c (ViCLCreate (snd h')))
        then app_rev l' (((uop, v) :: h) :: t)
        else SortViCLsAdd uop v t (h::l')
      | None => SortViCLsAdd uop v t (h::l')
      end
  | (OtherViCL _ c _ _, h::t) =>
      match hd_error h with
      | Some h' =>
        if andb (SameAddress uop (fst h')) (beq_loc c (ViCLCreate (snd h')))
        then app_rev l' (((uop, v) :: h) :: t)
        else SortViCLsAdd uop v t (h::l')
      | None => SortViCLsAdd uop v t (h::l')
      end
  | (_, []) => [(uop, v)] :: l'
  end.

Fixpoint SortViCLs
  (l : list (Microop * ViCL))
  (r : list (list (Microop * ViCL)))
  : list (list (Microop * ViCL)) :=
  match l with
  | (h_uop, h_vicl)::t => SortViCLs t (SortViCLsAdd h_uop h_vicl r [])
  | [] =>
      let r := Println r ["SortViCLs: Found "; stringOfNat (List.length r);
        " ViCL/Location ordering points"] in
      r
  end.

Fixpoint NoDuplicatesEdges
  (r : list GraphEdge)
  (l : list (Microop * ViCL))
  : list GraphEdge :=
  match l with
  | (h1_uop, h1_vicl)::t =>
      match t with
      | (h2_uop, h2_vicl)::t =>
          NoDuplicatesEdges
          (((h1_uop, ViCLEvict h1_vicl), (h2_uop, ViCLCreate h2_vicl),
            "NoDuplicates") :: r) t
      | [] => r
      end
  | [] => r
  end.

Definition NoDuplicatesScenarios
  (m : MicroopPathMap)
  : list (list GraphEdge) :=
  let vicls := GetViCLs m [] in
  let sorted_vicls := SortViCLs vicls [] in
  let orders := Map (AllPermutations (fun _ => true)) sorted_vicls in
  let edge_orders := Map (fun x => Map (NoDuplicatesEdges []) x) orders in
  let cp := CrossProduct edge_orders in
  let scenarios := Map (fun x => fold_left (app (A:=_)) x []) cp in
  scenarios.

Definition EnumerateNoDuplicatesEdges
  (a : AdjacencyList)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  let scenarios := NoDuplicatesScenarios c in
  let f s :=
    let s := Println s ["ENODE: Adding "; stringOfNat (List.length s); " edges"] in
    ((NormalGraph, fold_left AdjacencyListAddEdge2 s a), c) in
  Map f scenarios.

(** ** Putting it all together *)

Fixpoint NumberGraphs
  (l : list (list GraphEdge * MicroopPathMap))
  (l' : list (NumberedEdgeList * MicroopPathMap))
  (n : nat)
  : list (NumberedEdgeList * MicroopPathMap) :=
  match l with
  | (g, c) :: t =>
     NumberGraphs t ((((NormalGraph, [mkTraceEntry "Paths" n]), g), c) :: l') (S n)
  | [] => l'
  end.

Definition CalcWSScenarios
  (last_values : list (Address * Data))
  (p : Program)
  : list (list (list Microop)) :=
  let uop_list := fold_left (app_tail (A:=_)) p [] in
  let w := SortWrites uop_list in
  WSScenarios w last_values.

Definition ApplyWSEdges
  (ws_scen : list (list (list Microop)))
  (graph : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let nodes := NodesFromEdges graph in
  let new_els := Map (ExecutionPerformEdgesWS c nodes graph) ws_scen in
  Map (fun x => ((NormalGraph, x), c)) new_els.

Definition ConvertToNumberedAL
  (g : NumberedEdgeList * MicroopPathMap)
  : NumberedAdjacencyList * MicroopPathMap :=
  match g with
  | ((tr, el), c) => ((tr, AdjacencyListFromEdges el), c)
  end.

(** *** [ProgramGraphs] *)
(** Calculate the set of graphs representing the possible executions of the
given [Program] on the given [Processor]. *)
Definition ProgramGraphs
  (keep_pruned : nat)
  (last_values : list (Address * Data))
  (processor : Processor)
  (program : Program)
  : list (NumberedAdjacencyList * MicroopPathMap) :=
  let po_edges := EnumerateProgramOrderEdges (pipes processor) program [] in
  let po_path_edges := EnumeratePathEdges program processor po_edges in
  (* list (list GraphEdge * MicroopPathMap) *)
  let po_path_adjs_nodes := NumberGraphs po_path_edges [] 0 in
  (* list (NumberedEdgeList * MicroopPathMap) *)
  let empty_counts := mkCounts 1 0 0 [] [] [] in
  let constrained_graphs := GenerationStep keep_pruned "Constraints0"
    EnumerateSinglePassConstraints (empty_counts, po_path_adjs_nodes) in
  let constrained_graphs := GenerationStep keep_pruned "Constraints1"
    EnumerateIterativeConstraints constrained_graphs in
  let addr_list := GetAddressList (fold_left (app_rev (A:=_)) program []) in
  let po_path_cache_adjs :=
    (fst constrained_graphs, Map ConvertToNumberedAL (snd constrained_graphs)) in
  let po_path_cache_prop_adjs := GenerationStepAdj keep_pruned "Propagate"
    PropagateEdges po_path_cache_adjs in
  (* list (GraphGenerationStepResultAdj * MicroopPathMap) *)
  let (counts, r) := GenerationStepAdj keep_pruned "NoDuplicates"
    EnumerateNoDuplicatesEdges po_path_cache_prop_adjs in
  match r with
  | [] => Warning r ["No graphs for program!"]
  | _ => Warning r [StringOfGraphCounts counts]
  end.

(** ** Cyclic Check *)

(** *** [IsObservable] *)
(** Check whether there is any observable execution of a given [Program] on a
given [Processor] (i.e., whether there is some non-cyclic execution. *)
Definition IsObservable
  (graphs : list (NumberedAdjacencyList * MicroopPathMap))
  : bool :=
  negb (fold_left andb (Map IsCyclic' graphs) true).

(** *** [FindObservable] *)
Fixpoint FindObservable
  (counts : GraphCounts)
  (graphs : list (NumberedAdjacencyList * MicroopPathMap))
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match graphs with
  | h::t =>
      match fst h with
      | ((NormalGraph, _), a) =>
          if IsCyclic a
          then FindObservable (UpdateCyclicCount counts) t
          else (UpdateAcyclicCount counts, Some h)
      | ((PrunedGraph, _), _) =>
          Warning (FindObservable counts t) ["Pruned graph still being evaluated"]
      | ((InvalidGraph _, _), _) =>
          Warning (FindObservable counts t) ["Invalid graph still being evaluated"]
      end
  | [] => (counts, None)
  end.

Fixpoint GenerationStepNoDuplicates
  (c : GraphCounts)
  (l : list (NumberedAdjacencyList * MicroopPathMap))
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match l with
  | h::t =>
      let (c', new_graphs) := GenerationStepAdj 0 "NoDuplicates"
        EnumerateNoDuplicatesEdges (c, [h]) in
      match FindObservable c new_graphs with
      | (c'', Some g) => (c'', Some g)
      | (c'', None) => GenerationStepNoDuplicates c'' t
      end
  | [] => (c, None)
  end.

Fixpoint GenerationStepPropagate
  (c : GraphCounts)
  (l : list (NumberedEdgeList * MicroopPathMap))
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match l with
  | h::t =>
      let (c', new_graphs) := GenerationStepAdj 0 "Propagate"
        PropagateEdges (c, [ConvertToNumberedAL h]) in
      match GenerationStepNoDuplicates c' new_graphs with
      | (c'', Some g) => (c'', Some g)
      | (c'', None  ) => GenerationStepPropagate c'' t
      end
  | [] => (c, None)
  end.

Fixpoint GenerationStepConstraints1
  (c : GraphCounts)
  (l : list (NumberedEdgeList * MicroopPathMap))
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match l with
  | h::t =>
      let (c', new_graphs) := GenerationMultiStep 0 "Constraints1"
        EnumerateIterativeConstraints (c, [h]) in
      match GenerationStepPropagate c' new_graphs with
      | (c'', Some g) => (c'', Some g)
      | (c'', None) => GenerationStepConstraints1 c'' t
      end
  | [] => (c, None)
  end.

Fixpoint GenerationStepWS
  (ws_scenarios : list (list (list Microop)))
  (c : GraphCounts)
  (l : list (NumberedEdgeList * MicroopPathMap))
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match l with
  | h::t =>
      let (c', new_graphs) := GenerationStep 0 "SingleWriter"
        (ApplyWSEdges ws_scenarios) (c, [h]) in
      match GenerationStepConstraints1 c' new_graphs with
      | (c'', Some g) => (c'', Some g)
      | (c'', None) => GenerationStepWS ws_scenarios c'' t
      end
  | [] => (c, None)
  end.

Fixpoint IDOfFirstTraceEntryHelper
  (l : list GraphGenerationTraceEntry)
  : string :=
  match l with
  | [] => "?"
  | [mkTraceEntry _ n] => stringOfNat n
  | _::t => IDOfFirstTraceEntryHelper t
  end.

Definition IDOfFirstTraceEntry
  (g : NumberedEdgeList * MicroopPathMap)
  : string :=
  match g with
  | (((_, l), _), _) => IDOfFirstTraceEntryHelper l
  end.

Fixpoint GenerationStepConstraints0DF
  (ws_scenarios : list (list (list Microop)))
  (c : GraphCounts)
  (l : NumberedEdgeList * MicroopPathMap)
  (m : MicroopPathMap)
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match m with
  | h::t =>
      let (c', new_graphs) := GenerationStep 0 "Constraints0"
        (EnumerateSinglePassConstraintsDF h) (c, [l]) in
      let f x y :=
        match x with
        | (c'', None) => GenerationStepConstraints0DF ws_scenarios c'' y t
        | (c'', Some g) => (c'', Some g)
        end in
      fold_left f new_graphs (c', None)
  | [] => GenerationStepWS ws_scenarios c [l]
  end.

Fixpoint GenerationStepConstraints0
  (ws_scenarios : list (list (list Microop)))
  (c : GraphCounts)
  (l : list (NumberedEdgeList * MicroopPathMap))
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match l with
  | h::t =>
      let h := Println h ["Testing Paths Combination "; IDOfFirstTraceEntry h] in
      match GenerationStepConstraints0DF ws_scenarios c h (snd h) with
      | (c', Some g) => (c', Some g)
      | (c', None) => GenerationStepConstraints0 ws_scenarios c' t
      end
  | [] => (c, None)
  end.

Definition EnumeratePathsAddToCurrent
  (current : list GraphEdge * MicroopPathMap)
  (new : list GraphEdge * MicroopPathMap)
  : list GraphEdge * MicroopPathMap :=
  match (current, new) with
  | ((el, m), (el', m')) => (app_rev el el', app_rev m m')
  end.

Fixpoint ZipRangeHelper
  {A : Type}
  (l : list A)
  (r : list (A * nat))
  (n : nat)
  : list (A * nat) :=
  match l with
  | h::t => ZipRangeHelper t ((h, n) :: r) (S n)
  | [] => r
  end.

Definition ZipRange
  {A : Type}
  (l : list A)
  : list (A * nat) :=
  ZipRangeHelper l [] 0.

Fixpoint EnumeratePathsDF
  (ws_scenarios : list (list (list Microop)))
  (current : list GraphEdge * MicroopPathMap)
  (trace : list GraphGenerationTraceEntry)
  (counts : GraphCounts)
  (remaining : list (list (list GraphEdge * MicroopPathMap)))
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  let (current_g, current_m) := current in
  match remaining with
  | h_instruction :: t_instructions =>
      let f
        (x : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap))
        (y : (list GraphEdge * MicroopPathMap) * nat) :=
        let (c, r) := x in
        let (inst_path, path_num) := y in
        match r with
        | Some g => (c, Some g)
        | None =>
            EnumeratePathsDF ws_scenarios
            (EnumeratePathsAddToCurrent current inst_path)
            ((mkTraceEntry "InstPath" path_num) :: trace) c t_instructions
      end in
      fold_left f (ZipRange h_instruction) (counts, None)
  | [] =>
      let g :=
        (((NormalGraph, trace), fst current), snd current) in
      GenerationStepConstraints0 ws_scenarios counts [g]
  end.

(** *** [ProgramGraphsFindAnyObservableOutcome] *)
Fixpoint ProgramGraphsFindAnyObservableOutcome
  (keep_pruned : nat)
  (counts : GraphCounts)
  (last_values : list (Address * Data))
  (processor : Processor)
  (programs : list Program)
  : GraphCounts * option (NumberedAdjacencyList * MicroopPathMap) :=
  match programs with
  | h::t =>
    let po_edges := EnumerateProgramOrderEdges (pipes processor) h [] in
    let ws_scenarios := CalcWSScenarios last_values h in
    match EnumeratePathsDF ws_scenarios (po_edges, []) [] counts
      (ProgramPathExecutionsDF h (pipes processor)) with
    | (c', Some g) => (c', Some g)
    | (c', None) => ProgramGraphsFindAnyObservableOutcome keep_pruned c'
        last_values processor t
    end
  | [] => (counts, None)
  end.

