Require Import CoreData.CoreData.
Require Import Ingest.SQIRIngest.
Require Import CoreRules.CoreRules.
From Coq Require Import Lists.List.
From Coq Require Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.Compare_dec.
Import ListNotations.
Require Import Lia.

(* Intake graphical ZX data type with connection information into semantically equivalent ZX diagram *)

(*  This entire section has the goal of constructing any general 
    ZX swap structure that can swap between any two qubit permutations.
    The ZX swap only swaps adjacent wires, so a bubblesort is needed.
*)

Definition indexed_list (A : Type) : Type := list (A * nat).

(*  Provides indices for an existing list invreverse order
    so the element closest to nil is index 0
    [1, 2, 3] -> [(1, 2), (2, 1), (3, 0)]*)
Definition create_indexed_list {A : Type} (l : list A) : indexed_list A :=
  combine l (rev (seq 0 (length l))).

Definition indexed_list_to_list {A : Type} (il : indexed_list A) : list A :=
  map (fun l' => fst l') il.

(* Correctness/WF proof *)
Fixpoint indexed_list_correct_aux {A : Type} (il : indexed_list A) (i : nat) : Prop :=
  match il with
  | (_, n) :: ils => n = i /\ (indexed_list_correct_aux ils (pred i))
  | [] => True
  end.

Definition indexed_list_correct {A : Type} (il : indexed_list A) : Prop :=
  indexed_list_correct_aux il (pred (length il)).

Lemma rev_seq_S : 
  forall (len : nat) (start : nat), rev (seq start (S len)) = [(add start len)] ++ rev (seq start len).
Proof.
    intros; rewrite seq_S; rewrite rev_app_distr; auto.
Qed.

Lemma create_indexed_list_WF : 
  forall (A : Type) (l : list A), indexed_list_correct (create_indexed_list l).
Proof.
    intros. induction l; unfold create_indexed_list, indexed_list_correct in *; simpl.
    - auto.
    - simpl. destruct (length l) eqn:E. simpl; split; auto.
    apply length_zero_iff_nil in E; subst; auto.
    rewrite rev_seq_S; simpl; split; rewrite combine_length in *; rewrite app_length in *; 
    rewrite rev_length in *; rewrite seq_length in *; simpl in *;
    rewrite E in *; rewrite PeanoNat.Nat.add_1_r in *; rewrite PeanoNat.Nat.min_id in *; simpl in *; auto.
Qed.

(* Again, this is general as this should really be bounded by the length
  of the list it is referring to, it should only contain indices that
  can represent a swap in list l -> [0, length l) *)
Definition swap_list : Type := list nat.

(* Attribute this properly *)
(* I grabbed this from here: https://codeberg.org/mathprocessing/coq-examples/src/branch/master/sorts/bubblesort.v
    There is a verified version here which could replace this:
    https://github.com/holmuk/Sorticoq/blob/master/src/BubbleSort.v *)
Fixpoint bubblesort_pass (l : indexed_list nat) (sl : swap_list) : (indexed_list nat * swap_list * bool) :=
  match l with
  | [] => ([], sl, false)
  | x :: xs =>
      match bubblesort_pass xs sl with
      | ([], sl', b) => ([x], sl', b)
      | (x' :: xs', sl', b) =>
          if Nat.ltb (fst x') (fst x) 
            then (((fst x'), (snd x)) :: ((fst x), (snd x')) :: xs', ((snd x') :: sl'), true)
            else (x :: x' :: xs', sl', b)
      end
  end.

Fixpoint bubblesort_aux (gas : nat) (l : indexed_list nat) (sl : swap_list) : indexed_list nat * swap_list :=
  match gas with
  | O => (l, sl)
  | S gas' => 
    match bubblesort_pass l sl with
      | (x :: xs, sl', true) => 
        match (bubblesort_aux gas' xs sl) with
        |(xs', sl'') => ((x :: xs'), (rev sl') ++ sl'')
        end
      | _ => (l, sl)
      end
  end.

(* Needs proof of correctness *)
Definition bubblesort (l : list nat) : indexed_list nat * swap_list :=
  bubblesort_aux (pred (length l)) (create_indexed_list l) [].

Definition generate_swap_list (l : list nat) : swap_list := 
  snd (bubblesort l).

(* Could be tested more *)
(* The correct swapping procedure. Given index i, swaps the ith and i + 1th index. *)
(* 0 <= i < len(il), with index conventions as above *)
Fixpoint swap_adjacent_in_ind_list (il : indexed_list nat) (i : nat) : indexed_list nat :=
  match il with
  | [] => []
  | (x, i') :: xs => 
    match xs with
    | [] => [(x, i')]
    | (x', i'') :: xs' => 
      if (i =? i'') then 
        (x', i') :: (x, i'') :: xs'
      else
        (x, i') :: swap_adjacent_in_ind_list xs i
    end
  end.

(*  Constructing the swap structure *)
(*  From a swap index, the idea is to create a stack of wires with a 
    swap at the correct index. The convention used is imagining the 
    wire permutation indicies increasing from bottom to top in a stack.
    [(wire_1, 2), (wire_2, 1), (wire_3), 0] --> [wire_1, 2]
                                                [wire_2, 1]
                                                [wire_3, 0]
    A swap index of 1 would swap wire_1 and wire_2 above. 
    A swap index of 0 would swap wire_2 and wire_3 above. 
*)                                              
Lemma build_swap_at_index_aux_aux : 
  forall i len, le 2 len -> le (plus 2 i) len -> 
    len = plus (sub len (plus 2 i)) (plus 2 i).
Proof.
  lia.
Qed.

(* This could be rewritten as below ones *)
Fixpoint build_swap_at_index (i len : nat) : ZX len len.
Proof.
  destruct (le_lt_dec (plus 2 i) len); destruct (le_lt_dec 2 len).
  - eapply cast. 
    + eapply (build_swap_at_index_aux_aux i len).
      * exact l0.
      * exact l.
    + eapply (build_swap_at_index_aux_aux i len).
      * exact l0.
      * exact l.
    + eapply (pad_top (sub len (plus 2 i)) (pad_bot i Swap)).
  - exact (n_wire len).
  - exact (n_wire len).
  - exact (n_wire len).
Defined.

Lemma _eq_nat_eq : forall n m : nat, eq_nat n m -> n = m.
Proof.
  induction n; simpl; intro m; destruct m; simpl.
  - reflexivity.
  - contradiction.
  - contradiction.
  - intros; apply f_equal; exact (IHn m H).
Defined.

(* Putting it all together, to find the sequence of arbitrary swaps between
    two arbitrary permutations, two bubble sorts are done for each and the
    second is reversed, which creates a path between the permutations *)

(* Preserves left-right order (head-first list order) of swap list *)
Definition arbitrary_swap_from_swaplist (sl : swap_list) (len : nat) : ZX len len :=
  fold_left (fun cur_zx r => cur_zx ⟷ (build_swap_at_index r len))
            sl (n_wire len).

Definition create_arbitrary_swap (l l' : list nat) : ZX (length l) (length l).
Proof.
  destruct (eq_nat_decide (length l) (length l')).
  - eapply Compose.
      + eapply (arbitrary_swap_from_swaplist (generate_swap_list l) (length l)).
      + eapply cast.
        * eapply _eq_nat_eq; exact e.
        * eapply _eq_nat_eq; exact e.
        * eapply (arbitrary_swap_from_swaplist (rev (generate_swap_list l')) (length l')).
  - (* Dummy case *)
    exact (n_wire (length l)).
Defined.

Local Hint Unfold 
  create_arbitrary_swap
  arbitrary_swap_from_swaplist
  pad_bot
  pad_top
  : bubblesort_swap_eval_db.

Ltac eval_bubblsort_swap :=
try (
  repeat(
  autounfold with bubblesort_swap_eval_db;
  simpl);
  simpl_casts;
  cleanup_zx;
  simpl_casts;
  simpl)
.

(* Paste these examples into the ZX visualizer once simplified, equivs are clearly not true just to make a prop *)
Example bubblesort_test0 : (create_arbitrary_swap [1%nat;2%nat;3%nat] [3%nat;2%nat;1%nat]) ∝ n_wire 3.
Proof.
  eval_bubblsort_swap.
Abort.

Example bubblesort_test1 : (create_arbitrary_swap [] []) ∝ n_wire 0.
Proof.
  eval_bubblsort_swap.
Abort.

Example bubblesort_test2 : (create_arbitrary_swap [1%nat] [1%nat]) ∝ n_wire 1.
Proof.
  eval_bubblsort_swap.
Abort.

Example bubblesort_test3 : (create_arbitrary_swap [1%nat;7%nat;9%nat;3%nat] [3%nat;1%nat;9%nat;7%nat]) ∝ n_wire 4.
Proof.
  eval_bubblsort_swap.
Abort.

(* Semantic proof section here *)


(* Full translation *)

(* ZX Digraph input type *)

Inductive zx_color : Type :=
  | X_typ
  | Z_typ
.

Record zx_node := mk_node
{ id_no : nat;
  color : zx_color;
  angle : R 
}.

Definition dummy_node := (mk_node 0%nat X_typ R0). 

Inductive zx_output_node : nat -> Type :=
  | Outp (n : nat) : zx_output_node n.

(* Inputs, outputs, and nodes are all disjoint, with unique nat assignments *)
(* Mapping corresponds to nodes exactly with id_no information lining up *)
(* EDGE RULES HERE *)
Record zx_graph := mk_graph
{ mapping : list zx_node;
  inputs : list nat;
  outputs : list nat;
  nodes : list nat;
  edges : list (nat * nat)
}.

Definition get_zx_node_by_id (G : zx_graph) (n : nat) : zx_node :=
  match (find (fun node => (id_no node) =? n) (mapping G)) with
  | Some x => x
  | _ => dummy_node (* Could change this*)
  end.

Definition inb_zx_edge_list (l : list (nat * nat)) (e : nat * nat) : bool :=
  match e with
  | (e1, e2) => match (find (fun e' => ((fst e' =? e1) && (snd e' =? e2)) || ((snd e' =? e1) && (fst e' =? e2))) l) with
                | Some _ => true
                | _ => false
                end
  end.


Definition inb_zx_node_list (l : list nat) (x : nat) : bool :=
  if (in_dec Nat.eq_dec x l) then true else false.

Fixpoint remove_one {A} (eq_dec : (forall x y : A, {x = y}+{x <> y})) (x : A) (l : list A) : list A := 
  match l with
      | [] => []
      | x'::xs => if (eq_dec x x') then xs else x'::(remove_one eq_dec x xs)
  end.

Definition flatten_list_of_pairs {A} (l : list (A * A)) : list A :=
  fold_right 
    (fun e es => match e with (e1, e2) => e1::e2::es end)
    []
    l. 

Definition join_list_partition {A} (l : list A * list A) : list A :=
  fst l ++ snd l.

(*  Given two lists, lsplit (list to be split), and lpool, returns 
    a pair of lists, the left list is elements of lsplit that are in lpool
    , and the right is those that are not. This accounts for duplicates,
    so its like subtracting lpool from lsplit *)
Fixpoint largest_subset_and_rest_split (lsplit lpool : list nat) : list nat * list nat  :=
  match lsplit with
  | [] => ([], [])
  | x::xs =>  if (inb_zx_node_list lpool x) then 
                match (largest_subset_and_rest_split xs (remove_one Nat.eq_dec x lpool)) with
                | (l1, l2) => (x :: l1, l2)
                end
              else
                match (largest_subset_and_rest_split xs lpool) with
                | (l1, l2) => (l1, x::l2)
                end
  end.

(* Test more? *)
(* Compute (largest_subset_and_rest_split [1%nat; 2%nat; 3%nat; 4%nat; 4%nat] [4%nat; 5%nat; 4%nat; 3%nat]). *)


Definition get_connections (G : zx_graph) (node : nat) : list (nat * nat) :=
  filter (fun n => orb (node =? (fst n)) (node =? (snd n))) (edges G).

Definition get_neighbors (G : zx_graph) (node : nat) : list nat :=
  map (fun n => if ((fst n) =? node) then (snd n) else fst n) (get_connections G node).


Definition partition_self_edges (G : zx_graph) : list (nat * nat) * list (nat * nat) :=
  partition (fun n => ((fst n) =? (snd n))) (edges G).


Definition get_self_edges (G : zx_graph) : list (nat * nat) :=
  fst (partition_self_edges G).


Definition removed_self_edges (G : zx_graph) : list (nat * nat) :=
  snd (partition_self_edges G).

Definition get_edges_within_boundary_state (G : zx_graph) (b_state : list nat) : list (nat * nat) :=
  filter (fun e => match e with (e1, e2) => 
    (inb_zx_node_list b_state e1) && (inb_zx_node_list b_state e2) end) (edges G).

Definition get_input_state_loops_unflattened (G : zx_graph) : list nat * list nat :=
    (largest_subset_and_rest_split
      (inputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (inputs G)))).

Definition get_output_state_loops_unflattened (G : zx_graph) : list nat * list nat :=
    (largest_subset_and_rest_split
      (outputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (outputs G)))).

Definition get_input_state_cleaned (G : zx_graph) : list nat :=
  snd
    (largest_subset_and_rest_split
      (inputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (inputs G)))).

Definition get_output_state_cleaned (G : zx_graph) : list nat :=
  snd
    (largest_subset_and_rest_split
      (outputs G)
      (flatten_list_of_pairs (get_edges_within_boundary_state G (outputs G)))).

Definition get_input_state_loops_ordered (G : zx_graph) : list nat :=
  let es := (get_edges_within_boundary_state G (inputs G)) in
    (flatten_list_of_pairs es) ++ (get_input_state_cleaned G).

Definition get_output_state_loops_ordered (G : zx_graph) : list nat :=
  let es := (get_edges_within_boundary_state G (outputs G)) in
  (flatten_list_of_pairs es) ++ (get_output_state_cleaned G).

(* Check on pair order here *)
Definition distribute_inputs_outputs (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat * list nat :=
  largest_subset_and_rest_split (get_neighbors G cur_node) cur_state.

Definition get_cur_inputs (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  fst (distribute_inputs_outputs G cur_state cur_node).

Definition get_cur_outputs (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  snd (distribute_inputs_outputs G cur_state cur_node).

Definition split_cur_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat * list nat :=
  largest_subset_and_rest_split cur_state (get_cur_inputs G cur_state cur_node).

Definition get_goal_ordering (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  join_list_partition (split_cur_state G cur_state cur_node).

Definition get_cur_inputs_in_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  fst (split_cur_state G cur_state cur_node).

Definition get_rest_cur_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  snd (split_cur_state G cur_state cur_node).

Definition get_new_state (G : zx_graph) (cur_state : list nat) (cur_node : nat) : list nat :=
  (repeat cur_node (length (get_cur_outputs G cur_state cur_node))) ++ 
  (get_rest_cur_state G cur_state cur_node).


Lemma largest_subset_and_rest_split_length : 
  forall lsplit lpool l1 l2,
  largest_subset_and_rest_split lsplit lpool = (l1, l2) ->
  length lsplit = ((length l1) + (length l2))%nat.
Proof.
  induction lsplit; intros.
    - inversion H; easy.
    - simpl; simpl in H; destruct (inb_zx_node_list lpool a).
      + destruct (largest_subset_and_rest_split lsplit (remove_one Nat.eq_dec a lpool)) eqn: E; inversion H;
        simpl; f_equal; eapply (IHlsplit (remove_one Nat.eq_dec a lpool) l l2); subst; exact E.
      + destruct (largest_subset_and_rest_split lsplit lpool) eqn:E; inversion H; simpl; subst;
        rewrite Nat.add_comm; simpl; f_equal; rewrite Nat.add_comm; eapply IHlsplit; exact E.
Defined.

Lemma build_node_structure_aux : forall G (cur_state : list nat) cur_node, 
  length cur_state = ((length (get_cur_inputs_in_state G cur_state cur_node)) + (length (get_rest_cur_state G cur_state cur_node)))%nat.
Proof.
  intros; unfold get_rest_cur_state, get_cur_inputs_in_state, split_cur_state.
  destruct (largest_subset_and_rest_split cur_state (get_cur_inputs G cur_state cur_node)) eqn:E.
  eapply largest_subset_and_rest_split_length; simpl; exact E.
Qed.

(* Check that this swap is correct *)
Definition build_swap_structure (G : zx_graph) (cur_state : list nat) (cur_node : nat) : ZX (length cur_state) (length cur_state) :=
  create_arbitrary_swap cur_state (get_goal_ordering G cur_state cur_node).

Definition zx_node_id_to_spider_aux (G : zx_graph) (id_no n m : nat) : ZX n m :=
  let node := (get_zx_node_by_id G id_no) in 
    match color node with 
    | X_typ => X_Spider n m (angle node)
    | _ => Z_Spider n m (angle node)
    end.


Fixpoint add_k_self_loops_to_spider {n m} (k : nat) (cur : ZX (k + n) (k + m))  : ZX n m.
Proof.
  destruct k.
  - exact cur.
  - apply add_k_self_loops_to_spider with (k := k); eapply Compose.
    + exact (pad_bot (k + n) ⊂).
    + eapply Compose. assert (H : forall i, (2 + i = 1 + S (i))%nat). reflexivity.
      * eapply cast.
        { specialize H with (k + n)%nat; exact H. }
        { specialize H with (k + m)%nat; exact H. }
        { eapply Stack. eapply Wire. exact cur. }
      *  exact (pad_bot (k + m) ⊃).
Defined.

Definition get_self_edges_by_id (G : zx_graph) (self_edges : list (nat * nat)) (id_no : nat) : list (nat * nat) :=
  filter (fun e => (fst e =? id_no)) self_edges.

(* Need to consider box edges? *)
Definition zx_node_id_to_spider (G : zx_graph) (self_edges : list (nat * nat)) (id_no n m : nat) : ZX n m :=
  let k := (length (get_self_edges_by_id G self_edges id_no)) in
    add_k_self_loops_to_spider k (zx_node_id_to_spider_aux G id_no (k + n) (k + m))%nat.


Definition build_node_structure (G : zx_graph) (self_edges : list (nat * nat)) (cur_state : list nat) (cur_node : nat) : 
  ZX (length cur_state) ((length (get_cur_outputs G cur_state cur_node)) + (length (get_rest_cur_state G cur_state cur_node))).
Proof.
  intros; eapply cast.
  - exact (build_node_structure_aux G cur_state cur_node).
  - reflexivity.
  - exact (pad_bot 
    (length (get_rest_cur_state G cur_state cur_node))
    (zx_node_id_to_spider G self_edges cur_node 
      (length (get_cur_inputs_in_state G cur_state cur_node))
      (length (get_cur_outputs G cur_state cur_node)))).
Defined.

Definition one_node_translate (G : zx_graph) (self_edges : list (nat * nat)) (cur_state : list nat) (cur_node : nat) : 
  ZX (length cur_state) ((length (get_cur_outputs G cur_state cur_node)) + (length (get_rest_cur_state G cur_state cur_node))) :=
  (build_swap_structure G cur_state cur_node) ⟷ (build_node_structure G self_edges cur_state cur_node). 


(* Dummys could be replaced *)
Definition dummy_spider (n m : nat) : ZX n m := X_Spider n m R0.

Fixpoint build_n_capcup (n : nat) (cup : bool) : ZX (if cup then Nat.double n else 0) (if cup then 0 else Nat.double n).
Proof.
  assert (Htemp : forall n, ((S (n + (S n)) = (2 + (Nat.double n)))%nat)). 
  intros; unfold Nat.double in *; lia.
  induction n; destruct cup eqn:Ec; unfold Nat.double in *.
  - exact Empty.
  - exact Empty. 
  - simpl; eapply cast.
    + exact (Htemp n).
    + exact (eq_sym (Nat.add_0_r (0%nat))).
    + eapply Stack.
      * eapply Cup.
      * exact (build_n_capcup n true).
  - simpl; eapply cast.
    + exact (eq_sym (Nat.add_0_r (0%nat))).
    + exact (Htemp n).
    + eapply Stack.
      * eapply Cap.
      * exact (build_n_capcup n false).
Defined.

Lemma remove_loops_from_output_aux_aux : forall G (loops outps : list nat), 
  (get_output_state_loops_unflattened G) = (loops, outps) -> 
  (length (outputs G)) = ((length loops) + (length outps))%nat.
Proof.
  intros. 
  unfold get_output_state_loops_unflattened in H. 
  apply (largest_subset_and_rest_split_length) with (lpool :=  (flatten_list_of_pairs
  (get_edges_within_boundary_state G (outputs G)))); exact H.
Defined.

Definition remove_loops_from_output_aux (G : zx_graph) (n m halfn : nat) (Heven : n = (Nat.double halfn)%nat) : 
  ZX m (n + m).
Proof.
  eapply cast.
    - assert (H :  m = (0 + m)%nat). reflexivity. exact H.
    - reflexivity.
    - eapply Stack.
      * eapply cast.
        { reflexivity. }
        { exact Heven. }
        { exact (build_n_capcup halfn false). }
      * exact (n_wire m).
Defined.

Lemma even_explicit_div2 : forall n m, 
  Nat.even n = true -> m = div2 n -> n = (Nat.double m)%nat.
Proof.
  intros; apply Nat.even_spec in H; subst; eapply Nat.Even_double; easy.
Defined.

Definition remove_loops_from_output (G : zx_graph) : ZX (length (get_output_state_cleaned G)) (length (outputs G)).
Proof.
  destruct (get_output_state_loops_unflattened G) as [loops outps] eqn:Eoutps; 
  destruct (Nat.even (length loops)) eqn:Eeven;
    remember (div2 (length loops)) as halfn.
  - eapply Compose.
    +  eapply cast.
      * unfold get_output_state_cleaned; unfold get_output_state_loops_unflattened in Eoutps;
        destruct (largest_subset_and_rest_split (outputs G)
          (flatten_list_of_pairs
          (get_edges_within_boundary_state G (outputs G)))); 
          simpl; inversion Eoutps; reflexivity.
      * apply remove_loops_from_output_aux_aux; exact Eoutps.
      * exact (remove_loops_from_output_aux G (length loops) (length outps) halfn
              (even_explicit_div2 (length loops) halfn Eeven Heqhalfn)).
    + destruct (eq_nat_decide (length (get_output_state_loops_ordered G)) (length (outputs G))) as [L|R]. 
      apply _eq_nat_eq in L; eapply cast.
      * exact (eq_sym L).
      * exact (eq_sym L).
      * exact (create_arbitrary_swap (get_output_state_loops_ordered G) (outputs G)).
      * (* Another dummy case*) apply dummy_spider.
  - (* dummy case, there would always be an even number here *)
    apply dummy_spider.
Defined.

Definition gtb_last_fence_post (G : zx_graph) (cur_state : list nat) : ZX (length cur_state) (length (outputs G)).
Proof.
  eapply Compose.
  - exact (create_arbitrary_swap cur_state (get_output_state_cleaned G)).
  - destruct (eq_nat_decide (length cur_state) (length (get_output_state_cleaned G))) as [L | R].
    + eapply cast.
      * exact (_eq_nat_eq (length cur_state) (length (get_output_state_cleaned G)) L).
      * reflexivity.
      * exact (remove_loops_from_output G).
    (* Dummy output below *)
    + apply dummy_spider.
Defined.

(* Remove rewrites? *)
Lemma graph_to_block_structure_aux_aux : 
  forall G cur_state cur_node, (length (get_new_state G cur_state cur_node) = (length (get_cur_outputs G cur_state cur_node) + length (get_rest_cur_state G cur_state cur_node)))%nat.
Proof.
  intros; unfold get_new_state.
  rewrite app_length; rewrite repeat_length; easy.
Qed.

Fixpoint graph_to_block_structure_aux (G : zx_graph) (node_order : list nat) (cur_state : list nat) (self_edges : list (nat * nat)) : 
  ZX (length cur_state) (length (outputs G)).
Proof.
  destruct node_order as [| cur_node ns] eqn:E.
  - exact (gtb_last_fence_post G cur_state).
  - eapply Compose.
    + exact (one_node_translate G self_edges cur_state cur_node).
    + eapply cast.
      * exact (eq_sym (graph_to_block_structure_aux_aux G cur_state cur_node)). 
      * reflexivity.
      * exact (graph_to_block_structure_aux G ns (get_new_state G cur_state cur_node) self_edges).
Defined.

Lemma remove_loops_from_input_aux_aux : forall G (loops inpts : list nat), 
  (get_input_state_loops_unflattened G) = (loops, inpts) -> 
  (length (inputs G)) = ((length loops) + (length inpts))%nat.
Proof.
  intros. 
  unfold get_input_state_loops_unflattened in H. 
  apply (largest_subset_and_rest_split_length) with (lpool := (flatten_list_of_pairs
  (get_edges_within_boundary_state G (inputs G)))); exact H.
Defined.

Definition remove_loops_from_input_aux (G : zx_graph) (n m halfn : nat) (Heven : n = (Nat.double halfn)%nat) : 
  ZX (n + m) m.
Proof.
  eapply cast.
    - reflexivity.
    - assert (H :  m = (0 + m)%nat). reflexivity. exact H.
    - eapply Stack.
      * eapply cast.
        { exact Heven. }
        { reflexivity. }
        { exact (build_n_capcup halfn true). }
      * exact (n_wire m).
Defined.

Definition remove_loops_from_input (G : zx_graph) : ZX (length (inputs G)) (length (get_input_state_cleaned G)) .
Proof.
  destruct (get_input_state_loops_unflattened G) as [loops inpts] eqn:Einpts; 
  destruct (Nat.even (length loops)) eqn:Eeven; remember (div2 (length loops)) as halfn.
  - eapply Compose.
    + exact (create_arbitrary_swap (inputs G) (get_input_state_loops_ordered G)).
    + eapply cast.
      * apply remove_loops_from_input_aux_aux; exact Einpts.
      * unfold get_input_state_cleaned; unfold get_input_state_loops_unflattened in Einpts;
        destruct (largest_subset_and_rest_split (inputs G)
          (flatten_list_of_pairs
          (get_edges_within_boundary_state G (inputs G)))); 
          simpl; inversion Einpts; reflexivity.
      * exact (remove_loops_from_input_aux G (length loops) (length inpts) halfn
              (even_explicit_div2 (length loops) halfn Eeven Heqhalfn)).
  - (* dummy case, there would always be an even number here *)
    apply dummy_spider.
Defined.

(* Translation function *)
Definition graph_to_block_structure (G : zx_graph) : ZX (length (inputs G)) (length (outputs G)) :=
  let G' := mk_graph (mapping G) (inputs G) (outputs G) (nodes G) (removed_self_edges G) in
    (remove_loops_from_input G') ⟷
    graph_to_block_structure_aux G' (nodes G') (get_input_state_cleaned G') (get_self_edges G).

Local Hint Unfold 
  graph_to_block_structure 
  remove_loops_from_input
  remove_loops_from_input_aux
  graph_to_block_structure_aux 
  get_edges_within_boundary_state
  get_input_state_loops_unflattened
  get_input_state_cleaned
  get_input_state_loops_ordered
  gtb_last_fence_post
  get_output_state_loops_unflattened
  get_output_state_cleaned
  get_output_state_loops_ordered
  build_n_capcup
  Nat.double
  one_node_translate
  build_node_structure
  build_swap_structure
  zx_node_id_to_spider
  get_self_edges_by_id
  add_k_self_loops_to_spider
  zx_node_id_to_spider_aux
  get_new_state
  get_rest_cur_state
  get_cur_inputs_in_state
  get_goal_ordering
  split_cur_state
  get_cur_outputs
  get_cur_inputs
  distribute_inputs_outputs
  removed_self_edges
  get_self_edges
  partition_self_edges
  get_neighbors
  get_connections
  remove_loops_from_output
  remove_loops_from_output_aux
  inb_zx_node_list
  : graph_translate_eval_db.

Ltac eval_graph_translation :=
  try (
    repeat(
    autounfold with graph_translate_eval_db;
    simpl);
    simpl_casts;
    cleanup_zx;
    simpl)
  .
(* Need to update tactic *)

Definition node0 := mk_node 9%nat X_typ R0.
Definition node1 := mk_node 4%nat X_typ R1.
Definition node2 := mk_node 5%nat X_typ PI.
Definition node4 := mk_node 4%nat X_typ R0.
Definition node5 := mk_node 5%nat X_typ R0.
Definition node6 := mk_node 6%nat X_typ R0.
Definition node7 := mk_node 7%nat Z_typ R0.
Definition node8 := mk_node 8%nat Z_typ R0.
Definition node9 := mk_node 9%nat Z_typ R0.



(* inputs and outputs are just nat ids as well *)
Definition test0 := mk_graph
  [node0] 
  [0%nat]
  [1%nat]
  [4%nat]
  [(0%nat, 4%nat); (4%nat, 4%nat); (4%nat, 4%nat); (4%nat, 1%nat)].

Definition test1 := mk_graph
  [node1; node2] 
  [1%nat; 0%nat]
  [2%nat; 3%nat]
  [4%nat; 5%nat]
  [(0%nat, 4%nat); (1%nat, 5%nat); (4%nat, 3%nat); (5%nat, 2%nat)].

(* Compute (get_zx_node_by_id test1 5%nat). *)

Definition test2 := mk_graph
  [node4; node5; node6; node7; node8; node9]
  [0%nat; 1%nat]
  [2%nat; 3%nat]
  [4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat]
  [(0%nat, 7%nat); (7%nat, 4%nat); (7%nat, 5%nat); (4%nat, 0%nat); (4%nat, 8%nat);
   (5%nat, 8%nat); (5%nat, 9%nat); (6%nat, 8%nat); (6%nat, 9%nat); (6%nat, 2%nat);
   (9%nat, 3%nat)].

Definition test3 := mk_graph
  [node8]
  [0%nat; 1%nat; 2%nat; 3%nat]
  [4%nat; 5%nat; 6%nat; 7%nat]
  [8%nat]
  [(0%nat, 2%nat); (4%nat, 7%nat); (1%nat, 6%nat); (3%nat, 8%nat); (8%nat, 5%nat)].

(* Need to account for even predicate in simplifying *)

(* Compute ((graph_to_block_structure test3)). *)

Example see_if_algo_works3 : 
  (graph_to_block_structure test3) ∝ (n_wire 4).
Proof.
  (* eval_graph_translation.
  simpl.
  unfold remove_loops_from_output_aux_aux.
  (* unfold largest_subset_and_rest_split_length. *)
  simpl.
  unfold even_explicit_div2.
  unfold Nat.double.
  simpl.
  simpl_casts. *)
  (* simpl_casts.
  simpl.
  simpl_casts. *)
  
  
  (* simpl.
  simpl_casts.


(* Example see_if_algo_works : 
  (graph_to_block_structure test1) ∝ X_Spider (length (inputs test1)) (length (outputs test1)) R0.
Proof.
  eval_graph_translation.
  Abort. *)
(* 
Compute  (graph_to_block_structure test2).
Compute ((get_self_edges test2)).

Example see_if_algo_works2 : 
  (graph_to_block_structure test2) ∝ Swap.
Proof.
  *) *)