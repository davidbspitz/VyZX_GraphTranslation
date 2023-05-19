From Coq Require Import Lists.List.
From Coq Require Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.Compare_dec.
Import ListNotations.
Require Import CoreData.CoreData.
(* From Coq Require Import Sorting.Permutation. *)
Require Import Ingest.SQIRIngest.
Require Import Lia.

(*  This entire section has the goal of constructing any general 
    ZX swap structure that can swap between any two permutations.
    The ZX swap only swaps adjacent indices, so a bubblesort is needed.
*)

(*  This is more general than a correct indexed list, but we can have a 
    well formedness property instead *)
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


(* Fixpoint debug_batch_swap_adj_in_ind_list (il : indexed_list nat) (sl : swap_list) : list (indexed_list nat) :=
  match sl with
  | [] => []
  | s :: ss => (swap_adjacent_in_ind_list il s) :: (debug_batch_swap_adj_in_ind_list (swap_adjacent_in_ind_list il s) ss)
  end.

Definition prettify (l : list (indexed_list nat)) : list (list nat) :=
  map (fun l' => List.map fst l') l.

Definition mylist := [2%nat; 9%nat; 6%nat; 8%nat; 1%nat; 5%nat; 4%nat; 7%nat].

Compute (generate_swap_list mylist).

Compute prettify (debug_batch_swap_adj_in_ind_list (create_indexed_list mylist) (snd (bubblesort mylist))).

Fixpoint batch_swap_adj_in_ind_list (il : indexed_list nat) (sl : swap_list) : indexed_list nat :=
  match sl with
  | [] => il
  | s :: ss => batch_swap_adj_in_ind_list (swap_adjacent_in_ind_list il s) ss
  end. *)


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
        * eapply eq_nat_eq; exact e.
        * eapply eq_nat_eq; exact e.
        * eapply (arbitrary_swap_from_swaplist (rev (generate_swap_list l')) (length l')).
  - exact (n_wire (length l)).
Defined.

Compute (create_arbitrary_swap [1%nat;2%nat;3%nat] [3%nat;2%nat;1%nat]).

Compute (build_swap_at_index 3 5).



(* Definition test_l := [53; 185; 96; 31; 142; 77; 193; 168; 12; 55; 23; 110; 182; 171; 147]. *)

(* Compute bubblesort test_l.

Compute indexed_list_to_list(batch_swap_adj_in_ind_list 
(create_indexed_list test_l)
(snd (bubblesort test_l))). *)


(* 
Inductive sorted: list nat -> Prop := 
| sorted_nil:
    sorted []
| sorted_1: forall x,
    sorted [x]
| sorted_cons: forall x y l,
   x <= y -> sorted [y;l] -> sorted [x;y;l].

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al). *)

(* Lemma bubblesort_correct : is_a_sorting_algorithm (bubblesort).
Proof.
intros l; induction l.
Admitted. *)