(* do I need to cite this *)

(* Preloaded.v

   The key definitions and notations presented in this file are
   adapted from the Software Foundations series, an excellent
   resource for learning Coq:
   https://softwarefoundations.cis.upenn.edu/current/index.html

   The copyright notice of the series is reproduced below as
   follows:

   Copyright (c) 2019

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
   THE SOFTWARE. *)

(* Volume 3: Verified Functional Algorithms *)

(* Basic Techniques for Permutations and Ordering (Perm) *)

From Coq Require Import Lists.List.
From Coq Require Import Nat.
Import ListNotations.
Require Import Permutation.

Notation "a >? b" := (Nat.ltb b a)
  (at level 70, only parsing) : nat_scope.

Definition indexed_list (A : Type) : Type := list (A * nat).

Definition create_indexed_list {A : Type} (l : list A) : indexed_list A :=
  combine l (rev (seq 0 (length l))).

Fixpoint indexed_list_to_list {A : Type} (il : indexed_list A) : list A :=
  match il with
  | [] => []
  | (x, i) :: xs => x :: indexed_list_to_list xs
  end.

Fixpoint indexed_list_correct_aux {A : Type} (il : indexed_list A) (i : nat) : Prop :=
  match il with
  | (_, n) :: ils => n = i /\ (indexed_list_correct_aux ils (pred i))
  | [] => True
  end.

Definition indexed_list_correct {A : Type} (il : indexed_list A) : Prop :=
  indexed_list_correct_aux il (pred (length il)).

Lemma rev_seq_S : 
  forall len start, rev (seq start (S len)) = [start + len] ++ rev (seq start len).
Proof.
intros; rewrite seq_S; rewrite rev_app_distr; auto.
Qed.

Lemma indexed_list_correct_lemma : 
  forall (A : Type) (l : list A), indexed_list_correct (create_indexed_list l).
Proof.
intros. induction l; unfold create_indexed_list, indexed_list_correct in *; simpl.
- exact I.
- simpl. destruct (length l) eqn:E. simpl; split; auto.
  apply length_zero_iff_nil in E; subst; auto.
  rewrite rev_seq_S; simpl; split; rewrite combine_length in *; rewrite app_length in *; 
  rewrite rev_length in *; rewrite seq_length in *; simpl in *;
  rewrite E in *; rewrite PeanoNat.Nat.add_1_r in *; rewrite PeanoNat.Nat.min_id in *; simpl in *; auto.
Qed.

Definition swap_list : Type := list nat.

Fixpoint bubblesort_pass (l : indexed_list nat) (sl : swap_list) : (indexed_list nat * swap_list * bool) :=
  match l with
  | [] => ([], sl, false)
  | x :: xs =>
      match bubblesort_pass xs sl with
      | ([], sl', b) => ([x], sl', b)
      | (x' :: xs', sl', b) =>
          if (fst x) >? (fst x')
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

Definition bubblesort (l : list nat) : indexed_list nat * swap_list :=
  bubblesort_aux (pred (length l)) (create_indexed_list l) [].

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

Fixpoint batch_swap_adj_in_ind_list (il : indexed_list nat) (sl : swap_list) : indexed_list nat :=
  match sl with
  | [] => il
  | s :: ss => batch_swap_adj_in_ind_list (swap_adjacent_in_ind_list il s) ss
  end.

Definition test_l := [53; 185; 96; 31; 142; 77; 193; 168; 12; 55; 23; 110; 182; 171; 147].

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
