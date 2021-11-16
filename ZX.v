Require Import Coq.Vectors.Fin.
Require Import externals.QuantumLib.Quantum.
Require Import externals.QuantumLib.Proportional.

Declare Scope ZX_scope.
Local Open Scope ZX_scope.

Local Open Scope R_scope.
Inductive ZX : nat -> nat -> Type :=
  | Empty : ZX 0 0
  | X_Spider nIn nOut (α : R) : ZX nIn nOut
  | Z_Spider nIn nOut (α : R) : ZX nIn nOut
  | Cap : ZX 0 2
  | Cup : ZX 2 0
  | Stack {nIn0 nIn1 nOut0 nOut1} (zx0 : ZX nIn0 nOut0) (zx1 : ZX nIn1 nOut1) :
      ZX (nIn0 + nIn1) (nOut0 + nOut1)
  | Compose {nIn nMid nOut} (zx0 : ZX nIn nMid) (zx1 : ZX nMid nOut) : ZX nIn nOut.
Local Close Scope R_scope.

Definition bra_ket_MN (bra: Matrix 1 2) (ket : Vector 2) {n m} : Matrix (2 ^ m) (2 ^ n) := 
  (m ⨂ ket) × (n ⨂ bra).
Transparent bra_ket_MN. 

Definition Spider_Semantics_Impl (bra0 bra1 : Matrix 1 2) (ket0 ket1 : Vector 2) (α : R) {n m : nat} : Matrix (2 ^ m) (2 ^ n) :=
  (bra_ket_MN bra0 ket0) .+ (Cexp α) .* (bra_ket_MN bra1 ket1). 
Transparent Spider_Semantics_Impl.

Fixpoint ZX_semantics {nIn nOut} (zx : ZX nIn nOut) : 
  Matrix (2 ^ nOut) (2 ^nIn) := 
  match zx with
  | Empty => I 1
  | X_Spider _ _ α => Spider_Semantics_Impl (hadamard × (ket 0))† (hadamard × (ket 1))† (hadamard × (ket 0)) (hadamard × (ket 1)) α
  | Z_Spider _ _ α => Spider_Semantics_Impl (bra 0) (bra 1) (ket 0) (ket 1) α
  | Cup => list2D_to_matrix [[C1;C0;C0;C1]]
  | Cap => list2D_to_matrix [[C1];[C0];[C0];[C1]]  
  | Stack zx0 zx1 => (ZX_semantics zx0) ⊗ (ZX_semantics zx1)
  | Compose zx0 zx1 => (ZX_semantics zx1) × (ZX_semantics zx0)
  end.

Theorem WF_ZX : forall nIn nOut (zx : ZX nIn nOut), WF_Matrix (ZX_semantics zx).
Proof.
  intros.
  induction zx; try (simpl; auto 10 with wf_db).
  - unfold Spider_Semantics_Impl, bra_ket_MN; try apply WF_plus; try apply WF_scale; apply WF_mult; try restore_dims; try auto with wf_db.
  - unfold Spider_Semantics_Impl, bra_ket_MN; try apply WF_plus; try apply WF_scale; apply WF_mult; try restore_dims; try auto with wf_db.
  - apply WF_list2D_to_matrix.
    + easy.
    + intros.
      simpl in H; repeat destruct H; try discriminate; try (subst; easy).
  - apply WF_list2D_to_matrix.
    + easy.
    + intros.
      simpl in H; destruct H; try discriminate; try (subst; easy).
Qed.

Global Hint Resolve WF_ZX : wf_db.

Lemma ZX_Semantics_Stack_Empty_r : forall {nIn nOut} (zx : ZX nIn nOut),
  ZX_semantics (Stack zx Empty) = ZX_semantics zx.
Proof. intros; simpl; apply kron_1_r. Qed.
  
Lemma ZX_Semantics_Stack_Empty_l : forall {nIn nOut} (zx : ZX nIn nOut),
  ZX_semantics (Stack Empty zx) = ZX_semantics zx.
Proof. intros; simpl; apply kron_1_l. apply WF_ZX. Qed.

Lemma ZX_Semantics_Compose_Empty_r : forall {nIn} (zx : ZX nIn 0),
  ZX_semantics (Compose zx Empty) = ZX_semantics zx.
Proof. intros; simpl; apply Mmult_1_l; restore_dims; auto with wf_db. Qed.

  
Lemma ZX_Semantics_Compose_Empty_l : forall {nOut} (zx : ZX 0 nOut),
  ZX_semantics (Compose Empty zx) = ZX_semantics zx.
Proof. intros; simpl; apply Mmult_1_r; restore_dims; auto with wf_db. Qed.

Definition Wire : ZX 1 1 := Z_Spider _ _ 0.

Lemma bra_ket_id : ket 0 × bra 0 .+ ket 1 × bra 1 = I 2.
Proof. solve_matrix. Qed.

Theorem wire_identity_semantics : ZX_semantics Wire = I 2.
Proof.
  simpl.
  unfold Spider_Semantics_Impl, bra_ket_MN.
  rewrite Cexp_0.
  rewrite Mscale_1_l.
  unfold kron_n.
  repeat rewrite kron_1_l; try auto with wf_db.
  apply bra_ket_id.
Qed.

Global Opaque Wire.

Global Hint Resolve wire_identity_semantics : zx_sem_db.

Fixpoint nStack {nIn nOut} (zx : ZX nIn nOut) n : ZX (n * nIn) (n * nOut) :=
  match n with
  | 0 => Empty
  | S n' => Stack zx (nStack zx n')
  end.

Fixpoint nStack1 (zx : ZX 1 1) n : ZX n n :=
  match n with
  | 0 => Empty
  | S n' => Stack zx (nStack1 zx n')
  end.

Lemma nStack1_n_kron : forall n (zx : ZX 1 1), ZX_semantics (nStack1 zx n) = n ⨂ ZX_semantics zx.
Proof.
  intros.
  induction n.
  - unfold nStack1. simpl. auto.
  - simpl.
    rewrite IHn.
    Msimpl.
    rewrite <- kron_n_assoc; auto with wf_db.
Qed.

Definition nWire := (nStack1 Wire).

Global Opaque nWire.

Local Close Scope ZX_scope.
