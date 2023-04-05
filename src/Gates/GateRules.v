Require Import QuantumLib.Quantum.
Require Export ZXCore.
Require Export GateDefinitions.
Require Export CoreRules.

Local Open Scope ZX_scope.

Lemma Z_is_Z : ZX_semantics (_Z_) = σz.
Proof.
  simpl.
  unfold Z_semantics.
  autorewrite with Cexp_db.
  simpl.
  solve_matrix.
Qed.

Lemma X_is_X : ZX_semantics (_X_) = σx.
Proof.
  simpl.
  unfold X_semantics; solve_matrix.
  all: autorewrite with Cexp_db.
  all: C_field_simplify; try lca.
  all: split; nonzero.
Qed.


Lemma _H_is_box : _H_ ∝ □.
Proof.
  prop_exists_nonzero (Cexp (PI/4)).
  simpl.
  unfold X_semantics, Z_semantics.
  Msimpl.
  solve_matrix;
  field_simplify_eq [Cexp_PI2 Cexp_PI4 Ci2 Csqrt2_sqrt2_inv Csqrt2_inv]; 
  try apply c_proj_eq; try simpl; try R_field_simplify; try reflexivity; (try split; try apply RtoC_neq; try apply sqrt2_neq_0; try auto).
Qed.


Lemma cnot_l_is_cnot : ZX_semantics _CNOT_ = (/ √ 2)%C .* cnot.
Proof.
  simpl.
  unfold Z_semantics, X_semantics.
  solve_matrix.
  all: autorewrite with Cexp_db.
  all: lca.
Qed.

Lemma cnot_inv_is_swapped_cnot : ZX_semantics _CNOT_inv_ = (/ √ 2)%C .* (swap × cnot × swap)%M.
Proof.
  simpl.
  unfold Z_semantics, X_semantics.
  solve_matrix.
  all: autorewrite with Cexp_db.
  all: lca.
Qed.

Lemma _Rz_is_Rz : forall α, ZX_semantics (_Rz_ α) = phase_shift α.
Proof.
  intros.
  simpl.
  unfold Z_semantics, phase_shift.
  simpl.
  lma.
Qed.