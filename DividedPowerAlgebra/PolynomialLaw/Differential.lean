/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import DividedPowerAlgebra.PolynomialLaw.Polarized
import DividedPowerAlgebra.PolynomialLaw.Prod

/-! # Differentials of polynomial laws (work in progress)

In this file we propose a first formalization of the definition of the differential of a polynomial
law, following [Roby63, definition in pg. 239].

## Main definitions

* `PolynomialLaw.dividedDifferential'`: the differential of order `k` of a polynomial law,
  denoted by `D^k f` in [Roby63].

* `PolynomialLaw.dividedPartialDerivative'`: the `n`th divided partial derivative of `f` at `x`.

## TODO

* Prove the Taylor formula for polynomial laws [Roby63, Prop. II.2]

-/

noncomputable section

open MvPolynomial TensorProduct

universe u

variable {R : Type u} [CommSemiring R] {M M' N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N] (f : M →ₚₗ[R] N) (n p : ℕ)

namespace PolynomialLaw

/-- `n`-th divided differential of a polynomial law ([Roby1963], §II.4, p. 239). -/
def dividedDifferential : (M →ₚₗ[R] N) →ₗ[R] ((M × M) →ₚₗ[R] N) where
  toFun f := PolynomialLaw.lfsum (fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f)
  map_add' f g := by
    ext S _ _ sm
    simp only [add_def, Pi.add_apply, polarizedProd_biComponent, map_add]
    simp only [← toFun_eq_toFun']
    have hfg : LocFinsupp fun p ↦ (polarizedProd f).biComponent (p, n) +
        (polarizedProd g).biComponent (p, n) :=
      locFinsupp_add (locFinsupp_polarizedProd_biComponent n f)
        (locFinsupp_polarizedProd_biComponent n g)
    rw [← lfsumHom_apply hfg, ← lfsumHom_apply (locFinsupp_polarizedProd_biComponent n f),
      ← lfsumHom_apply (locFinsupp_polarizedProd_biComponent n g), ← add_toFun_apply]
    simp only [polarizedProd_biComponent, ← lfsumHom_add (hfg := hfg)]
    rfl -- the two functions are definitionally equal
  map_smul' r f := by
    ext S _ _ sm
    simp only [RingHom.id_apply, smul_def, Pi.smul_apply, polarizedProd_biComponent]
    rw [← PolynomialLaw.smul_def_apply]
    have hf := (locFinsupp_polarizedProd_biComponent n f)
    have hrf : LocFinsupp fun p ↦ (biComponent (p, n)) (polarizedProd (r • f)) := by
        simp only [map_smul]
        exact locFinsupp_smul (locFinsupp_polarizedProd_biComponent n f) r
    rw [← lfsumHom_apply hf, ← lfsumHom_apply hrf, ← lfsumHom_smul hf (locFinsupp_smul hf r)]
    simp only [map_smul]
    rfl -- the functions are definitionally equal

lemma biCoeffBaseChange_polarizedProd (a n : ℕ) (m m' : M) :
    biCoeffBaseChange f.polarizedProd ((1 : R) ⊗ₜ[R] (m, m')) (a, n) =
      1 ⊗ₜ[R] ((coeff ![m, m']) f) ((finTwoArrowEquiv' ℕ).symm (a, n)) := by
  rw [biCoeffBaseChange_eq, biCoeffBaseChange'_apply_tmul]
  simp only [scalarRTensorAlgEquiv, AlgEquiv.toLinearEquiv_trans, Fin.isValue, map_add,
    assoc_symm_tmul, LinearEquiv.rTensor_tmul, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, rTensorAlgEquiv_apply, rTensorAlgHom,
    Algebra.TensorProduct.lift_tmul, mapAlgHom_apply, eval₂_X, AlgHom.coe_comp,
    IsScalarTower.coe_toAlgHom', algebraMap_eq, Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, map_mul, mapAlgEquiv_apply, map_X, map_C,
    RingHom.coe_coe, Algebra.TensorProduct.lid_tmul, smul_eq_mul, mul_one, C_1,
    finTwoArrowEquiv'_symm_apply, rTensor_apply, Nat.succ_eq_add_one, Nat.reduceAdd]
  rw [toFun_eq_toFun', polarizedProd_toFun'_apply]
  simp only [Fin.isValue, map_add, prodRight_tmul, tmul_zero, Prod.mk_add_mk, add_zero, zero_add]
  rw [← toFun_eq_toFun', toFun_add_tmul_eq_coeff_sum]
  simp only [finTwoArrowEquiv_symm_apply, Fin.isValue]
  rw [Finsupp.sum]
  simp only [Fin.isValue, map_sum, LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars,
    MvPolynomial.lcoeff_apply]
  have h2' (e : Fin 2 →₀ ℕ) : X (R := R) 0 ^ e 0 * X 1 ^ e 1 = ∏ (i : Fin 2), X i ^ e i := by
    simp [Fin.isValue, Fin.prod_univ_two]
  simp_rw [h2', prod_X_pow_eq_monomial', coeff_monomial]
  simp only [ite_tmul, Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  intro h0
  rw [h0, tmul_zero]

lemma dividedDifferential_eq_coeff (n : ℕ) (m m' : M) :
    f.dividedDifferential n (m, m') =
      Polynomial.scalarRTensor R N (f.toFun' (Polynomial R)
          ((1 : Polynomial R) ⊗ₜ[R] m + Polynomial.X (R := R) ⊗ₜ[R] m')) n := by
  have hf : LocFinsupp fun p ↦ f.polarizedProd.biComponent (p, n) :=
    locFinsupp_polarizedProd_biComponent n f
  simp only [dividedDifferential, LinearMap.coe_mk, AddHom.coe_mk, ground_apply]
  simp only [Polynomial.scalarRTensor_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [lfsum_toFun'_eq_of_locFinsupp hf]
  simp only [Finsupp.sum]
  conv_rhs => {
    simp only [← toFun_eq_toFun']
    rw [toFun_add_tmul_eq_coeff_sum]
    rw [map_finsuppSum]
    simp only [Finsupp.sum, finTwoArrowEquiv_symm_apply, Fin.isValue, one_pow, one_mul,
    LinearMap.rTensor_tmul, Polynomial.lcoeff_apply, Polynomial.coeff_X_pow]
    simp only [Fin.isValue, ite_tmul] }
  rw [Finset.sum_ite]
  simp only [Fin.isValue, Finset.sum_const_zero, add_zero]
  set V := (Finsupp.ofSupportFinite (fun i ↦ (f.polarizedProd.biComponent
    (i, n)).toFun' R (1 ⊗ₜ[R] (m, m'))) (hf _ _)).support with hV
  have : ∑ x ∈ ((coeff ![m, m']) f).support with n = x 1, (1 : R) ⊗ₜ[R] ((coeff ![m, m']) f) x =
      ∑ a ∈ V, 1 ⊗ₜ[R] ((coeff ![m, m']) f) ((finTwoArrowEquiv' ℕ).symm (a, n)) := by
    refine (Finset.sum_bij (fun x _ ↦ x 0) (fun a ↦ ?_) ?_ ?_ ?_)
    · intro ha
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finset.mem_filter,
        Finsupp.mem_support_iff, ne_eq] at ha
      simp only [hV, biComponent_apply_toFun', Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, ne_eq]
      rw [biCoeffBaseChange_polarizedProd, ha.2]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, finTwoArrowEquiv', Fin.isValue,
        Equiv.symm_trans_apply, finTwoArrowEquiv_symm_apply]
      intro ha'
      have h0 : (0 : R ⊗[R] N) = 1 ⊗ₜ 0 := by simp
      rw [h0] at ha'
      rw [← (TensorProduct.lid R N).injective.eq_iff] at ha'
      simp only [Fin.isValue, lid_tmul, _root_.one_smul, tmul_zero, map_zero] at ha'
      apply ha.1
      simpa using ha'
    · intro a ha b hb h
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue] at h
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finset.mem_filter,
        Finsupp.mem_support_iff, ne_eq] at ha hb
      refine Finsupp.ext ?_
      simp [Fin.forall_fin_two, h, ← ha.2, ← hb.2]
    · intro a ha
      simp only [hV, biComponent_apply_toFun', Finsupp.mem_support_iff, ne_eq,
        Finsupp.ofSupportFinite_coe] at ha
      use (finTwoArrowEquiv' ℕ).symm (a, n)
      constructor
      · simp [finTwoArrowEquiv']
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, finTwoArrowEquiv',
        Equiv.symm_trans_apply, finTwoArrowEquiv_symm_apply, Finset.mem_filter,
        Finsupp.mem_support_iff, ne_eq, Finsupp.equivFunOnFinite_symm_apply_toFun,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, and_true]
        by_contra ha'
        apply ha
        simp [biCoeffBaseChange_polarizedProd, finTwoArrowEquiv', ha']
    · intro x hx
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finset.mem_filter,
        Finsupp.mem_support_iff, ne_eq] at hx
      simp [Nat.succ_eq_add_one, Nat.reduceAdd, finTwoArrowEquiv', Fin.isValue, hx.2]
  rw [this]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finsupp.ofSupportFinite_coe, biComponent.toFun'_apply, biCoeffBaseChange_polarizedProd]

-- Roby63, pg 239
lemma dividedDifferential_map_add_snd (m m₁ m₂ : M) :
    f.dividedDifferential 1 (m, m₁ + m₂) = f.dividedDifferential 1 (m, m₁) +
      f.dividedDifferential 1 (m, m₂) := by
  classical
  simp only [dividedDifferential_eq_coeff]
  simp only [← toFun_eq_toFun', toFun_add_tmul_eq_coeff_sum, finTwoArrowEquiv_symm_apply,
    Fin.isValue, one_pow, one_mul, Polynomial.scalarRTensor_apply, ← map_add,
    EmbeddingLike.apply_eq_iff_eq]
  simp only [Finsupp.sum, Fin.isValue, map_sum, LinearMap.rTensor_tmul, Polynomial.lcoeff_apply,
    Polynomial.coeff_X_pow, map_add]
  simp only [Fin.isValue, ite_tmul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have (x : Fin 2 →₀ ℕ) (hx : x 1 = 1) : x ∈ ((coeff ![m, m₁ + m₂]) f).support := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finsupp.mem_support_iff, ne_eq]
    simp only [coeff_eq, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, EmbeddingLike.map_eq_zero_iff, ne_eq]
    sorry
  sorry

open LinearMap

-- Roby63, pg 239 (?)
lemma dividedDifferential_map_add_snd_toFun' {S : Type u} [CommSemiring S] [Algebra R S]
    (m m₁ m₂ : S ⊗[R] M) :
    (f.dividedDifferential 1).toFun' S
      ((inl R M M).toPolynomialLaw.toFun' S m + (inr R M M).toPolynomialLaw.toFun' S (m₁ + m₂)) =
      (f.dividedDifferential 1).toFun' S
        ((inl R M M).toPolynomialLaw.toFun' S m + (inr R M M).toPolynomialLaw.toFun' S m₁) +
      (f.dividedDifferential 1).toFun' S
        ((inl R M M).toPolynomialLaw.toFun' S m + (inr R M M).toPolynomialLaw.toFun' S m₂) := by
  sorry

-- Roby63, pg 239 (?)
lemma dividedDifferential_map_add_snd_toFun {S : Type*} [CommSemiring S] [Algebra R S]
    (m m₁ m₂ : S ⊗[R] M) :
    (f.dividedDifferential 1).toFun S
      ((inl R M M).toPolynomialLaw.toFun S m + (inr R M M).toPolynomialLaw.toFun S (m₁ + m₂)) =
      (f.dividedDifferential 1).toFun S
        ((inl R M M).toPolynomialLaw.toFun S m + (inr R M M).toPolynomialLaw.toFun S m₁) +
      (f.dividedDifferential 1).toFun S
        ((inl R M M).toPolynomialLaw.toFun S m + (inr R M M).toPolynomialLaw.toFun S m₂) := by
  sorry

-- Roby63, pg 239
lemma dividedDifferential_smul_right (r : R) (m m' : M) :
    f.dividedDifferential 1 (m, r • m') = r • f.dividedDifferential 1 (m, m') := by
  sorry

-- Roby63, pg 239 (?)
lemma dividedDifferential_map_smul_snd_toFun' {S : Type u} [CommSemiring S] [Algebra R S] (r : R)
    (m m' : S ⊗[R] M) :
    (f.dividedDifferential 1).toFun' S ((inl R M M ).toPolynomialLaw.toFun' S m +
      (inr R M M ).toPolynomialLaw.toFun' S (r • m')) =
      r • (f.dividedDifferential 1).toFun' S
        ((inl R M M ).toPolynomialLaw.toFun' S m + (inr R M M ).toPolynomialLaw.toFun' S m') := by
  sorry

-- Roby63, pg 239 (?)
lemma dividedDifferential_map_smul_snd_toFun {S : Type*} [CommSemiring S] [Algebra R S] (r : R)
    (m m' : S ⊗[R] M) :
    (f.dividedDifferential 1).toFun S ((inl R M M).toPolynomialLaw.toFun S m +
      (inr R M M).toPolynomialLaw.toFun S (r • m')) =
        r • (f.dividedDifferential 1).toFun S
          ((inl R M M).toPolynomialLaw.toFun S m + (inr R M M).toPolynomialLaw.toFun S m') := by
  sorry

variable {f n p}

-- Roby63, pg 239
lemma dividedDifferential_eq_biComponent_of_le (hf : IsHomogeneous p f) (hnp : n ≤ p) :
    (f.dividedDifferential n) = (polarizedProd f).biComponent (p - n, n) := by
  simp only [dividedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
  ext S _ _ sm
  rw [lfsum_toFun'_eq_of_locFinsupp (locFinsupp_polarizedProd_biComponent _ _)]
  simp only [Finsupp.sum, Finsupp.ofSupportFinite_coe]
  rw [Finset.sum_eq_single (p - n)]
  · sorry
  · exact fun hp ↦ by simpa [Finsupp.ofSupportFinite_coe] using hp

-- Roby63, pg 239
lemma dividedDifferential_eq_zero_of_gt (hf : IsHomogeneous p f) (hnp : p < n) :
    (f.dividedDifferential n) = 0 := by
  have hk (k : ℕ) : polarizedProd_biComponent (k, n) f = 0 := by
    have hf' := isHomogeneous_polarizedProd hf
    ext S _ _ sm
    sorry
  simp only [dividedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
  ext S _ _ sm
  rw [lfsum_toFun'_eq_of_locFinsupp (locFinsupp_polarizedProd_biComponent _ _)]
  simp [Finsupp.sum, zero_def, hk, Finsupp.ofSupportFinite_coe, Finset.sum_const_zero]

lemma polarizedProd_id_eq : id.polarizedProd = (fst R M M + snd R M M).toPolynomialLaw := by
  ext S _ _ sm
  simp only [polarizedProd_toFun'_apply, id_apply']
  simp only [id_eq, toPolynomialLaw_toFun', baseChange_add, add_apply]
  rw [baseChange_snd_eq_prodRight_snd, baseChange_fst_eq_prodRight_fst]

lemma fst_biComponent_eq_zero (p : ℕ) : (fst R M M).toPolynomialLaw.biComponent (p, 1) = 0 := by
  ext S _ _ sm
  simp only [biComponent, zero_def, Pi.zero_apply, biCoeffBaseChange_apply, Fin.isValue, map_add,
    rTensor_apply, toFun_eq_toFun', LinearMap.coe_mk, AddHom.coe_mk, fst_toFun'_apply, Prod.fst_add]
  convert add_zero _
  · induction sm using TensorProduct.induction_on with
    | zero => simp only [Fin.isValue, map_zero, tmul_zero, Prod.fst_zero]
    | tmul s m =>
      simp only [Fin.isValue, compSndRight_tmul, inrRight_tmul, assoc_symm_tmul,
        LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, prodRight_tmul, tmul_zero, map_zero]
    | add sm sm' hsm hsm' =>
      simp only [Fin.isValue, map_add, tmul_add, Prod.fst_add, hsm, hsm', add_zero]
  · induction sm using TensorProduct.induction_on with
    | zero => simp only [Fin.isValue, map_zero, tmul_zero, Prod.fst_zero]
    | tmul s m =>
      have h0 : MvPolynomial.coeff ((finTwoArrowEquiv' ℕ).symm (p, 1))
          (scalarRTensorAlgEquiv (X 0 ⊗ₜ[R] s)) = 0 := by
        simp only [scalarRTensorAlgEquiv, Fin.isValue, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
          mapAlgEquiv_apply, coeff_map, coeff_rTensorAlgHom_tmul, coeff_X', RingHom.coe_coe,
          Algebra.TensorProduct.lid_tmul, ite_smul, _root_.one_smul, _root_.zero_smul]
        rw [if_neg]
        simp [Finsupp.ext_iff, finTwoArrowEquiv',]
      simp only [Fin.isValue, compFstRight_tmul, inlRight_tmul, assoc_symm_tmul,
        LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, prodRight_tmul, tmul_zero,
        LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars, lcoeff_apply, h0, zero_tmul]
    | add sm sm' hsm hsm' =>
      simp only [← hsm, ← hsm', Fin.isValue, map_add, tmul_add, Prod.fst_add, zero_add]

lemma biCoeffBaseChange_snd_eq_zero_of_ne {S : Type*} [CommSemiring S] [Algebra R S]
    (sm : S ⊗[R] (M × M)) {n : ℕ × ℕ} (hn : n.2 ≠ 1) :
    biCoeffBaseChange (snd R M M).toPolynomialLaw sm n = 0 := by
  induction sm using TensorProduct.induction_on with
  | zero =>
    simp [biCoeffBaseChange_apply, snd_toFun_apply,finTwoArrowEquiv'_symm_apply, ]
  | tmul s m =>
    simp only [biCoeffBaseChange_apply_tmul, scalarRTensorAlgEquiv, AlgEquiv.toLinearEquiv_trans,
      Fin.isValue, map_add, assoc_symm_tmul, LinearEquiv.rTensor_tmul, LinearEquiv.trans_apply,
      AlgEquiv.toLinearEquiv_apply, rTensorAlgEquiv_apply, mapAlgEquiv_apply, snd_toFun_apply,
      prodRight_tmul, tmul_zero, Prod.mk_add_mk, add_zero, zero_add, finTwoArrowEquiv'_symm_apply,
      rTensor_apply, rTensor_tmul, coe_restrictScalars, lcoeff_apply, coeff_map,
      coeff_rTensorAlgHom_tmul, coeff_X', RingHom.coe_coe, Algebra.TensorProduct.lid_tmul, ite_smul,
      _root_.one_smul, _root_.zero_smul]
    rw [if_neg, zero_tmul]
    rw [Finsupp.ext_iff]
    simp [Fin.forall_fin_two, Finsupp.single_eq_same, (Ne.symm hn)]
  | add sm sm' hsm hsm' =>
    simp only [biCoeffBaseChange_apply, Fin.isValue, map_add, snd_toFun_apply, Prod.snd_add,
      finTwoArrowEquiv'_symm_apply, Finsupp.coe_add, Pi.add_apply, rTensor_apply,
      tmul_add] at hsm hsm' ⊢
    rw [add_add_add_comm, hsm, hsm', zero_add]

lemma dividedDifferential_id_eq :
    id.dividedDifferential 1 = (snd R M M).toPolynomialLaw := by
  ext S _ _ sm
  simp only [dividedDifferential, polarizedProd_biComponent, coe_mk, AddHom.coe_mk,
    polarizedProd_id_eq, map_add, fst_biComponent_eq_zero, zero_add]
  rw [← recompose_biComponent (snd R M M).toPolynomialLaw, lfsum_toFun'_eq_of_locFinsupp
    (LocFinsupp_biComponent (snd R M M).toPolynomialLaw), lfsum_toFun'_eq_of_locFinsupp]
  · simp only [Finsupp.sum, biComponent_apply_toFun', Finsupp.ofSupportFinite_coe]
    apply Finset.sum_of_injOn (fun p ↦ (p, 1))
    · simp only [Prod.mk.injEq, and_true, implies_true, Set.injOn_of_eq_iff_eq]
    · simp only [Set.MapsTo, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
      intro p hp
      simpa [recompose_biComponent, Finsupp.ofSupportFinite_coe] using hp
    · intro n hn hn'
      simp only [Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, ne_eq, Set.mem_image,
        Finset.mem_coe, not_exists, not_and] at hn hn'
      simp_rw [recompose_biComponent] at hn'
      by_cases hn1 : n.2 = 1
      · rw [← hn1] at hn'
        exact absurd rfl (hn' n.1 hn)
      · exact biCoeffBaseChange_snd_eq_zero_of_ne sm hn1
    · intro p hp
      rw [recompose_biComponent]
    · intro T _ _ tm
      set U := (Function.support fun i ↦
        ((fun n ↦ (snd R M M).toPolynomialLaw.biComponent n) i).toFun' T tm) with hU_def
      suffices hU : Finite U by
        apply Set.Finite.of_injOn (f := fun p ↦ (p, 1)) ?_ ?_ hU
        · simp only [Set.MapsTo, biComponent_apply_toFun', Function.mem_support, ne_eq]
          intro p hp
          simpa [hU_def, biComponent_apply_toFun', Function.mem_support, ne_eq,
            recompose_biComponent] using hp
        apply Function.Injective.injOn
        exact Prod.mk_left_injective 1
      apply LocFinsupp_biComponent (snd R M M).toPolynomialLaw _

open TensorProduct

lemma locFinsupp_differential (f : M →ₚₗ[R] N) : LocFinsupp fun n ↦ f.dividedDifferential n := by
  simp only [LocFinsupp]
  intro S _ _ sm
  simp only [dividedDifferential, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [lfsum_toFun'_eq_of_locFinsupp (locFinsupp_polarizedProd_biComponent _ f)]
  have : (Function.support fun i ↦ (Finsupp.ofSupportFinite (fun i_1 ↦
    (polarizedProd_biComponent (i, i_1) f).toFun' S sm) (by sorry)).sum fun x m ↦
      m) = ?_ := by
    let g := (polarizedProd f)
    --let e := el_S''' (N := N) sm g
    -- Ideal: take the RHS to be the Set.range of the total degree of `e`, and show
    -- that LHS ⊆ RHS
    ext x
    simp only [biComponent_apply_toFun', Function.mem_support, ne_eq]
    sorry
  · sorry
  · sorry

private theorem sum_coeff_eq [DecidableEq N] (f : M →ₚₗ[R] N) (m m' : M) :
  ∑ x ∈ ((coeff fun x ↦ m + m') f).support, ((coeff fun (x : Unit) ↦ m + m') f) x =
    ∑ y ∈ ((coeff ![m, m']) f).support with
      ¬∑ x ∈ ((coeff ![m, m']) f).support with y 1 = x 1, ((coeff ![m, m']) f) x = 0,
      ((coeff ![m, m']) f) y  := by
  sorry

lemma map_add_eq_sum_differential_apply (m m' : M) :
    f (m + m') = lfsum (fun n ↦ f.dividedDifferential n) (m, m') := by
  classical
  rw [lfsum_ground_eq_of_locFinsupp (locFinsupp_differential f), Finsupp.sum]
  simp only [Finsupp.ofSupportFinite_coe, dividedDifferential_eq_coeff]
  simp only [ground_apply, ← toFun_eq_toFun', toFun_tmul_eq_coeff_sum, PUnit.zero_eq, one_pow,
    toFun_add_tmul_eq_coeff_sum, finTwoArrowEquiv_symm_apply, Fin.isValue, one_mul, map_finsuppSum,
    lid_tmul, _root_.one_smul, Fin.isValue, Finsupp.sum_apply]
  simp only [Finsupp.sum, Fin.isValue]
  rw [Finset.sum_comm]
  simp only [Polynomial.scalarRTensor_apply, LinearMap.rTensor_tmul, Polynomial.lcoeff_apply,
    Polynomial.coeff_X_pow, lid_tmul, ite_smul, _root_.one_smul, _root_.zero_smul,
    Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, ite_not, zero_add, Finsupp.ofSupportFinite_coe]
  exact sum_coeff_eq f m m'

-- Section II.5

variable (R N) in
/-- The nth divided partial derivative of `f` at `x`. -/
def dividedPartialDerivative (n : ℕ) (x : M) : (M →ₚₗ[R] N) →ₗ[R] (M →ₚₗ[R] N) where
  toFun f := (f.dividedDifferential n).comp
    ((inl R M M).toPolynomialLaw + (inr R M M).toPolynomialLaw.comp (const R M M x))
  map_add' f g := by
    ext S _ _ sm
    simp [map_add, comp_toFun', add_def, Function.comp_apply, Pi.add_apply]
  map_smul' r f := by
    ext S _ _ sm
    simp [map_smul, comp_toFun', smul_def, add_def, Function.comp_apply, Pi.add_apply,
      Pi.smul_apply, RingHom.id_apply]

-- TODO: correct RHS (check)
lemma dividedDifferential_toFun_eq_coeff {S : Type*} [CommSemiring S] [Algebra R S] (n : ℕ)
    (m m' : S ⊗[R] M) :
    (f.dividedDifferential n).toFun S
      ((inl R M M).toPolynomialLaw.toFun S m + (inr R M M).toPolynomialLaw.toFun S m') =
    Polynomial.rTensor _ _ _ (f.toFun _ ((LinearEquiv.rTensor (R := R) M
      (Polynomial.scalarRTensorAlgEquiv _ _).toLinearEquiv)
        (((TensorProduct.assoc R (Polynomial R) S M).symm ((1 : Polynomial R) ⊗ₜ m)) +
          ((TensorProduct.assoc R (Polynomial R) S M).symm
            ((Polynomial.X : Polynomial R) ⊗ₜ m'))))) n := by
  sorry

-- pg 239
lemma dividedPartialDerivative_eq_coeff {S : Type*} [CommSemiring S] [Algebra R S] (x : M)
    (sm : S ⊗[R] M) : (dividedPartialDerivative R N n x f).toFun S sm =
    Polynomial.rTensor _ _ _ (f.toFun _ ((LinearEquiv.rTensor (R := R) M
      (Polynomial.scalarRTensorAlgEquiv _ _).toLinearEquiv)
        (((TensorProduct.assoc R (Polynomial R) S M).symm ((1 : Polynomial R) ⊗ₜ sm))) +
          (Polynomial.X ⊗ₜ[R] x))) n := by
  have : (Polynomial.scalarRTensorAlgEquiv R S) (Polynomial.X ⊗ₜ[R] 1) ⊗ₜ[R] x =
      (Polynomial.X) ⊗ₜ[R] x  := by
    simp only [Polynomial.scalarRTensorAlgEquiv, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv]
    simp only [Polynomial.rTensorAlgEquiv, AlgEquiv.ofLinearEquiv_apply]
    congr
    ext d
    rw [Polynomial.coeff_map, Polynomial.rTensorLinearEquiv_coeff_tmul]
    simp only [RingHom.coe_coe, Algebra.TensorProduct.lid_tmul]
    simp [Polynomial.coeff_X, ite_smul, _root_.one_smul, _root_.zero_smul]
  simp only [dividedPartialDerivative, LinearMap.coe_mk, AddHom.coe_mk, comp_toFun,
    Function.comp_apply]
  simp only [add_toFun, comp_toFun, Pi.add_apply, Function.comp_apply, const_toFun]
  rw [dividedDifferential_toFun_eq_coeff]
  simp only [assoc_symm_tmul, map_add, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, this]

-- Roby63, pg 240
lemma dividedPartialDerivative_isHomogeneous_of_le [Nontrivial R]
    (hf : IsHomogeneous p f) (hnp : n ≤ p) (x : M) :
    (dividedPartialDerivative R N n x f).IsHomogeneous (p - n) := by
  sorry

-- Roby63, pg 240
lemma dividedPartialDerivative_eq_zero_of_gt (hf : IsHomogeneous p f) (hnp : p < n) (x : M) :
    dividedPartialDerivative R N n x f = 0 := by
  ext S _ _ sm
  simp only [dividedPartialDerivative, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dividedDifferential_eq_zero_of_gt hf hnp]
  simp [comp_toFun']

-- Roby63, pg 240 (Prop. II.2)
lemma taylor_sum (m x : M) :
    f (m + x) = lfsum (fun (n : ℕ) ↦ dividedPartialDerivative R N n x f) m := by
  rw [map_add_eq_sum_differential_apply]
  simp only [ground_apply, dividedPartialDerivative, LinearMap.coe_mk, AddHom.coe_mk,
    EmbeddingLike.apply_eq_iff_eq]
  rw [lfsum_toFun'_eq_of_locFinsupp (locFinsupp_differential f), lfsum_toFun'_eq_of_locFinsupp
    (fun S _ _ sm ↦ locFinsupp_differential f S ((prodRight R S S M M).symm (sm, (1 : S) ⊗ₜ x)))]
  simp only [Finsupp.sum, Finsupp.ofSupportFinite_coe]
  apply Finset.sum_congr
  · ext n
    simp only [Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, ne_eq]
    simp [← toFun_eq_toFun', comp_toFun, Function.comp_apply, add_toFun, const_toFun,
      inl_toFun_apply, inr_toFun_apply, inlRight_tmul, inrRight_tmul, ← tmul_add]
  · intro n hn
    simp [← toFun_eq_toFun', comp_toFun, Function.comp_apply, add_toFun, const_toFun,
      inl_toFun_apply, inr_toFun_apply, inlRight_tmul, inrRight_tmul, ← tmul_add]

-- Roby63, pg 240 (Prop. II.2)
lemma dividedPartialDerivative_comp (x : M) :
    dividedPartialDerivative R N n x (dividedPartialDerivative R N p x f) =
      (n.choose p) • dividedPartialDerivative R N (n + p) x f := by
  sorry

-- Section II.6

-- Roby63, pg 240 (Prop. II.3)
lemma dividedDifferential_toFun_eq_lfsum {S : Type*} [CommSemiring S] [Algebra R S]
    (sm sm' : S ⊗[R] M) {k : ℕ} {s : Fin k → S} {x : Fin k → M} (hsm' : sm' = ∑ i, (s i) ⊗ₜ (x i)) :
    (dividedDifferential 1 f).toFun S ((prodRight R S S M M).symm (sm, sm')) =
      ∑ i, (s i) • (dividedPartialDerivative R N 1 (x i) f).toFun S sm := by
  sorry

-- Section II.7

-- Roby63, pg 241 (Prop. II.4 for n = 2)
-- Generalized as in remark after Prop. II.5
lemma dividedPartialDerivative_comp_eq_coeff {S : Type*} [CommSemiring S] [Algebra R S] (k₁ k₂ : ℕ)
    (x₁ x₂ : M) (sm : S ⊗[R] M) :
    (dividedPartialDerivative R N k₁ x₁ (dividedPartialDerivative R N k₂ x₂ f)).toFun S sm =
      MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
        ((LinearEquiv.rTensor  (R := R) M scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S M).symm
            ((1 ⊗ₜ[R] sm) + (X (R := R) (0 : Fin 2) ⊗ₜ[R] ((1 : S) ⊗ₜ x₁)) +
              X (1 : Fin 2) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] x₂))))) ((finTwoArrowEquiv' ℕ).symm (k₁, k₂)) := by
  sorry

example (F : Fin n → (M →ₚₗ[R] N) →ₗ[R] M →ₚₗ[R] N) :
    List ((M →ₚₗ[R] N) →ₗ[R] M →ₚₗ[R] N) := by
  exact List.map F (List.finRange n)

-- Roby63, pg 241 (Prop. II.5)
-- Generalized as in remark after Prop. II.5
lemma dividedPartialDerivative_comm {S : Type*} [CommSemiring S] [Algebra R S] (k₁ k₂ : ℕ)
    (x₁ x₂ : M) (sm : S ⊗[R] M) :
    (dividedPartialDerivative R N k₁ x₁ (dividedPartialDerivative R N k₂ x₂ f)).toFun S sm =
      (dividedPartialDerivative R N k₂ x₂ (dividedPartialDerivative R N k₁ x₁ f)).toFun S sm :=
  sorry

variable (R N) in
-- Roby63, pg 241 (Prop. II.5)
-- Generalized as in remark after Prop. II.5
lemma dividedPartialDerivativeCommute (k₁ k₂ : ℕ) (x₁ x₂ : M) :
    Commute (dividedPartialDerivative R N k₁ x₁) (dividedPartialDerivative R N k₂ x₂) := by
  sorry

-- Roby63, pg 241 (Prop. II.4 for general n)
lemma firstPartialDerivative_comp_multiple_eq_coeff {S : Type*} [CommSemiring S] [Algebra R S]
    {n : ℕ}
    (k : Fin n →₀ ℕ) (hk : ∀ i, k i = 1) (x : Fin n → M) (sm : S ⊗[R] M) :
    ((List.map (fun (i : Fin n) ↦ dividedPartialDerivative R N 1 (x i))
      (List.finRange n)).prod f).toFun S sm =
      MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin n) S)
        ((LinearEquiv.rTensor (R := R) M scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin n) R) S M).symm
            ((1 ⊗ₜ[R] sm) + ∑ (i : Fin n), (X (R := R) i) ⊗ₜ[R]  ((1 : S) ⊗ₜ[R] x i) )))) k := by
  induction n generalizing S sm with
  | zero =>
    simp only [List.finRange_zero, List.map_nil, List.prod_nil, Module.End.one_apply,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [MvPolynomial.rTensor_apply]
    simp only [Subsingleton.eq_zero k]
    let g := MvPolynomial.CAlgHom (R := R) (A := S) (σ := Fin 0)
    let h := (MvPolynomial.aeval (R := S) (S₁ := S) (σ := Fin 0) 0).restrictScalars R
    set j := (lcoeff S (σ := Fin 0) 0).restrictScalars R with hj_def
    have hj : j = h.toLinearMap := by
      ext p
      simp only [hj_def, LinearMap.coe_restrictScalars, lcoeff_apply, Matrix.zero_empty,
        AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', h]
      rw [show ![] = 0 by simp only [Matrix.zero_empty]]
      rw [aeval_zero]
      simp only [Algebra.algebraMap_self, constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, RingHom.id_apply]
    have hg := f.isCompat_apply g sm
    have hh := f.isCompat_apply h (LinearMap.rTensor M g sm)
    simp only [← LinearMap.rTensor_comp_apply] at hh
    have heq : h.toLinearMap ∘ₗ ↑g = LinearMap.id := by
      ext
      simp only [Matrix.zero_empty, LinearMap.coe_comp, LinearMap.coe_coe, Function.comp_apply,
        CAlgHom_apply, AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', algHom_C,
        Algebra.algebraMap_self, RingHom.id_apply, LinearMap.id_coe, id_eq, h, g]
    simp only [heq, LinearMap.rTensor_id, LinearMap.id_coe, id_eq] at hh
    rw [hj]
    rw [f.isCompat_apply]
    congr
    simp only [LinearEquiv.rTensor_apply, AlgEquiv.toLinearEquiv_toLinearMap]
    induction sm using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | add sm sm' hsm hsm' =>
      simp only [f.isCompat_apply, forall_const, ← LinearMap.rTensor_comp_apply,
        heq, LinearMap.rTensor_id, LinearMap.id_coe, id_eq, forall_const] at hsm hsm'
      simp only [tmul_add, map_add, ← LinearMap.rTensor_comp_apply, ← hsm, ← hsm']
    | tmul s m =>
      simp only [assoc_symm_tmul, LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply,
        AlgHom.toLinearMap_apply]
      simp only [Matrix.zero_empty, AlgHom.coe_restrictScalars', h]
      rw [show ![] = 0 by simp only [Matrix.zero_empty]]
      rw [aeval_zero]
      simp only [Algebra.algebraMap_self, constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, RingHom.id_apply]
      congr
      rw [coeff_scalarRTensorAlgEquiv]
      simp only [coeff_zero_one, _root_.one_smul]
  | succ n hn =>
    rw [List.finRange_succ, List.map_cons, List.prod_cons]
    set x' : Fin n → M := fun i ↦ x (Fin.succ i)
    have : (List.map (fun i ↦ dividedPartialDerivative R N 1 (x i))
        (List.map Fin.succ (List.finRange n))) =
          (List.map (fun i ↦ dividedPartialDerivative R N 1 (x' i)) (List.finRange n)) := by
      simp [x']
    sorry

lemma firstPartialDerivative_comp_multiple_eq_coeff' {ι S : Type*} [CommSemiring S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] {L : List ι} (hL : L.Nodup)
    (k : ι →₀ ℕ) (hk : ∀ i, k i = 1) (x : ι → M) (sm : S ⊗[R] M) :
    ((List.map (fun i ↦ dividedPartialDerivative R N 1 (x i)) L).prod f).toFun S sm =
      MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
        ((LinearEquiv.rTensor (R := R) M scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S M).symm
            ((1 ⊗ₜ[R] sm) +
            List.sum (List.map (fun i ↦ (X (R := R) i) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] x i)) L))))) k := by
  induction L generalizing S sm with
  | nil => sorry
  | cons i L hL' =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons, map_add,
      assoc_symm_tmul, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply]
    set sm' : (Polynomial S) ⊗[R] M :=
      LinearMap.rTensor M Polynomial.CAlgHom.toLinearMap sm + (Polynomial.X) ⊗ₜ[R] (x i)
    -- have := optionEquivRight
    sorry

-- Roby63, pg 241 (Prop. II.4 for general n)
lemma dividedPartialDerivative_comp_multiple_eq_coeff {S : Type*} [CommSemiring S] [Algebra R S]
    {n : ℕ} (k : Fin n →₀ ℕ) (x : Fin n → M) (sm : S ⊗[R] M) :
    ((List.map (fun (i : Fin n) ↦ dividedPartialDerivative R N (k i) (x i))
      (List.finRange n)).prod f).toFun S sm =
      MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin n) S)
        ((LinearEquiv.rTensor (R := R) M scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin n) R) S M).symm
            ((1 ⊗ₜ[R] sm) + ∑ (i : Fin n), (X (R := R) i) ⊗ₜ[R]  ((1 : S) ⊗ₜ[R] x i) )))) k := by
  sorry

-- Roby63, pg 241 (Prop. II.4 for general n)
lemma dividedPartialDerivative_comp_multiple_eq_coeff' {S : Type*} [CommSemiring S] [Algebra R S]
    {n : ℕ} (k : Fin n →₀ ℕ) (x : Fin n → M) (sm : S ⊗[R] M) (f : M →ₚₗ[R] N) :
    (Finset.univ.noncommProd (fun i ↦ dividedPartialDerivative R N (k i) (x i))
    (fun a _ b _ _ ↦  dividedPartialDerivativeCommute R N (k a) (k b) (x a) (x b)) f).toFun S sm =
      MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin n) S)
        ((LinearEquiv.rTensor  (R := R) M scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin n) R) S M).symm
            ((1 ⊗ₜ[R] sm) + ∑ (i : Fin n), (X (R := R) i) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] x i) )))) k := by
  classical
  set g := fun (i : Fin n) ↦ dividedPartialDerivative (R := R) (N := N) (k i) (x i)
  set S := (Finset.univ.image g)
  let U := Finset.univ.noncommProd
    (fun i ↦ dividedPartialDerivative R N (k i) (x i))
    (fun a _ b _ _ ↦  dividedPartialDerivativeCommute R N (k a) (k b) (x a) (x b))
  sorry

-- Roby63, pg 242 (Partial derivative of constant polynomial law).
lemma dividedPartialDerivative_of_isHomogeneous_zero_eq_zero (hn : 0 < n) (x : M)
    (hf : IsHomogeneous 0 f) : dividedPartialDerivative R N n x f = 0 :=
  dividedPartialDerivative_eq_zero_of_gt hf hn x

-- Roby63, pg 242 (Partial derivative of constant polynomial law; 2nd version).
lemma dividedPartialDerivative_of_constant_eq_zero (hn : 0 < n) (x : M) (t : N) :
    dividedPartialDerivative R N n x (const R M N t) = 0 :=
  dividedPartialDerivative_of_isHomogeneous_zero_eq_zero hn x
    (const_isHomogeneous_zero t)

-- Roby63, pg 242 (Partial derivative of linear polynomial law).
lemma dividedPartialDerivative_of_linear_eq_constant (x : M) (hf : IsHomogeneous 1 f) :
    dividedPartialDerivative R N 1 x f = (const R M N (f x)) :=
  sorry

lemma dividedPartialDerivative_of_linear_apply (x m : M) (hf : IsHomogeneous 1 f) :
    dividedPartialDerivative R N 1 x f m = f x := by
  rw [dividedPartialDerivative_of_linear_eq_constant x hf]
  simp [ground, const_toFun']

-- Section II.8

variable (R M N) in
-- Roby63, pg 242 (Prop. II.6).
/-- The `R`-linear map sending `x : M` to `dividedPartialDerivative R N 1 x`. -/
def dividedPartialDerivativeHom : M →ₗ[R] ((M →ₚₗ[R] N) →ₗ[R] (M →ₚₗ[R] N)) where
  toFun x       := dividedPartialDerivative R N 1 x
  map_add' x y  := by
    ext f S _ _ sm
    simp only [dividedPartialDerivative, LinearMap.coe_mk, AddHom.coe_mk, comp_toFun', add_def,
      Function.comp_apply, Pi.add_apply, LinearMap.add_apply]
    rw [← dividedDifferential_map_add_snd_toFun']
    simp [const_toFun', tmul_add]
  map_smul' r x := by
    ext f S _ _ sm
    simp only [dividedPartialDerivative, LinearMap.coe_mk, AddHom.coe_mk, comp_toFun', add_def,
      Function.comp_apply, Pi.add_apply, RingHom.id_apply, LinearMap.smul_apply, smul_def,
      Pi.smul_apply]
    rw [← dividedDifferential_map_smul_snd_toFun']
    simp [const_toFun']

-- Roby63, pg 243 (Prop. II.7).
lemma dividedPartialDerivativeHom_ker_eq :
  LinearMap.ker (dividedPartialDerivativeHom R M N) =
    sSup {P : Submodule R M | ∀ l : M →ₗ[R] N, Submodule.map l P = 0} := sorry

-- Section II.9

-- Roby63, pg 243
lemma dividedPartialDerivative_prod_eq (f : (M × M') →ₚₗ[R] N) (x : M × M') :
    f.dividedPartialDerivative R N 1 x =
      f.dividedPartialDerivative R N 1 (x.1, 0) + f.dividedPartialDerivative R N 1 (0, x.2) := by
  ext S _ _ sm
  simp only [dividedPartialDerivative, LinearMap.coe_mk, AddHom.coe_mk, add_def, Pi.add_apply,
    comp_toFun', add_def, Function.comp_apply, const_toFun']
  have hx : (1 : S) ⊗ₜ[R] x = 1 ⊗ₜ[R] (x.1, 0) + 1 ⊗ₜ[R] (0, x.2) := by
    simp [← tmul_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
  rw [hx, dividedDifferential_map_add_snd_toFun']

-- Roby63, pg 244 (Prop II.8)
lemma dividedPartialDerivative_add (x y : M) :
    dividedPartialDerivative (R := R) (N := N) n (x + y) =
      ∑ i : Fin (n + 1), (dividedPartialDerivative (R := R) (N := N) i x).comp
        (dividedPartialDerivative (R := R) (N := N) (n - i) y) := by
  ext f S _ _ sm
  sorry

-- Roby63, pg 244 (Prop II.9 for n = 2)
lemma taylor_sum_prod (f : (M × M') →ₚₗ[R] N) (m x : M × M') :
    f (m + x) = lfsum (fun (n : ℕ × ℕ) ↦ dividedPartialDerivative R N n.1 (x.1, 0)
      (dividedPartialDerivative R N n.2 (0, x.2) f)) m := by
  sorry

-- Roby63, pg 244 (Prop. II.9 for n = 2)
lemma dividedPartialDerivative_fst_comp (f : (M × M') →ₚₗ[R] N) (x : M × M') :
    dividedPartialDerivative R N n (x.1, 0) (dividedPartialDerivative R N p (x.1, 0) f) =
      (n.choose p) • dividedPartialDerivative R N (n + p) (x.1, 0) f := by
  sorry

-- Roby63, pg 244 (Prop. II.9 for n = 2)
lemma dividedPartialDerivative_snd_comp (f : (M × M') →ₚₗ[R] N) (x : M × M') :
    dividedPartialDerivative R N n (0, x.2) (dividedPartialDerivative R N p (0, x.2) f) =
      (n.choose p) • dividedPartialDerivative R N (n + p) (0, x.2) f := by
  sorry

theorem lfsum_dividedPartialDerivative (x : M) (f : M →ₚₗ[R] N) :
    lfsum (fun k ↦ f.dividedPartialDerivative R N k x) = f.translation x :=
  sorry

-- Roby63, pg 244 (Taylor formula, Prop II.9 for general n)
lemma taylor_sum_pi {M : Fin n → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (f : (Π i, M i) →ₚₗ[R] N) (m x : Π i, M i) :
    f (m + x) = lfsum (fun (k : Fin n →₀ ℕ) ↦ ((List.map (fun (i : Fin n) ↦
      dividedPartialDerivative R N (k i) (Pi.single i (x i)))
        (List.finRange n).reverse)).prod f) m := by
  sorry

-- Roby63, pg 244 (Prop. II.9 for general n)
lemma dividedPartialDerivative_comp_single {M : Fin n → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (f : (Π i, M i) →ₚₗ[R] N) (x : Π i, M i) (i : Fin n) :
    dividedPartialDerivative R N n (Pi.single i (x i))
      (dividedPartialDerivative R N p (Pi.single i (x i)) f) =
        (n.choose p) • dividedPartialDerivative R N (n + p) (Pi.single i (x i)) f := by
  sorry

end PolynomialLaw
