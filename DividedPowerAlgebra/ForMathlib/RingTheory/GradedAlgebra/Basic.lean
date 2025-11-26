/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Miscellaneous results about `GradedAlgebra` -/

noncomputable section

open Finset MvPolynomial DirectSum

section

theorem Finsupp.prod_mem_grade {κ A R : Type*} [AddCommMonoid κ] [DecidableEq κ] [CommSemiring A]
    [CommSemiring R] [Algebra R A] {𝒜 : κ → Submodule R A} [GradedAlgebra 𝒜] {σ : Type*}
    {c : σ →₀ ℕ} {f : σ → A} {d : σ → κ} (hc : ∀ s ∈ c.support, f s ∈ 𝒜 (d s)) :
    (c.prod fun s e => f s ^ e) ∈ 𝒜 (c.sum fun s e => e • d s) := by
  classical
  rw [Finsupp.prod, Finsupp.sum]
  suffices ∀ s (hs : s ⊆ c.support), ∏ a ∈ s, f a ^ c a ∈ 𝒜 (∑ a ∈ s, c a • d a) by
    exact this c.support (subset_refl _)
  intro s hs
  induction s using Finset.induction_on with
  | empty => exact (SetLike.one_mem_graded 𝒜)
  | insert a t ha ht =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    apply SetLike.mul_mem_graded
    · apply SetLike.pow_mem_graded _ (hc _ (hs (mem_insert_self a t)))
    · apply ht (subset_trans (subset_insert a t) hs)

end

namespace GradedAlgebra

section CommSemiring

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]

section AddCommMonoid

variable {ι : Type*} [AddCommMonoid ι] (𝒜 : ι → Submodule R A)

namespace GradeZero

theorem coe_smul (r : R) (x : 𝒜 0) : (↑(r • x) : A) = r • x := rfl

@[simp] theorem coe_zero : (↑(0 : 𝒜 0) : A) = 0 := rfl

variable [DecidableEq ι] [GradedAlgebra 𝒜]

instance : One (𝒜 0) where
  one : 𝒜 0 := ⟨1, SetLike.one_mem_graded 𝒜⟩

instance : Mul (𝒜 0) where
  mul := fun x y => ⟨x * y, by
    convert SetLike.mul_mem_graded x.2 y.2
    rw [add_zero]⟩

@[simp] theorem coe_mul (x y : 𝒜 0) : (↑(x * y) : A) = x * y := rfl

@[simp] theorem val_mul (x y : 𝒜 0) : (x * y).val = x.val * y.val := rfl

@[simp] theorem coe_one : (↑(1 : 𝒜 0) : A) = 1 := rfl

theorem one_mem : (1 : A) ∈ 𝒜 0 := SetLike.one_mem_graded 𝒜

instance commSemiring : CommSemiring (𝒜 0) :=
  { (inferInstance : AddCommMonoid (𝒜 0)) with
    add  := (· + ·)
    zero := 0
    mul := (· * ·)
    one := 1
    natCast_zero := by simp only [Nat.cast_zero]
    natCast_succ := fun n ↦ by simp only [Nat.cast_succ] -- TODO: Zulip?
    zero_mul := fun x => by ext; rw [coe_mul, coe_zero, zero_mul]
    mul_zero := fun x => by ext; rw [coe_mul, coe_zero, mul_zero]
    mul_assoc := fun x y z => by ext; simp only [coe_mul, mul_assoc]
    one_mul := fun x => by ext; rw [coe_mul, coe_one, one_mul]
    mul_one := fun x => by ext; rw [coe_mul, coe_one, mul_one]
    left_distrib := fun x y z => by ext; simp only [Submodule.coe_add, coe_mul, left_distrib]
    right_distrib := fun x y z => by ext; simp only [Submodule.coe_add, coe_mul, right_distrib]
    mul_comm := fun x y => by ext; simp only [coe_mul, mul_comm] }

instance algebra : Algebra R (𝒜 0) :=
  Algebra.ofModule' (fun r x => by ext; simp [SetLike.val_smul, Algebra.smul_mul_assoc, one_mul])
    (fun r x => by ext; simp only [SetLike.val_smul, Algebra.mul_smul_comm, mul_one])

end GradeZero

variable [DecidableEq ι] [GradedAlgebra 𝒜]

/-- The projection from `A` to the degree `i` component `𝒜 i`, as an `R`-linear map. -/
def proj' (i : ι) : A →ₗ[R] 𝒜 i where
  toFun a       := decompose 𝒜 a i
  map_add' a b  := by simp only [decompose_add, add_apply]
  map_smul' r a := by simp only [decompose_smul, RingHom.id_apply]; rfl

end AddCommMonoid

variable {ι : Type*} [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  (𝒜 : ι → Submodule R A) [DecidableEq ι] [GradedAlgebra 𝒜]

/-- The projection from `A` to `𝒜 0`, as a `RingHom`. -/
@[simps]
def proj'_zeroRingHom : A →+* 𝒜 0 where
  toFun a := proj' 𝒜 0 a
  map_one' := by
    ext
    simp only [proj', LinearMap.coe_mk, AddHom.coe_mk,
     decompose_of_mem_same 𝒜 (GradeZero.one_mem 𝒜), GradeZero.coe_one]
  map_zero'    := by simp only [proj', decompose_zero, LinearMap.coe_mk, AddHom.coe_mk, zero_apply]
  map_add' _ _ := by simp only [proj', decompose_add, LinearMap.coe_mk, AddHom.coe_mk, add_apply]
  map_mul' x y := by
    ext
    simp only [proj', LinearMap.coe_mk, AddHom.coe_mk, GradeZero.coe_mul,
      ← GradedRing.projZeroRingHom_apply 𝒜, ← _root_.map_mul]

end CommSemiring

section CommRing

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid ι] [PartialOrder ι]
  [CanonicallyOrderedAdd ι] (𝒜 : ι → Submodule R A) [DecidableEq ι] [GradedAlgebra 𝒜]

namespace GradeZero

instance commRing : CommRing (𝒜 0) :=
{ (inferInstance : AddCommGroup (𝒜 0)) with
    add  := (· + ·)
    zero := 0
    mul  := (· * ·)
    one  := 1
    natCast_zero := by simp only [Nat.cast_zero]
    natCast_succ := fun n ↦ by simp only [Nat.cast_succ]
    intCast_ofNat := fun n ↦ by simp only [Int.cast_natCast]
    intCast_negSucc := fun n ↦ by rw [← Int.cast_negSucc]
    zero_mul := fun x => by ext; rw [coe_mul, coe_zero, zero_mul]
    mul_zero := fun x => by ext; rw [coe_mul, coe_zero, mul_zero]
    mul_assoc := fun x y z => by ext; simp only [coe_mul, mul_assoc]
    one_mul := fun x => by ext; rw [coe_mul, coe_one, one_mul]
    mul_one := fun x => by ext; rw [coe_mul, coe_one, mul_one]
    left_distrib := fun x y z => by ext; simp only [Submodule.coe_add, coe_mul, left_distrib]
    right_distrib := fun x y z => by ext; simp only [Submodule.coe_add, coe_mul, right_distrib]
    mul_comm := fun x y => by ext; simp only [coe_mul, mul_comm]
     }

end GradeZero

end CommRing

end GradedAlgebra

section GradedAlgebra

variable {R S : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]

/-- An `R`-algebra map `f` between graded algebras `A` and `B` is homogeneous if for every degree
  `i`, `f(𝒜 i) ⊆ ℬ (φ i)`, where `φ : ι → κ` is some provided map. -/
def GAlgHom.IsHomogeneous {ι κ : Type*} {A : Type*} [CommSemiring A] [Algebra R A]
    (𝒜 : ι → Submodule R A) {B : Type*} [CommSemiring B] [Algebra R B] [Algebra S B]
    (ℬ : κ → Submodule S B) (φ : ι → κ) (f : A →ₐ[R] B) : Prop :=
  ∀ i a, a ∈ 𝒜 i → f a ∈ ℬ (φ i)

/-- The evaluation of a weighted homogeneous polynomial at
  elements of adequate grades is homogeneous -/
theorem GAlgHom.IsHomogeneous_aeval {σ : Type*} {ι κ : Type*} [AddCommMonoid ι] [AddCommMonoid κ]
    [DecidableEq κ] (A : Type*) [CommSemiring A] [Algebra R A] (𝒜 : κ → Submodule R A)
    [GradedAlgebra 𝒜] {w : σ → ι} (φ : ι →+ κ) (f : σ → A) (h : ∀ s : σ, f s ∈ 𝒜 (φ (w s))) :
    GAlgHom.IsHomogeneous (weightedHomogeneousSubmodule R w) 𝒜 φ (MvPolynomial.aeval f) := by
  intro i p hp
  simp only [mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous] at hp
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro c hc
  rw [aeval_monomial, ← smul_eq_mul, algebraMap_smul]
  apply Submodule.smul_mem
  convert Finsupp.prod_mem_grade fun s _ => h s
  rw [← hp (mem_support_iff.mp hc), Finsupp.weight_apply,
    Finsupp.sum, map_sum, Finsupp.sum_of_support_subset _ subset_rfl]
  · exact Finset.sum_congr rfl (fun _ _ ↦ map_nsmul _ _ _ )
  · exact fun _ _ ↦ zero_smul _ _

end GradedAlgebra
