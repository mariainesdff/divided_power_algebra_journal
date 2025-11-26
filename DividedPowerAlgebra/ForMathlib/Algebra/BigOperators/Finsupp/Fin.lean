/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.BigOperators.Finsupp.Fin

lemma finTwoArrowEquiv'_symm_apply' (X : Type*) [Zero X] :
    ⇑(finTwoArrowEquiv' X).symm = fun x ↦ Finsupp.ofSupportFinite ![x.1, x.2] (Set.toFinite _) := by
  ext
  simp [finTwoArrowEquiv'_symm_apply, Finsupp.equivFunOnFinite_symm_apply_toFun,
    Finsupp.ofSupportFinite_coe]

@[simp]
theorem Finsupp.equivFunOnFinite.symm_apply_two {α : Type*} [Zero α] (n : Fin 2 →₀ α) :
    Finsupp.equivFunOnFinite.symm ![n 0, n 1] = n := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩
