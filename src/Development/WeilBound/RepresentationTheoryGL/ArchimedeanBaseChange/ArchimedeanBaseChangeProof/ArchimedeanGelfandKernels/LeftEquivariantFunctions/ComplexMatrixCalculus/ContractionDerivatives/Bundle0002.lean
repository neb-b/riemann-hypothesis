module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.DerTop
section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.CxbDer

open PositivityTheory.RgBcC

variable {n : ℕ}

def Gpi (g : X n) : Finset (Md n) → Finset (Md n) → ℂ := fun B' A => F (fb n A) g B'

theorem gamM_fun : (fun g : X n => (gamM (n := n) (Matrix.of g) : Finset (Md n) → Finset (Md n) → ℂ)) = Gpi := by
  funext g B' A
  simp only [gamM, matL, Gpi, F, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, Module.Basis.equivFun_apply]

theorem Gpi_contDiff : ContDiff ℂ ∞ (Gpi (n := n)) :=
  contDiff_pi.2 fun B' => contDiff_pi.2 fun A => contDiff_pi.1 (key (fb n A)).1 B'

def Lpi (n : ℕ) : X n →L[ℂ] (Finset (Md n) → Finset (Md n) → ℂ) :=
  ContinuousLinearMap.pi fun B' => ContinuousLinearMap.pi fun A =>
    (ContinuousLinearMap.proj B').comp (Classical.choose (key (n := n) (fb n A)).2)

theorem Gpi_hasFDerivAt : HasFDerivAt (Gpi (n := n)) (Lpi n) (one' n) := by
  refine hasFDerivAt_pi.2 fun B' => ?_
  refine hasFDerivAt_pi.2 fun A => ?_
  have h := (Classical.choose_spec (key (n := n) (fb n A)).2).1
  exact (hasFDerivAt_pi'.1 h) B'

theorem Lpi_apply (B : X n) (B' A : Finset (Md n)) :
    Lpi n B B' A = (fb n).equivFun (Dop B (fb n A)) B' := by
  simp only [Lpi, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [(Classical.choose_spec (key (n := n) (fb n A)).2).2 B]

theorem matL_Dop (B : X n) : (matL n (Dop B) : Finset (Md n) → Finset (Md n) → ℂ) =
    fun B' A => (fb n).equivFun (Dop B (fb n A)) B' := by
  funext B' A
  simp only [matL, LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]

theorem matL_Ers (r s : Md n) : matL n (Ers r s) = creL n (Pi.single r 1) * annL n (Pi.single s 1) := by
  simp only [Ers, matL, creL, annL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_mk,
    AddHom.coe_mk]
  exact LinearMap.toMatrix_mul _ _ _

theorem matL_Dop_sum (B : X n) : matL n (Dop B) = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dop, map_sum, map_smul, matL_Ers]

end PositivityTheory.RgBcC.CxbDer

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.CxbDer

section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Lpi_eq {n : ℕ} (B : Matrix (Md n) (Md n) ℂ) :
    (Lpi n B : Finset (Md n) → Finset (Md n) → ℂ) = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  exact (funext fun B' => funext fun A => Lpi_apply B B' A).trans ((matL_Dop B).symm.trans (matL_Dop_sum B))

theorem gamM_hasFDerivAt (n : ℕ) : ∃ L : type_of% (fderiv ℂ (gamM (n := n)) 1), HasFDerivAt (gamM (n := n)) L 1 ∧
    ∀ B : Matrix (Md n) (Md n) ℂ, L B = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  refine ⟨Lpi n, ?_, Lpi_eq⟩
  have h := Gpi_hasFDerivAt (n := n)
  rw [← gamM_fun] at h
  have h1 : (1 : Matrix (Md n) (Md n) ℂ) = one' n := by
    ext i j
    simp [one', Matrix.one_apply]
  rw [h1]
  exact h

theorem gamM_contDiff (n : ℕ) : ContDiff ℂ ∞ (gamM (n := n)) := by
  have h := Gpi_contDiff (n := n)
  rw [← gamM_fun] at h
  exact h

theorem gamDer : GamDer := by
  intro n
  obtain ⟨L, hL, hv⟩ := gamM_hasFDerivAt n
  refine ⟨gamM_contDiff n, fun B => ?_⟩
  rw [hL.fderiv, hv B]

end

end PositivityTheory.RgBcC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ToLinSmulOne
section
noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxb

open PositivityTheory.RgBcC

variable {n : ℕ}

abbrev ιE (n : ℕ) : (Md n → ℂ) →ₗ[ℂ] abelian₂ n := ExteriorAlgebra.ι ℂ

theorem fb_eq (A : Finset (Md n)) : ∃ w : Fin A.card → (Md n → ℂ), fb n A = ExteriorAlgebra.ιMulti ℂ A.card w :=
  ⟨_, by rw [fb, ExteriorAlgebra.basis_apply]⟩

theorem toLin'_smul_one (s : ℂ) : Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)) = s • LinearMap.id := by
  rw [map_smul, Matrix.toLin'_one]

theorem map_smul_ι (s : ℂ) (v : Md n → ℂ) :
    ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) (ιE n v) = s • ιE n v := by
  rw [toLin'_smul_one, ExteriorAlgebra.map_apply_ι]
  simp

theorem map_smul_prod (s : ℂ) (l : List (Md n → ℂ)) :
    ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) (l.map (ιE n)).prod =
      s ^ l.length • (l.map (ιE n)).prod := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, map_smul_ι, ih, List.length_cons, smul_mul_smul_comm, pow_succ, mul_comm s]

def Pm (n : ℕ) (s : ℂ) : abelian₂ n →ₗ[ℂ] abelian₂ n :=
  ∑ m : Md n, LinearMap.mul ℂ (abelian₂ n) (ιE n (Pi.single m 1)) *
    (ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))).toLinearMap *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1))

theorem ι_anticomm (a b : Md n → ℂ) : ιE n a * ιE n b = -(ιE n b * ιE n a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

theorem Pm_apply (s : ℂ) (y : abelian₂ n) : Pm n s y = ∑ m : Md n, ιE n (Pi.single m 1) *
    ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1)) y) := by
  simp only [Pm, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]

theorem Pm_ι_mul (s : ℂ) (v : Md n → ℂ) (y : abelian₂ n) :
    Pm n s (ιE n v * y) = ιE n v * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) y +
      s • (ιE n v * Pm n s y) := by
  have hv : ∑ m : Md n, v m • ιE n (Pi.single m 1) = ιE n v := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [← LinearMap.map_smul, ← map_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hm : ∀ m : Md n, ιE n (Pi.single m 1) * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1)) (ιE n v * y)) =
      v m • (ιE n (Pi.single m 1) * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ))) y) +
      s • (ιE n v * (ιE n (Pi.single m 1) * ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single m 1)) y))) := by
    intro m
    have hd : dualOf (Pi.single m 1) v = v m := by simp [dualOf]
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, map_smul_ι, hd]
    rw [mul_sub, mul_smul_comm, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ι_anticomm, neg_mul, mul_assoc,
      smul_neg, sub_neg_eq_add]
  rw [Pm_apply, Pm_apply, Finset.sum_congr rfl (fun m _ => hm m), Finset.sum_add_distrib]
  congr 1
  · simp_rw [← smul_mul_assoc]
    rw [← Finset.sum_mul, hv]
  · rw [Finset.mul_sum, Finset.smul_sum]

theorem ofFn_eq {k : ℕ} (w : Fin k → Md n → ℂ) :
    (List.ofFn fun i => ExteriorAlgebra.ι ℂ (w i)) = (List.ofFn w).map (ιE n) := by
  rw [List.map_ofFn]; rfl

theorem Pm_one (s : ℂ) : Pm n s 1 = 0 := by
  simp [Pm_apply, CliffordAlgebra.contractLeft_one]

theorem Pm_prod (s : ℂ) (l : List (Md n → ℂ)) :
    Pm n s (l.map (ιE n)).prod = ((l.length : ℂ) * s ^ (l.length - 1)) • (l.map (ιE n)).prod := by
  induction l with
  | nil => simp [Pm_one]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Pm_ι_mul, map_smul_prod, ih, mul_smul_comm, mul_smul_comm, smul_smul, ← add_smul]
    congr 1
    rw [List.length_cons]
    have hk : ∀ k : ℕ, s ^ k + s * ((k : ℂ) * s ^ (k - 1)) = ((k + 1 : ℕ) : ℂ) * s ^ (k + 1 - 1) := by
      intro k
      rcases k with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]
        push_cast
        ring
    exact hk _

end PositivityTheory.RgBcC.Cxb

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.Cxb

theorem gamScal : GamScal := by
  intro n s
  ext B A
  rw [gamM_eq, matL, LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  obtain ⟨w, hw⟩ := fb_eq (n := n) A
  have h : (ExteriorAlgebra.map (Matrix.toLin' (s • (1 : Matrix (Md n) (Md n) ℂ)))).toLinearMap (fb n A) =
      s ^ A.card • fb n A := by
    rw [AlgHom.toLinearMap_apply, hw, ExteriorAlgebra.ιMulti_apply, ofFn_eq, map_smul_prod, List.length_ofFn]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases e : A = B
  · subst e; simp
  · simp [e, Ne.symm e]

theorem number : Number := by
  intro n s
  have e : ∑ m : Md n, creL n (Pi.single m 1) * gamM (s • (1 : Matrix (Md n) (Md n) ℂ)) * annL n (Pi.single m 1) =
      matL n (Pm n s) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Pm, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [creL_eq, gamM_eq, annL_eq, ← matL_mul, ← matL_mul]
  rw [e]
  ext B A
  rw [matL, LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  obtain ⟨w, hw⟩ := fb_eq (n := n) A
  have h : Pm n s (fb n A) = ((A.card : ℂ) * s ^ (A.card - 1)) • fb n A := by
    rw [hw, ExteriorAlgebra.ιMulti_apply, ofFn_eq, Pm_prod, List.length_ofFn]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases e : A = B
  · subst e; simp
  · simp [e, Ne.symm e]

end PositivityTheory.RgBcC
end
end

