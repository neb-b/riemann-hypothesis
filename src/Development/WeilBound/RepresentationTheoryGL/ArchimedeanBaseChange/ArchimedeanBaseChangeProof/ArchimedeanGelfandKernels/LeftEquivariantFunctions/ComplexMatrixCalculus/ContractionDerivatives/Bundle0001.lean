module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ContractLeftMap
section
noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxb

open PositivityTheory.RgBcC

variable {n : ℕ}

theorem map_comp' {M N P : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [AddCommGroup P]
    [Module ℂ P] (f : N →ₗ[ℂ] P) (g : M →ₗ[ℂ] N) :
    ExteriorAlgebra.map (f ∘ₗ g) = (ExteriorAlgebra.map f).comp (ExteriorAlgebra.map g) := by
  ext m
  simp

theorem creL_eq (v : Md n → ℂ) : creL n v = matL n (LinearMap.mul ℂ (abelian₂ n) (ExteriorAlgebra.ι ℂ v)) := rfl

theorem annL_eq (w : Md n → ℂ) :
    annL n w = matL n (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf w)) := rfl

theorem gamM_eq (g : Matrix (Md n) (Md n) ℂ) : gamM g = matL n (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap := rfl

theorem matL_mul (f h : abelian₂ n →ₗ[ℂ] abelian₂ n) : matL n (f * h) = matL n f * matL n h := LinearMap.toMatrix_mul _ _ _

theorem matL_one : matL n (1 : abelian₂ n →ₗ[ℂ] abelian₂ n) = 1 := LinearMap.toMatrix_one _

theorem contractLeft_map (f : (Md n → ℂ) →ₗ[ℂ] (Md n → ℂ)) (d : Module.Dual ℂ (Md n → ℂ)) (y : abelian₂ n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) d (ExteriorAlgebra.map f y) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (d ∘ₗ f) y) := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | ι_mul x m hx =>
    have e : ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m * x) =
        CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) * ExteriorAlgebra.map f x := by
      rw [map_mul]
      exact congrArg (· * _) (ExteriorAlgebra.map_apply_ι f m)
    rw [e, CliffordAlgebra.contractLeft_ι_mul, hx, CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul]
    rw [show ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) m) =
      CliffordAlgebra.ι (0 : QuadraticForm ℂ (Md n → ℂ)) (f m) from ExteriorAlgebra.map_apply_ι f m]
    rfl

end PositivityTheory.RgBcC.Cxb

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.Cxb

theorem gamMul : GamMul := by
  intro n
  refine ⟨?_, fun g h => ?_⟩
  · rw [gamM_eq, Matrix.toLin'_one, ExteriorAlgebra.map_id]
    exact LinearMap.toMatrix_id _
  · rw [gamM_eq, gamM_eq, gamM_eq, Matrix.toLin'_mul, map_comp', AlgHom.comp_toLinearMap, ← matL_mul]
    rfl

theorem car : Car := by
  intro n v w
  rw [annL_eq, creL_eq, ← matL_mul, ← matL_mul, ← map_add (f := _), ← matL_one, ← map_smul]
  congr 1
  apply LinearMap.ext
  intro y
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.mul_apply', LinearMap.mul_apply', CliffordAlgebra.contractLeft_ι_mul]
  show (w ⬝ᵥ v) • y - _ + _ = _
  abel

theorem gamCre : GamCre := by
  intro n g v w
  refine ⟨?_, ?_⟩
  · rw [gamM_eq, creL_eq, creL_eq, ← matL_mul, ← matL_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, LinearMap.mul_apply', map_mul, ExteriorAlgebra.map_apply_ι,
      Matrix.toLin'_apply]
  · rw [gamM_eq, annL_eq, annL_eq, ← matL_mul, ← matL_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply]
    have hd : dualOf w ∘ₗ Matrix.toLin' g = dualOf (gᵀ *ᵥ w) := by
      refine LinearMap.ext fun u => ?_
      simp only [LinearMap.comp_apply, dualOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.toLin'_apply]
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [contractLeft_map, hd]

end PositivityTheory.RgBcC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.SumSingleSmul
section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.CxbDer

open PositivityTheory.RgBcC

variable {n : ℕ}

abbrev X (n : ℕ) := Md n → Md n → ℂ

def one' (n : ℕ) : X n := fun r s => if r = s then 1 else 0

def mv (B : X n) (m : Md n → ℂ) : Md n → ℂ := fun r => ∑ s, B r s * m s

def F (y : abelian₂ n) (g : X n) : Finset (Md n) → ℂ :=
  (fb n).equivFun (ExteriorAlgebra.map (Matrix.toLin' (Matrix.of g)) y)

theorem ι_anticomm (a b : Md n → ℂ) :
    ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b = -(ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ a) := by
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

def Ers (r s : Md n) : abelian₂ n →ₗ[ℂ] abelian₂ n :=
  LinearMap.mul ℂ (abelian₂ n) (ExteriorAlgebra.ι ℂ (Pi.single r 1)) *
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf (Pi.single s 1))

def Dop (B : X n) : abelian₂ n →ₗ[ℂ] abelian₂ n := ∑ r, ∑ s, B r s • Ers r s

theorem Dop_apply (B : X n) (x : abelian₂ n) : Dop B x = ∑ r, ∑ s, B r s •
    (ExteriorAlgebra.ι ℂ (Pi.single r 1) * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ)))
      (dualOf (Pi.single s 1)) x) := by
  simp only [Dop, LinearMap.sum_apply, LinearMap.smul_apply, Ers, Module.End.mul_apply, LinearMap.mul_apply']

theorem Dop_algebraMap (B : X n) (r : ℂ) : Dop B (algebraMap ℂ (abelian₂ n) r) = 0 := by
  rw [Dop_apply]
  simp [CliffordAlgebra.contractLeft_algebraMap]

theorem sum_single_smul (u : Md n → ℂ) : ∑ r, u r • (Pi.single r (1 : ℂ) : Md n → ℂ) = u := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem Dop_ι_mul (B : X n) (m : Md n → ℂ) (x : abelian₂ n) :
    Dop B (ExteriorAlgebra.ι ℂ m * x) = ExteriorAlgebra.ι ℂ (mv B m) * x + ExteriorAlgebra.ι ℂ m * Dop B x := by
  have hds : ∀ s, dualOf (Pi.single s (1 : ℂ)) m = m s := by
    intro s
    show Pi.single s 1 ⬝ᵥ m = m s
    simp [dotProduct, Pi.single_apply]
  have h1 : ExteriorAlgebra.ι ℂ (mv B m) =
      ∑ r, ∑ s, (B r s * m s) • ExteriorAlgebra.ι ℂ (Pi.single r (1 : ℂ)) := by
    conv_lhs => rw [← sum_single_smul (mv B m)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, mv, Finset.sum_smul]
  rw [Dop_apply, Dop_apply, h1, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [CliffordAlgebra.contractLeft_ι_mul, hds, mul_sub, ← mul_assoc, ι_anticomm, neg_mul, sub_neg_eq_add,
    smul_add, mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm, mul_assoc]

def Philin (n : ℕ) : (Md n → ℂ) →ₗ[ℂ] (Finset (Md n) → ℂ) →ₗ[ℂ] (Finset (Md n) → ℂ) :=
  LinearMap.mk₂ ℂ (fun u c => (fb n).equivFun (ExteriorAlgebra.ι ℂ u * (fb n).equivFun.symm c))
    (fun u u' c => by simp [map_add (f := _), add_mul])
    (fun a u c => by simp [map_smul, smul_mul_assoc])
    (fun u c c' => by simp [map_add (f := _), mul_add])
    (fun a u c => by simp [map_smul, mul_smul_comm])

def Phi (n : ℕ) : (Md n → ℂ) →L[ℂ] (Finset (Md n) → ℂ) →L[ℂ] (Finset (Md n) → ℂ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Finset (Md n) → ℂ) →ₗ[ℂ] (Finset (Md n) → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Philin n)

theorem Phi_apply (u : Md n → ℂ) (c : Finset (Md n) → ℂ) :
    Phi n u c = (fb n).equivFun (ExteriorAlgebra.ι ℂ u * (fb n).equivFun.symm c) := rfl

def mvL (m : Md n → ℂ) : X n →L[ℂ] (Md n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => mv g m
      map_add' := fun g h => by ext r; simp [mv, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c g => by ext r; simp [mv, Finset.mul_sum, mul_assoc] }

theorem mvL_apply (m : Md n → ℂ) (g : X n) : mvL m g = mv g m := rfl

theorem mv_one' (m : Md n → ℂ) : mv (one' n) m = m := by
  ext r; simp [mv, one']

theorem F_one (y : abelian₂ n) : F y (one' n) = (fb n).equivFun y := by
  have h : Matrix.of (one' n) = 1 := by
    ext r s
    simp [one', Matrix.one_apply]
  unfold F
  rw [h, Matrix.toLin'_one, ExteriorAlgebra.map_id, AlgHom.id_apply]

theorem F_ι_mul (m : Md n → ℂ) (x : abelian₂ n) :
    F (ExteriorAlgebra.ι ℂ m * x) = fun g => Phi n (mvL m g) (F x g) := by
  funext g
  simp only [F, Phi_apply, mvL_apply, map_mul, ExteriorAlgebra.map_apply_ι, LinearEquiv.symm_apply_apply]
  rfl

set_option maxHeartbeats 800000 in
theorem key (y : abelian₂ n) : ContDiff ℂ ∞ (F y) ∧
    ∃ L : X n →L[ℂ] (Finset (Md n) → ℂ), HasFDerivAt (F y) L (one' n) ∧ ∀ B, L B = (fb n).equivFun (Dop B y) := by
  refine CliffordAlgebra.left_induction _ ?_ ?_ ?_ y
  · intro r
    have hF : F (algebraMap ℂ (abelian₂ n) r) = fun _ => (fb n).equivFun (algebraMap ℂ (abelian₂ n) r) := by
      funext g
      unfold F
      rw [AlgHom.commutes]
    refine ⟨?_, 0, ?_, fun B => ?_⟩
    · rw [hF]
      exact contDiff_const
    · rw [hF]
      exact hasFDerivAt_const _ _
    · rw [ContinuousLinearMap.zero_apply, Dop_algebraMap, map_zero]
  · rintro x z ⟨hxc, Lx, hxd, hxL⟩ ⟨hzc, Lz, hzd, hzL⟩
    have hF : F (x + z) = fun g => F x g + F z g := by
      funext g
      unfold F
      rw [map_add (f := _), map_add (f := _)]
    refine ⟨?_, Lx + Lz, ?_, fun B => ?_⟩
    · rw [hF]
      exact hxc.add hzc
    · rw [hF]
      exact hxd.add hzd
    · rw [ContinuousLinearMap.add_apply, hxL, hzL, map_add (f := _), map_add (f := _)]
  · rintro x m ⟨hxc, Lx, hxd, hxL⟩
    rw [F_ι_mul]
    have hd := (Phi n).hasFDerivAt_of_bilinear (mvL m).hasFDerivAt hxd
    have hc : ContDiff ℂ ∞ (fun g => Phi n (mvL m g) (F x g)) :=
      ContDiff.clm_apply ((Phi n).contDiff.comp (mvL m).contDiff) hxc
    refine ⟨hc, _, hd, fun B => ?_⟩
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.precompL_apply, mvL_apply, mvL_apply, mv_one', F_one,
      hxL, Phi_apply, Phi_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, Dop_ι_mul, map_add,
      add_comm]

end PositivityTheory.RgBcC.CxbDer
end
end

