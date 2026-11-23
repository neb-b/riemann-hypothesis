module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0045
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import GroundTheory.GlobalFields.CompletionAtPlace
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0041
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0043
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0025
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0046
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0030

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtSubSIns
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC mat_ext psiT_sigR finPart_sigR)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem compAt_sub_sIns {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (hdet : IsUnit fr.det) (y : Mx D m n) :
    (y - sIns τ fr (piF θ τ fr y)).map (psiT D τ) = 0 := by
  have hp : Matrix.of (piF θ τ fr y) = fr⁻¹ * compAt θ τ y := rfl
  rw [Matrix.map_sub (psiT D τ) (fun a b => map_sub (psiT D τ) a b), ← PlaceFactsH.compAt_eq_psiT hθ,
    ← PlaceFactsH.compAt_eq_psiT hθ, show sIns (D := D) τ fr (piF θ τ fr y) = insT τ (fr * Matrix.of (piF θ τ fr y)) from rfl,
    compAt_insT hθ, if_pos rfl, hp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, sub_self]


set_option synthInstance.maxHeartbeats 400000 in
theorem inner_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} (x x' z : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D))
    (hz : z.map (psiT D τ) = 0) : inner V x z = inner V x' z := by
  apply mat_ext D
  · intro τ''
    rw [map_inner, map_inner]
    by_cases h : τ'' = τ
    · subst h; rw [hz, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero]
    · have := hx τ'' h
      rw [eq_thetaC D hθ] at this
      change x.map (psiT D τ'') = x'.map (psiT D τ'') at this
      rw [this]
  · have ha : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      simp only [adj, Matrix.map_apply, Matrix.transpose_apply, cA]
      rw [finPart_sigR, finPart_sigR]
      congr 1
      exact congrFun (congrFun hf j) i
    show (adj x * (gA V * z)).map (finPart D) = (adj x' * (gA V * z)).map (finPart D)
    rw [Matrix.map_mul, ha, ← Matrix.map_mul]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivationOfQuadraticForm
section
noncomputable section

open Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def Dv (X : Matrix (Fin m) (Fin m) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  MvPolynomial.mkDerivation ℂ (fun k : Fin m × Fin n × Bool => xyP X k.1 k.2.1 k.2.2)

theorem Dv_X (X : Matrix (Fin m) (Fin m) ℂ) (k : Fin m × Fin n × Bool) :
    Dv X (MvPolynomial.X k : PX m n) = xyP X k.1 k.2.1 k.2.2 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem Dv_eq (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    Dv X P = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k P := by
  let D₂ : Derivation ℂ (PX m n) (PX m n) :=
    ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • pderiv k
  have hs : ∀ Q : PX m n, D₂ Q = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k Q := by
    intro Q
    show (Derivation.coeFnAddMonoidHom (R := ℂ) (A := PX m n) (M := PX m n)
      (∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • (pderiv k : Derivation ℂ (PX m n) (PX m n)))) Q = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
  have h : Dv X P = D₂ P := by
    refine MvPolynomial.derivation_eq_of_forall_mem_vars (fun i _ => ?_)
    rw [hs, Dv_X]
    simp [pderiv_X, Pi.single_apply]
  rw [h, hs]

def Q2 (m n : ℕ) : PX m n := ∑ a, ∑ i, MvPolynomial.X (a, i, false) * MvPolynomial.X (a, i, true)

theorem derivation_quadraticForm_eq_sum (X : Matrix (Fin m) (Fin m) ℂ) :
    Dv X (Q2 m n) = ∑ a, ∑ i, (MvPolynomial.X (a, i, false) * xyP X a i true + MvPolynomial.X (a, i, true) * xyP X a i false) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Q2, map_sum, Derivation.leibniz, Dv_X, smul_eq_mul]

theorem vfX_eq_Dv (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    vfX c X P = Dv X P - C (c : ℂ) * Dv X (Q2 m n) * P := by
  rw [Dv_eq, derivation_quadraticForm_eq_sum, vfX]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  ring

theorem eval_xyP (X : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (xyP X a i b) =
      if b then star (matL X u a i) else matL X u a i := by
  cases b <;> simp [xyP, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord, matL_apply, star_sum, star_mul']

theorem gs_eq (c : ℝ) (u : Fin m → Fin n → ℂ) :
    gs c u = Complex.exp (-(c : ℂ) * MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (Q2 m n)) := by
  rw [gs]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Q2, map_sum, map_mul, MvPolynomial.eval_X, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord]
  push_cast
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Finset.mul_sum]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {σ : Type*} [Fintype σ] (g : ℝ → σ → ℂ) (g' : σ → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (Q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0 := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun Q => HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0) Q ?_ ?_ ?_
  · intro a
    simpa using hasDerivAt_const (0 : ℝ) a
  · intro p q hp hq
    refine ((hp.fun_add hq).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [mul_add, Finset.sum_add_distrib]
    · exact Filter.Eventually.of_forall (fun t => by simp)
  · intro p k hp
    refine ((hp.fun_mul (hg k)).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib,
        apply_ite, Finset.sum_ite_eq]
      rw [add_comm]
      congr 1
      · ring
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    · exact Filter.Eventually.of_forall (fun t => by simp)

theorem hasDerivAt_curve (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) (fP c (vfX c X P) x) 0 := by
  set u : ℝ → (Fin m → Fin n → ℂ) := fun t => matL (NormedSpace.exp ((t : ℂ) • X)) x with hu
  have hu0 : u 0 = x := by simp [hu, matL_one]
  clear_value u
  rw [show (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) =
    fun t => fP c P (u t) by rw [hu]]
  let e : (Fin m → Fin n → ℂ) → Fin m × Fin n × Bool → ℂ :=
    fun v k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k v
  have hg : ∀ k, HasDerivAt (fun t => e (u t) k) (MvPolynomial.eval (e x) (xyP X k.1 k.2.1 k.2.2)) 0 := by
    rintro ⟨a, i, b⟩
    have hlin : HasDerivAt (fun t => u t a i) (matL X x a i) 0 := by
      have hs := HasDerivAt.fun_sum (u := Finset.univ)
        (fun c (_ : c ∈ Finset.univ) => (hasDerivAt_entry X a c).mul_const (x c i))
      simpa only [hu, matL_apply] using hs
    rw [eval_xyP]
    cases b
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin.star
  have hf : (fun t : ℝ => fP c P (u t)) = fun t => MvPolynomial.eval (e (u t)) P *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e (u t)) (Q2 m n)) := by
    funext t
    rw [fP, gs_eq]
    rfl
  have hx : fP c (vfX c X P) x = MvPolynomial.eval (e x) (vfX c X P) *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e x) (Q2 m n)) := by
    rw [fP, gs_eq]
    rfl
  rw [hf, hx, vfX_eq_Dv, Dv_eq X P, Dv_eq X (Q2 m n)]
  have hP := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg P
  have hQ := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg (Q2 m n)
  have H := hP.fun_mul ((hQ.const_mul (-(c : ℂ))).cexp)
  rw [hu0] at H
  refine H.congr_deriv ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_mul, map_sum, MvPolynomial.eval_C]
  ring

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem locInst_of_cell_kvac (hc : LIcell) (hk : LIkvac) (hT : TensMem) : LocInst :=
  locInst_of hT lIl lIlin lIlaw hc lIcont lIrho lIkact lIvac hk

theorem locInst_of_cell (hc : LIcell) (hT : TensMem) : LocInst := locInst_of_cell_kvac hc lIkvac hT

theorem locInst_of_away (hA : AwayAct) (hT : TensMem) : LocInst :=
  locInst_of_cell (lIcell_of' hA lIcont lIlaw lIvac) hT

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem sigOK : SigOK := sigOK_of wittLBlt wittLBeq

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WeightFactorEqAutomorphy
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem lawM_of : TensInj → LawM := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  refine ⟨k - j, fun y a ha hy f hf => ?_⟩
  set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef
  have hAv : A.1 = a := rfl
  have hAi : (A⁻¹).1 = a⁻¹ := by rw [Matrix.coe_units_inv, hAv]
  have hyA : y = LocLawH.mOf A := by
    apply GR_ext
    rw [hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]
    rfl
  have hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0 := by simp [LocLawH.mR_mOf]
  have haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A := Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)
  have hsc := LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false)
    (cnt_add _) (LocLawH.mOf A) hy0
  rw [haOf] at hsc
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy,
    siegelP_jF _ hy0, cnt_add]
  have hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a := by rw [LocLawH.mR_mOf]; simp [hAv]
  rw [hbl]
  have hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x := by
    refine hΨ.1 _ _ (fun τ' h => ?_) ?_
    · rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]
    · rw [LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]
  simp only [tens, hΨx, levF]
  rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]
  have hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x := rfl
  rw [hof]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

