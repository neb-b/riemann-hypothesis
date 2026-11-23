module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjSmoothVectorConjugateModelMemSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSmooth

open GlobalTheory.ConjDS

theorem conj_list_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    A * l.prod * A⁻¹ = (l.map fun x => A * x * A⁻¹).prod := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  induction l with
  | nil => simp [h1]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc A * (x * l.prod) * A⁻¹ = A * x * (A⁻¹ * A) * l.prod * A⁻¹ := by rw [h2]; noncomm_ring
      _ = A * x * A⁻¹ * (A * l.prod * A⁻¹) := by noncomm_ring

theorem cj_mem_sm : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  intro D Y S M τ w hw
  apply Submodule.subset_span
  intro k Xs hXs
  set A := (conjModel M).fr τ with hAdef
  have hA : IsUnit A := (conjModel M).fr_unit τ
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet

  have hrep : ∀ g, M.rep τ g (cj (M.H τ) w) = cj (M.H τ) ((conjModel M).σ τ (A * g * A⁻¹) w) := by
    intro g
    have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
      rw [inv_submatrix_equiv]
      have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
          rv (M.fr τ * g * (M.fr τ)⁻¹) := by
        ext i j
        simp [rv, Matrix.mul_apply]
      rw [this, rv_rv]
    show M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj (M.H τ) w) = M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj (M.H τ) w)
    rw [e]

  have hX' : ∀ i, A * Xs i * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((conjModel M).ε τ)) := by
    intro i
    have hg : Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A = gramAt D Y τ := (conjModel M).fr_gram τ
    have hi : (Xs i)ᴴ * gramAt D Y τ + gramAt D Y τ * Xs i = 0 := hXs i
    have h3 : (A⁻¹)ᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) = 0
    rw [← hg] at hi
    have : (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) =
        (A⁻¹)ᴴ * ((Xs i)ᴴ * (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) + (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) * Xs i) * A⁻¹ := by
      simp only [Matrix.conjTranspose_mul]
      calc _ = (A⁻¹)ᴴ * (Xs i)ᴴ * Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + 1 * Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) := by
              rw [Matrix.one_mul]; noncomm_ring
        _ = _ := by rw [← h3]; simp only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul]
    rw [this, hi, Matrix.mul_zero, Matrix.zero_mul]
  have hprod : ∀ t : Fin k → ℝ, A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * A⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * A⁻¹))).prod := by
    intro t
    rw [conj_list_prod hA, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp]
    rw [← Matrix.exp_conj A _ hA, Matrix.mul_smul, Matrix.smul_mul]
  have hc := hw k (fun i => A * Xs i * A⁻¹) hX'
  let L : Cj (M.H τ) →L[ℝ] M.H τ :=
    { toFun := cj (M.H τ)
      map_add' := map_add (cj (M.H τ))
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
        rfl
      cont := (cj (M.H τ)).continuous }
  have hL := L.contDiff.comp hc
  convert hL using 1
  funext t
  rw [hrep, hprod]
  rfl

end GlobalTheory.ConjSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftScalarOfInnerProductFormula
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_gW (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (x y : (R.HW i σ).H) :
    ⟪R.gW i σ g x, R.gW i σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨R.gW i σ g, GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ g⟩ x y

theorem adjoint_projH (hC : GlobalTheory.Hk3.Core R F) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (GlobalTheory.LiftLower.projH R i σ) = GlobalTheory.LiftLower.projH R i σ := by
  have hc : ∀ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
    intro g
    unfold RealDat.eC
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv σ 1
    have h2 := (hX χ hχ).map_inv σ g⁻¹
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast]
    rw [h2, ← h1]
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [← inner_gW hC i σ g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem projH_projH (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    GlobalTheory.LiftLower.projH R i σ (GlobalTheory.LiftLower.projH R i σ x) = GlobalTheory.LiftLower.projH R i σ x := by
  classical
  have h1 : ∀ g, ∑ a, RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g) = RealDat.eC (A := A) σ g := by
    intro g
    unfold RealDat.eC
    conv_rhs => rw [← idemOf_mul_self A.X hX]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp only [map_mul]
  unfold GlobalTheory.LiftLower.projH
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_congr rfl fun g _ => by rw [← h1 g, Finset.sum_smul]]
  rw [Finset.sum_comm (f := fun g a => (RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g)) • R.gW i σ g x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_nbij' (fun g => a * g) (fun g => a⁻¹ * g) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [inv_mul_cancel_left, map_mul, Module.End.mul_apply, mul_comm]

theorem eq_of_ext {V : HSp D} {c : CoefA V} (hc : c.Is) {H : HMod (Bridge.Gf V → c.W)} (hinj : Function.Injective H.e) {z z' : H.H}
    (h : ∀ x w, inner ℂ (c.ext (H.e z) x) w = inner ℂ (c.ext (H.e z') x) w) : z = z' := by
  refine hinj (funext fun u => ?_)
  have e : c.ext (H.e z) (GlobalTheory.AdelicScalar.finLift V u) = c.ext (H.e z') (GlobalTheory.AdelicScalar.finLift V u) :=
    ext_inner_right ℂ fun w => h _ w
  exact (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z) u).symm.trans (e.trans (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z') u))

end GlobalTheory.ConjScalarProof

namespace GlobalTheory.ConjScalarProof

set_option maxHeartbeats 1000000 in
open GlobalTheory.LiftLower in
theorem conjScalarAt_of_sourceLevelLaw_fock_zeta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hCore hX hSL hIPF hFC hFZ hRC
  intro gramR c0R c0L hT i σ hσ μ' η' c c₁ H j th hD ev
  have hμ := hD.1
  have hη := hD.2.1
  have hf := hD.2.2.1
  have hL := hD.2.2.2
  have hL2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hL
  obtain ⟨ω, hL3⟩ := hL2
  obtain ⟨f₀, f, B, io, thP, hL4⟩ := hL3
  have hLD := hL4.1
  have hP := hL4.2
  have h38 := GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum R F hCore gramR c0R c0L hT i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hLD
  obtain ⟨s, m, h39⟩ := h38
  have hC := h39.1
  have hν := h39.2.1
  have hy := h39.2.2.1
  have hH := h39.2.2.2
  have hth := hLD.2.2.2
  have hio := hC.2.2.2.2.2.2.2.2.2.2
  have hc : c.Is := hC.2.2.2.2.2.2.2.2.2.1
  have hv0 := hio.2.2
  let v := hv0.choose
  have hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 := hv0.choose_spec.choose_spec.1
  let K : ℂ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)
  have hKdef : K = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := rfl
  have hK0 : K ≠ 0 := by
    rw [hKdef, Finset.prod_ne_zero_iff]
    intro ρ _
    have h1 := GlobalTheory.AdelicScalar.one_le_dimK i σ ρ
    exact_mod_cast (show (dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) ≠ 0 by positivity)
  have hKc : starRingEnd ℂ K = K := by
    rw [hKdef, map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  have hadj : ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W), inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w = K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h :=
    _root_.GlobalTheory.ConjAdjoint.adjoint_eq_upLift R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv thP th hth hP
  have hpp : ∀ y, projH R i σ (projH R i σ y) = projH R i σ y := projH_projH hX i σ
  have hsa : LinearMap.adjoint (projH R i σ) = projH R i σ := adjoint_projH hCore hX i σ
  have hinj : Function.Injective H.e := hH.1
  have hadjP : ∀ y, LinearMap.adjoint th (projH R i σ y) = LinearMap.adjoint th y := fun y =>
    eq_of_ext (V := Vc D i) (c := c) (H := H) hc hinj fun x w =>
      (hadj (projH R i σ y) x w).trans ((congrArg (fun z => K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e z fun ρ => v ρ) x) (hpp y)).trans (hadj y x w).symm)
  have hfix : ∀ u, projH R i σ (th u) = th u := fun u => ext_inner_right ℂ fun y =>
    (LinearMap.adjoint_inner_right (projH R i σ) (th u) y).symm.trans
      ((congrArg (fun A => inner ℂ (th u) (A y)) hsa).trans ((LinearMap.adjoint_inner_right th u (projH R i σ y)).symm.trans
        ((congrArg (inner ℂ u) (hadjP y)).trans (LinearMap.adjoint_inner_right th u y))))
  have hW : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => GlobalTheory.AdelicScalar.HMod_mem (hCore.models.HW i σ) y
  have hz : ∀ y h w, inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := by
    intro y h w
    have e1 : c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) = K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) :=
      (congrArg c.ext (H.e.map_smul K⁻¹ _)).trans (c.ext.map_smul K⁻¹ _)
    have e2 : starRingEnd ℂ K⁻¹ = K⁻¹ := by simp only [map_inv₀, hKc]
    calc inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w
        = inner ℂ (K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) h) w := congrArg (fun Fn => inner ℂ (Fn h) w) e1
      _ = starRingEnd ℂ K⁻¹ * inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w := inner_smul_left _ _ _
      _ = K⁻¹ * (K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h) := by simp only [e2, hadj y h w]
      _ = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := inv_mul_cancel_left₀ hK0 _
  have hG := _root_.GlobalTheory.UnitCoefIP.exists_scalar R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv ev
  let C := hG.choose
  have hC2 := hG.choose_spec
  let b := stdOrthonormalBasis ℂ c.W
  have key : ∀ u, th u ∈ partH R i σ ev → ∀ y₂,
      inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by
    intro u hu y₂
    have e1 := _root_.GlobalTheory.LiftGram.inner_eq_sum_upLift R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv
      _ (hW (projH R i σ (th u))) _ (hW (projH R i σ y₂)) _ _ (hz (th u)) (hz y₂) b
    have hu' : projH R i σ (th u) ∈ partH R i σ ev := (hfix u).symm ▸ hu
    have e2 : inner ℂ (projH R i σ (th u)) (projH R i σ y₂) = inner ℂ (th u) y₂ :=
      (congrArg (fun z => inner ℂ z (projH R i σ y₂)) (hfix u)).trans
        ((congrArg (fun A => inner ℂ (th u) (A y₂)) hsa.symm).trans
          ((LinearMap.adjoint_inner_right (projH R i σ) (th u) y₂).trans (congrArg (fun z => inner ℂ z y₂) (hfix u))))
    have e4 : inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂) =
        (Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂) := by
      refine e1.trans ?_
      rw [Finset.sum_congr rfl fun k _ => hC2 _ hu' (projH R i σ y₂) (b k) (b.orthonormal.1 k), e2, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul]
    have e3 : ∀ y, LinearMap.adjoint th y = K • (K⁻¹ • LinearMap.adjoint th y) := fun y =>
      (smul_inv_smul₀ hK0 _).symm
    calc inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂)
        = inner ℂ (K • (K⁻¹ • LinearMap.adjoint th (th u))) (K • (K⁻¹ • LinearMap.adjoint th y₂)) :=
          congrArg₂ (inner ℂ) (e3 _) (e3 _)
      _ = starRingEnd ℂ K * (K * inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂)) :=
          (inner_smul_left _ _ _).trans (congrArg (fun z => starRingEnd ℂ K * z) (inner_smul_right _ _ _))
      _ = K * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂))) :=
          (congrArg (fun z => starRingEnd ℂ K * (K * z)) e4).trans
            (congrArg (fun k => k * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂)))) hKc)
      _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by ring
  refine ⟨(K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re, fun u hu => ?_⟩
  by_cases h0 : th u = 0
  · simp only [h0, map_zero, smul_zero]
  have hre : (((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) := by
    have e0 : ((‖LinearMap.adjoint th (th u)‖ : ℝ) : ℂ) ^ 2 = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * ((‖th u‖ : ℝ) : ℂ) ^ 2 :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (LinearMap.adjoint th (th u))).symm.trans
        ((key u hu (th u)).trans (congrArg (fun z => (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * z) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (th u))))
    have hn : ((‖th u‖ : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.2 h0)
    have e' : (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) = ((‖LinearMap.adjoint th (th u)‖ ^ 2 / ‖th u‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff hn]
      exact e0.symm
    exact (congrArg (fun z : ℂ => ((z.re : ℝ) : ℂ)) e').trans ((congrArg (fun r : ℝ => (r : ℂ)) (Complex.ofReal_re _)).trans e'.symm)
  refine ext_inner_right ℂ fun y => ?_
  calc inner ℂ (th (LinearMap.adjoint th (th u))) y = inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y) :=
        (LinearMap.adjoint_inner_right th _ y).symm
    _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y := key u hu y
    _ = inner ℂ ((((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) • th u) y :=
      (congrArg (fun z => z * inner ℂ (th u) y) ((Complex.conj_ofReal _).trans hre)).symm.trans (inner_smul_left _ _ _).symm

end GlobalTheory.ConjScalarProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelFrameMatrixFactsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLocFacts

variable {n : ℕ}

theorem conj_mem_lie {F J G X : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hX : Xᴴ * G + G * X = 0) : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = 0 := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have e : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = (F⁻¹)ᴴ * (Xᴴ * G + G * X) * F⁻¹ := by
    rw [← hG]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    congr 1
    · rw [h1, Matrix.mul_one]
    · rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul]
  rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem ofFr_mem_UH {F J G g : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hg : gᴴ * J * g = J) : F⁻¹ * g * F ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
  rw [← hG]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul, ← Matrix.mul_assoc F F⁻¹, h1, Matrix.one_mul,
    ← Matrix.mul_assoc J g F, ← Matrix.mul_assoc gᴴ (J * g) F, ← Matrix.mul_assoc gᴴ J g, hg]

theorem rev_conj (F g : Matrix (Fin n) (Fin n) ℂ) :
    F.submatrix Fin.revPerm (Equiv.refl _) * g * (F.submatrix Fin.revPerm (Equiv.refl _))⁻¹ =
      GlobalTheory.ConjDS.rv (F * g * F⁻¹) := by
  rw [Matrix.inv_submatrix_equiv]
  ext i j
  simp [GlobalTheory.ConjDS.rv, Matrix.mul_apply]

theorem frame_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  intro D θ hθ Y S M τ
  have hF : IsUnit (M.fr τ) := M.fr_unit τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hF
  have hA : ∀ g, (GlobalTheory.ConjDS.conjModel M).fr τ * g * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (M.fr τ * g * (M.fr τ)⁻¹) := fun g => rev_conj (M.fr τ) g
  have hcan : ∀ U : Matrix (Fin Y.rank) (Fin Y.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * U * M.fr τ) * (M.fr τ)⁻¹ = U := by
    intro U
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  refine ⟨fun u => ⟨?_, ?_, ?_⟩, fun X hX => ⟨?_, fun s => ?_⟩⟩
  · exact ofFr_mem_UH hF (M.fr_gram τ) u.2
  · show _ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * _ = _
    rw [hA, hcan]
  · show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * (M.fr τ)⁻¹) = _
    rw [hcan]
  · exact conj_mem_lie ((GlobalTheory.ConjDS.conjModel M).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M).fr_gram τ) hX
  · have hmem : NormedSpace.exp (s • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) :=
      GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit Y τ) hX s
    have hc : cmp θ τ (oneP θ Y τ X s) = NormedSpace.exp (s • X) :=
      (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hmem).2.1
    rw [hc]
    refine ⟨hmem, ?_⟩
    rw [← Matrix.exp_conj _ _ ((GlobalTheory.ConjDS.conjModel M).fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.PackLocFacts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteTopSpaceColumnValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.CoreOnto

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem coefPlus_is (G : GridData L sc) (θ : InfFam D) (hθ : IsInfFam θ) : (coefPlus G θ).Is := by
  obtain ⟨hc, hs⟩ := GlobalTheory.CoefModel.realGL_laws hθ (Xp G)
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Xp G).gram
  refine GlobalTheory.CoefModel.coefOf_is _ _ _ (fun h hh => ?_) (fun h τ => ?_) (fun τ => ?_) (fun g hg => ?_)
  · have : GlobalTheory.CoefModel.realGL θ (Xp G) h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom (Xp G) h) = 1
      rw [show infHom (Xp G) h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, this, map_one]
  · exact GlobalTheory.CoefModel.invTr_unitary (g := GlobalTheory.CoefModel.realGL θ (Xp G) h τ)
      (GlobalTheory.RecDictModel.archM_unitary _ (hθ τ) h)
  · refine ((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹ τ : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) ℂ) = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (invTrK g) fun τ => by
      have := GlobalTheory.CoefModel.invTr_unitary (hg τ)
      rwa [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (posDef_Xp G _).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, e]
    exact funext fun τ => GlobalTheory.CoefModel.invTr_invTr _

theorem eps_core_m (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m))) :
    ∀ τ a, M.ε τ a = true := by
  intro τ a
  obtain ⟨-, q, -, hS⟩ := M.enum τ
  have h : (q a, M.ε τ a) ∈ Node.par D sc.cGap (.core D.R.m) τ := hS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
  have e : Node.par D sc.cGap (.core D.R.m) τ = (num D sc.cGap τ).parX 0 := (num D sc.cGap τ).parPi_m
  rw [e] at h
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 h
  exact (congrArg Prod.snd hx).symm

theorem topCols : TopCols := by
  intro D _ T L μ0 _ sc G W Mv _ M y hy w
  obtain ⟨pr, hpr⟩ := _root_.GlobalTheory.TopCoefPair.exists_dualPair G W.θ W.θ_is M
  obtain ⟨c, hc, e⟩ := _root_.GlobalTheory.TopColumn.exists_col G W.θ W.θ_is M (eps_core_m G M) (coefPlus_is G W.θ W.θ_is) pr hpr y hy
  refine ⟨c, hc, pr.flip w, ?_⟩
  subst e
  rfl

end GlobalTheory.CoreOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  first | exact @GlobalTheory.HoweGlobal.TensorMap.exists_tensL | exact GlobalTheory.HoweGlobal.TensorMap.exists_tensL | (intros; apply GlobalTheory.HoweGlobal.TensorMap.exists_tensL <;> assumption)
end

