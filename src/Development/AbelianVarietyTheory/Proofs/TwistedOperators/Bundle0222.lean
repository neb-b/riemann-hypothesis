module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationLevelProjectorFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH.LevelFix

theorem castGA_symm_mem {I I' : Formalism.MainNotions.S.AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

theorem iotaX_symm_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ : X.B.I.GA) (hγ : γ ∈ X.B.I.GFset) : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
  refine (Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_
  show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact castGA_symm_mem _ γ hγ

theorem mult_lev {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intro v k _ g; simp
  | add x y _ _ hx hy =>
    intro v k hk g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx =>
    intro v k hk g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]
    ring

end GlobalTheory.RowEvalHH.LevelFix


open GlobalTheory.RowEvalHH GlobalTheory.RowEvalHH.LevelFix in
theorem GlobalTheory.RowEvalHH.Re_evF : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → ∀ S ∈ EP R F, ∀ y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), X.B.Re (GlobalTheory.RowEvalHH.evF R X h t c S y) = GlobalTheory.RowEvalHH.evF R X h t c S y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  classical
  have hSM := Formalism.IndefR.Mult.goodPart_le _ _ _ _ _ hS
  have hcl := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (MP R) R.θ _ _ hSM (vecOf R X c y)
  have hlev := mult_lev hSM (vecOf R X c y)
  let ιY : X.B.I.GA ≃* GA D (Yc D 0) := (iotaX X h).symm.toMulEquiv
  unfold evF
  by_cases hm : MemLp (fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X)
  · rw [dite_eq_left hm]
    set f : X.B.I.GA → ℂ := fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) with hf
    have hm0 : MemLp (fun x => star (f x)) 2 (muX X) := hm.star
    have eF : star (hm.toLp f) = hm0.toLp (fun x => star (f x)) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp, hm0.coeFn_toLp] with x a1 a2 a3
      rw [a1, a3, Pi.star_apply, a2]
    rw [eF]
    have hfY : ∀ x, f x = S (vecOf R X c y) (ιY x * t) := fun x => rfl
    have hinv : ∀ γ ∈ X.B.I.GFset, ∀ x, star (f (γ * x)) = star (f x) := by
      intro γ hγ x
      congr 1
      rw [hfY, hfY, map_mul, mul_assoc]
      exact hcl.2 _ (iotaX_symm_rat X h γ hγ) _
    have hmeas : Measurable fun x => star (f x) := by
      haveI : IsTopologicalGroup (GA D (D.sp.Y 0)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
      have : Continuous f := hcl.1.comp ((iotaX X h).symm.continuous.mul continuous_const)
      exact (continuous_star.comp this).measurable
    have hright : ∀ k ∈ X.K2, ∀ x, star (f (x * (1, k))) = X.chi2 k * star (f x) := by
      intro k hk x
      have ek : (kap X h t k : GA D (Yc D 0)) = t⁻¹ * ιY (1, k) * t := rfl
      have e2 : ιY (x * (1, k)) * t = (ιY x * t) * kap X h t k := by
        rw [ek, map_mul]
        simp only [mul_assoc, mul_inv_cancel_left]
      have h1 : f (x * (1, k)) = star (X.chi2 k) * f x := by
        have hl := hlev _ (hLM k hk).1 (ιY x * t)
        rw [(hLM k hk).2] at hl
        rw [hfY, hfY, e2]
        exact hl
      rw [h1, star_mul', star_star, mul_comm]
    have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
    have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
    have hKM : MeasurableSet X.K2 := (Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL).isOpen.measurableSet
    have hfix : ∀ᵐ z ∂(X.B.I.muA X.B.μf), ∫ g, X.B.e g * star (f (z * (1, g))) ∂X.B.μf = star (f z) := by
      refine Filter.Eventually.of_forall fun z => ?_
      have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
      have hfun : (fun g => X.B.e g * star (f (z * (1, g)))) =
          X.K2.indicator (fun _ => star (f z) / ((X.B.μf X.K2).toReal : ℂ)) := by
        funext g
        rw [X.e_eq g]
        by_cases hg : g ∈ X.K2
        · have hg' : g ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
          rw [if_pos hg', Set.indicator_of_mem hg, hright g hg z]
          have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
          have hc : star (X.chi2 g) * X.chi2 g = 1 := by
            rw [RCLike.star_def, RCLike.conj_mul, hn]; simp
          show star (X.chi2 g) / ((X.B.μf X.K2).toReal : ℂ) * (X.chi2 g * star (f z)) =
            star (f z) / ((X.B.μf X.K2).toReal : ℂ)
          rw [div_mul_eq_mul_div, ← mul_assoc, hc, one_mul]
        · have hg' : g ∉ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
          rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
      rw [hfun, integral_indicator hKM, setIntegral_const]
      simp only [measureReal_def, Complex.real_smul]
      have hC : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hC]
    exact Formalism.L2.SG.Pf.idempotent_fixes_invariant_L2 X (fun x => star (f x)) hmeas hinv hm0 hfix
  · rw [dite_eq_right hm]
    have h0 : (star (0 : L2X X)) = 0 := (Formalism.L2.SG.RowDict.conjL (muX X)).map_zero
    rw [h0, map_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientModelEqConjTraceFormulaDiscreteSer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeInt

section Frame

open Formalism.L2.SG.InstExistsPf

def frP (D : D7) (τ : D.what₂.Tau) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
  (instOf D).P (Formalism.L2.Host.tauPl D τ)

theorem frP_unit (D : D7) (τ : D.what₂.Tau) : IsUnit (frP D τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((instOf D).P_unit _)

theorem fr_gram (D : D7) (τ : D.what₂.Tau) :
    ((frP D τ)⁻¹)ᴴ * Formalism.REAL.Jm (epsV D) * (frP D τ)⁻¹ = gramAt D (D.sp.Y 0) τ := by
  have h : (frP D τ)ᴴ * gramAt D (D.sp.Y 0) τ * frP D τ = Formalism.REAL.Jm (epsV D) := by
    have h0 := (instOf D).P_spec (Formalism.L2.Host.tauPl D τ)
    have hJ : (instOf D).J.map ((instOf D).φ (Formalism.L2.Host.tauPl D τ)) = gramAt D (D.sp.Y 0) τ := by
      show (Jv D).map (embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D τ))) = _
      rw [Equiv.symm_apply_apply]; rfl
    rw [hJ] at h0
    exact h0
  rw [← h]
  have h1 := Matrix.mul_nonsing_inv (frP D τ) (frP_unit D τ)
  have h2 : ((frP D τ)⁻¹)ᴴ * (frP D τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc _ (frP D τ), h1, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem exists_conj_intertwiner (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) (hmult : GlobalTheory.Dec.LowKMultOne)
    (hstrict : GlobalTheory.DSId.StrictLow) {D : D7} (I : AutInst) (hI : I = instOf D)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (n_eq : I.n = D.R.r)
    (eps_eq : ∀ v (i : Fin I.n), I.ε v i = epsS D.R (Fin.cast n_eq i))
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (lam_eq : ∀ v (i : Fin I.n), lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i))
    (ds : ∀ v, IsDS (I.ε v) (lam v) (σ v)) (low : ∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v))
    (N : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) :
    ∃ c : ∀ τ, N.H τ ≃ₗᵢ⋆[ℂ] H (pl.symm τ),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ m : Matrix (Fin I.n) (Fin I.n) ℂ,
        HEq m ((frP D τ)⁻¹ * g * frP D τ) → ∀ x, c τ (N.rep τ g x) = σ (pl.symm τ) m (c τ x)) ∧
      ∀ τ, (c τ).symm (w (pl.symm τ)) ∈ N.sm τ := by
  subst hI
  let M0 : DSModel (D.sp.Y 0) (parA (tparRec D) 0) :=
    { H := fun τ => H (pl.symm τ)
      σ := fun τ => σ (pl.symm τ)
      lam := fun τ => lam (pl.symm τ)
      ε := fun τ => (instOf D).ε (pl.symm τ)
      fr := fun τ => (frP D τ)⁻¹
      enum := fun τ => by
        have e1 : lam (pl.symm τ) = fun i => lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by rw [lam_eq, Equiv.apply_symm_apply]
        have e2 : (instOf D).ε (pl.symm τ) = fun i => epsS D.R (Fin.cast n_eq i) := funext fun i => eps_eq _ i
        rw [e1, e2]
        exact GlobalTheory.RowLev.isEnum_parA_zero D n_eq τ
      ds := fun τ => ds _
      fr_unit := fun τ => Matrix.isUnit_nonsing_inv_iff.mpr ((instOf D).P_unit _)
      fr_gram := fun τ => fr_gram D τ }
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M0
  obtain ⟨U, hUi⟩ := hU.exists_intertwiner (M := (M' : DSModel (D.sp.Y 0) (parB (tparRec D) 0))) (M' := N)
  have key : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ x,
      c τ (U τ (N.rep τ g x)) = M0.rep τ g (c τ (U τ x)) := by
    intro τ g hg x
    exact (congrArg (c τ) (hUi τ g hg x)).trans (hc τ g hg _)
  refine ⟨fun τ => (U τ).trans (c τ), ?_, ?_⟩
  · intro τ g hg m hm x
    have hm' : m = (frP D τ)⁻¹ * g * frP D τ := eq_of_heq hm
    show c τ (U τ (N.rep τ g x)) = σ (pl.symm τ) m (c τ (U τ x))
    rw [key τ g hg x, hm']
    show σ (pl.symm τ) ((frP D τ)⁻¹ * g * ((frP D τ)⁻¹)⁻¹) _ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ (frP_unit D τ)]
  · intro τ
    have hw : w (pl.symm τ) ∈ M0.sm τ := by
      obtain ⟨S, hS, hSle⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D _ _ M0 τ
      have hHC := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M0.enum τ).1 (M0.ds τ)
      have : CompleteSpace (H (pl.symm τ)) := (ds _).1
      have h1 := (hstrict _ _ _ hHC (H (pl.symm τ)) (σ (pl.symm τ)) (ds _)).1
      have h2 := hmult _ _ _ _ (σ (pl.symm τ)) hHC (ds _) _ _ h1 hS
      exact hSle (h2 ▸ (low _).2)
    set e := (U τ).trans (c τ) with he
    have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
        e.symm (M0.rep τ g y) = N.rep τ g (e.symm y) := by
      intro g hg y
      apply e.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      have := key τ g hg (e.symm y)
      change e (N.rep τ g (e.symm y)) = M0.rep τ g (e (e.symm y)) at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    exact GlobalTheory.ConjMult.span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit _ τ) e.symm hint hw

end Frame

theorem conjModel_of_setting : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  intro hcl D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod _hhost hιE
  obtain ⟨-, hreal, -⟩ := _root_.GlobalTheory.IotaReal.iotaX_real_finite R F X h hlev hgrp hmod hιE
  obtain ⟨-, -, -, -, hmult, -, hstrict⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hcl
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_of_classification hcl
  obtain ⟨c, hc1, hc2⟩ := exists_conj_intertwiner hU hmult hstrict X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ X.B.w
    X.B.lam X.lam_eq X.ds X.low (MP R)
  exact ⟨c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x, hc2⟩

end GlobalTheory.SeeInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal TensorProduct

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def term (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E) : ℂ :=
  res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G) 0

def phase (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) : ℂ :=
  ψ (symplO V W (isoPart V W C' (Matrix.map y (incA D))) (isoPart V W C κ))

def pairQ (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin W.rank) D.host.E :=
  D.host.xi0 • (adj D y * W.gram)

def ratPair (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) : ℝ :=
  ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * x)) : ℚ) : ℝ)

def dirAt (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin r) ℂ) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  z * (adj D C * V.gram).map (tauE D τ)

def derAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  ∑ τ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G

def finLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 0 1 : AF D.host.F) ⊗ₜ[D.host.F] e

end GlobalTheory.MixedTerm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwines
section
open scoped InnerProductSpace

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta
open GlobalTheory.SmoothGlob (lieSet)

namespace GlobalTheory.GKLie

theorem dRep_conj_Kset (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ) :
    ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H,
      Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v →
      Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  intro κ hκ X hX v hv
  have h1 : κᴴ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ.1
  have h2 : κ * κᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ.1
  have hu : IsUnit κ := IsUnit.of_mul_eq_one _ h2
  have hinv : κ⁻¹ * κ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det κ).1 hu)
  have hκU : κ ∈ UJset ε := by
    change κᴴ * Jm ε * κ = Jm ε
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, a * b ∈ UJset ε := fun a ha b hb => by
    change (a * b)ᴴ * Jm ε * (a * b) = Jm ε
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hb' : bᴴ * Jm ε * b = Jm ε := hb
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hb']
  have hE : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε := fun t =>
    GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t
  have hinvU : κ⁻¹ ∈ UJset ε := by
    have hκinv : κ⁻¹ = κᴴ := Matrix.inv_eq_left_inv h1
    rw [hκinv]
    change κᴴᴴ * Jm ε * κᴴ = Jm ε
    rw [Matrix.conjTranspose_conjTranspose, hκ.2, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hfun : (fun t : ℝ => ρ (NormedSpace.exp (t • (κ * X * κ⁻¹))) (ρ κ v)) =
      fun t : ℝ => ρ κ (ρ (NormedSpace.exp (t • X)) v) := by
    funext t
    have hc : NormedSpace.exp (t • (κ * X * κ⁻¹)) = κ * NormedSpace.exp (t • X) * κ⁻¹ := by
      rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
    rw [hc]
    have hA : κ * NormedSpace.exp (t • X) * κ⁻¹ ∈ UJset ε := hmul _ (hmul _ hκU _ (hE t)) _ hinvU
    rw [← ContinuousLinearMap.comp_apply, ← hρ.2 _ hA _ hκU, Matrix.mul_assoc _ κ⁻¹ κ, hinv, Matrix.mul_one,
      hρ.2 _ hκU _ (hE t), ContinuousLinearMap.comp_apply]
  unfold dRep
  rw [hfun]
  have hd := (differentiableAt_orbit hv hX).hasDerivAt
  have hL : HasFDerivAt (ρ κ) ((ρ κ).restrictScalars ℝ) (ρ (NormedSpace.exp ((0 : ℝ) • X)) v) :=
    ((ρ κ).restrictScalars ℝ).hasFDerivAt
  exact (hL.comp_hasDerivAt (0 : ℝ) hd).deriv

end GlobalTheory.GKLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfSEEofTT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.SeeIsoRow

variable {D : D7} {S : D.what₂.Tau → SPar}

theorem sEEofTT_apply {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    sEEofTT M μ 𝓕 E St Gd ι t c T = conjHH St Gd (hE.choose_spec.2.choose T) := by
  unfold sEEofTT
  simp only [dif_pos hE]
  rfl

theorem norm_sq_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re := by
  have h := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h
  rw [h]
  exact (hE.choose_spec.2.choose_spec T).2

theorem eq_zero_of_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E)
    (h : ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ = 0) : T = 0 := by
  have h1 := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h1
  have h2 : ‖hE.choose_spec.2.choose T‖ = 0 := h1.symm.trans h
  exact (LinearEquiv.map_eq_zero_iff _).1 (norm_eq_zero.1 h2)

theorem seeIso_row : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (hK : X.LevelSubgroupCharacter) (Zs : DefSub A3.fam3.amb3) (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX X)) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cS κS : ℝ) (uS : ℂ), R.toRealDat.IsModels → (R.toCx3 F).zs = Zs → F.Dc Zs = Dc → HEq (F.Sp Zs) (spOf (X := X) (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD pw bR) → HEq sEE sEEc → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS → ‖uS‖ = 1 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) ((uS * (κS : ℂ)) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩)) → (0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), ‖(κ' : ℂ) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖) → ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H), R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) → RealDat.nP F.lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)) → (R.toCx3 F).SEEIso sEE := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X Gd hK Zs Dc wdD pw bR sEE sEEc ι tS cS κS uS hM hzs hDc hSp hh hE _ hDef hK'
  subst hzs
  subst hDc
  have hSp' := eq_of_heq hSp
  have hHE := hM.HE
  have hle := (_root_.GlobalTheory.GoodRowsLevel.eeat_sub_principal R.toRealDat hM).1 (R.toRealDat.levR F.lv2 true)
  have key : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 = cS * ‖x‖ ^ 2 := by
    intro x hx
    rw [norm_sq_sEEofTT hE]
    congr 1
    show (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2
    rw [← hHE.2.2]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (Tw.out x)
  have hex : ∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖(κ' : ℂ) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖ := by
    by_cases hc : 0 < cS
    · have hsp : 0 < Real.sqrt cS := Real.sqrt_pos.2 hc
      refine ⟨(Real.sqrt cS)⁻¹, inv_pos.2 hsp, fun x hx => ?_⟩
      have h1 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = Real.sqrt cS * ‖x‖ := by
        rw [← pow_left_inj₀ (norm_nonneg _) (mul_nonneg hsp.le (norm_nonneg _)) two_ne_zero, key x hx, mul_pow,
          Real.sq_sqrt hc.le]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hsp).le, h1, ← mul_assoc,
        inv_mul_cancel₀ hsp.ne', one_mul]
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h2 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 ≤ 0 := by
        rw [key x hx]
        exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (sq_nonneg _)
      have h0 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = 0 :=
        pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
      have hT := eq_zero_of_sEEofTT hE _ h0
      have he0 : R.HE.e (Tw.out x) = 0 := congrArg Subtype.val hT
      have hx0 : Tw.out x = 0 := (map_eq_zero_iff _ hHE.1).1 he0
      rw [norm_smul, h0, mul_zero]
      show 0 = ‖Tw.out x‖
      rw [hx0, norm_zero]
  have hn := hK'.2 hex
  refine GlobalTheory.Mem.SJ.RowIso.clauses (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR (F.Sp (R.toCx3 F).zs)
    hSp' ((R.toCx3 F).EEl true) ((R.toCx3 F).nP true) sEE sEEc hh (fun e he => hn e he) (fun e he => ?_) ?_
  · refine (congrArg (fun y : Tw (twAt D.what₂.embLL A3.A.v0) (HHX X) =>
      ((Tw.out y : HHX X) : L2X X) ∈ goodSub X Gd) (hDef e he)).mpr ?_
    show (((uS * (κS : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out e), he⟩ : HHX X) : L2X X) ∈ goodSub X Gd
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    unfold sEEofTT
    rw [dif_pos hE]
    exact (mem_EEC X Gd _).1 (hE.choose_spec.2.choose _).2
  · refine (GlobalTheory.Mem.SJ.RowIso.finrank_of_evalTieT hE).trans ?_
    refine Eq.symm ((GlobalTheory.Mem.SJ.RowIso.finrank_twSub (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0)
      ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e)).trans ?_)
    refine GlobalTheory.Mem.SJ.RowIso.finrank_comap_of_le_range _ hHE.1 _ ?_
    rw [hHE.2.1]
    exact hle

end GlobalTheory.Twist.SeeIsoRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointMatrixHalfIdempotentSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (c : D.host.E) (x : WO S T), IsHalf (cA D e) x → adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  first | exact @GlobalTheory.AdjScalar.adjA_half_smul | exact GlobalTheory.AdjScalar.adjA_half_smul | (intros; apply GlobalTheory.AdjScalar.adjA_half_smul <;> assumption)
end

