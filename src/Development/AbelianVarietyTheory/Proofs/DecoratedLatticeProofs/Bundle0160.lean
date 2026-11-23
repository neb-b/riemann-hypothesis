module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0283
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionOnAdelicFunctionsEqZeroOfNoLift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := by
  intro w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  exact (GlobalTheory.SmoothCyclic.sm_eq M τ).ge (h.2.2.1 w hw)

theorem tprod_eq_zero_of_kFin_off (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) (hΛ : SepCont M Λ)
    (h0 : ∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) (s : Finset D.what₂.Tau) :
    ∀ v : M.Vec, (∀ τ, τ ∉ s → IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)) → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  induction s using Finset.induction_on with
  | empty => exact fun v hv => h0 v fun τ => hv τ (Finset.notMem_empty τ)
  | insert a s ha ih =>
    intro v hv
    obtain ⟨ℓ, hℓ, hℓv⟩ := hΛ a v
    have hk : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M a, ℓ w = 0 := by
      intro w hw
      rw [hℓv ⟨w, kFin_le_sm hHC M a hw⟩]
      refine ih _ fun τ hτ => ?_
      by_cases e : τ = a
      · subst e
        rw [Function.update_self]
        exact hw
      · rw [Function.update_of_ne e]
        exact hv τ (by simp [e, hτ])
    have := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D V S M a ℓ hℓ hk (v a) (v a).2
    rw [hℓv (v a), Function.update_eq_self] at this
    exact this

theorem eq_zero_of_sepCont : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ), SepCont M Λ → (∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) → Λ = 0 := by
  intro hHC D V S M Λ hΛ h0
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
  exact tprod_eq_zero_of_kFin_off hHC M Λ hΛ h0 Finset.univ v fun τ hτ => absurd (Finset.mem_univ τ) hτ

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

def Good (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (F : GA D (D.sp.Y 0) → ℂ) : Prop :=
  Continuous F ∧ (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) ∧ (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, F (γ * g) = F g) ∧
    (∀ k ∈ J, ∀ g, F (g * k) = χ k * F g)

theorem good_add {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F G : GA D (D.sp.Y 0) → ℂ}
    (hF : Good J χ F) (hG : Good J χ G) : Good J χ (F + G) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  obtain ⟨c2, ⟨C2, b2⟩, l2, r2⟩ := hG
  refine ⟨c1.add c2, ⟨C1 + C2, fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))⟩,
    fun γ hγ g => by simp [l1 γ hγ g, l2 γ hγ g], fun k hk g => by simp [r1 k hk g, r2 k hk g, mul_add]⟩

theorem good_smul {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F : GA D (D.sp.Y 0) → ℂ} (c : ℂ)
    (hF : Good J χ F) : Good J χ (c • F) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  refine ⟨continuous_const.mul c1, ⟨‖c‖ * C1, fun g => ?_⟩, fun γ hγ g => by simp [l1 γ hγ g],
    fun k hk g => by simp [r1 k hk g]; ring⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)

theorem good_of_mem (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar}
    {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ}
    {T : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)} (hT : T ∈ MultT θ M J χ) (x : SmT M) : Good J χ (T x) := by
  have h1 := (GlobalTheory.MultMem.mem_mult_iff D θ _ S M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul]
    refine good_smul c ?_
    have e : T (PiTensorProduct.tprod ℂ v) = (PiTensorProduct.lift.symm T) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    exact ⟨(h1.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h1.aut v) (h1.cusp v), (h1.aut v).left,
      fun k hk g => h1.lev v k hk g⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact good_add ha hb

end GlobalTheory.Core.Mi.TranslatedRow

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

theorem castGA_symm_mem' {I I' : Formalism.MainNotions.S.AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

theorem rat_of_GF (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ : X.B.I.GA) (hγ : γ ∈ X.B.I.GFset) : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
  refine (Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_
  show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact castGA_symm_mem' _ γ hγ

theorem rowFun_of_good (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t : GA D (D.sp.Y 0)} (hm : Matches X h J χ t)
    {F : GA D (D.sp.Y 0) → ℂ} (hF : Good J χ F) : RowFun X (evS X h t F) := by
  obtain ⟨hc, ⟨C, hb⟩, hl, hr⟩ := hF
  refine ⟨hc.comp ((iotaX X h).symm.continuous.mul continuous_const), ⟨C, fun x => hb _⟩, fun γ hγ x => ?_,
    fun k hk x => ?_⟩
  · show F ((iotaX X h).symm (γ * x) * t) = F ((iotaX X h).symm x * t)
    rw [map_mul, mul_assoc]
    exact hl _ (rat_of_GF X h γ hγ) _
  · show F ((iotaX X h).symm (x * (1, k)) * t) = star (X.chi2 k) * F ((iotaX X h).symm x * t)
    set κ := t⁻¹ * (iotaX X h).symm (1, k) * t with hκ
    have hc1 := hm.2 κ
    have e1 : t⁻¹⁻¹ * κ * t⁻¹ = (iotaX X h).symm (1, k) := by simp [hκ, mul_assoc]
    rw [e1] at hc1
    have hrow : (iotaX X h).symm (1, k) ∈ rowJ X h := by
      simp only [rowJ, Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply, Set.mem_setOf_eq]
      exact ⟨trivial, hk⟩
    have hκJ : κ ∈ J := hc1.1.2 hrow
    have hχ := hc1.2 hκJ
    have e2 : (iotaX X h).symm (x * (1, k)) * t = ((iotaX X h).symm x * t) * κ := by
      simp [hκ, map_mul, mul_assoc]
    have e3 : rowChi X h ((iotaX X h).symm (1, k)) = star (X.chi2 k) := by
      simp only [rowChi, ContinuousMulEquiv.apply_symm_apply]
    rw [e2, hr κ hκJ, ← hχ, e3]

theorem muX_finite (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : IsFiniteMeasure (muX X) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact (GlobalTheory.AdelicVol.vol_finite_pos X.B.I X.B.μf X.B.fund X.B.fund_spec).1

end GlobalTheory.Core.Mi.TranslatedRow


open GlobalTheory.Core.Mi.TranslatedRow in
theorem GlobalTheory.Core.Mi.rowFun_evS : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), IsInfFam θ → Matches X h J χ t → ∀ T ∈ MultT θ M J χ, ∀ x : SmT M, RowFun X (evS X h t (T x)) ∧ MemLp (evS X h t (T x)) 2 (muX X) := by
  intro hP D X h θ S M J χ t hθ hm T hT x
  have hg := good_of_mem hP hθ hT x
  have hR := rowFun_of_good X h hm hg
  refine ⟨hR, ?_⟩
  haveI := muX_finite X
  obtain ⟨C, hC⟩ := hR.bdd
  exact MemLp.of_bound hR.cont.aestronglyMeasurable C (.of_forall hC)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjOfBForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.UpInjScal

theorem exists_lvals {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hsc : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R) (t : T) (c : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.EigSys D)
    (hne : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c ≠ ⊥) :
    ∃ z : Fin D.R.m → ℝ, (∀ i, 0 < z i) ∧ ∀ i, IsLval R i t c (z i) := by
  obtain ⟨κ, -, hs⟩ := hsc
  obtain ⟨⟨B, hB⟩, hall⟩ := hs t c hne
  obtain ⟨hstep, htop⟩ := hall B hB
  have h : ∀ i : Fin D.R.m, ∃ l, GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsLValue R t B ((i : ℕ) + 1) l := by
    intro i
    by_cases hi : (i : ℕ) + 1 < D.R.m
    · obtain ⟨l, hl, -⟩ := hstep i hi
      exact ⟨l, hl⟩
    · have e : (i : ℕ) + 1 = D.R.m := by omega
      obtain ⟨l, hl, -⟩ := htop
      exact ⟨l, by rw [e]; exact hl⟩
  choose z hz using h
  exact ⟨z, fun i => (hz i).2.1, fun i => ⟨B, hB, hz i⟩⟩

end GlobalTheory.Core.Rk.UpInjScal


open GlobalTheory.Hk3 in
theorem GlobalTheory.Core.Rk.upInj_of_bForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF → UpInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI hsc SF hSF hB
  obtain ⟨κ₀, hκ₀, hE⟩ := hB
  have hM := hC.models
  have hs : ∀ (t : T) (c : Eig D), ∃ s : ℝ, 0 < s ∧ ∀ x ∈ EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((s : ℝ) : ℂ) • x := by
    intro t c
    by_cases hne : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c = ⊥
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h1 : R.HE.e x ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c :=
        (GlobalTheory.ChainScalar.mem_rowPart (R := R) hM.HE).1 (GlobalTheory.ChainScalar.eec_le (R := R) hSF t c hM.HE hx)
      rw [hne, Submodule.mem_bot] at h1
      have hx0 : x = 0 := hM.HE.1 (h1.trans (LinearMap.map_zero _).symm)
      subst hx0
      exact ((congrArg (R.Th t) (LinearMap.map_zero _)).trans (LinearMap.map_zero _)).trans (smul_zero _).symm
    · have hz0 : ∃ z : Fin D.R.m → ℝ, (∀ i, 0 < z i) ∧ ∀ i, IsLval R i t c (z i) :=
        GlobalTheory.Core.Rk.UpInjScal.exists_lvals (T := T) R hsc t c hne
      obtain ⟨z, hz, hl⟩ := hz0
      exact ⟨κ₀ * ∏ i, z i, mul_pos hκ₀ (Finset.prod_pos fun i _ => hz i), hE t c z hl⟩
  intro t
  choose s hs0 hsE using hs t
  refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
  obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c) (fun c => ((s c : ℝ) : ℂ))
    (fun c => Complex.ofReal_ne_zero.2 (hs0 c).ne') (fun c x hx => hsE c x hx) ?_ h0
  rw [hsp]; trivial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightTieTrueCols
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem weightTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), DelNat (I.rec7 l Z) → ∀ u : B.Word, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (numDatumOfParameters (I.rec7 l Z) L) (X := B.fields) (Pr := B.primes X) B.wts (plRec (I.rec7 l Z)) u (codeRec L u) := by
  intro B X I _ l Z L hD u
  obtain ⟨n, hn⟩ := hD
  have hfl : ((⌊(I.rec7 l Z).s.Del⌋₊ : ℕ) : ℚ) = (I.rec7 l Z).s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨B.wts_isOk, fun z => ?_, fun z => ⟨?_, fun i => ?_⟩⟩
  · exact GlobalTheory.ColumnNormCompare.mem_tops_rec (I.rec7 l Z) z
  · exact B.wts_isOk.hc_row u _
  · change ((I.rec7 l Z).hcW u (plRec (I.rec7 l Z) z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < (I.rec7 l Z).R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < (I.rec7 l Z).R.k
    · rw [dite_eq_left h]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk : k < (I.rec7 l Z).R.k - 2 := by omega
      have a := (I.rec7 l Z).s.u_letter u (plRec (I.rec7 l Z) z) k hk
      have hv := (I.rec7 l Z).hcW_v u (plRec (I.rec7 l Z) z)
      rw [a, hv, ← hfl]
      rfl
    · rw [dite_eq_right h]
      by_cases h0 : i = 0
      · subst h0
        exact (I.rec7 l Z).hcW_first u _ hi'
      · have h1 : i = (I.rec7 l Z).R.k - 1 := by omega
        subst h1
        exact (I.rec7 l Z).hcW_last u _ (by omega)

end GlobalTheory.CoreHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem coef_zero_of_heis_relations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ (g : GA D S) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), ∑ i, a i • heisO ψ S T (y i) F = F → ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F = 0 → ∫ w in X, om (g, 1) F w * conj (F w) ∂m = 0 := by
  intro D ψ S T χS χT om hw m X hm F hF g n a y h1 h2
  have hψ := hw.std
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have laws := fun {u v : WO S T → ℂ} (hu : IsThetaFunO ψ S T u) (hv : IsThetaFunO ψ S T v) =>
    GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T m X hψ hm u v hu hv
  have hG : IsThetaFunO ψ S T (om (g, 1) F) := hw.om_pres _ F hF

  have key : ∀ i, (∫ x in X, om (g, 1) F x * conj (heisO ψ S T (y i) F x) ∂m) =
      ∫ x in X, om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m := by
    intro i
    have hact : actO S T g 1 (actO S T g⁻¹ 1 (-(y i))) = -(y i) := by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))
      rwa [inv_one] at this
    rw [hw.om_heis g 1 _ F hF, hact]
    have := ((laws hG hF).2.2.2.2.2.2.1 (-(y i))).2
    rw [neg_neg] at this
    exact this.symm
  have hpt : ∀ x, om (g, 1) F x * conj (F x) =
      ∑ i, conj (a i) * (om (g, 1) F x * conj (heisO ψ S T (y i) F x)) := by
    intro x
    have e := congrFun h1 x
    rw [Finset.sum_apply] at e
    conv_lhs => rw [← e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have hz : ∀ x, om (g, 1) (∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) =
      ∑ i, conj (a i) * (om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x)) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  calc (∫ x in X, om (g, 1) F x * conj (F x) ∂m)
      = ∫ x in X, ∑ i, conj (a i) * (om (g, 1) F x * conj (heisO ψ S T (y i) F x)) ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ i, conj (a i) * ∫ x in X, om (g, 1) F x * conj (heisO ψ S T (y i) F x) ∂m := by
        rw [integral_finsetSum _ (fun i _ => ((laws hG (hth _ F hF)).1).const_mul _)]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = ∑ i, conj (a i) * ∫ x in X, om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m :=
        Finset.sum_congr rfl fun i _ => by rw [key i]
    _ = ∫ x in X, ∑ i, conj (a i) * (om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x)) ∂m := by
        rw [integral_finsetSum _ (fun i _ => ((laws (hw.om_pres _ _ (hth _ F hF)) hF).1).const_mul _)]
        exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
    _ = ∫ x in X, om (g, 1) (∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hz x).symm)
    _ = 0 := by simp [h2]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.SupThetaGrowth

theorem om_sup_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (height S g * height T h) ^ A := by
  intro D ψ S T χS χT om hom f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨N, hN⟩ := GlobalTheory.WeilWordGrowth.om_pointwise D ψ S T χS χT om hom θ hθ
  obtain ⟨c, -, hc⟩ := hN f hf
  exact ⟨c, N, hc⟩

end GlobalTheory.SupThetaGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartan
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.CartanFockDeg

theorem om_annih_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (sS : RealMat S) (sT : RealMat T)
    (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (k : GA D S)
    (hk : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (k, 1) (annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z f) =
      annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) (om (k, 1) f) := by
  have hψ := hW.std
  have hm1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T (1 : GA D T)) = 1 := by
    rw [hm1]
    exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)
  have hinv : compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
    have a := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k
    have b : compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
      have := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k⁻¹
      rwa [inv_inv] at this
    calc compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ
        = compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ * (compAt θ τ (Formalism.L2.Theta.mt S k) * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) := by
          rw [a, Matrix.mul_one]
      _ = compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * (compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ) * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
          rw [hk τ]; simp only [Matrix.mul_assoc]
      _ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
          rw [← Matrix.mul_assoc, b, Matrix.one_mul]
  have hJ : cplxO (sS τ) (sT τ) (z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) =
      cplxO (sS τ) (sT τ) z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
    unfold cplxO
    rw [Matrix.smul_mul]
    simp only [Matrix.mul_assoc, hinv]
  have e : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, compAt θ τ (Formalism.L2.Theta.mt T (1 : GA D T)) * w * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) =
      w * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := fun w => by rw [h1, Matrix.one_mul]
  unfold annih
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hW hθ k 1 τ z hf, GlobalTheory.OrientedHeis.om_dRho hW hθ k 1 τ _ hf, e, e, hJ]

theorem om_keeps_fockDeg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ k : GA D S, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ (N : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0) → ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) = 0 := by
  intro D ψ θ S T χS χT om sS sT hW hθ k hk N f hf hl l hlen
  have hψ := hW.std
  have hth : ∀ (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ}, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
    intro l g hg
    induction l with
    | nil => exact hg
    | cons p l ih => exact GlobalTheory.FockIndep.annih_theta hψ hθ p.1 _ p.2 ih
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ),
      om (k, 1) (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f) =
        (l.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k⁻¹))).foldr
          (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih =>
      rw [List.foldr_cons, List.map_cons, List.foldr_cons, om_annih_move sS sT hW hθ k hk p.1 p.2 (hth l hf), ih]
  let l' := l.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k))
  have hl' : l = l'.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k⁻¹)) := by
    simp only [l', List.map_map]
    conv_lhs => rw [← List.map_id l]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, id_eq, Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  rw [hl', ← key, hl l' (by simp [l', hlen]), map_zero]

end GlobalTheory.CartanFockDeg
end

