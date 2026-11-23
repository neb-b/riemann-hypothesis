module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerAbsOfCuspRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem kerAbs_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, KerAbs D := by
  intro hP D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  have hfinV := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V νV 𝓗 hS.haarV hS.fdV
  refine ⟨hfinV.ne, fun f hf φ hφ hc => ?_⟩
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hf
  obtain ⟨μ', 𝓕', hμ'⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  have hb := (hC χV χW om hS.weil μ' 𝓕' hμ' f hl).2
  set s := (GlobalTheory.Size.sobO ψ θ μ' 𝓕' d f).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V (fun τ => hS.posDef (tauE D τ))
  obtain ⟨M₀, hM₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  set M := max M₀ 1 with hMdef
  have hM : ∀ c ∈ K, GlobalTheory.Grow.height V c ≤ M := fun c hc => (hM₀ c hc).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := zero_le_one.trans (le_max_right _ _)

  have hunif : ∀ h g, ‖thetaKO om h g f‖ ≤ C * s * M ^ A * GlobalTheory.Grow.height W g ^ A := by
    intro h g
    obtain ⟨γ, hγ, c, hc', rfl⟩ := hcov h
    rw [GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hS.weil hf g γ hγ c]
    calc ‖thetaKO om c g f‖ ≤ C * s * (GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g) ^ A := hb c g
      _ = C * s * GlobalTheory.Grow.height V c ^ A * GlobalTheory.Grow.height W g ^ A := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (GlobalTheory.Grow.height_pos V c).le (hM c hc') A) (mul_nonneg hC0 hs0))
            (pow_nonneg (GlobalTheory.Grow.height_pos W g).le A)
  have hR := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  obtain ⟨B0, hB0⟩ := hR.decay A
  have hq : ∀ h g, ‖star (thetaKO om h g f)‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A := by
    intro h g
    rw [norm_star]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO om h g f)
      (GlobalTheory.Chain.LiftConv.thetaKO_left hS.weil hf h) (hunif h) g
  have hfinW := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W νW 𝓖 hS.haarW hS.fdW
  refine ⟨C * s * M ^ A * 2 ^ A * B0 * νW.real 𝓖, fun h => ⟨?_, ?_⟩⟩
  · exact hR.integrableOn_mul_of_le hS.haarW hS.fdW
      (GlobalTheory.Chain.LiftConv.thetaKO_continuous hS.weil hf h).star.aestronglyMeasurable (hq h)
  · refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const hfinW fun g _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have h1 := hq h g
    rw [norm_star] at h1
    have hK0 : 0 ≤ C * s * M ^ A * 2 ^ A := by positivity
    calc ‖thetaKO om h g f‖ * ‖φ g‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A * ‖φ g‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * s * M ^ A * 2 ^ A * (‖φ g‖ * GlobalTheory.Grow.quotHeight W g ^ A) := by ring
      _ ≤ C * s * M ^ A * 2 ^ A * B0 := mul_le_mul_of_nonneg_left (hB0 g) hK0

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem representation_inv_mul_apply_cancel_left {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H)
    (v : W) : ρ (γ * h)⁻¹ (ρ γ v) = ρ h⁻¹ v := by
  rw [← Module.End.mul_apply, ← map_mul]; congr 2; group

theorem representation_inv_mul_smul_one_of_trivial_right {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (h κ : H)
    (hκ : ρ κ⁻¹ = 1) (c : ℂ) (v : W) : ρ (h * κ)⁻¹ (c • ρ 1 v) = c • ρ h⁻¹ v := by
  rw [map_one, Module.End.one_apply, map_smul, _root_.mul_inv_rev, map_mul, hκ, one_mul]

theorem extV_law (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    (R.HV i t).e y (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
      ((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ) • (R.cV i).ρ γ ((R.HV i t).e y x) := by
  have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ _
  exact (SetLike.ext_iff.mp (hM.HV i t).2.1 ((R.HV i t).e y)).mp h1 γ x k

theorem extV_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (γ * h) = R.extV i t y h := by
  have hx : (finHom (Vc D i)).rangeRestrict (γ * h) = Formalism.IndefR.Bridge.ratF (Vc D i) ⟨γ, hγ⟩ *
      (finHom (Vc D i)).rangeRestrict h * ((1 : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [Formalism.IndefR.Bridge.ratF]
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h)) = (R.cV i).ρ γ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y ⟨γ, hγ⟩ ((finHom (Vc D i)).rangeRestrict h) 1
      _ = _ := by simp only [map_one, Units.val_one, one_smul]
  show (R.cV i).ρ (γ * h)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h))) =
    (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_apply_cancel_left _ γ h _

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (κ : GA D (Vc D i)) (hκ : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • R.extV i t y h := by
  let k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J := ⟨(finHom (Vc D i)).rangeRestrict κ, hκ.2⟩
  have hx : (finHom (Vc D i)).rangeRestrict (h * κ) = Formalism.IndefR.Bridge.ratF (Vc D i) 1 *
      (finHom (Vc D i)).rangeRestrict h * (k : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [k]
  have hχ : (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ := rfl
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • (R.cV i).ρ 1 ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y 1 ((finHom (Vc D i)).rangeRestrict h) k
      _ = _ := congrArg (· • _) hχ
  show (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ))) =
    _ • (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_smul_one_of_trivial_right _ h κ ((hM.cV i).1 _ ((GfC (Vc D i)).inv_mem hκ.1)) _ _

def compF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ) :
    GA D (Vc D i) → ℂ :=
  fun h => l (R.extV i t y h)

theorem compF_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (compF R i t y l) := by
  intro k hk h
  exact (congrArg l (extV_type R hM i t y k hk h)).trans (by rw [map_smul, smul_eq_mul]; rfl)

theorem compF_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    compF R i t y l (γ * h) = compF R i t y l h :=
  congrArg l (extV_left R hM i t y γ hγ h)

theorem theta_left (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hP : R.FullP)
    (φ : WO (Vc D i) (Wc D i) → ℂ) (hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ) (g : GA D (Wc D i))
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) (γ * h) g φ = thetaKO (R.ωP i t) h g φ := by
  have hm : ((γ * h, g) : GA D (Vc D i) × GA D (Wc D i)) = (γ, 1) * (h, g) := by rw [Prod.mk_mul_mk, one_mul]
  show R.ωP i t (γ * h, g) φ 0 = R.ωP i t (h, g) φ 0
  rw [hm, map_mul, Module.End.mul_apply]
  exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ φ hφ)

theorem theta_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (φ : WO (Vc D i) (Wc D i) → ℂ)
    (g : GA D (Wc D i)) (κ h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) φ) = thetaKO (R.ωP i t) (h * κ) g φ := by
  show R.ωP i t (h, g) (R.ωP i t (κ, 1) φ) 0 = R.ωP i t (h * κ, g) φ 0
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem theta_avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        thetaKO (R.ωP i t) (h * (κ j)⁻¹) g f := by
  rw [← Finset.sum_congr rfl fun j _ => congrArg (_ * ·) (theta_transl R i t f g (κ j)⁻¹ h)]
  show R.ωP i t (h, g) (avgW R i t PP a tr ε κ f) 0 = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [avgW, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem sum_compF_eq_zero (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (hNC : NoChi R i t y) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (ha : a ≠ 0) (tr : Bool) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (κ : G → GA D (Vc D i)) (hκ : IsLifts R i t κ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (h : GA D (Vc D i)) :
    ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      compF R i t y l (h * κ j) = 0 := by
  have h0 := congrFun (hNC PP a ha tr ε hε l) h
  refine Eq.trans ?_ h0
  simp only [gaL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = mirC R i PP a tr ε j * actG0 (Vc D i) (R.βV i) (R.datVt i t) (R.eG j) (compF R i t y l) h
  rw [level_action_spec (compF_type R hM i t y l) ⟨κ j, hκ j⟩ (κ j) (hκ j) h]
  ring

def termF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) : GA D (Vc D i) → ℂ :=
  fun h => thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h

theorem termF_eq (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) :
    (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ⁻¹, 1) f) * l (R.extV i t y h)) = termF R i t y l f g κ := by
  funext h
  exact congrArg (· * l (R.extV i t y h)) (theta_transl R i t f g κ⁻¹ h)

theorem termF_left (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.FullP) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f)
    (g : GA D (Wc D i)) (κ : GA D (Vc D i)) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    termF R i t y l f g κ (γ * h) = termF R i t y l f g κ h := by
  show thetaKO (R.ωP i t) (γ * h * κ⁻¹) g f * compF R i t y l (γ * h) =
    thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h
  rw [mul_assoc, theta_left R i t hP f hf g γ hγ, compF_left R hM i t y l γ hγ h]

theorem avgLaw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC PP a ha tr ε hε κ hκ f hf l g
  have hM := hG.core.models
  obtain ⟨hmeas, hfd⟩ := hM.νV i t
  haveI : (R.νV i t).IsHaarMeasure := hmeas.1
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hmeas.1
  have hu_int : ∀ j, IntegrableOn (termF R i t y l f g (κ j)) (R.fdV i t) (R.νV i t) := by
    intro j
    have h1 := _root_.GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand D G Pl0 T A Ks R F hG hP i t y (R.ωP i t ((κ j)⁻¹, 1) f) l g
      ((hP i t).datum.om_pres _ f hf)
    exact (congrArg (fun φ => IntegrableOn φ (R.fdV i t) (R.νV i t)) (termF_eq R i t y l f g (κ j))).mp h1
  have hv_int : ∀ j, IntegrableOn (fun h => termF R i t y l f g (κ j) (h * κ j)) (R.fdV i t) (R.νV i t) :=
    fun j => GlobalTheory.integrableOn_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h) (hu_int j)
  have hsub : ∀ j, ∫ h in R.fdV i t, termF R i t y l f g (κ j) h ∂(R.νV i t) =
      ∫ h in R.fdV i t, termF R i t y l f g (κ j) (h * κ j) ∂(R.νV i t) :=
    fun j => (GlobalTheory.setIntegral_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h)).symm
  have hpt1 : ∀ h, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        termF R i t y l f g (κ j) h := by
    intro h
    rw [theta_avgW, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  have hpt2 : ∀ h, ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      termF R i t y l f g (κ j) (h * κ j) = 0 := by
    intro h
    have e : ∀ j, termF R i t y l f g (κ j) (h * κ j) = thetaKO (R.ωP i t) h g f * compF R i t y l (h * κ j) := by
      intro j
      show thetaKO (R.ωP i t) (h * κ j * (κ j)⁻¹) g f * _ = _
      rw [mul_inv_cancel_right]
    simp only [e]
    rw [← mul_zero (thetaKO (R.ωP i t) h g f), ← sum_compF_eq_zero R hM i t y hNC PP a ha tr ε hε κ hκ l h,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h ∂(R.νV i t) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1),
    integral_finsetSum _ fun j _ => (hu_int j).const_mul _]
  simp only [integral_const_mul]
  simp only [hsub]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun j _ => (hv_int j).const_mul _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt2)]
  exact integral_zero _ _

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearRelationSectionsSpanEq
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.KerBaseChange

theorem mem_span_of_sum_mul {F : Type} [Field F] (σ : F →+* ℂ) {κ J : Type} [Fintype κ]
    (α : κ → J → F) (z : κ → ℂ) (hz : ∀ j, ∑ k, z k * σ (α k j) = 0) :
    z ∈ Submodule.span ℂ ((fun c : κ → F => fun k => σ (c k)) '' {c | ∀ j, ∑ k, c k * α k j = 0}) := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hsm : ∀ (a : F) (x : ℂ), a • x = σ a * x := fun a x => by rw [Algebra.smul_def]; rfl
  let W : Submodule F ℂ := Submodule.span F (Set.range z)
  have hzW : ∀ k, z k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  haveI : FiniteDimensional F W := FiniteDimensional.span_of_finite F (Set.finite_range z)
  let ζ := Module.finBasis F W
  let β : κ → Fin (Module.finrank F W) → F := fun k m => ζ.repr ⟨z k, hzW k⟩ m
  have hzexp : ∀ k, z k = ∑ m, σ (β k m) * (ζ m : ℂ) := by
    intro k
    have h2 := congrArg Subtype.val (ζ.sum_repr ⟨z k, hzW k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hsm] at h2
    exact h2.symm
  have hlin : LinearIndependent F (fun m => (ζ m : ℂ)) :=
    ζ.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
  have hsol : ∀ m j, ∑ k, β k m * α k j = 0 := by
    intro m j
    have hs : ∑ m, (∑ k, β k m * α k j) • (ζ m : ℂ) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [hsm, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm, ← hz j]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hzexp k, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    exact (Fintype.linearIndependent_iff.1 hlin) _ hs m
  have hz2 : z = ∑ m, (ζ m : ℂ) • (fun k => σ (β k m)) := by
    funext k
    rw [hzexp k, Finset.sum_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hz2]
  exact Submodule.sum_mem _ fun m _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun k => β k m, hsol m, rfl⟩)

theorem mem_span_of_sum_smul {F V Y : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup Y] [Module ℂ Y]
    (σ : F →+* ℂ) (r : V →ₛₗ[σ] Y) (S : Submodule F V)
    (hI : ∀ (n : ℕ) (b : Fin n → V), (∀ i, b i ∈ S) → LinearIndependent F b →
      LinearIndependent ℂ (fun i => r (b i)))
    {κ ι : Type} [Fintype κ] [Fintype ι] (A : κ → ι → V) (hA : ∀ k i, A k i ∈ S)
    (z : κ → ℂ) (hz : ∀ i, ∑ k, z k • r (A k i) = 0) :
    z ∈ Submodule.span ℂ ((fun c : κ → F => fun k => σ (c k)) '' {c | ∀ i, ∑ k, c k • A k i = 0}) := by
  let V' : Submodule F V := Submodule.span F (Set.range fun p : κ × ι => A p.1 p.2)
  have hAV : ∀ k i, A k i ∈ V' := fun k i => Submodule.subset_span ⟨(k, i), rfl⟩
  have hV'S : V' ≤ S := Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hA p.1 p.2)
  haveI : FiniteDimensional F V' := FiniteDimensional.span_of_finite F (Set.finite_range _)
  let b := Module.finBasis F V'
  let bv : Fin (Module.finrank F V') → V := fun m => (b m : V)
  have hbS : ∀ m, bv m ∈ S := fun m => hV'S (b m).2
  have hbli : LinearIndependent F bv := b.linearIndependent.map' V'.subtype (Submodule.ker_subtype _)
  have hrli := hI _ bv hbS hbli
  let α : κ → ι × Fin (Module.finrank F V') → F := fun k p => b.repr ⟨A k p.1, hAV k p.1⟩ p.2
  have hAexp : ∀ k i, A k i = ∑ m, α k (i, m) • bv m := by
    intro k i
    have h2 := congrArg Subtype.val (b.sum_repr ⟨A k i, hAV k i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hz' : ∀ p : ι × Fin (Module.finrank F V'), ∑ k, z k * σ (α k p) = 0 := by
    rintro ⟨i, m⟩
    have h := hz i
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hAexp, map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul] at h
    rw [Finset.sum_comm] at h
    simp_rw [← Finset.sum_smul] at h
    exact (Fintype.linearIndependent_iff.1 hrli) _ h m
  refine Submodule.span_mono ?_ (mem_span_of_sum_mul σ α z hz')
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, fun i => ?_, rfl⟩
  simp_rw [hAexp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  exact Finset.sum_eq_zero fun m _ => by rw [hc (i, m), zero_smul]

end GlobalTheory.KerBaseChange

namespace GlobalTheory

theorem kerC_span_rat : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ), Formalism.L2.Pj.RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom w n → ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (A : κ → ι → Rul (T.Q.Xo j) T.Q.c), (∀ k i, A k i ∈ sec (T.Q.Xo j) T.Q.c w n) → ∀ z : κ → ℂ, (∀ i, ∑ k, z k • rdU (T.U j σ) (A k i) = 0) → z ∈ Submodule.span ℂ ((fun c : κ → T.Q.c.F => fun k => σ (c k)) '' {c | ∀ i, ∑ k, c k • A k i = 0}) := by
  intro D T j σ hI w n hd κ ι _ _ A hA z hz
  exact KerBaseChange.mem_span_of_sum_smul σ (rdU (T.U j σ)) (sec (T.Q.Xo j) T.Q.c w n) (hI w n hd) A hA z hz

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocationsDistinguishedByGenerics
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty

set_option synthInstance.maxHeartbeats 400000 in
theorem sameLoc_iff_heckeCong : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  intro D cf jE A M C tup big L hB j w i i' hi hi' x x'
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB

  have hiC : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (z : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a z = Sp.iotaC j w (Sp.phO j w a ha z) := by
    intro a ha z
    rw [← Sp.iotaC_coh j w a ha z]
    show ((L.Y.naut.iotaQC a).toRingHom.comp (L.Y.naut.iotaQ a)) (algebraMap _ _ z) = _
    rw [RingHom.comp_apply, Au.iotaQ, Au.iotaQC]
    rfl

  have key : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (y : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a y ∈ (A.pl.plB w).nonunits ↔ y ∈ IsLocalRing.maximalIdeal (L.X.nd.O a) := by
    intro a ha y
    have hw : L.X.nd.w a = w := ((L.X.nd.locs_mem j w a).1 ha).2
    subst hw
    obtain ⟨h, e⟩ := Au.kFbar a y
    rw [ValuationSubring.mem_nonunits_iff]
    have e1 : (A.pl.plB (L.X.nd.w a)).valuation (iotaO L.X.nd L.Y.naut a y) =
        (A.pl.plB (L.X.nd.w a)).valuation ((⟨_, h⟩ : A.pl.plB (L.X.nd.w a)) : ℂ) := rfl
    rw [e1, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff,
      ← IsLocalRing.residue_eq_zero_iff, ← map_eq_zero (L.Y.naut.kFbar a), ← e]
    simp only [EmbeddingLike.map_eq_zero_iff]

  have gen : ∀ v k, GenAt D (D.what₂.places.resChar w) (C.Q w) v k ↔
      GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
    intro v k; rw [Sp.Qc_eq]
  constructor
  · rintro rfl v k hvk
    have hvk' := (gen v k).1 hvk
    have e1 := Sp.ptX_hT j w i hi x v k hvk'
    have e2 := Sp.ptX_hT j w i hi' x' v k hvk'
    have hc : Formalism.L2.NCov.cls (Sp.ptX j w i hi x).1 = Formalism.L2.NCov.cls (Sp.ptX j w i hi' x').1 :=
      (Sp.ptX j w i hi x).2.1.trans (Sp.ptX j w i hi' x').2.1.symm
    generalize (Sp.ptX j w i hi x).1 = ψ at e1 hc
    generalize (Sp.ptX j w i hi' x').1 = ψ' at e2 hc
    generalize (⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk', rfl⟩⟩ : heckeAlg Sp.B j w) = t at e1 e2
    have hmem : t - algebraMap _ _ (ψ t) ∈ Formalism.L2.NCov.cls ψ' := by
      rw [← hc, Formalism.L2.NCov.cls, RingHom.mem_ker]
      change IsLocalRing.residue _ (ψ (t - algebraMap _ _ (ψ t))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
    rw [Formalism.L2.NCov.cls, RingHom.mem_ker] at hmem
    change IsLocalRing.residue _ (ψ' (t - algebraMap _ _ (ψ t))) = 0 at hmem
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_sub, sub_eq_zero, ← e1, ← e2] at hmem
    have r := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi).symm hmem
    simp only [RingEquiv.symm_apply_apply] at r
    rw [← map_sub]
    refine (key i hi _).2 ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, r, sub_self]
  · intro H
    apply Sp.mx_inj j w hi hi'
    rw [← (Sp.ptX j w i hi x).2.1, ← (Sp.ptX j w i' hi' x').2.1]
    refine GlobalTheory.PtLocalEig.cls_eq_of_residue _ _ _ ?_
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [← Sp.ptX_hT j w i hi x v k hvk, ← Sp.ptX_hT j w i' hi' x' v k hvk]
    have h1 := H v k ((gen v k).2 hvk)
    have hz : iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') =
        iotaO L.X.nd L.Y.naut i ((Sp.phO j w i hi).symm
          (Sp.phO j w i' hi' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x'))) := by
      rw [hiC i hi, hiC i' hi', RingEquiv.apply_symm_apply]
    rw [hz, ← map_sub, key i hi, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h1
    have h2 := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi) h1
    rwa [RingEquiv.apply_symm_apply] at h2

end GlobalTheory.CoefDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodTypes

theorem seriesConj_of_labTie : Green → ∀ (D : D7) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    GlobalTheory.GoodTypes.SeriesConj D :=
  fun hG D L hL k f hf =>
    GlobalTheory.GLq.GalSer.eSer_galois hG D ((eSerTie_iff D).2 ⟨L, hL⟩) starRingAut k f hf

end GlobalTheory.GoodTypes
end

