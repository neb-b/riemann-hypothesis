module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspForm
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
namespace GlobalTheory.Core.Rk.NegOrbit
open GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

variable {D : D7} (V : HSp D)

def IsNeg (x : GA D (dblSp V)) : Prop := ¬ ∃ δ ∈ GQ V, x * (io V (δ, 1))⁻¹ ∈ siegel V

variable {V}

theorem isNeg_siegel_mul {p x : GA D (dblSp V)} (hp : p ∈ siegel V) : IsNeg V (p * x) ↔ IsNeg V x := by
  unfold IsNeg
  refine not_congr ⟨fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩, fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩⟩
  · have := (siegel V).mul_mem ((siegel V).inv_mem hp) h
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using (siegel V).mul_mem hp h

theorem isNeg_mul_io {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) → IsNeg V x := by
  intro h ⟨δ, hδ, hx⟩
  refine h ⟨γ₂⁻¹ * δ * γ₁, (GQ V).mul_mem ((GQ V).mul_mem ((GQ V).inv_mem h₂) hδ) h₁, ?_⟩
  have e : x * io V (γ₁, γ₂) * (io V (γ₂⁻¹ * δ * γ₁, 1))⁻¹ = x * (io V (δ, 1))⁻¹ * io V (γ₂, γ₂) := by
    simp only [mul_assoc, ← map_inv, ← map_mul]
    congr 2
    ext <;> simp [mul_assoc]
  rw [e]
  exact (siegel V).mul_mem hx ((io_mem_siegel V).2 rfl)

theorem isNeg_mul_io_iff {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) ↔ IsNeg V x := by
  refine ⟨isNeg_mul_io h₁ h₂, fun h => isNeg_mul_io ((GQ V).inv_mem h₁) ((GQ V).inv_mem h₂) ?_⟩
  have e : ((γ₁, γ₂) * (γ₁⁻¹, γ₂⁻¹) : GA D V × GA D V) = 1 := by ext <;> simp
  rw [mul_assoc, ← map_mul, e, map_one, mul_one]
  exact h

theorem exists_out_rmul (q : SiegelCosets V) (g : GQ (dblSp V)) : ∃ p ∈ siegelQ V,
    (((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) = p * (q.out : GQ (dblSp V)) * g := by
  have e : mk ((siegel V).subgroupOf (GQ (dblSp V))) (q.out * g) = mk _ (rmul _ g q).out :=
    ((rmul_mk g q.out).symm.trans (congrArg (rmul _ g) (Quotient.out_eq q))).trans (Quotient.out_eq _).symm
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  refine ⟨((p : GQ (dblSp V)) : GA D (dblSp V)), ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩, ?_⟩
  rw [← hp]
  simp [mul_assoc]

theorem isNeg_out_rmul_iff (q : SiegelCosets V) {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V ((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q).out : GQ (dblSp V)) ↔ IsNeg V (q.out : GQ (dblSp V)) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩
  rw [e, mul_assoc, isNeg_siegel_mul hp.1]
  exact isNeg_mul_io_iff h₁ h₂

theorem apply_out_rmul {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) (q : SiegelCosets V) (g : GQ (dblSp V)) (y : GA D (dblSp V)) :
    φ ((((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ ((q.out : GQ (dblSp V)) * g * y) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q g
  rw [e, mul_assoc, mul_assoc, apply_siegelQ_mul V a hμ hφ hp, mul_assoc]

abbrev NegCosets (V : HSp D) : Type := {q : SiegelCosets V // IsNeg V (q.out : GQ (dblSp V))}

def ioEquiv {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) : NegCosets V ≃ NegCosets V where
  toFun q := ⟨rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1, (isNeg_out_rmul_iff q.1 h₁ h₂).2 q.2⟩
  invFun q := ⟨rmul _ ⟨io V (γ₁⁻¹, γ₂⁻¹), io_mem_GQ V (inv_mem h₁) (inv_mem h₂)⟩ q.1,
    (isNeg_out_rmul_iff q.1 (inv_mem h₁) (inv_mem h₂)).2 q.2⟩
  left_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))
  right_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))

def negAction (V : HSp D) : MulAction (GQ V) (NegCosets V) where
  smul δ q := ioEquiv (inv_mem δ.2) (one_mem (GQ V)) q
  one_smul q := Subtype.ext (by
    show rmul _ _ q.1 = q.1
    convert rmul_one q.1 using 2
    ext1; simp; exact map_one (io V))
  mul_smul δ₁ δ₂ q := Subtype.ext (by
    show rmul _ _ q.1 = rmul _ _ (rmul _ _ q.1)
    rw [← rmul_mul]
    congr 1
    ext1; simp [← map_mul])

attribute [local instance] negAction

@[simp] theorem io_one_one : io V (1, 1) = 1 := map_one (io V)

theorem smul_val (δ : GQ V) (q : NegCosets V) : (δ • q).1 =
    rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ q.1 := rfl

theorem mem_map_stabilizer_iff (y : NegCosets V) (x : GA D V) :
    x ∈ (MulAction.stabilizer (GQ V) y).map (GQ V).subtype ↔
      x ∈ GQ V ∧ ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ siegel V := by
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨δ.2, ?_⟩
    obtain ⟨p, hp, e⟩ := exists_out_rmul y.1 ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩
    have hv : rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ y.1 = y.1 :=
      (smul_val δ y).symm.trans (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hδ))
    rw [hv] at e
    have e' : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) =
        p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) := e
    have h' : p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) * io V ((δ : GA D V), 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ = p := by
      rw [mul_assoc (p * _), ← map_mul]
      simp [io_one_one]
    rw [← e'] at h'
    rw [Subgroup.coe_subtype, h']
    exact hp.1
  · rintro ⟨hx, hs⟩
    refine ⟨⟨x, hx⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext ?_), rfl⟩
    rw [smul_val]
    conv_lhs => rw [← Quotient.out_eq y.1]
    have hr : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ GQ (dblSp V) :=
      mul_mem (mul_mem (y.1.out).2 (io_mem_GQ V hx (one_mem _))) (inv_mem (y.1.out).2)
    refine ((rmul_mk _ _).trans (mk_eq_iff.2 ⟨⟨⟨_, hr⟩, Subgroup.mem_subgroupOf.2 hs⟩, ?_⟩)).trans (Quotient.out_eq _)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left, ← map_mul]
    simp [io_one_one]

theorem leftInv_negIntegrand {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) {f₁ f₂ : GA D V → ℂ} (hf₁ : LeftInv (GQ V) f₁)
    (hf₂ : LeftInv (GQ V) f₂) : LeftInv ((GQ V).prod (GQ V))
      (dblIntegrand V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h₁, h₂⟩ ⟨g₁, g₂⟩
  have hE : (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) =
      ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂)) := by
    refine (tsum_congr fun q => ?_).trans ((ioEquiv h₁ h₂).tsum_eq
      (fun q : NegCosets V => φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))))
    show _ = φ ((((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1).out : GQ (dblSp V)) : GA D (dblSp V)) *
      io V (g₁, g₂))
    rw [apply_out_rmul hμ hφ, map_mul, mul_assoc]
  show (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) *
      conj (f₁ (γ₁ * g₁)) * f₂ (γ₂ * g₂) * (μ (detA V (γ₂ * g₂)) : ℂ)⁻¹ =
    (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))) *
      conj (f₁ g₁) * f₂ g₂ * (μ (detA V g₂) : ℂ)⁻¹
  rw [hE, hf₁ γ₁ h₁, hf₂ γ₂ h₂, map_mul, map_mul, apply_detA hμ h₂, one_mul]

theorem integral_neg_eq_zero : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = 0 := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hc
  haveI := hm
  show ∫ x, dblIntegrandQ V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x
    ∂(autMeasure V m).prod (autMeasure V m) = 0
  set E : GA D (dblSp V) → ℂ := fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)
    with hEdef
  by_cases hI : Integrable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m))
  swap
  · exact integral_undef hI
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_negIntegrand hμ hφ h₁.1 h₂.1
  have hconv : DblConv V μ m E f₁ f₂ := ⟨hli, hI⟩
  have h𝓕 : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V)
  obtain ⟨hint, heq⟩ := hconv.dblInt_eq h𝓕
  refine (heq : dblInt V μ m E f₁ f₂ = _).trans ?_
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  rw [← Measure.prod_restrict, integral_prod_symm _ hint]
  have hφc : Continuous φ := hφ.2.1
  have hcont : ∀ q : SiegelCosets V, Continuous
      (dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂) := fun q =>
    continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous h₂.continuous
  set G : SiegelCosets V → GA D V × GA D V → ENNReal := fun q x =>
    ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ with hGdef
  have hGm : ∀ q, Measurable (G q) := fun q => (hcont q).measurable.enorm
  have hfin := (GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 h𝓕
  rw [← Measure.prod_restrict, ← lintegral_tsum fun q => (hGm q).aemeasurable,
    lintegral_prod_symm _ (Measurable.tsum hGm).aemeasurable] at hfin
  have hae := ae_lt_top (Measurable.tsum hGm).lintegral_prod_left' hfin
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with g₂ hg₂
  set Φ : NegCosets V → GA D V → ℂ := fun y h =>
    dblIntegrand V μ (fun x => φ (((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ (h, g₂) with hΦdef
  have hpt : ∀ g₁, dblIntegrand V μ E f₁ f₂ (g₁, g₂) = ∑' y, Φ y g₁ := fun g₁ => by
    simp only [hΦdef, dblIntegrand, hEdef]
    rw [← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right]
  have hΦm : ∀ y, Measurable (Φ y) := fun y =>
    ((hcont y.1).comp (continuous_id.prodMk continuous_const)).measurable
  have hsum : ∑' y, ∫⁻ h, ‖Φ y h‖ₑ ∂(m.restrict 𝓕) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hg₂.ne ?_
    have hl := lintegral_tsum (μ := m.restrict 𝓕) (f := fun q h => G q (h, g₂))
      fun q => ((hGm q).comp measurable_prodMk_right).aemeasurable
    rw [hl]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun q => ∫⁻ h, G q (h, g₂) ∂(m.restrict 𝓕))
  rw [integral_congr_ae (.of_forall hpt), integral_tsum (fun y => (hΦm y).aestronglyMeasurable) hsum]
  refine GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero (GA D V) m (GQ V) (NegCosets V) 𝓕 h𝓕 Φ hΦm ?_ hsum ?_
  · intro γ y h
    have e : io V ((γ : GA D V)⁻¹, 1) * io V (γ * h, g₂) = io V (h, g₂) := by
      rw [← map_mul]; simp
    simp only [hΦdef, dblIntegrand]
    rw [h₁.1 _ γ.2, smul_val, apply_out_rmul hμ hφ, mul_assoc _ _ (io V _)]
    erw [e]
  · intro y 𝓖 h𝓖 hi
    exact _root_.GlobalTheory.DblOrbit.integral_eq_zero_of_not_open D V a μ hμ s φ hφ _ (y.1.out).2 y.2 f₁ f₂ h₁.continuous h₂.continuous h₁.1 hc g₂ _
      (mem_map_stabilizer_iff y) m hm 𝓖 h𝓖 hi

end GlobalTheory.Core.Rk.NegOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqualIdentificationPairPriceLeSixFifths
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section
namespace GlobalTheory.Core.Deg

theorem exp_le_inv_one_sub_pg (x : ℝ) (hx1 : x < 1) : Real.exp x * (1 - x) ≤ 1 := by
  have h := Real.add_one_le_exp (-x)
  have hp := Real.exp_pos x
  have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem one_factor_sharp (k b g : ℝ) (f : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hg : (k * b) ^ 8 ≤ g) (hf : (f : ℝ) ≤ k) :
    (1 + 3 / g) ^ f ≤ Real.exp (3 / 256) := by
  have hb8 : (256 : ℝ) ≤ b ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb 8
    norm_num at this ⊢; linarith
  have hk8 : k ≤ k ^ 8 := le_self_pow₀ hk (by norm_num)
  have hkb : 256 * k ≤ (k * b) ^ 8 := by
    rw [mul_pow]
    have : 256 * k ≤ k ^ 8 * 256 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb8 (by positivity : (0 : ℝ) ≤ k ^ 8)]
  have hg0 : 0 < g := by nlinarith
  have hx : (f : ℝ) * (3 / g) ≤ 3 / 256 := by
    rw [mul_div_assoc', div_le_div_iff₀ hg0 (by norm_num)]
    nlinarith
  calc (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := by
        apply pow_le_pow_left₀ (by positivity)
        have := Real.add_one_le_exp (3 / g)
        linarith
    _ = Real.exp (f * (3 / g)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (3 / 256) := Real.exp_le_exp.2 hx

theorem exp_pair_le_six_fifths : Real.exp (3 / 256) * Real.exp (3 / 256) ≤ 6 / 5 := by
  rw [← Real.exp_add]
  have h := exp_le_inv_one_sub_pg (3 / 256 + 3 / 256) (by norm_num)
  have hp := Real.exp_pos (3 / 256 + 3 / 256 : ℝ)
  norm_num at h ⊢
  nlinarith

theorem pgC_le_six_fifths : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 6 / 5 := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' Formalism.L2.SG.Pf.splitPrimeLoc_holds
    Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := one_factor_sharp (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := one_factor_sharp (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (3 / 256) * Real.exp (3 / 256) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 6 / 5 := exp_pair_le_six_fifths

end GlobalTheory.Core.Deg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HalfInd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def wr (α : Frame p S n') (β : Frame p T n) : Matrix n n' k →+ WO S T where
  toFun x := (β.b * x * α.b').map p.sec
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]

theorem wr_apply (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) (i : Fin T.rank) (j : Fin S.rank) :
    wr α β x i j = p.sec ((β.b * x * α.b') i j) := rfl

theorem rd_eq (α : Frame p S n') (β : Frame p T n) (t : WO S T) :
    rd α β t = β.b' * (Matrix.map t p.pr : Matrix (Fin T.rank) (Fin S.rank) k) * α.b := rfl

theorem isHalf_wr (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : IsHalf p.e (wr α β x) := fun i j => by
  rw [wr_apply, ← p.sec_pr, p.pr_sec]

theorem wr_rd (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) : wr α β (rd α β t) = t := by
  ext i j
  rw [wr_apply, rd_eq, Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb',
    Matrix.mul_one, Matrix.map_apply, p.sec_pr, ht i j]


set_option maxHeartbeats 800000 in
theorem open_compact_sec (p : SplitPt D k) {LS : Lat S} {LT : Lat T} (hS : Submodule.IsFullLattice D.host.E LS)
    (hT : Submodule.IsFullLattice D.host.E LT) :
    IsOpen {y : Matrix (Fin T.rank) (Fin S.rank) k | y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} ∧
    IsCompact {y : Matrix (Fin T.rank) (Fin S.rank) k |
      y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.toIsLattice.fg hT.toIsLattice.fg
  obtain ⟨N, hN, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  let A : AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) k) :=
    (latO S T (LS : Set _) (LT : Set _) fun _ => True).comap p.sec.mapMatrix
  have hA : ∀ y, y ∈ A ↔ y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := fun _ => Iff.rfl
  have hO : ∀ a : k, a ∈ (𝒪[k]).toAddSubgroup ↔ finPart D (p.sec a) ∈ intAE D := p.int_iff
  have key := GlobalTheory.PlaceCoord.isOpen_isCompact_of_comm (𝒪[k]).toAddSubgroup
    (Valuation.isOpen_integer (v := valuation k)) (IsNonarchimedeanLocalField.isCompact_closedBall k 1) A hN hM
    (fun y hy => by
      have ht : IsHalf p.e (y.map p.sec : WO S T) := fun i j => by
        rw [Matrix.map_apply, ← p.sec_pr, p.pr_sec]
      have h1 : (N • y).map p.sec = N • y.map p.sec := Matrix.ext fun i j => map_nsmul p.sec N (y i j)
      rw [hA, h1]
      exact hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) ht) fun i j =>
        GlobalTheory.PlaceCoord.toEAf_mem ((hO _).1 (hy i j)))
    (fun y hy i j => by
      have h1 : p.sec ((M : k) * y i j) = (M : AE D) * p.sec (y i j) := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      rw [hO, h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ ((hA y).1 hy) i j)
  exact key

theorem exists_idem (p : SplitPt D k) : ∃ ε, IsPlaceIdem D p.v ε ∧ algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
  obtain ⟨ε, hε, h⟩ := p.above
  exact ⟨ε, hε, by rw [← h, add_mul, p.split.1, mul_comm, p.split.2.1, add_zero]⟩

theorem compact_open (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) :
    IsCompact {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} ∧
      IsOpen {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} := by
  obtain ⟨ε, hε, heε⟩ := exists_idem p
  have hh : ∀ x, wr α β x ∈ GlobalTheory.PlaceModel.half S T p.e := fun x => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (isHalf_wr α β x)
  obtain ⟨ho, hc⟩ := open_compact_sec p (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S LS hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T LT hT)
  have h1 : {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} =
      {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h.1, fun h => ⟨?_, isHalf_wr α β x⟩⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h).1
    rwa [(GlobalTheory.PlaceModel.mem_half S T).1 (hh x)] at h2
  rw [h1]
  refine ⟨?_, ho.preimage (f := fun x : Matrix n n' k => β.b * x * α.b')
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)⟩
  convert hc.image (f := fun y => β.b' * y * α.b)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) using 1
  ext x
  refine ⟨fun h => ⟨β.b * x * α.b', h, ?_⟩, ?_⟩
  · beta_reduce
    rw [Matrix.mul_assoc β.b, ← Matrix.mul_assoc β.b', β.b'b, Matrix.one_mul, Matrix.mul_assoc, α.b'b, Matrix.mul_one]
  · rintro ⟨y, hy, rfl⟩
    change (β.b * (β.b' * y * α.b) * α.b').map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
    rwa [Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb', Matrix.mul_one]

theorem exists_SB_extFun_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ Ψ : Matrix n n' k → ℂ, Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix n n' k) ∧ extFun α β Ψ = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT
  have := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨hc, ho⟩ := compact_open α β hS hT
  refine ⟨fun x => halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (wr α β x), ?_, ?_⟩
  · unfold halfInd
    convert GlobalTheory.FinPl.Comm.ite_mem_SB hc ho
  · funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      beta_reduce
      rw [wr_rd α β ht]
    · rw [if_neg ht, halfInd, if_neg fun h => ht h.2]

end GlobalTheory.FinPl.HalfInd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem frameLat_isSelfDualC {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [h]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

end GlobalTheory.Core.Rk.IP
end

