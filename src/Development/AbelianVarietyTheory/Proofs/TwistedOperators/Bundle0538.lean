module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawPeriodNonvanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeEqDirectionalAddPhase
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

noncomputable section

open IsDedekindDomain

namespace GlobalTheory.HeisDerivFormula

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add (evIHom F) a b

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul (evIHom F) a b

theorem evI_dot {κ : Type} [Fintype κ] (v w : κ → AF F) :
    evI F (v ⬝ᵥ w) = (fun i => evI F (v i)) ⬝ᵥ fun i => evI F (w i) :=
  RingHom.map_dotProduct (evIHom F) v w

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t := by
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem snd_realAd (t : ℝ) : (realAd F t).2 = 0 := by simp [realAd]


variable (F) in
def ofInf (y : mixedEmbedding.mixedSpace F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evI_ofInf (y : mixedEmbedding.mixedSpace F) : evI F (ofInf F y) = y := by
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y

theorem snd_ofInf (y : mixedEmbedding.mixedSpace F) : (ofInf F y).2 = 0 := rfl


variable (F) in
def rInt (κ : Type) (z : κ → AF F) : ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1 (fun i => (z i).2)

theorem rInt_eq_one {κ : Type} (z : κ → AF F) (hz : ∀ i, (z i).2 = 0) : rInt F κ z = 1 := by
  unfold rInt
  rw [Set.indicator_of_mem]
  · rfl
  · intro i _ v
    show (z i).2 v ∈ v.adicCompletionIntegers F
    rw [hz i]
    show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem (v.adicCompletionIntegers F)

theorem rest_rInt {κ : Type} [Fintype κ] (g : SInf F κ) :
    Rest (evI F) (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (rInt F κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨g, _, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ, rfl⟩⟩
  have h2 : ∀ i, (z i).2 = 0 := by
    intro i
    let c : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
    have hc : evI F c = 0 := map_zero _
    have h3 : c * z i = 0 := congrFun (hz c hc) i
    have h4 := congrArg Prod.snd h3
    exact (one_mul _).symm.trans h4
  unfold rInt
  congr 1
  funext i
  show (x i).2 + (z i).2 = (x i).2
  rw [h2 i, add_zero]

theorem schr_line {κ : Type} [Fintype κ] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (g : SInf F κ) (a b : κ → AF F) (y : κ → mixedEmbedding.mixedSpace F) (t : ℝ) :
    GlobalTheory.WeilM.schr ψ (realAd F t • (a, b)) (tens (evI F) (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (rInt F κ))
      (fun i => ofInf F (y i)) =
    Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F (b i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i))) : ℝ) : ℂ)) *
      g (y + t • fun i => evI F (a i)) := by
  unfold GlobalTheory.WeilM.schr
  simp only [Prod.smul_fst, Prod.smul_snd]
  have hp : (fun i => ofInf F (y i)) ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b)) =
      realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))) := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  have hAt : At (evI F) (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))) := by
    intro c hc
    have hc1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hc
    have h0 : c * realAd F t = 0 := Prod.ext (by show c.1 * (realAd F t).1 = 0; rw [hc1, zero_mul])
      (by show c.2 * (realAd F t).2 = 0; rw [snd_realAd, mul_zero])
    rw [smul_eq_mul, ← mul_assoc, h0, zero_mul]
  have hy : (fun i => evI F (ofInf F (y i))) = y := funext fun i => evI_ofInf (y i)
  have he : evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))) =
      t • ((y ⬝ᵥ fun i => evI F (b i)) +
        t • (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i)))) := by
    rw [evI_mul, evI_add, evI_mul, evI_mul, evI_dot, evI_dot, hy, evI_realAd, Algebra.smul_def, Algebra.smul_def]
    ring
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))))) =
      t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F (b i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i))) := by
    rw [he, map_smul, map_add (f := _), map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hg : (fun i => evI F (((fun i => ofInf F (y i)) + realAd F t • a) i)) = y + t • fun i => evI F (a i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [evI_add, evI_mul, evI_realAd, evI_ofInf, Algebra.smul_def]
  have hr : rInt F κ ((fun i => ofInf F (y i)) + realAd F t • a) = 1 := by
    refine rInt_eq_one _ fun i => ?_
    show (0 : FiniteAdeleRing (𝓞 F) F) + (realAd F t).2 * (a i).2 = 0
    rw [snd_realAd, zero_mul, add_zero]
  rw [hp, hψ.2.2 _ hAt, htr]
  unfold tens
  rw [hg, hr, mul_one]

theorem heisLine_deriv_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evI F) u →
    ActsD (evI F) (M.heisLine ψ u) g h → ∀ (y : Fin n × Fin d → mixedEmbedding.mixedSpace F),
    h y = fderiv ℝ (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) y (fun i => evI F ((M.co.e u).1 i)) +
      (-(2 * Real.pi * Complex.I) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) : ℝ) : ℂ)) * g y := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ g h u _ hD y
  set A : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hA
  set TY : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) with hTY
  set TC : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (evI F ⅟(2 : AF F) * (A ⬝ᵥ fun i => evI F ((M.co.e u).2 i))) with hTC
  have h1 := hD (rInt F _) (rest_rInt g) (fun i => ofInf F (y i))
  have hfun : (fun t => M.heisLine ψ u t (tens (evI F) (g : _ → ℂ) (rInt F _)) (fun i => ofInf F (y i))) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * TY + t ^ 2 * TC : ℝ) : ℂ)) * g (y + t • A) := by
    funext t
    unfold Model.heisLine GlobalTheory.WeilM.Darboux.rho
    rw [LinearEquiv.map_smul]
    exact schr_line ψ hψ g _ _ y t
  have hval : tens (evI F) (h : _ → ℂ) (rInt F _) (fun i => ofInf F (y i)) = h y := by
    unfold tens
    rw [rInt_eq_one _ fun i => snd_ofInf (y i), mul_one]
    congr 1
    exact funext fun i => evI_ofInf (y i)
  have hL : HasDerivAt (fun t : ℝ => t * TY + t ^ 2 * TC) TY 0 := by
    have h2 := ((hasDerivAt_id' (0 : ℝ)).mul_const TY).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const TC)
    exact h2.congr_deriv (by simp)
  have hE := (hL.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have hl : HasDerivAt (fun t : ℝ => y + t • A) A 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const A).const_add y
  have hG : HasDerivAt (fun t : ℝ => g (y + t • A)) (fderiv ℝ (g : _ → ℂ) y A) 0 :=
    (g.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq 0 hl (by simp)
  have hder := hE.mul hG
  rw [hfun] at h1
  have := h1.unique hder
  rw [hval] at this
  rw [this]
  simp
  ring

end GlobalTheory.HeisDerivFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitary
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

namespace GlobalTheory.RealLieFock

theorem lie_deriv_pol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol ψ τ,
          (∃ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁) ∧
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ
  choose T hT' using fun t : ℝ => _root_.GlobalTheory.ArchFactorPair.exists_archOperator_pair F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe
    (γ (Multiplicative.ofAdd t)) (hγ.2 _)
  have hvac : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : M.Pol ψ τ ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, _root_.GlobalTheory.GaussLinePair.smooth_vacuum_line F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h,
        _root_.GlobalTheory.HeisOrbitReal.orbit_heis_real F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  intro f hf
  obtain ⟨-, -, f', hf', hd⟩ := hPN hf
  have hA : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f' := by
    intro r hr x
    have h1 : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r :=
      fun t => hT' t f r hr
    simp only [h1]
    exact (hd _).mul_const (r x)
  refine ⟨⟨f', hA⟩, fun f₁ h₁ => ?_⟩
  have e : f₁ = f' := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ f').2.2.1 _ h₁ hA
  rw [e]; exact hf'

end GlobalTheory.RealLieFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRung
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.AscBottom

variable {D : D7}

theorem rapidDec_star {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun γ hγ g => by simp [Pi.star_apply, h1 γ hγ g], h2.star, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  exact ⟨C, fun g => by simpa [Pi.star_apply, norm_star] using hC g⟩

theorem rung0 (hF : FockTot) : Rung0 := by
  intro D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h
  have hm : 0 < D.R.m := by omega
  obtain ⟨hom, homC, -, hev, hdep, hdn, hpart, -, -, -⟩ := _root_.GlobalTheory.Asc.conjRead_holds D hq T L μ0 hL sc G W M hM 0 hm
  obtain ⟨hchT, hchS⟩ := hev ⟨0, rfl⟩
  obtain ⟨hrap, hch⟩ := hΨ
  obtain ⟨f, hf, hΨ0⟩ := hch 0 hm
  have hhf := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vT : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hhf.1, hhf.2⟩
  let ρ₀ : G.RealVec := fun _ => 0
  let Φ₀ : G.Datum := fun _ => default
  have hu' : RapidDec (Yc D 0) (star u) := rapidDec_star (hu ρ₀ Φ₀ 0 (Nat.zero_le _))
  have hφ : RapidDec (G.V (.core 1)) (star (Ψ 1)) := rapidDec_star (hrap 1 (by omega))

  set a := G.ch.chi (D.R.m - 0) with ha
  have homR : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta) (omRow W 0) := by
    have := hom
    rwa [hchS, hchT] at this
  have homX : IsWeilDatumO W.ψ _ _ a⁻¹ (a⁻¹ * L.eta * L.eta⁻¹) (omCore W 0) := by
    rw [mul_inv_cancel_right]; exact homC
  have hHeta : IsHeckeChar D L.eta := by
    have := GlobalTheory.HeckeCharsOfSquare.isHeckeChar_mul (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homR.hecS) homR.hecT
    rwa [inv_inv, mul_inv_cancel_left] at this
  have hReta : ResEta D L.eta (negSp F.Lz).rank := by
    have h1 := Formalism.L2.Theta.resEta_mul (Formalism.L2.Theta.resEta_inv homC.resT) homR.resT
    rw [inv_inv, mul_inv_cancel_left] at h1
    refine Formalism.L2.Theta.resEta_parity h1 ?_
    have hr : (G.V (.grid 0 0)).rank + 1 = (G.V (.core 0)).rank := by
      have := F.oz.rank_add; rw [F.rk] at this; exact this
    show _ = F.Lz.rank % 2
    rw [F.rk]
    omega
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.core 1)) (negSp F.Lz) W.ψ a⁻¹⁻¹ L.eta W.ψ_std
    (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv homX.hecS) hHeta (Formalism.L2.Theta.resEta_inv homX.resS) hReta

  have hΞ : VacG W.ψ _ _ (latCore G 0) (star f) := (hdep f).1 hf
  have hlift : liftT (omCore W 0) (v 1).μ (v 1).𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := by
    rw [hΨ0]; exact (hdn v f (Ψ 1)).symm
  have hint : (∫ x in vT.𝓕, liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) (F.oz.emb (x, 1)) *
      star u x ∂vT.μ) ≠ 0 := by
    have e : (fun x : GA D (Yc D 0) => liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f)
        (F.oz.emb (x, 1)) * star u x) = fun x => (starRingEnd ℂ) (Ψ 0 (stabilizerEmbedding G.sp.dec0 x) * u x) := by
      funext x
      have hl : liftT (omCore W 0) (F.jac v 0 h).v0.μ (F.jac v 0 h).v0.𝓕 (star (Ψ 1)) (star f) = star (Ψ 0) := hlift
      rw [hl, hE.bot x, map_mul]; rfl
    rw [e, integral_conj]
    intro h0
    apply hper
    have := congrArg (starRingEnd ℂ) h0
    rw [Complex.conj_conj, map_zero] at this
    exact this
  obtain ⟨Φ', Φz, hΦ', hΦz, hne⟩ := _root_.GlobalTheory.LastSeesaw.upLast D W.ψ (F.jac v 0 h) (G.V (.core 0)) (Yc D 0) F.Lz F.oz (latRow G 0) (ΓL 0)
    (latCore G 0) F.rk (hG.last h) (F.ζ 0) a⁻¹ (a⁻¹ * L.eta) L.eta (omRow W 0) (omCore W 0) omz homR homX homz vT
    (star (Ψ 1)) (star u) hφ hu' (star f) hΞ hint

  let ℓ : (WO (G.V (.grid 1 0)) (G.V (.grid 0 0)) → ℂ) → ℂ := fun Φ =>
    (F.jac v 0 h).per W.ψ (F.ζ 0) omz (star (Ψ 1)) (liftS (omRow W 0) vT.μ vT.𝓕 (star u) Φ) Φz
  have hT : Tame W.ψ _ _ ℓ :=
    (_root_.GlobalTheory.LiftTame.lift_periods_tame D W.ψ (Yc D 0) vT (star u) hu').2 0 (F.jac v 0 h) a⁻¹ (a⁻¹ * L.eta) (omRow W 0) homR (negSp F.Lz)
      (F.ζ 0) a⁻¹⁻¹ L.eta omz homz (star (Ψ 1)) Φz hφ hΦz.1
  have hK : ∃ κ P, ℓ (star (W.fock (.chi 0 0) (W.cosVec 0 κ) P)) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hne (hF D hq T L μ0 hL sc G W M hM ⟨0, hm⟩ ℓ hT hno Φ' hΦ')
  obtain ⟨κ, P, hκP⟩ := hK
  let ρ : G.RealVec := Function.update ρ₀ ⟨0, hm⟩ P
  let Φ : G.Datum := Function.update Φ₀ ⟨0, hm⟩ κ
  refine ⟨a⁻¹⁻¹, omz, homz, ρ, Φ, Φz, hΦz, ?_⟩
  have hp := hpart ρ Φ u
  have hd : W.datum ρ Φ ⟨0, hm⟩ = W.fock (.chi 0 0) (W.cosVec 0 κ) P := by
    show W.fock (.chi 0 0) (W.cosVec 0 (Φ ⟨0, hm⟩)) (ρ ⟨0, hm⟩) = _
    simp only [ρ, Φ, Function.update_self]
  rw [hd] at hp
  change ℓ _ ≠ 0 at hκP
  convert hκP using 2
  exact hp

end GlobalTheory.AscBottom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormJets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.NFJetProof

theorem exists_nf_of_finite (E : Set ℂ) (hE : E.Finite) (hA : ∀ z ∈ E, IsAlgebraic ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ E ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite E := hE.to_subtype
  refine ⟨IntermediateField.adjoin ℚ E, IntermediateField.finiteDimensional_adjoin fun z hz => (hA z hz).isIntegral,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ E hz⟩, rfl⟩⟩

def dset {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) : Set (PureDat G t) :=
  {d | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}

end GlobalTheory.NFJetProof

namespace GlobalTheory.NFJetProof

theorem jetCl_of_choice {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (hI : GlobalTheory.NormSum.Inp D) (hok : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hD : GlobalTheory.SumSize.DictAt ch) : InNF fun _ σ => JetCl σ ch.S.toGridChoice := by
  have hok' : ∀ t Φ, ch.S.SumOK t Φ := fun t Φ => by
    obtain ⟨a, rfl⟩ := _root_.GlobalTheory.ChoiceSurjectivity.choice_phi_surj large₂ F hS ch hch Φ
    exact hok t a
  haveI : Finite T := hS.fin
  haveI : Finite ch.G.Datum := Finite.of_surjective ch.Phi fun Φ => _root_.GlobalTheory.ChoiceSurjectivity.choice_phi_surj large₂ F hS ch hch Φ
  set S := ch.S.toGridChoice with hSdef
  let E : Set ℂ := ⋃ t, ⋃ Φ, ⋃ β ∈ S.supp t Φ, ⋃ d ∈ dset S t Φ β (expDepth S t Φ β), ⋃ c : S.Classes t Φ β,
    ((⋃ j : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.1 j) (S.ptTop c j) (S.ptTop c (j + 1)) a b}) ∪
      (⋃ i : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.2 i) (S.ptRow c i) (S.ptRow c (i + 1)) a b}))
  have hE : E.Finite := by
    refine Set.finite_iUnion fun t => Set.finite_iUnion fun Φ => Set.Finite.biUnion (hok' t Φ).fin fun β _ =>
      Set.Finite.biUnion (_root_.GlobalTheory.RowTest.CosetFin.finite_pureDat_of_depth S t Φ β _) fun d _ => ?_
    haveI := (hok' t Φ).cls β
    exact Set.finite_iUnion fun c => Set.Finite.union
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
  have hA : ∀ z ∈ E, IsAlgebraic ℚ z := by
    intro z hz
    simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop] at hz
    obtain ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hdτ⟩, c, h⟩ := hz
    obtain ⟨hk, hexp, hcos⟩ := hτ
    obtain ⟨e, -, hP, -⟩ := id hexp
    have hw := (hok' t Φ).wts
    have hv := (hok' t Φ).vec β τ hexp d hdτ
    rcases h with ⟨j, a, b, rfl⟩ | ⟨i, a, b, rfl⟩
    · exact _root_.GlobalTheory.KernelAlg.kk_isAlgebraic large₂ F hS ch hch hI hD t (.top t j) (show (j : ℕ) + 1 ≤ D.R.m from j.2) (hw j j.2).1 _ (d.1 j) hk
        ((hcos d hdτ).1 j) ((hP d hdτ).1 j).2.2 ((hP d hdτ).1 j).1 (hv.1 j) _ _ a b
    · exact _root_.GlobalTheory.KernelAlg.kk_isAlgebraic large₂ F hS ch hch hI hD t (.chi i D.R.m) (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨i.2, rfl⟩) (hw i i.2).2 _
        (d.2 i) hk ((hcos d hdτ).2 i) ((hP d hdτ).2 i).2.2 ((hP d hdτ).2 i).1 (hv.2 i) _ _ a b
  obtain ⟨M, hM, hsub⟩ := exists_nf_of_finite E hE hA
  refine ⟨M, hM, fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hsub ?_, fun i a b => hsub ?_⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inl ⟨j, a, b, rfl⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inr ⟨i, a, b, rfl⟩⟩

theorem nfJet_holds : SumOKK → (∀ D, GlobalTheory.NormSum.Inp D) → (Big fun ch => GlobalTheory.SumSize.DictAt ch) → NFJet := by
  intro h1 h2 h3
  obtain ⟨C, hC⟩ := Big.and h1 h3
  refine ⟨C, fun ε CF hCF => ?_⟩
  obtain ⟨x, hx⟩ := hC ε CF hCF
  exact ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    jetCl_of_choice large₂ F hS ch hch (h2 D) (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).1
      (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).2⟩

end GlobalTheory.NFJetProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

theorem kkVec_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (c • f) x y = c • kkVec S p f x y := by
  intro D T L sc G W U S p c f x y
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  have hT : jetTab W S.N.frC p (c • f) (x * S.N.u _) (y * S.N.u _) =
      c • jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _) := by
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, Pi.smul_apply, smul_eq_mul,
      GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_smul]
  have h := (GlobalTheory.JetIdentity.jetOpL (K := ℂ) (wt G p.small) (wt G p.big) (nuEnd G p)).map_smul c
    (jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _))
  simp only [GlobalTheory.JetIdentity.jetOpL, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply] at h
  rw [hT, h, smul_comm]

end GlobalTheory.TopZeroInv
end
end

