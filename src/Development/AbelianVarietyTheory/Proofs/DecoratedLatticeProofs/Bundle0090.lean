module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.ParCont

variable {D : D7} {m n : ℕ}

theorem eventually_close {P : Type} [TopologicalSpace P] (K : Mx D m n → P → ℂ) (hc : Continuous (Function.uncurry K))
    (hp : ∀ γ ∈ ratMx D m n, ∀ x p, K (γ + x) p = K x p) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∀ x, ‖K x p - K x p₀‖ ≤ ε := by
  obtain ⟨-, -, -, -, -, C, hC, hCc⟩ := lattice_Mx D m n
  have h : ∀ᶠ p in nhds p₀, ∀ x ∈ C, ‖K x p - K x p₀‖ < ε := by
    refine hC.eventually_forall_of_forall_eventually (P := fun p x => ‖K x p - K x p₀‖ < ε) fun y _ => ?_
    have h1 : Continuous fun z : P × Mx D m n => ‖K z.2 z.1 - K z.2 p₀‖ :=
      ((hc.comp (continuous_snd.prodMk continuous_fst)).sub
        (hc.comp (continuous_snd.prodMk continuous_const))).norm
    exact (isOpen_lt h1 continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [h] with p h x
  obtain ⟨γ, hγ, hx⟩ := hCc x
  rw [← hp γ hγ x p, ← hp γ hγ x p₀]
  exact (h _ hx).le

theorem isCovolOne_map {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕)
    (e : Mx D m n ≃+ Mx D m n) (he : Continuous e) (he' : Continuous e.symm)
    (hr : ∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n) :
    IsCovolOne (ratMx D m n) (μ.map e) (e '' 𝓕) ∧ MeasurableEmbedding e := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := h.1
  let f : Mx D m n ≃ₜ Mx D m n := { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  refine ⟨⟨e.isAddHaarMeasure_map μ he he', ?_, ?_⟩, hemb⟩
  · let g : ratMx D m n ≃ ratMx D m n :=
      { toFun := fun γ => ⟨e.symm γ, (hr _).1 (by rw [e.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨e γ, (hr _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine h.2.1.image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable.aemeasurable, ?_⟩
      have : (μ.map e).map e.symm = μ := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m n → Mx D m n) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add (f := _), e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective]
    exact h.2.2

theorem parCont : ∀ (D : D7) (m n : ℕ) (v : VolM D m n) (P : Type) [TopologicalSpace P] (K : Mx D m n → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ ratMx D m n, ∀ x p, K (γ + x) p = K x p) → (∀ p, IntegrableOn (fun x => K x p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ x in v.𝓕, K x p ∂v.μ) ∧ (∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ x, ‖K x p‖ ≤ C) ∧ ∀ (e : Mx D m n ≃+ Mx D m n), Continuous e → Continuous e.symm → (∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n) → ∀ p, ∫ x in v.𝓕, K (e x) p ∂v.μ = ∫ x in v.𝓕, K x p ∂v.μ := by
  intro D m n v P _ K hc hp
  have hx : ∀ p, Continuous fun x => K x p := fun p => hc.comp (continuous_id.prodMk continuous_const)
  have hi : ∀ p, IntegrableOn (fun x => K x p) v.𝓕 v.μ := fun p =>
    covolOne_integrableOn v.covol _ (hx p) fun γ hγ a => hp γ hγ a p
  refine ⟨hi, ?_, fun p₀ => ?_, fun e he he' hr p => ?_⟩
  · refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [eventually_close K hc hp p₀ (half_pos hε)] with p h
    rw [dist_eq_norm, ← integral_sub (hi p) (hi p₀)]
    have h1 : v.μ v.𝓕 = 1 := v.covol.2.2
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := v.μ) (s := v.𝓕) (f := fun x => K x p - K x p₀) (C := ε / 2)
      (by rw [h1]; exact ENNReal.one_lt_top) fun x _ => h x
    rw [Measure.real, h1, ENNReal.toReal_one, mul_one] at h2
    linarith
  · obtain ⟨-, -, -, -, -, C, hC, hCc⟩ := lattice_Mx D m n
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hx p₀).continuousOn
    refine ⟨B + 1, ?_⟩
    filter_upwards [eventually_close K hc hp p₀ one_pos] with p h x
    obtain ⟨γ, hγ, ha⟩ := hCc x
    have h1 : ‖K x p₀‖ ≤ B := by rw [← hp γ hγ x p₀]; exact hB _ ha
    calc ‖K x p‖ = ‖K x p₀ + (K x p - K x p₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖K x p₀‖ + ‖K x p - K x p₀‖ := norm_add_le _ _
      _ ≤ B + 1 := add_le_add h1 (h x)
  · obtain ⟨h1, hemb⟩ := isCovolOne_map v.covol e he he' hr
    rw [← covolOne_integral_eq v.covol h1 (fun x => K x p) fun γ hγ a => hp γ hγ a p,
      hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]

end GlobalTheory.Unf.ParCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.CocompactParam

theorem eventually_close {G P : Type*} [TopologicalSpace G] [TopologicalSpace P] (K : G → P → ℂ)
    (hK : Continuous (Function.uncurry K)) {C : Set G} (hC : IsCompact C) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∀ g ∈ C, ‖K g p - K g p₀‖ < ε := by
  refine hC.eventually_forall_of_forall_eventually (P := fun p g => ‖K g p - K g p₀‖ < ε) fun g _ => ?_
  have h1 : Continuous fun z : P × G => K z.2 z.1 := hK.comp (continuous_snd.prodMk continuous_fst)
  have h2 : Continuous fun z : P × G => K z.2 p₀ := hK.comp (continuous_snd.prodMk continuous_const)
  have hc : Continuous fun z : P × G => ‖K z.2 z.1 - K z.2 p₀‖ := (h1.sub h2).norm
  exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)

theorem continuous_setIntegral_of_unif {G P : Type*} [MeasurableSpace G] [TopologicalSpace P] (μ : Measure G)
    (𝓕 : Set G) (hfin : μ 𝓕 < ⊤) (K : G → P → ℂ) (hint : ∀ p, IntegrableOn (fun g => K g p) 𝓕 μ)
    (hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε) :
    Continuous fun p => ∫ g in 𝓕, K g p ∂μ := by
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have hδ : 0 < ε / (μ.real 𝓕 + 1) := by positivity
  filter_upwards [hcl p₀ _ hδ] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_setIntegral_le_of_norm_le_const hfin fun g _ => (hp g).le) ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

theorem continuous_integral_param : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ (v : Vol V) (P : Type) [TopologicalSpace P] (K : GA D V → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ GQ V, ∀ g p, K (γ * g) p = K g p) → (∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ g in v.𝓕, K g p ∂v.μ) ∧ ∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ g, ‖K g p‖ ≤ C := by
  intro D V hV v P _ K hK hinv
  obtain ⟨C, hC, hcov⟩ := hV
  have hcov' : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := fun h => by
    obtain ⟨γ, hγ, hc⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, γ * h, hc, by rw [inv_mul_cancel_left]⟩
  have hcont : ∀ p, Continuous fun g => K g p := fun p => hK.comp (continuous_id.prodMk continuous_const)
  have hint : ∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ := fun p =>
    GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov' _ (hcont p)
      fun γ hγ h => hinv γ hγ h p
  have hfin : v.μ v.𝓕 < ⊤ := by
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov'
      (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε := fun p₀ ε hε => by
    filter_upwards [eventually_close K hK hC p₀ hε] with p hp g
    obtain ⟨γ, hγ, hc⟩ := hcov g
    have := hp _ hc
    rwa [hinv γ hγ, hinv γ hγ] at this
  refine ⟨hint, continuous_setIntegral_of_unif v.μ v.𝓕 hfin K hint hcl, fun p₀ => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hcont p₀).continuousOn
  refine ⟨M + 1, ?_⟩
  filter_upwards [hcl p₀ 1 one_pos] with p hp g
  obtain ⟨γ, hγ, hc⟩ := hcov g
  have h0 := hM _ hc
  simp only [hinv γ hγ] at h0
  have := norm_sub_norm_le (K g p) (K g p₀)
  linarith [hp g]

end GlobalTheory.CocompactParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
section
namespace I195MixedCoordinates_18f638bfe5f22e80269acda3

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_18f638bfe5f22e80269acda3

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.EvalCont

def Tame {B Z : Type} [TopologicalSpace B] [TopologicalSpace Z] (F : B → Z → ℂ) : Prop :=
  Continuous (fun p : B × Z => F p.1 p.2) ∧ ∀ b₀, ∃ C : ℝ, ∀ᶠ b in nhds b₀, ∀ z, ‖F b z‖ ≤ C

section General

variable {B Z Z' Y : Type} [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace Z'] [TopologicalSpace Y]

theorem Tame.comp {F : B → Z → ℂ} (h : Tame F) {u : Z' → Z} (hu : Continuous u) : Tame fun b z => F b (u z) :=
  ⟨h.1.comp (continuous_fst.prodMk (hu.comp continuous_snd)), fun b₀ =>
    (h.2 b₀).imp fun _ hC => hC.mono fun _ hb z => hb (u z)⟩

theorem Tame.mul {F G : B → Z → ℂ} (h : Tame F) (h' : Tame G) : Tame fun b z => F b z * G b z := by
  refine ⟨h.1.mul h'.1, fun b₀ => ?_⟩
  obtain ⟨C, hC⟩ := h.2 b₀
  obtain ⟨C', hC'⟩ := h'.2 b₀
  refine ⟨C * C', (hC.and hC').mono fun b hb z => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hb.1 z) (hb.2 z) (norm_nonneg _) ((norm_nonneg _).trans (hb.1 z))

theorem tame_of_bounded {F : B → Z → ℂ} (hc : Continuous fun p : B × Z => F p.1 p.2) {C : ℝ} (hb : ∀ b z, ‖F b z‖ ≤ C) :
    Tame F := ⟨hc, fun _ => ⟨C, .of_forall hb⟩⟩

theorem Tame.integral [FirstCountableTopology B] [FirstCountableTopology Z] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) (s : Set Y) (hs : μ s < ⊤) {F : B → Z → Y → ℂ} (h : Tame fun b (q : Z × Y) => F b q.1 q.2) :
    Tame fun b z => ∫ y in s, F b z y ∂μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  refine ⟨continuous_iff_continuousAt.2 fun p₀ => ?_, fun b₀ => ?_⟩
  · obtain ⟨C, hC⟩ := h.2 p₀.1
    refine continuousAt_of_dominated (bound := fun _ => C) (.of_forall fun p => ?_) ?_ (integrable_const C)
      (.of_forall fun y => ?_)
    · exact (h.1.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)) :
        Continuous fun y => F p.1 p.2 y).aestronglyMeasurable
    · exact (continuous_fst.continuousAt.eventually hC).mono fun p hp => .of_forall fun y => hp (p.2, y)
    · exact (h.1.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)) :
        Continuous fun p : B × Z => F p.1 p.2 y).continuousAt
  · obtain ⟨C, hC⟩ := h.2 b₀
    exact ⟨C * (μ.restrict s).real Set.univ, hC.mono fun b hb z =>
      norm_integral_le_of_norm_le_const (.of_forall fun y => hb (z, y))⟩

theorem Tame.continuous_integral [FirstCountableTopology B] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) (s : Set Y) (hs : μ s < ⊤) {F : B → Y → ℂ} (h : Tame F) : Continuous fun b => ∫ y in s, F b y ∂μ :=
  (Tame.integral μ s hs (F := fun b (_ : Unit) y => F b y) (h.comp continuous_snd)).1.comp
    (continuous_id.prodMk (continuous_const (y := ())))

end General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem vol_lt_top {V : HSp D} (hV : CoCpt V) (v : Vol V) : v.μ v.𝓕 < ⊤ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, hc⟩ := hV
  have := v.haar
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) v.μ
  refine lt_of_le_of_lt (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers v.fund (.of_forall fun g => ?_))
    hK.measure_lt_top
  obtain ⟨γ, hγ, h⟩ := hc g
  exact ⟨⟨γ, hγ⟩, h⟩

theorem bounded_of_contAut {V : HSp D} (hV : CoCpt V) {φ : GA D V → ℂ} (hφ : IsContAut V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨K, hK, hc⟩ := hV
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.2.continuousOn
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hc g
  rw [← hφ.1 γ hγ g]
  exact hC _ h

theorem heisO_apply_zero (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) : heisO ψ S T w f 0 = f w := by
  simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

theorem om_rat {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (w : WO S T) : om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w) := by
  have e : actO S T γ γ' (actO S T γ⁻¹ γ'⁻¹ w) = w := by
    rw [actO_eq, actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      mt_mul_inv, Matrix.mul_one]
  rw [← heisO_apply_zero (ψ := ψ) S T w (om (γ, γ') f), ← heisO_apply_zero (ψ := ψ) S T _ f,
    ← hom.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf _), hom.om_heis _ _ _ _ hf, e]

theorem tame_om {S T A T₀ : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hA : CoCpt A) (hT : CoCpt T₀) (a : GA D A →* GA D S)
    (b : GA D T₀ →* GA D T) (ha : Continuous a) (hb : Continuous b) (ha' : ∀ γ ∈ GQ A, a γ ∈ GQ S)
    (hb' : ∀ γ ∈ GQ T₀, b γ ∈ GQ T) :
    Tame fun (h : GA D T) (q : (GA D A × GA D T₀) × WO S T) => om (a q.1.1, b q.1.2 * h) f q.2 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have hc : Continuous fun p : GA D T × (GA D A × GA D T₀) × WO S T => om (a p.2.1.1, b p.2.1.2 * p.1) f p.2.2 :=
    (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hf).comp
      (((ha.comp continuous_snd.fst.fst).prodMk ((hb.comp continuous_snd.fst.snd).mul continuous_fst)).prodMk
        continuous_snd.snd)
  refine ⟨hc, fun h₀ => ?_⟩
  obtain ⟨U, hU, hU'⟩ := exists_compact_mem_nhds h₀
  obtain ⟨KA, hKA, cA⟩ := hA
  obtain ⟨KT, hKT, cT⟩ := hT
  obtain ⟨-, -, -, -, -, K, hK, cK⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨C, hC⟩ := (hU.prod ((hKA.prod hKT).prod hK)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, Filter.mem_of_superset hU' fun h hh => ?_⟩
  rintro ⟨⟨g, g'⟩, w⟩
  obtain ⟨γ, hγ, hg⟩ := cA g
  obtain ⟨γ', hγ', hg'⟩ := cT g'
  have e : ((a g, b g' * h) : GA D S × GA D T) = (a γ⁻¹, b γ'⁻¹) * (a (γ * g), b (γ' * g') * h) := by
    rw [Prod.mk_mul_mk, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_left, inv_mul_cancel_left]
  have ht := hom.om_pres (a (γ * g), b (γ' * g') * h) f hf
  change ‖om (a g, b g' * h) f w‖ ≤ C
  rw [e, map_mul, Module.End.mul_apply, om_rat hom ht (ha' _ (inv_mem hγ)) (hb' _ (inv_mem hγ'))]
  obtain ⟨_, ⟨δ, rfl⟩, hδ⟩ := cK (actO S T (a γ⁻¹)⁻¹ (b γ'⁻¹)⁻¹ w)
  have h1 := hC (h, (γ * g, γ' * g'), _) ⟨hh, ⟨hg, hg'⟩, hδ⟩
  have h2 := congrArg norm (ht.quasi δ (actO S T (a γ⁻¹)⁻¹ (b γ'⁻¹)⁻¹ w))
  rw [norm_mul, hom.std.1.2.1, one_mul] at h2
  rw [← h2]
  exact h1

section Mixed

variable {B Z : Type} [TopologicalSpace B] [TopologicalSpace Z] [FirstCountableTopology B] [FirstCountableTopology Z]

theorem tame_mixS (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)
    (x : Mx D T.rank ρ) {F : B → Z → WO S T → ℂ} (h : Tame fun b (q : Z × WO S T) => F b q.1 q.2) :
    Tame fun b (q : Z × WO S₀ T) => (_root_.I195MixedCoordinates_18f638bfe5f22e80269acda3.source d) T ψ v.μ v.𝓕 (F b q.1) x q.2 := by
  obtain ⟨i1, -, i3, -⟩ := lattice_Mx D T.rank S₀.rank
  have : FirstCountableTopology (WO S₀ T) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  obtain ⟨j1, -⟩ := lattice_Mx D T.rank S.rank
  have : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  change Tame fun b (q : Z × WO S₀ T) => ∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T q.2) (F b q.1))) 0 ∂v.μ
  simp_rw [HypDec.integrandS_eq]
  refine Tame.integral v.μ v.𝓕 (by rw [v.covol.2.2]; exact ENNReal.one_lt_top) ?_
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have h0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
  refine Tame.mul (tame_of_bounded (C := 1) ?_ fun _ _ => (hψ.1.2.1 _).le) (h.comp
    (u := fun q : (Z × WO S₀ T) × Mx D T.rank ρ => (q.1.1, d.extY T q.2 + d.extX T x + d.ext0 T q.1.2)) ?_)
  · exact hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_snd.snd) continuous_const)
  · exact continuous_fst.fst.prodMk (((hY.comp continuous_snd).add continuous_const).add (h0.comp continuous_fst.snd))

end Mixed

section Step

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

theorem om_evalBF (hd : Descent D) (hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D) (hv : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D)
    {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (h₀ : GA D B.A) (h' : GA D J.W₀) :
    s.om₀ (B.o.emb (h₀, 1), h') (evalBF s Ψ) = evalBF s (s.om (embA B.d B.o h₀, J.d.emb0 h') Ψ) := by
  obtain ⟨om₁, h₁⟩ := (hd ψ _ _ _ _ _ s.weil).1 _ _ B.d
  have hS := hm.1 ψ _ _ _ _ B.d _ _ _ _ s.weil h₁ _ _ s.vS.covol
  have hT := hm.2 ψ _ _ _ _ J.d _ _ _ _ h₁ s.weil₀ _ _ s.vT.covol
  have hf := (hv ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol _ hΨ (xZero J.d)
  have ex : mt J.W (J.d.emb0 h')⁻¹ ⬝ xZero J.d = xZero J.d := by
    rw [← map_inv]; exact J.d.wittDecomp_anisotropicEmbedding_inclX _
  have ey : mt B.V₀ (B.o.emb (h₀, 1))⁻¹ ⬝ yZero B.V₀ ρ (vecB B.o B.ζ) = yZero B.V₀ ρ (vecB B.o B.ζ) := by
    rw [← map_inv, Prod.inv_mk, inv_one, yZero_vecB, ← Matrix.mul_assoc, B.o.emb_jB, mt_one, Matrix.mul_one]
  have e1 : ((embA B.d B.o h₀, J.d.emb0 h') : GA D B.V × GA D J.W) =
      (B.d.emb0 (B.o.emb (h₀, 1)), 1) * (1, J.d.emb0 h') := by
    rw [Prod.mk_mul_mk, mul_one, one_mul, embA_apply]
  have e2 : ((B.o.emb (h₀, 1), h') : GA D B.V₀ × GA D J.W₀) = (B.o.emb (h₀, 1), 1) * (1, h') := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  unfold evalBF evalZero evalAt
  simp only [e1, e2, map_mul, Module.End.mul_apply]
  change s.om₀ (B.o.emb (h₀, 1), 1) (s.om₀ (1, h')
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d B.V₀ ψ s.vT.μ s.vT.𝓕
      (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d))
      (yZero B.V₀ ρ (vecB B.o B.ζ)))) =
    _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d B.V₀ ψ s.vT.μ s.vT.𝓕
      (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕
        (s.om (B.d.emb0 (B.o.emb (h₀, 1)), 1) (s.om (1, J.d.emb0 h') Ψ)) (xZero J.d))
      (yZero B.V₀ ρ (vecB B.o B.ζ))
  rw [(hS _ (s.weil.om_pres _ _ hΨ)).core, (hS _ hΨ).target, ex, (hT _ (h₁.om_pres _ _ hf)).source, ey, (hT _ hf).core]

theorem firstCountable_GA (V : HSp D) : FirstCountableTopology (GA D V) :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _

theorem continuous_embL (B : BesLev D ρ) : Continuous fun h₀ : GA D B.A => B.o.emb (h₀, 1) :=
  B.o.continuous_emb.comp (continuous_id.prodMk continuous_const)

theorem continuous_mt_inv (V : HSp D) : Continuous fun g : GA D V => mt V g⁻¹ :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  (continuous_mt V).comp continuous_inv

theorem continuous_ptT {T T₀ : HSp D} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ) : Continuous (ptT d S y) :=
  continuous_const.matrix_mul ((continuous_mt_inv T).matrix_mul continuous_const)

theorem continuous_cenT {T T₀ : HSp D} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ) : Continuous (cenT d S y) :=
  GlobalTheory.OrientedHeis.continuous_symplOH continuous_const ((continuous_mt_inv T).matrix_mul continuous_const)

theorem continuous_psiFlag (hψ : Continuous ψ) {T T₀ : HSp D} (d : HypDec T T₀ ρ) : Continuous (psiFlag ψ d) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hb : Continuous (blockX d) := continuous_const.matrix_mul ((continuous_mt T).matrix_mul continuous_const)
  refine hψ.comp (ht.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_))
  split_ifs <;> first | exact hb.matrix_elem i j | exact continuous_const

end Step

end GlobalTheory.Unf.EvalCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSplitPartAgreeSupportedAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul (S : HSp D) (g g' : GA D S) : mt S (g * g') = mt S g * mt S g' := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem eq_of_parts {A : Type*} [CommRing A] {e f m m' o : A} (k1 : (e + f) * (m - o) = m - o)
    (k2 : (e + f) * (m' - o) = m' - o) (k3 : e * m = e * m') (k4 : f * m' = f * m) : m = m' := by
  linear_combination (-1 : A) * k1 + k2 + k3 - k4

theorem mt_unit (S : HSp D) (g : GA D S) :
    ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g = (HSpace.gram S).map (incA D) := g.2

theorem gram_mul_conj_inv (S : HSp D) (e : AE D) (g : GA D S) :
    (HSpace.gram S).map (incA D) * (cA D e • mt S g⁻¹) =
      ((e • mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
  have hu := mt_unit S g
  have h1 : mt S g * mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hmap : (e • mt S g).map (cA D) = cA D e • (mt S g).map (cA D) := by
    ext i j; simp [Matrix.map_apply, map_mul]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc (HSpace.gram S).map (incA D) * mt S g⁻¹
      = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g * mt S g⁻¹ := by rw [hu]
    _ = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
        rw [Matrix.mul_assoc _ (mt S g), h1, Matrix.mul_one]

theorem eq_of_split_part : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h →
    SuppAt e S h' → (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  intro D S e h h' _ hs hs' hee
  have hJu : IsUnit ((HSpace.gram S).map (incA D)).det := by
    have hd : ((HSpace.gram S).map (incA D)).det = incA D (HSpace.gram S).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]; exact (gram_isUnit_det S).map _
  have hE : e • mt S h = e • mt S h' := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul]; exact hee i j
  have hN : cA D e • mt S h⁻¹ = cA D e • mt S h'⁻¹ := by
    have h2 := (gram_mul_conj_inv S e h).trans
      ((congrArg (fun X : Matrix (Fin S.rank) (Fin S.rank) (AE D) => (X.map (cA D)).transpose * (HSpace.gram S).map (incA D)) hE).trans
        (gram_mul_conj_inv S e h').symm)
    have h3 := congrArg (fun X => ((HSpace.gram S).map (incA D))⁻¹ * X) h2
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul] using h3
  have a1 : mt S h⁻¹ * mt S h = 1 := by rw [← mt_mul, inv_mul_cancel, mt_one]
  have a2 : mt S h' * mt S h'⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hM : cA D e • mt S h' = cA D e • mt S h := by
    calc cA D e • mt S h' = cA D e • (mt S h' * mt S h⁻¹ * mt S h) := by
          rw [Matrix.mul_assoc, a1, Matrix.mul_one]
      _ = mt S h' * (cA D e • mt S h⁻¹) * mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = mt S h' * (cA D e • mt S h'⁻¹) * mt S h := by rw [hN]
      _ = cA D e • mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, a2, Matrix.one_mul]
  have hMM : mt S h = mt S h' := by
    ext i j
    have k1 := hs i j
    have k2 := hs' i j
    have k3 := hee i j
    have k4 : cA D e * mt S h' i j = cA D e * mt S h i j := by
      have := congrFun (congrFun hM i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this; exact this
    simp only [Matrix.sub_apply] at k1 k2
    exact eq_of_parts k1 k2 k3 k4
  exact Subtype.ext (Units.ext hMM)

end GlobalTheory.UnitSplit

end
end

