module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsInt
section
noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def φinv (p : G × G) : G := p.2⁻¹ * p.1

theorem continuous_φinv : Continuous (φinv : G × G → G) := by
  unfold φinv
  exact continuous_snd.inv.mul continuous_fst

theorem measurable_φinv : Measurable (φinv : G × G → G) := continuous_φinv.measurable

theorem coef_shift {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (γ z u z' u' : G) :
    ⟪σ (u⁻¹ * z) w, σ γ (σ (u'⁻¹ * z') w)⟫_ℂ = ⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ := by
  obtain ⟨h1, hmul, hinn, -⟩ := hσ
  have e : ∀ a : HH, σ u (σ u⁻¹ a) = a := fun a => by
    rw [← ContinuousLinearMap.mul_apply, ← hmul, mul_inv_cancel, h1, ContinuousLinearMap.one_apply]
  rw [← hinn u, hmul u⁻¹ z, ContinuousLinearMap.mul_apply, e]
  simp only [hmul, ContinuousLinearMap.mul_apply]

theorem norm_W_shift {σ : G → (HH →L[ℂ] HH)} {μ ν : Measure G} {d : ℝ} {w : HH} {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V} (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S)
    {u : G} (hu : u ∈ S) (z : G) : ‖W (u⁻¹ * z)‖ = ‖W z‖ := by
  have hu' : u⁻¹ ∈ S := hinv u hu
  have h := hW.2.2.1 u⁻¹ hu' (W z) (W z)
  rw [hW.2.2.2.1 u⁻¹ hu' z, norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h]

theorem enorm_rk1A_le (a : V) (b : V') : ‖rk1A a b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  have h := norm_rk1A_le a b
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  push_cast
  exact h

def bInt (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (W' : G → V') (γ z z' s s' : G) : ℝ≥0∞ :=
  ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ

theorem continuous_coef5 {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (γ : G) :
    Continuous (fun q : G × G × G × G => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ) := by
  obtain ⟨-, hmul, -, hc⟩ := hσ
  have e : (fun q : G × G × G × G => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ) =
      fun q => ⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹ * q.2.1) w⟫_ℂ := by
    funext q
    rw [hmul (q.2.2.1 * γ * q.2.2.2⁻¹) q.2.1, ContinuousLinearMap.mul_apply]
  rw [e]
  have hg : Continuous fun q : G × G × G × G => q.2.2.1 * γ * q.2.2.2⁻¹ * q.2.1 := by fun_prop
  exact ((hc w).comp continuous_fst).inner ((hc w).comp hg)

theorem lintegral_four {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    (f : G → G → G → G → ℝ≥0∞) (hf : Measurable (fun q : G × G × G × G => f q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    ∫⁻ p, f p.1.1 p.2.1 p.1.2 p.2.2 ∂((ν.prod μS).prod (ν'.prod μS')) =
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', f z z' s s' ∂μS' ∂μS ∂ν' ∂ν := by
  have hm : Measurable (fun p : (G × G) × (G × G) => f p.1.1 p.2.1 p.1.2 p.2.2) := by
    have hg : Measurable (fun p : (G × G) × (G × G) => (p.1.1, p.2.1, p.1.2, p.2.2)) := by fun_prop
    exact hf.comp hg
  have h1 : Measurable fun x : G × G => ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS') :=
    hm.lintegral_prod_right'
  calc ∫⁻ p, f p.1.1 p.2.1 p.1.2 p.2.2 ∂((ν.prod μS).prod (ν'.prod μS'))
      = ∫⁻ x, ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS') ∂(ν.prod μS) :=
        lintegral_prod (fun p : (G × G) × (G × G) => f p.1.1 p.2.1 p.1.2 p.2.2) hm.aemeasurable
    _ = ∫⁻ z, ∫⁻ s, ∫⁻ y, f z y.1 s y.2 ∂(ν'.prod μS') ∂μS ∂ν :=
        lintegral_prod (fun x : G × G => ∫⁻ y, f x.1 y.1 x.2 y.2 ∂(ν'.prod μS')) h1.aemeasurable
    _ = ∫⁻ z, ∫⁻ s, ∫⁻ z', ∫⁻ s', f z z' s s' ∂μS' ∂ν' ∂μS ∂ν := by
        refine lintegral_congr fun z => lintegral_congr fun s => ?_
        have hg : Measurable (fun y : G × G => (z, y.1, s, y.2)) := by fun_prop
        exact lintegral_prod (fun y : G × G => f z y.1 s y.2) (hf.comp hg).aemeasurable
    _ = ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', f z z' s s' ∂μS' ∂μS ∂ν' ∂ν := by
        refine lintegral_congr fun z => ?_
        have hg : Measurable (fun p : (G × G) × G => (z, p.1.2, p.1.1, p.2)) := by fun_prop
        have hk : Measurable (fun p : (G × G) × G => f z p.1.2 p.1.1 p.2) := hf.comp hg
        have hk' : Measurable (fun x : G × G => ∫⁻ s', f z x.2 x.1 s' ∂μS') :=
          hk.lintegral_prod_right'
        exact lintegral_lintegral_swap (f := fun s z' => ∫⁻ s', f z z' s s' ∂μS') hk'.aemeasurable

theorem measurable_bInt {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun q : G × G × G × G => bInt σ w W W' γ q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold bInt
  have h1 : Measurable fun q : G × G × G × G =>
      ‖⟪σ q.1 w, σ (q.2.2.1 * γ * q.2.2.2⁻¹) (σ q.2.1 w)⟫_ℂ‖ₑ :=
    (continuous_enorm.comp (continuous_coef5 hσ w γ)).measurable
  have h2 : Measurable fun q : G × G × G × G => ‖W q.1‖ₑ :=
    (continuous_enorm.comp (hW.comp continuous_fst)).measurable
  have h3 : Measurable fun q : G × G × G × G => ‖W' q.2.1‖ₑ :=
    (continuous_enorm.comp (hW'.comp (continuous_fst.comp continuous_snd))).measurable
  exact (h1.mul h2).mul h3

theorem ae_mem_four {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS'] {S S' : Set G}
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) :
    ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.1.2 ∈ S ∧ p.2.2 ∈ S' := by
  have hS : ∀ᵐ s ∂μS, s ∈ S := ae_iff.mpr h0
  have hS' : ∀ᵐ s ∂μS', s ∈ S' := ae_iff.mpr h0'
  have a1 : ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.1.2 ∈ S :=
    quasiMeasurePreserving_fst.ae (quasiMeasurePreserving_snd.ae hS)
  have a2 : ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')), p.2.2 ∈ S' :=
    quasiMeasurePreserving_snd.ae (quasiMeasurePreserving_snd.ae hS')
  exact a1.and a2

theorem prod_map_φinv {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) :
    μ.prod μ = ((ν.prod μS).prod (ν'.prod μS')).map (Prod.map φinv φinv) := by
  calc μ.prod μ = ((ν.prod μS).map φinv).prod ((ν'.prod μS').map φinv) := by
        rw [← hm, ← hm']
    _ = _ := map_prod_map _ _ measurable_φinv measurable_φinv

theorem enorm_kG_shift_le {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ ν ν' : Measure G} {d : ℝ} {w : HH}
    {S S' : Set G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (γ z u z' u' : G) (hu : u ∈ S) (hu' : u' ∈ S') :
    ‖kG σ d w W W' γ (u⁻¹ * z, u'⁻¹ * z')‖ₑ ≤ ‖(d : ℂ)‖ₑ * bInt σ w W W' γ z z' u u' := by
  have e1 : ‖W (u⁻¹ * z)‖ₑ = ‖W z‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq ((norm_W_shift hW) hinv hu z)
  have e2 : ‖W' (u'⁻¹ * z')‖ₑ = ‖W' z'‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq ((norm_W_shift hW') hinv' hu' z')
  have hR : ‖Formalism.L2.SG.Pf.EnergyAbs.rk1A (W (u⁻¹ * z)) (W' (u'⁻¹ * z'))‖ₑ ≤ ‖W z‖ₑ * ‖W' z'‖ₑ := by
    rw [← e1, ← e2]
    exact enorm_rk1A_le _ _
  simp only [kG, bInt]
  rw [coef_shift hσ, enorm_smul, enorm_mul]
  calc ‖(d : ℂ)‖ₑ * ‖⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖Formalism.L2.SG.Pf.EnergyAbs.rk1A (W (u⁻¹ * z)) (W' (u'⁻¹ * z'))‖ₑ
      ≤ ‖(d : ℂ)‖ₑ * ‖⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ‖ₑ * (‖W z‖ₑ * ‖W' z'‖ₑ) := by gcongr
    _ = _ := by simp only [mul_assoc]

private theorem ae_enorm_kG_le_bInt {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS]
    [SFinite ν'] [SFinite μS'] {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) {μ : Measure G} {d : ℝ}
    {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : Formalism.L2.SG.Pf.EnergyAbs.IsWAbs μ σ d w S τ ν W) (hW' : Formalism.L2.SG.Pf.EnergyAbs.IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (γ : G) :
    ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')),
      ‖kG σ d w W W' γ (p.1.2⁻¹ * p.1.1, p.2.2⁻¹ * p.2.1)‖ₑ ≤
        ‖(d : ℂ)‖ₑ * bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2 := by
  have hmem := ae_mem_four (ν := ν) (ν' := ν') h0 h0'
  refine hmem.mono fun p hp => ?_
  exact enorm_kG_shift_le hσ hW hW' hinv hinv' γ p.1.1 p.1.2 p.2.1 p.2.2 hp.1 hp.2

private theorem measurable_bInt_prod {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (w : HH)
    {W : G → V} {W' : G → V'} (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun p : (G × G) × (G × G) => bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2) := by
  obtain ⟨-, hmul, -, hc⟩ := hσ
  have e : (fun p : (G × G) × (G × G) => bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2) =
      fun p => ‖⟪σ p.1.1 w, σ (p.1.2 * γ * p.2.2⁻¹ * p.2.1) w⟫_ℂ‖ₑ * ‖W p.1.1‖ₑ * ‖W' p.2.1‖ₑ := by
    funext p
    unfold bInt
    rw [hmul (p.1.2 * γ * p.2.2⁻¹) p.2.1, ContinuousLinearMap.mul_apply]
  rw [e]
  have hg : Continuous fun p : (G × G) × (G × G) => p.1.2 * γ * p.2.2⁻¹ * p.2.1 := by fun_prop
  have h1 : Measurable fun p : (G × G) × (G × G) =>
      ‖⟪σ p.1.1 w, σ (p.1.2 * γ * p.2.2⁻¹ * p.2.1) w⟫_ℂ‖ₑ :=
    (continuous_enorm.comp
      (((hc w).comp (continuous_fst.comp continuous_fst)).inner ((hc w).comp hg))).measurable
  have h2 : Measurable fun p : (G × G) × (G × G) => ‖W p.1.1‖ₑ :=
    (continuous_enorm.comp (hW.comp (continuous_fst.comp continuous_fst))).measurable
  have h3 : Measurable fun p : (G × G) × (G × G) => ‖W' p.2.1‖ₑ :=
    (continuous_enorm.comp (hW'.comp (continuous_fst.comp continuous_snd))).measurable
  exact (h1.mul h2).mul h3


set_option maxHeartbeats 800000 in
private theorem lintegral_const_mul_bInt_eq_iterated {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS]
    [SFinite ν'] [SFinite μS'] {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (w : HH) {W : G → V}
    {W' : G → V'} (hW : Continuous W) (hW' : Continuous W') (γ : G) (c : ℝ≥0∞) :
    ∫⁻ p : (G × G) × (G × G), c * bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2
        ∂((ν.prod μS).prod (ν'.prod μS')) =
      c * ∫⁻ z : G, ∫⁻ z' : G, ∫⁻ s : G, ∫⁻ s' : G, bInt σ w W W' γ z z' s s'
        ∂μS' ∂μS ∂ν' ∂ν := by
  have hc := measurable_bInt_prod hσ w hW hW' γ
  have e1 := lintegral_const_mul (μ := (ν.prod μS).prod (ν'.prod μS')) c hc
  have e2 := lintegral_four (ν := ν) (μS := μS) (ν' := ν') (μS' := μS')
    (bInt σ w W W' γ) (measurable_bInt hσ w hW hW' γ)
  exact e1.trans (congrArg (fun x => c * x) e2)

theorem lintegral_kG_shift_lt_top {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ : Measure G} {d : ℝ} {w : HH} {S S' : Set G}
    {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ∫⁻ p, ‖kG σ d w W W' γ (p.1.2⁻¹ * p.1.1, p.2.2⁻¹ * p.2.1)‖ₑ ∂((ν.prod μS).prod (ν'.prod μS')) < ⊤ := by
  have hle := ae_enorm_kG_le_bInt hσ hW hW' hinv hinv' h0 h0' γ
  have h2 := lintegral_const_mul_bInt_eq_iterated (ν := ν) (μS := μS) (ν' := ν') (μS' := μS') hσ w
    hW.2.2.2.2.1 hW'.2.2.2.2.1 γ ‖(d : ℂ)‖ₑ
  have hd : ‖(d : ℂ)‖ₑ ≠ ⊤ := enorm_ne_top
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  rw [h2]
  exact (ENNReal.mul_ne_top hd hB.ne).lt_top

theorem integrable_kG {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
    {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    Integrable (kG σ d w W W' γ) (μ.prod μ) := by
  have hK : Continuous (kG σ d w W W' γ) :=
    continuous_kG hσ d w hW.2.2.2.2.1 hW'.2.2.2.2.1 γ
  refine ⟨hK.aestronglyMeasurable, ?_⟩
  have hF : Measurable (Prod.map φinv φinv : (G × G) × (G × G) → G × G) :=
    (continuous_φinv.prodMap continuous_φinv).measurable
  have hg : Measurable fun q : G × G => ‖kG σ d w W W' γ q‖ₑ :=
    (continuous_enorm.comp hK).measurable
  show ∫⁻ q, ‖kG σ d w W W' γ q‖ₑ ∂(μ.prod μ) < ⊤
  rw [prod_map_φinv hm hm', lintegral_map hg hF]
  exact lintegral_kG_shift_lt_top hσ hW hW' hinv hinv' h0 h0' γ hB

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensDense
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

def coeff (σs : K → (Hs →L[ℂ] Hs)) (a b : Hs) (x : K) : ℂ := ⟪b, σs x a⟫_ℂ

theorem continuous_coeff (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (a b : Hs) :
    Continuous (coeff σs a b) := by
  show Continuous fun x => ⟪b, σs x a⟫_ℂ
  exact continuous_const.inner (hstr a)

theorem norm_sq_of_mul_conj (z : ℂ) : ‖z * conj z‖ = ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_conj, sq]

private theorem integrable_norm_sq_coeff_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    Integrable (fun x => ‖coeff σs a b x‖ ^ 2) m := by
  obtain ⟨hi, -⟩ := h
  exact hi.norm.congr (ae_of_all _ fun x => norm_sq_of_mul_conj (coeff σs a b x))

private theorem lintegral_enorm_sq_coeff_eq_ofReal_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    ∫⁻ x, ‖coeff σs a b x‖ₑ ^ 2 ∂m = ENNReal.ofReal (∫ x, ‖coeff σs a b x‖ ^ 2 ∂m) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_coeff_of_SP h)
    (ae_of_all _ fun x => sq_nonneg _)]
  exact lintegral_congr fun x => enorm_sq_eq _

theorem memLp_of_diag (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) {a b : Hs} (h : SP m σs D a b a b) :
    MemLp (coeff σs a b) 2 m :=
  memLp_two_of_lintegral (continuous_coeff hstr a b).aestronglyMeasurable
    (by rw [lintegral_enorm_sq_coeff_eq_ofReal_of_SP h]; exact ENNReal.ofReal_lt_top)

private theorem mul_conj_eq_ofReal_norm_sq_complex (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem integral_norm_sq_coeff_eq_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    ∫ x, ‖coeff σs a b x‖ ^ 2 ∂m = ‖a‖ ^ 2 * ‖b‖ ^ 2 / D := by
  obtain ⟨-, h2⟩ := h
  have e1 : (fun x => ⟪b, σs x a⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) =
      fun x => ((‖coeff σs a b x‖ ^ 2 : ℝ) : ℂ) :=
    funext fun x => mul_conj_eq_ofReal_norm_sq_complex _
  rw [e1] at h2
  rw [integral_complex_ofReal] at h2
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ((∫ x, ‖coeff σs a b x‖ ^ 2 ∂m : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖b‖ ^ 2 / D : ℝ) : ℂ) := by
    rw [h2]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    rfl
  exact Complex.ofReal_injective h3

theorem lintegral_of_diag (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) {a b : Hs} (h : SP m σs D a b a b) :
    ∫⁻ x, ‖coeff σs a b x‖ₑ ^ 2 ∂m = ENNReal.ofReal (‖a‖ ^ 2 * ‖b‖ ^ 2 / D) := by
  rw [lintegral_enorm_sq_coeff_eq_ofReal_of_SP h, integral_norm_sq_coeff_eq_of_SP h]

theorem coeff_sub_a (a₁ a₂ b : Hs) : (fun x => coeff σs a₁ b x - coeff σs a₂ b x) = coeff σs (a₁ - a₂) b := by
  funext x
  simp only [coeff, map_sub, inner_sub_right]

theorem coeff_sub_b (a b₁ b₂ : Hs) : (fun x => coeff σs a b₁ x - coeff σs a b₂ x) = coeff σs a (b₁ - b₂) := by
  funext x
  simp only [coeff, inner_sub_left]

theorem small_of_close (c : ℝ) (hc : 0 ≤ c) (hD : 0 < D) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → ENNReal.ofReal (t ^ 2 * c / D) ≤ ε := by
  rcases eq_or_ne ε ⊤ with hte | hne
  · exact ⟨1, one_pos, fun _ _ _ => by rw [hte]; exact le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hne
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  refine ⟨min 1 (ε.toReal * D / (c + 1)), lt_min one_pos (div_pos (mul_pos he hD) hc1),
    fun t ht0 htδ => ?_⟩
  rw [← ENNReal.ofReal_toReal hne]
  apply ENNReal.ofReal_le_ofReal
  have h1 : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
  have h2 : t < ε.toReal * D / (c + 1) := lt_of_lt_of_le htδ (min_le_right _ _)
  have h4 : t * (c + 1) ≤ ε.toReal * D := by
    have h5 : t * (c + 1) < ε.toReal * D / (c + 1) * (c + 1) := mul_lt_mul_of_pos_right h2 hc1
    rw [div_mul_cancel₀ _ hc1.ne'] at h5
    exact h5.le
  have h3 : t ^ 2 ≤ t := by nlinarith
  have h6 : t ^ 2 * c ≤ t * c := mul_le_mul_of_nonneg_right h3 hc
  have h7 : t ^ 2 * c ≤ ε.toReal * D := by nlinarith
  have h8 : t ^ 2 * c / D ≤ ε.toReal * D / D := by
    exact div_le_div_of_nonneg_right h7 hD.le
  rwa [mul_div_cancel_right₀ _ hD.ne'] at h8

theorem SP_of_dense_a (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (b a' b' : Hs) (hA : ∀ a₀ ∈ Sp, SP m σs D a₀ b a' b')
    (hdiag : ∀ c ∈ Sp, SP m σs D c b c b) (hg : MemLp (coeff σs a' b') 2 m) (a : Hs) :
    SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
  obtain ⟨u, hu_mem, hu⟩ := mem_closure_iff_seq_limit.1 (hdense a)
  have hf2 : ∀ n, MemLp (coeff σs (u n) b) 2 m := fun n =>
    memLp_of_diag hstr (hdiag _ (hu_mem n))
  have hFm : AEStronglyMeasurable (coeff σs a b) m :=
    (continuous_coeff hstr a b).aestronglyMeasurable
  have hpt : ∀ x, Tendsto (fun n => coeff σs (u n) b x) atTop (𝓝 (coeff σs a b x)) := by
    intro x
    have hσ : Tendsto (fun n => σs x (u n)) atTop (𝓝 (σs x a)) := ((σs x).continuous.tendsto a).comp hu
    show Tendsto (fun n => ⟪b, σs x (u n)⟫_ℂ) atTop (𝓝 ⟪b, σs x a⟫_ℂ)
    exact tendsto_const_nhds.inner hσ
  have hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      ∫⁻ x, ‖coeff σs (u k) b x - coeff σs (u n) b x‖ₑ ^ 2 ∂m ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := small_of_close (‖b‖ ^ 2) (sq_nonneg _) hD ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq δ hδ
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsub : ∀ x, coeff σs (u k) b x - coeff σs (u n) b x =
        coeff σs (u k - u n) b x := fun x => congrFun (coeff_sub_a (σs := σs) (u k) (u n) b) x
    calc ∫⁻ x, ‖coeff σs (u k) b x - coeff σs (u n) b x‖ₑ ^ 2 ∂m
        = ∫⁻ x, ‖coeff σs (u k - u n) b x‖ₑ ^ 2 ∂m := by simp only [hsub]
      _ = ENNReal.ofReal (‖u k - u n‖ ^ 2 * ‖b‖ ^ 2 / D) :=
          lintegral_of_diag hstr (hdiag _ (Sp.sub_mem (hu_mem k) (hu_mem n)))
      _ ≤ ε := hsmall _ (norm_nonneg _) (by rw [← dist_eq_norm]; exact hN k hk n hn)
  have hL : Tendsto (fun n => ∫ x, coeff σs (u n) b x * conj (coeff σs a' b' x) ∂m) atTop
      (𝓝 (⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ))) := by
    have e : (fun n => ∫ x, coeff σs (u n) b x * conj (coeff σs a' b' x) ∂m) =
        fun n => ⟪a', u n⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ) := by
      funext n
      obtain ⟨-, he⟩ := hA _ (hu_mem n)
      exact he
    rw [e]
    have hin : Tendsto (fun n => ⟪a', u n⟫_ℂ) atTop (𝓝 ⟪a', a⟫_ℂ) := by
      exact tendsto_const_nhds.inner hu
    exact (hin.mul_const _).div_const _
  obtain ⟨hM, hI, hE⟩ := limit_memLp_and_integral_eq (fun n => coeff σs (u n) b)
    (coeff σs a b) (coeff σs a' b') hf2 hFm hg hpt hC hL
  exact ⟨And.intro hI hE, hM⟩

theorem SP_of_dense_b (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (a a' b' : Hs) (hB : ∀ b₀ ∈ Sp, SP m σs D a b₀ a' b')
    (hdiag : ∀ c ∈ Sp, SP m σs D a c a c) (hg : MemLp (coeff σs a' b') 2 m) (b : Hs) :
    SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
  obtain ⟨u, hu_mem, hu⟩ := mem_closure_iff_seq_limit.1 (hdense b)
  have hf2 : ∀ n, MemLp (coeff σs a (u n)) 2 m := fun n =>
    memLp_of_diag hstr (hdiag _ (hu_mem n))
  have hFm : AEStronglyMeasurable (coeff σs a b) m :=
    (continuous_coeff hstr a b).aestronglyMeasurable
  have hpt : ∀ x, Tendsto (fun n => coeff σs a (u n) x) atTop (𝓝 (coeff σs a b x)) := by
    intro x
    show Tendsto (fun n => ⟪u n, σs x a⟫_ℂ) atTop (𝓝 ⟪b, σs x a⟫_ℂ)
    exact hu.inner tendsto_const_nhds
  have hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      ∫⁻ x, ‖coeff σs a (u k) x - coeff σs a (u n) x‖ₑ ^ 2 ∂m ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := small_of_close (‖a‖ ^ 2) (sq_nonneg _) hD ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq δ hδ
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsub : ∀ x, coeff σs a (u k) x - coeff σs a (u n) x =
        coeff σs a (u k - u n) x := fun x => congrFun (coeff_sub_b (σs := σs) a (u k) (u n)) x
    calc ∫⁻ x, ‖coeff σs a (u k) x - coeff σs a (u n) x‖ₑ ^ 2 ∂m
        = ∫⁻ x, ‖coeff σs a (u k - u n) x‖ₑ ^ 2 ∂m := by simp only [hsub]
      _ = ENNReal.ofReal (‖u k - u n‖ ^ 2 * ‖a‖ ^ 2 / D) := by
          rw [lintegral_of_diag hstr (hdiag _ (Sp.sub_mem (hu_mem k) (hu_mem n))),
            mul_comm (‖a‖ ^ 2)]
      _ ≤ ε := hsmall _ (norm_nonneg _) (by rw [← dist_eq_norm]; exact hN k hk n hn)
  have hL : Tendsto (fun n => ∫ x, coeff σs a (u n) x * conj (coeff σs a' b' x) ∂m) atTop
      (𝓝 (⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ))) := by
    have e : (fun n => ∫ x, coeff σs a (u n) x * conj (coeff σs a' b' x) ∂m) =
        fun n => ⟪a', a⟫_ℂ * ⟪u n, b'⟫_ℂ / (D : ℂ) := by
      funext n
      obtain ⟨-, he⟩ := hB _ (hu_mem n)
      exact he
    rw [e]
    have hin : Tendsto (fun n => ⟪u n, b'⟫_ℂ) atTop (𝓝 ⟪b, b'⟫_ℂ) := by
      exact hu.inner tendsto_const_nhds
    exact (hin.const_mul _).div_const _
  obtain ⟨hM, hI, hE⟩ := limit_memLp_and_integral_eq (fun n => coeff σs a (u n))
    (coeff σs a b) (coeff σs a' b') hf2 hFm hg hpt hC hL
  exact ⟨And.intro hI hE, hM⟩

theorem isSchur_of_dense (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (hSp : ∀ a ∈ Sp, ∀ b ∈ Sp, ∀ a' ∈ Sp, ∀ b' ∈ Sp, SP m σs D a b a' b') :
    IsSchur m σs D := by

  have h1 : ∀ b ∈ Sp, ∀ a' ∈ Sp, ∀ b' ∈ Sp, ∀ a : Hs,
      SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
    intro b hb a' ha' b' hb' a
    exact SP_of_dense_a hstr hD Sp hdense b a' b' (fun a₀ h₀ => hSp a₀ h₀ b hb a' ha' b' hb')
      (fun c hc => hSp c hc b hb c hc b hb)
      (memLp_of_diag hstr (hSp a' ha' b' hb' a' ha' b' hb')) a

  have h2 : ∀ b ∈ Sp, ∀ b' ∈ Sp, ∀ a a' : Hs, SP m σs D a b a' b' := by
    intro b hb b' hb' a a'
    have h := SP_of_dense_a hstr hD Sp hdense b' a b
      (fun a₀ h₀ => SP_swap (h1 b hb a₀ h₀ b' hb' a).1)
      (fun c hc => hSp c hc b' hb' c hc b' hb')
      (h1 b hb b' hb' b' hb' a).2 a'
    exact SP_swap h.1

  have h3 : ∀ b' ∈ Sp, ∀ a a' b : Hs, SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
    intro b' hb' a a' b
    exact SP_of_dense_b hstr hD Sp hdense a a' b'
      (fun b₀ h₀ => h2 b₀ h₀ b' hb' a a')
      (fun c hc => h2 c hc c hc a a)
      (h1 b' hb' b' hb' b' hb' a').2 b

  refine ⟨hD, fun a b a' b' => ?_⟩
  have h4 := SP_of_dense_b hstr hD Sp hdense a' a b
    (fun b₀ h₀ => SP_swap (h3 b₀ h₀ a a' b).1)
    (fun c hc => h2 c hc c hc a' a')
    (h3 0 Sp.zero_mem a a b).2 b'
  exact SP_swap h4.1

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs' : Type} [NormedAddCommGroup Hs'] [InnerProductSpace ℂ Hs']
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs' : (∀ v, G v) → (Hs' →L[ℂ] Hs')} {tens : (∀ v, H v) → Hs'}

theorem isSchur_tens [OpensMeasurableSpace (∀ v, G v)] (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    (d : ι → ℝ) (hσ : ∀ v, IsUnitRep (σ v)) (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs' tens) :
    IsSchur (Measure.pi μ) σs' (∏ v, d v) := by
  have hU := isUnitRep_tens hσ h
  obtain ⟨-, -, -, hcont⟩ := hU
  have hh := h
  obtain ⟨-, -, hdense⟩ := hh
  have hD : 0 < ∏ v, d v := Finset.prod_pos fun v _ => by
    obtain ⟨hd, -⟩ := hS v
    exact hd
  have hE : ∀ a ∈ Set.range tens, ∀ b ∈ Set.range tens, ∀ a' ∈ Set.range tens, ∀ b' ∈ Set.range tens,
      SP (Measure.pi μ) σs' (∏ v, d v) a b a' b' := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩ _ ⟨α', rfl⟩ _ ⟨β', rfl⟩
    exact SP_pure μ d hS h α β α' β'
  exact isSchur_of_dense hcont hD (Submodule.span ℂ (Set.range tens)) hdense
    (SP_span hE)

end Tens

end Formalism.L2.S.Pv.SchurTens
end
end

