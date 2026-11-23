module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SingWeightRegFamilyTransport
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.Transport

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isOpen_compl_bdry (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hyt : A.chart j y ∈ (A.chart j).target := (A.chart j).map_source hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : AnalyticAt ℂ (s y ∘ (A.chart j).symm) (A.chart j y) :=
    hs.1 y j (A.chart j y) ⟨hyt, by
      show (A.chart j).symm (A.chart j y) ∈ L.U y
      rw [hsy]; exact L.mem_U y⟩
  have hcy : ContinuousAt (fun z => (s y ∘ (A.chart j).symm) (A.chart j z)) y :=
    ContinuousAt.comp (f := A.chart j) han.continuousAt ((A.chart j).continuousAt hj)
  have hne : (s y ∘ (A.chart j).symm) (A.chart j y) ≠ 0 := by
    show s y ((A.chart j).symm (A.chart j y)) ≠ 0
    rw [hsy]; exact hy
  have h1 : ∀ᶠ z in 𝓝 y, (s y ∘ (A.chart j).symm) (A.chart j z) ≠ 0 := hcy.eventually_ne hne
  filter_upwards [h1, (A.chart j).open_source.mem_nhds hj,
    (L.isOpen_U y).mem_nhds (L.mem_U y)] with z h1 h2 h3
  have h1' : s y z ≠ 0 := by
    have : s y ((A.chart j).symm (A.chart j z)) ≠ 0 := h1
    rwa [(A.chart j).left_inv h2] at this
  intro hz
  have hz' : s z z = 0 := hz
  have hg := hs.2 y z z ⟨h3, L.mem_U z⟩
  rw [hz'] at hg
  simp only [norm_zero, zero_mul] at hg
  have hpos : 0 < ‖s y z‖ * Real.exp (-L.φ y z) :=
    mul_pos (norm_pos_iff.2 h1') (Real.exp_pos _)
  exact hpos.ne' hg

theorem contDiffAt_two {A : FinHolAtlas e X} {U : Set X} {f : X → ℝ} (h : A.SmoothOn U f)
    (hU : IsOpen U) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hyU : (A.chart j).symm y ∈ U) : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y :=
  ((h j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hy, hyU⟩)).of_le
    ENat.LEInfty.out

theorem levi_eq_of_sub_re (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {W : Set X} (hW : IsOpen W) (hyW : (A.chart j).symm y ∈ W)
    {G : X → ℂ} (hG : A.HoloOn W G) {a b : X → ℝ} (hab : ∀ z ∈ W, a z - b z = (G z).re)
    (hb : ContDiffAt ℝ 2 (b ∘ (A.chart j).symm) y) (w : Fin e → ℂ) :
    levi (a ∘ (A.chart j).symm) y w = levi (b ∘ (A.chart j).symm) y w := by
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have hre : ContDiffAt ℝ 2 (fun z => ((G ∘ (A.chart j).symm) z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hGa.restrictScalars.contDiffAt
  have hev : (a ∘ (A.chart j).symm) =ᶠ[𝓝 y]
      fun z => (b ∘ (A.chart j).symm) z + 1 * ((G ∘ (A.chart j).symm) z).re := by
    have hmem : ∀ᶠ z in 𝓝 y, (A.chart j).symm z ∈ W :=
      ((A.chart j).continuousAt_symm hy).eventually_mem (hW.mem_nhds hyW)
    filter_upwards [hmem] with z hz
    have := hab _ hz
    simp only [Function.comp]
    linarith
  rw [levi_congr hev, levi_add_smul 1 hb hre, levi_re_analytic hGa]
  ring

theorem exists_re_base {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) {x u : X}
    (hu : u ∈ P.U x) : ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, P.φ x z - P.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G, hG, hW⟩ := hP.2 x u u ⟨hu, P.mem_U u⟩
  refine ⟨W ∩ P.U x ∩ P.U u, (oW.inter (P.isOpen_U x)).inter (P.isOpen_U u),
    ⟨⟨mW, hu⟩, P.mem_U u⟩, G, fun k => (hG k).mono fun y hy => ⟨hy.1, hy.2.1.1⟩, ?_⟩
  rintro z hz
  exact hW z hz

theorem exists_re_change {A : FinHolAtlas e X} {th th' : LocPot X} (hth : IsPotential A th)
    (hsame : SamePot A Set.univ th th') {x u : X} (hu : u ∈ th.U x) :
    ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, th.φ x z - th'.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G₁, h₁, e₁⟩ := exists_re_base hth hu
  obtain ⟨V, oV, mV, G₂, h₂, e₂⟩ := hsame u (Set.mem_univ _)
  refine ⟨W ∩ V, oW.inter oV, ⟨mW, mV⟩, fun z => G₁ z + G₂ z, fun k => ?_, ?_⟩
  · exact ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rintro z ⟨a, b⟩
    have h1 := e₁ z a
    have h2 := e₂ z b
    simp only [Complex.add_re]
    linarith

theorem isPshOn_transport {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} {th th' : LocPot X}
    {ph : X → ℝ} (hs : IsSection A L s) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hsm : A.SmoothOn (bdry s)ᶜ ph)
    (hpsh : IsPshOn A (bdry s)ᶜ (th' + LocPot.ofFun ph)) :
    IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun ph) := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1
  obtain ⟨W, oW, mW, G, hG, hW⟩ := exists_re_change hth hsame hyx
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨th'.mem_U _, Set.mem_univ _⟩, hyb⟩ w
  have hb : ContDiffAt ℝ 2 ((th' + LocPot.ofFun ph).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    (contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hsm (isOpen_compl_bdry A L s hs) j hyt hyb)
  rw [levi_eq_of_sub_re A j hyt oW mW hG (a := (th + LocPot.ofFun ph).φ x)
    (b := (th' + LocPot.ofFun ph).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := hW z hz
      show th.φ x z + ph z - (th'.φ _ z + ph z) = _
      linarith) hb w]
  exact h0

theorem isPsh_transport {A : FinHolAtlas e X} {Θ th th' : LocPot X} {f : X → ℝ} {c : ℝ}
    (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hf : A.Smooth f)
    (hpsh : IsPsh A (th' + LocPot.ofFun f + Θ.rsmul c)) :
    IsPsh A (th + LocPot.ofFun f + Θ.rsmul c) := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1.1
  have hyΘ : (A.chart j).symm y ∈ Θ.U x := hyU.2
  obtain ⟨W₁, o₁, m₁, G₁, h₁, e₁⟩ := exists_re_change hth hsame hyx
  obtain ⟨W₂, o₂, m₂, G₂, h₂, e₂⟩ := exists_re_base hΘ hyΘ
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨⟨th'.mem_U _, Set.mem_univ _⟩, Θ.mem_U _⟩⟩ w
  have hb : ContDiffAt ℝ 2
      ((th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hf isOpen_univ j hyt (Set.mem_univ _))).add
      (contDiffAt_const.mul (contDiffAt_two (hΘ.1 _) (Θ.isOpen_U _) j hyt (Θ.mem_U _)))
  have hG : A.HoloOn (W₁ ∩ W₂) fun z => G₁ z + (c : ℂ) * G₂ z := fun k =>
    ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add
      ((analyticOnNhd_const (v := (c : ℂ))).mul ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩))
  rw [levi_eq_of_sub_re A j hyt (o₁.inter o₂) ⟨m₁, m₂⟩ hG
    (a := (th + LocPot.ofFun f + Θ.rsmul c).φ x)
    (b := (th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := e₁ z hz.1
      have h2 := e₂ z hz.2
      show th.φ x z + f z + c * Θ.φ x z -
        (th'.φ _ z + f z + c * Θ.φ _ z) = _
      simp only [Complex.add_re, Complex.re_ofReal_mul]
      rw [← h1, ← h2]
      ring) hb w]
  exact h0

theorem singWeight_regFamily_transport : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (th th' : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ),
    IsPotential A Θ → IsSection A L s → IsPotential A th → IsPotential A th' → SamePot A Set.univ th th' →
    (IsSingWeight A L s th' ph C₅ → IsSingWeight A L s th ph C₅) ∧
      (IsRegFamily A Θ L s th' ph phT C t₀ → IsRegFamily A Θ L s th ph phT C t₀) := by
  intro e X _ A Θ L s th th' ph phT C₅ C t₀ hΘ hs hth hth' hsame
  constructor
  · rintro ⟨_, hsm, hpsh, hb⟩
    exact ⟨hth, hsm, isPshOn_transport hs hth hth' hsame hsm hpsh, hb⟩
  · rintro ⟨h0, h1, hreg⟩
    refine ⟨h0, h1, fun t ht ht' => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hreg t ht ht'
    exact ⟨a1, a2, a3, a4, isPsh_transport hΘ hth hth' hsame a1 a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.Ar.PB.Transport
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.SncPull

theorem holoOn_comp_pr {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {U : Set Z} {g : Z → ℂ} (hg : Ab.HoloOn U g) : A.HoloOn (pr ⁻¹' U) (fun x => g (pr x)) := by
  intro j t ht
  obtain ⟨k, hk⟩ := Ab.cover (pr ((A.chart j).symm t))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((Ab.chart k).open_source.preimage hp.1)
  have htO : t ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source) :=
    ⟨ht.1, hk⟩
  have h1 : AnalyticAt ℂ (Ab.chart k ∘ pr ∘ (A.chart j).symm) t := hp.2 j k t htO
  have hmem : (Ab.chart k ∘ pr ∘ (A.chart j).symm) t ∈
      (Ab.chart k).target ∩ (Ab.chart k).symm ⁻¹' U := by
    refine ⟨(Ab.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (Ab.chart k).left_inv hk]
    exact ht.2
  have h2 : AnalyticAt ℂ (g ∘ (Ab.chart k).symm) ((Ab.chart k ∘ pr ∘ (A.chart j).symm) t) :=
    hg k _ hmem
  have h3 := AnalyticAt.comp (g := g ∘ (Ab.chart k).symm)
    (f := Ab.chart k ∘ pr ∘ (A.chart j).symm) h2 h1
  refine h3.congr ?_
  filter_upwards [hO.mem_nhds htO] with t' ht'
  simp [Function.comp, (Ab.chart k).left_inv ht'.2]

theorem isSection_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} (hs : IsSection Ab L s) :
    IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) :=
  ⟨fun x => holoOn_comp_pr hp (hs.1 (pr x)), fun x x' y hy => hs.2 (pr x) (pr x') (pr y) hy⟩

theorem isSNC_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} {nb : ℕ} {m : Fin nb → ℕ} {W : Fin nb → Set Z}
    (hsnc : IsSNC Ab L s m W)
    (hprod : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧
        ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) :
    IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) := by
  intro x
  obtain ⟨ψb, hcb, hxb, hsub, σb, hinj, hW, u, hu, hu0, hfac⟩ := hsnc (pr x)
  obtain ⟨ψ, kb, σ, hc, hx, hpr⟩ := hprod x
  obtain ⟨ψ', hc', hsrc, hco⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap e n X Z A Ab pr ψ kb σ ψb hc hcb hpr
  have hsrc' : ∀ y ∈ ψ'.source, pr y ∈ ψb.source := fun y hy => by
    rw [hsrc] at hy; exact hy.2
  refine ⟨ψ', hc', by rw [hsrc]; exact ⟨hx, hxb⟩, fun y hy => hsub (hsrc' y hy),
    fun k => (σb k).map σ, ?_, ?_, fun y => u (pr y), ?_, fun y hy => hu0 _ (hsrc' y hy), ?_⟩
  · intro k k' i hk hk'
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hk
    obtain ⟨b, hb, hab⟩ := Option.map_eq_some_iff.1 hk'
    obtain rfl := σ.injective hab
    exact hinj k k' _ ha hb
  · intro k
    ext y
    constructor
    · rintro ⟨hyW, hy⟩
      have h1 : pr y ∈ W k ∩ ψb.source := ⟨hyW, hsrc' y hy⟩
      rw [hW k] at h1
      obtain ⟨-, i, hi, h0⟩ := h1
      exact ⟨hy, σ i, by simp [hi], by rw [hco y hy]; exact h0⟩
    · rintro ⟨hy, i, hi, h0⟩
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [hco y hy] at h0
      have h1 : pr y ∈ W k ∩ ψb.source := by
        rw [hW k]; exact ⟨hsrc' y hy, a, ha, h0⟩
      exact ⟨h1.1, hy⟩
  · exact fun j => (holoOn_comp_pr hp hu j).mono fun t ht => ⟨ht.1, hsrc' _ ht.2⟩
  · intro y hy
    show s (pr x) (pr y) = _
    rw [hfac _ (hsrc' y hy)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    cases h : σb k with
    | none => simp [h]
    | some i => simp [h, hco y hy]

theorem exists_adapted {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {nb : ℕ} {m : Fin nb → ℕ}
    {W : Fin nb → Set X} (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m W) :
    ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  choose φ S μ v hc hx hball h0 hU hμ hv hv0 hfac using _root_.GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form e X A L s nb m W hsnc
  have hb := fun x => _root_.GlobalTheory.CompanionTheory.Ar.PB.LocalModel.zero_set_and_bound e X A L s hL hs x (φ x) (S x) (μ x) (v x) (hc x) (hball x) (hU x)
    (hμ x) (hv x) (hv0 x) (hfac x)
  choose hzero M hM using fun x => And.intro (hb x).1 (hb x).2
  have hopen : ∀ x, IsOpen ((φ x).source ∩ φ x ⁻¹' Metric.ball (0 : Fin e → ℂ) 1) := fun x =>
    (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen (fun x _ =>
    Set.mem_iUnion.2 ⟨x, hx x, by simp [h0 x]⟩)
  let E := t.equivFin
  have hcov : ∀ x, ∃ i : Fin t.card, x ∈ (φ (E.symm i).1).source ∧
      φ (E.symm i).1 x ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    intro x
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    refine ⟨E ⟨p, hp⟩, ?_⟩
    simpa using hxp
  obtain ⟨B, hAB, hB1, hB2⟩ := atlasOfCompat A (fun i : Fin t.card => φ (E.symm i).1)
    (fun i => hc _) (fun x => (hcov x).imp fun _ h => h.1)
  refine ⟨B, hAB, ?_, ?_, ∑ i : Fin t.card, |M (E.symm i).1|, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    rw [hi]; exact hball _
  · intro x
    obtain ⟨i, hi, hi'⟩ := hcov x
    obtain ⟨j, hj⟩ := hB1 i
    exact ⟨j, by rw [hj]; exact hi, by rw [hj]; exact hi'⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    refine ⟨S (E.symm i).1, μ (E.symm i).1, hμ _, ?_, ?_⟩
    · rw [hi]; exact hzero _
    · rw [hi]
      intro y hy hy'
      exact ((hM _ y hy hy').trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun i : Fin t.card => |M (E.symm i).1|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem pullback_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  intro e n X Z _ _ _ _ _ _ A Ab Bb pr hp L s nb m W hL hs hsnc _ hprod
  have hL' := ReciprocityTheory.AnForm.M.isPotentialPullback Ab A pr hp L hL
  have hs' := isSection_pull hp hs
  have hn' := isSNC_pull hp hsnc hprod
  exact ⟨hL', hs', hn', exists_adapted A _ _ hL' hs' hn'⟩

end GlobalTheory.CompanionTheory.Ar.PB.SncPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPower
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def genLin : MvPolynomial (Fin 3) (MvPolynomial (Fin 3) ℝ) := ∑ i, X i * C (X i)

def coordHom : MvPolynomial (Fin 3) ℝ →+* (S2 → ℝ) :=
  RingHom.pi fun p : S2 => MvPolynomial.eval fun i => (p : E3) i

theorem coordHom_apply (g : MvPolynomial (Fin 3) ℝ) (p : S2) :
    coordHom g p = MvPolynomial.eval (fun i => (p : E3) i) g := rfl

theorem linear_form_eq_map_eval (n : Fin 3 → ℝ) : lin3 n = MvPolynomial.map (MvPolynomial.eval n) genLin := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin3, genLin, map_sum, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X]

theorem dotPoly_id_eq_map : dotPoly (id : S2 → S2) = MvPolynomial.map coordHom genLin := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotPoly, genLin, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext p
  rw [coordHom_apply, MvPolynomial.eval_X]
  rfl

theorem linear_expand (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (S : Finset (Fin 3 →₀ ℕ))
    (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q.support ⊆ S) :
    ℓ Q = ∑ m ∈ S, AddMonoidAlgebra.coeff Q m * ℓ (monomial m 1) := by
  calc ℓ Q = ℓ (∑ m ∈ Q.support, monomial m (AddMonoidAlgebra.coeff Q m)) := by rw [support_sum_monomial_coeff]
    _ = ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m * ℓ (monomial m 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show monomial m (AddMonoidAlgebra.coeff Q m) = (AddMonoidAlgebra.coeff Q m) • monomial m (1 : ℝ) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    _ = _ := Finset.sum_subset hQ fun m _ hm => by rw [notMem_support_iff.1 hm, zero_mul]

theorem stereo_one : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  intro ℓ N
  have : IsProbabilityMeasure sphereMeasure := GroundTheory.Heights₂.Heights.Inter.FibreLocal.isProbabilityMeasure_sphere
  have key : ∀ f : (Fin 3 → ℝ) → ℝ, Measurable f →
      (Integrable (fun a : ℂ => f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
        Integrable (fun m : S2 => f fun i => (m : E3) i) sphereMeasure) ∧
      ∫ a : ℂ, f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) =
        ∫ m : S2, f (fun i => (m : E3) i) ∂sphereMeasure :=
    fun f hf => (GlobalTheory.T.sphere_measure_stereographic_integral).1 f hf
  obtain ⟨G, hG⟩ : ∃ G, G = genLin ^ N := ⟨_, rfl⟩
  have hlin : ∀ a, lin3 (nS a) ^ N = MvPolynomial.map (MvPolynomial.eval (nS a)) G := fun a => by
    rw [hG, map_pow, linear_form_eq_map_eval]
  have hdot : dotPoly (id : S2 → S2) ^ N = MvPolynomial.map coordHom G := by
    rw [hG, map_pow, dotPoly_id_eq_map]
  rw [hdot]
  have hf : ∀ m, Continuous fun x : Fin 3 → ℝ => MvPolynomial.eval x (AddMonoidAlgebra.coeff G m) :=
    fun m => MvPolynomial.continuous_eval _
  have hcoord : Continuous fun p : S2 => fun i => (p : E3) i := by
    fun_prop
  have hsph : ∀ m, Integrable (fun p : S2 => MvPolynomial.eval (fun i => (p : E3) i) (AddMonoidAlgebra.coeff G m))
      sphereMeasure := fun m =>
    ((hf m).comp hcoord).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpl : ∀ m, Integrable (fun a : ℂ => MvPolynomial.eval (nS a) (AddMonoidAlgebra.coeff G m) *
      (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) := fun m =>
    (key _ (hf m).measurable).1.2 (hsph m)
  have hsupp : (momentPoly sphereMeasure (fun _ => 1) (MvPolynomial.map coordHom G)).support ⊆ G.support := by
    intro m hm
    by_contra h
    rw [mem_support_iff] at hm
    apply hm
    rw [GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly, coeff_map, notMem_support_iff.1 h]
    simp
  rw [linear_expand ℓ G.support _ hsupp, Finset.mul_sum]
  have hpt : ∀ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) = ∑ m ∈ G.support,
      (MvPolynomial.eval (nS a) (AddMonoidAlgebra.coeff G m) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) *
        (Real.pi * ℓ (monomial m 1)) := fun a => by
    rw [hlin, linear_expand ℓ G.support _ (support_map_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_map, wS]
    have hpi := Real.pi_ne_zero
    field_simp
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => (hpl m).mul_const _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, (key _ (hf m).measurable).2,
    GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly]
  simp only [coeff_map, one_mul, coordHom_apply]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

