module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFormulaOfInvM
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

lemma rp_mk (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (QuotientGroup.mk g : G ⧸ P) = p * g⁻¹ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul P g
  refine ⟨(k : G)⁻¹, P.inv_mem k.2, ?_⟩
  have : Quotient.out (QuotientGroup.mk g : G ⧸ P) = g * k := hk
  simp [rp, this]

lemma rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  obtain ⟨p, hp, e⟩ := rp_mk P (x⁻¹ * Quotient.out q)
  refine ⟨p, hp, ?_⟩
  have hq : (QuotientGroup.mk (x⁻¹ * Quotient.out q) : G ⧸ P) = x⁻¹ • q := by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [← hq, e]
  simp [rp]

lemma rp_mk_mem_iff {P : Subgroup G} {Ω : Set G} (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (g : G) :
    rp (QuotientGroup.mk g : G ⧸ P) ∈ Ω ↔ g⁻¹ ∈ Ω := by
  obtain ⟨p, hp, e⟩ := rp_mk P g
  rw [e]
  refine ⟨fun H => ?_, hl p hp _⟩
  simpa using hl p⁻¹ (P.inv_mem hp) _ H

def coord {N : Type} [Zero N] {P : Subgroup G} (Ω : Set G) (τ : G → N) (q : G ⧸ P) : N :=
  open Classical in if rp q ∈ Ω then τ (rp q) else 0

lemma coord_of_mem {N : Type} [Zero N] {P : Subgroup G} {Ω : Set G} {τ : G → N} {q : G ⧸ P}
    (hq : rp q ∈ Ω) : coord Ω τ q = τ (rp q) := by
  simp [coord, hq]

lemma isOpen_bar [IsTopologicalGroup G] {N : Type} [TopologicalSpace N] {P : Subgroup G} {Ω : Set G}
    {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) {U : Set N} (hU : IsOpen U) :
    IsOpen {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
  have hl' : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω := fun p hp x hx => (hl p hp x hx).1
  rw [← (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.isOpen_preimage]
  have : (QuotientGroup.mk : G → G ⧸ P) ⁻¹' {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U}
      = (fun g : G => g⁻¹) ⁻¹' (Ω ∩ τ ⁻¹' U) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [rp_mk_mem_iff hl' g]
    obtain ⟨p, hp, e⟩ := rp_mk P g
    refine and_congr_right fun hg => ?_
    rw [e, (hl p hp _ hg).2]
  rw [this]
  exact (hτ.isOpen_inter_preimage hΩ hU).preimage continuous_inv

lemma measurable_coord [IsTopologicalGroup G] {N : Type} [AddCommGroup N] [TopologicalSpace N]
    [MeasurableSpace N] [BorelSpace N] {P : Subgroup G} [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    {Ω : Set G} {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) : Measurable (coord Ω τ : G ⧸ P → N) := by
  refine measurable_of_isOpen fun U hU => ?_
  have hA := (isOpen_bar (P := P) hΩ hl hτ hU).measurableSet
  have hB : MeasurableSet {q : G ⧸ P | rp q ∈ Ω} := by
    have := (isOpen_bar (P := P) hΩ hl hτ (isOpen_univ (X := N))).measurableSet
    simpa using this
  by_cases h0 : (0 : N) ∈ U
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} ∪ {q : G ⧸ P | rp q ∈ Ω}ᶜ := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA.union hB.compl
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA

theorem cellFormula_of_invM (hI : InvM) : CellFormula := by
  intro G _ _ _ _ _ _ P _ _ h mu hs ν hν N _ _ _ _ _ _ _ _ lam _ Ω τ w nb hc hInv hh hnull
  haveI : IsFiniteMeasure ν := hν.1
  have ρc : Continuous fun y => h (w * nb y) := hs.cont.comp (continuous_const.mul hc.nbCont)
  have ρpos : ∀ y, 0 < h (w * nb y) := fun y => hs.pos _
  let D : N → ℝ≥0 := fun y => (1 / h (w * nb y)).toNNReal
  have Dc : Continuous D :=
    continuous_real_toNNReal.comp (continuous_const.div ρc fun y => (ρpos y).ne')
  have Dm : Measurable D := Dc.measurable
  let T : G ⧸ P → N := coord Ω τ
  have Tm : Measurable T := measurable_coord hc.isOpen hc.left hc.cont
  let lam' : Measure N := (ν.map T).withDensity fun y => (D y : ℝ≥0∞)
  have hlin : ∀ φ : N → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂lam' = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro φ hφ
    have h1 : Measurable fun y => (D y : ℝ≥0∞) := Dm.coe_nnreal_ennreal
    rw [lintegral_withDensity_eq_lintegral_mul _ h1 hφ, lintegral_map (h1.mul hφ) Tm]
    rfl
  have hae : ∀ᵐ q ∂ν, rp q ∈ Ω := by
    rw [ae_iff]
    exact hnull
  have hshift : ∀ (a : N) (φ : N → ℝ≥0∞), Measurable φ →
      ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (a + T q) ∂ν = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro a φ hφ
    have hF : Measurable fun q => (D (T q) : ℝ≥0∞) * φ (T q) :=
      ((Dm.comp Tm).coe_nnreal_ennreal).mul (hφ.comp Tm)
    rw [← (hI G P h mu hs ν hν (nb a) (hInv a)).2 _ hF]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    obtain ⟨p, hp, e⟩ := rp_smul P (nb a) q
    have hr := hc.right a _ hq
    have hl := hc.left p hp _ hr.1
    have hmem : rp ((nb a)⁻¹ • q) ∈ Ω := e ▸ hl.1
    have e1 : T ((nb a)⁻¹ • q) = τ (rp q) + a := by
      change coord Ω τ _ = _
      rw [coord_of_mem hmem, e, hl.2, hr.2]
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e1, e0, add_comm a]
    have hq1 := hh a _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p2 := ρpos (y + a)
    have p3 := hs.pos (rp q)
    have hD : (D y : ℝ≥0∞) = (D (y + a) : ℝ≥0∞) * ENNReal.ofReal (h (rp q * nb a) / h (rp q)) := by
      change ENNReal.ofReal _ = ENNReal.ofReal _ * _
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      linarith
    rw [hD]
    ring
  haveI hinv : lam'.IsAddLeftInvariant := by
    refine ⟨fun a => Measure.ext fun S hS => ?_⟩
    rw [Measure.map_apply (measurable_const_add a) hS]
    have hS' : MeasurableSet ((fun y => a + y) ⁻¹' S) := measurable_const_add a hS
    have hi : Measurable (S.indicator (1 : N → ℝ≥0∞)) := measurable_one.indicator hS
    have hi' : ((fun y => a + y) ⁻¹' S).indicator (1 : N → ℝ≥0∞)
        = fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) := by
      ext y
      by_cases hy : a + y ∈ S
      · rw [Set.indicator_of_mem (show y ∈ (fun y => a + y) ⁻¹' S from hy), Set.indicator_of_mem hy]
        rfl
      · rw [Set.indicator_of_notMem (show y ∉ (fun y => a + y) ⁻¹' S from hy),
          Set.indicator_of_notMem hy]
    have hi2 : Measurable fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) :=
      hi.comp (measurable_const_add a)
    rw [← lintegral_indicator_one hS', ← lintegral_indicator_one hS, hi', hlin _ hi2, hlin _ hi]
    exact hshift a _ hi
  haveI : IsLocallyFiniteMeasure lam' := IsLocallyFiniteMeasure.withDensity_coe Dc
  have e := Measure.isAddLeftInvariant_eq_smul lam' lam
  refine ⟨Measure.addHaarScalarFactor lam' lam, fun f hf hoc => ?_⟩
  rw [← e]
  have gc : Continuous fun y => f (w * nb y) := hf.1.comp (continuous_const.mul hc.nbCont)
  have ψc : Continuous fun y => D y • f (w * nb y) := Dc.smul gc
  have hcomp : (fun q => D (T q) • f (w * nb (T q))) =ᵐ[ν] fun q => f (rp q) / h (rp q) := by
    filter_upwards [hae] with q hq
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e0]
    have h1 := hoc _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p3 := hs.pos (rp q)
    have hDy : ((D y : ℝ≥0) : ℝ) = 1 / h (w * nb y) := Real.coe_toNNReal _ (by positivity)
    have c1 : (h (w * nb y) : ℂ) ≠ 0 := by exact_mod_cast p1.ne'
    have c3 : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast p3.ne'
    rw [NNReal.smul_def, Complex.real_smul, hDy]
    push_cast
    field_simp
    linear_combination -h1
  obtain ⟨hint, hmu⟩ := hν.2 f hf
  constructor
  · refine (integrable_withDensity_iff_integrable_smul Dm).2 ?_
    refine (integrable_map_measure ψc.aestronglyMeasurable Tm.aemeasurable).2 ?_
    exact hint.congr hcomp.symm
  · rw [hmu]
    change _ = ∫ y, f (w * nb y) ∂((ν.map T).withDensity fun y => (D y : ℝ≥0∞))
    rw [integral_withDensity_eq_integral_smul Dm, integral_map Tm.aemeasurable ψc.aestronglyMeasurable]
    exact (integral_congr_ae hcomp).symm

end GlobalTheory.CompanionTheory.RswCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CntBasicOfKerBasic
section
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelCount

theorem cnt_ne_top (X : Ctx) (Ω : Set X.G) (hΩ : IsCompact Ω) (x : X.G) : cnt X.Γ Ω x ≠ ⊤ := by
  have hC : IsCompact ((fun z => x * z * x⁻¹) '' Ω) :=
    hΩ.image (by fun_prop)
  have hfin := X.proper _ hC
  have hsupp : (Function.support fun γ : X.Γ =>
      Ω.indicator (1 : X.G → ℝ≥0∞) (x⁻¹ * (γ : X.G) * x)) ⊆ (hfin.toFinset : Set X.Γ) := by
    intro γ hγ
    have hmem : x⁻¹ * (γ : X.G) * x ∈ Ω := by
      by_contra h
      exact hγ (Set.indicator_of_notMem h _)
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    exact ⟨_, hmem, by group⟩
  unfold cnt
  rw [tsum_eq_sum (s := hfin.toFinset) (fun γ hγ => by
    by_contra h
    exact hγ (by simpa using hsupp h))]
  refine (ENNReal.sum_lt_top.2 fun γ _ => ?_).ne
  refine lt_of_le_of_lt (Set.indicator_le_self' (fun _ _ => zero_le) _) ?_
  simp

theorem cnt_mul_left (X : Ctx) (Ω : Set X.G) (γ : X.G) (hγ : γ ∈ X.Γ) (x : X.G) :
    cnt X.Γ Ω (γ * x) = cnt X.Γ Ω x := by
  unfold cnt
  rw [← Equiv.tsum_eq (MulAut.conj (⟨γ, hγ⟩ : X.Γ)).toEquiv]
  refine tsum_congr fun δ => ?_
  have : (γ * x)⁻¹ * (((MulAut.conj (⟨γ, hγ⟩ : X.Γ)).toEquiv δ : X.Γ) : X.G) * (γ * x)
      = x⁻¹ * (δ : X.G) * x := by
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, Subgroup.coe_mul,
      InvMemClass.coe_inv]
    group
  rw [this]

theorem cnt_mono (X : Ctx) {Ω Ω' : Set X.G} (h : Ω ⊆ Ω') (x : X.G) :
    cnt X.Γ Ω x ≤ cnt X.Γ Ω' x :=
  ENNReal.tsum_le_tsum fun _ => Set.indicator_le_indicator_of_subset h (fun _ => zero_le) _

theorem enorm_le_indicator {G : Type} [TopologicalSpace G] (φ : G → ℂ) (B : ℝ)
    (hB : ∀ z, ‖φ z‖ ≤ B) (z : G) :
    ‖φ z‖ₑ ≤ ENNReal.ofReal B * (tsupport φ).indicator (1 : G → ℝ≥0∞) z := by
  by_cases hz : z ∈ tsupport φ
  · rw [Set.indicator_of_mem hz, Pi.one_apply, mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB z)
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp

theorem cntBasic_of_kerBasic (h : KerBasic) : CntBasic := by
  intro X
  refine ⟨fun Ω hΩ x => cnt_ne_top X Ω hΩ x, fun Ω γ hγ x => cnt_mul_left X Ω γ hγ x,
    fun Ω Ω' hs x => cnt_mono X hs x, fun φ B hφ hB x => ?_⟩
  obtain ⟨-, -, -, -, -, hk⟩ := h X φ hφ
  refine (hk x x).trans ?_
  unfold cnt
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun γ => enorm_le_indicator φ B hB _

end GlobalTheory.CompanionTheory.KernelCount

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoarseLipschitzExponentialEstimate
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.EisCross

open PositivityTheory.RgEis

theorem pos_nonneg' {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (g : G) : 0 ≤ pos Δ P l g := by
  unfold pos
  exact tsum_nonneg fun _ => (Real.exp_pos _).le

theorem pos_mul_le {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (C : Set G) (A : ℝ)
    (hA : ∀ g, ∀ u ∈ C, |l (g * u) - l g| ≤ A) (hc : Conv Δ P l) (y v : G) (hv : v ∈ C) :
    pos Δ P l (y * v) ≤ Real.exp A * pos Δ P l y := by
  unfold pos
  have hle : ∀ q : Cos P Δ, Real.exp (l (rep q * (y * v))) ≤ Real.exp A * Real.exp (l (rep q * y)) := by
    intro q
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hA (rep q * y) v hv
    rw [mul_assoc] at h
    have h' := (abs_le.mp h).2
    linarith
  have hs : Summable fun q : Cos P Δ => Real.exp A * Real.exp (l (rep q * y)) := (hc y).mul_left _
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hs) hs

theorem exp_between (e₁ e₂ t s : ℝ) (h₁ : e₁ ≤ t) (h₂ : t ≤ e₂) :
    Real.exp (t * s) ≤ Real.exp (e₁ * s) + Real.exp (e₂ * s) := by
  rcases le_total 0 s with hs | hs
  · have h3 : t * s ≤ e₂ * s := mul_le_mul_of_nonneg_right h₂ hs
    have h4 := Real.exp_le_exp.mpr h3
    have h5 := Real.exp_pos (e₁ * s)
    linarith
  · have h3 : t * s ≤ e₁ * s := mul_le_mul_of_nonpos_right h₁ hs
    have h4 := Real.exp_le_exp.mpr h3
    have h5 := Real.exp_pos (e₂ * s)
    linarith

theorem exp_shift (e a b A : ℝ) (h : |a - b| ≤ A) :
    Real.exp (e * a) ≤ Real.exp (|e| * A) * Real.exp (e * b) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : e * (a - b) ≤ |e| * |a - b| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h2 : |e| * |a - b| ≤ |e| * A := mul_le_mul_of_nonneg_left h (abs_nonneg e)
  have h3 : e * (a - b) = e * a - e * b := by ring
  linarith

theorem dom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (Γ Δ P P' : Subgroup G) (ξ l₁ l₂ : G → ℝ) (H : ℂ → G → X)
    (a b e₁ e₂ M : ℝ),
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |ξ (g * u) - ξ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₁ (g * u) - l₁ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₂ (g * u) - l₂ g| ≤ A) →
    PositivityTheory.RgEis.Conv Δ P l₁ → PositivityTheory.RgEis.Conv Δ P' l₂ →
    (∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g, ‖H z g‖ ≤ M * (PositivityTheory.RgEis.pos Δ P l₁ g + PositivityTheory.RgEis.pos Δ P' l₂ g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    ∀ g : G, ∃ U ∈ 𝓝 g, ∃ u : PositivityTheory.RgEis.Cos Δ Γ → ℝ, Summable u ∧
      ∀ l : ℂ × ℂ, b ≤ l.1.re → l.1.re ≤ a → e₁ ≤ l.2.re → l.2.re ≤ e₂ → ∀ g' ∈ U, ∀ r,
        ‖Complex.exp (l.2 * ξ (PositivityTheory.RgEis.rep r * g')) • H l.1 (PositivityTheory.RgEis.rep r * g')‖ ≤ u r := by
  intro G _ _ _ _ X _ _ Γ Δ P P' ξ l₁ l₂ H a b e₁ e₂ M hξ hl₁ hl₂ hc₁ hc₂ hH s11 s21 s12 s22 g
  obtain ⟨C, hC1, -, hCc⟩ := local_compact_nhds (x := (1 : G)) Filter.univ_mem
  obtain ⟨Aξ, hAξ⟩ := hξ C hCc
  obtain ⟨A₁, hA₁⟩ := hl₁ C hCc
  obtain ⟨A₂, hA₂⟩ := hl₂ C hCc
  have hU : (fun g' => g⁻¹ * g') ⁻¹' C ∈ 𝓝 g := by
    apply (continuous_const_mul g⁻¹).continuousAt.preimage_mem_nhds
    simpa using hC1
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' C, hU, fun r => |M| *
      (Real.exp (|e₁| * Aξ) * Real.exp A₁ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₁ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₁| * Aξ) * Real.exp A₂ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₂ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g))), ?_, ?_⟩
  · exact Summable.mul_left |M|
      ((((s11 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₁)).add
        ((s21 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₁))).add
        ((s12 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₂)) |>.add
        ((s22 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₂)))
  · intro l hb ha he₁ he₂ g' hg' r
    have hw : g⁻¹ * g' ∈ C := hg'
    have hy : rep r * g' = rep r * g * (g⁻¹ * g') := by
      rw [mul_assoc, mul_inv_cancel_left]
    have hnorm : ‖Complex.exp (l.2 * ξ (rep r * g')) • H l.1 (rep r * g')‖ =
        Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖ := by
      rw [norm_smul, Complex.norm_exp]
      simp [Complex.mul_re]
    have hξw := hAξ (rep r * g) (g⁻¹ * g') hw
    rw [← hy] at hξw
    have hexp : Real.exp (l.2.re * ξ (rep r * g')) ≤
        Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
          Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by
      have h0 := exp_between e₁ e₂ l.2.re (ξ (rep r * g')) he₁ he₂
      have h1 := exp_shift e₁ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      have h2 := exp_shift e₂ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      linarith
    have hp1 : pos Δ P l₁ (rep r * g') ≤ Real.exp A₁ * pos Δ P l₁ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P l₁ C A₁ hA₁ hc₁ (rep r * g) (g⁻¹ * g') hw
    have hp2 : pos Δ P' l₂ (rep r * g') ≤ Real.exp A₂ * pos Δ P' l₂ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P' l₂ C A₂ hA₂ hc₂ (rep r * g) (g⁻¹ * g') hw
    have hH1 := hH l.1 hb ha (rep r * g')
    have hs0 : 0 ≤ pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g') :=
      add_nonneg (pos_nonneg' _ _ _ _) (pos_nonneg' _ _ _ _)
    have hH2 : ‖H l.1 (rep r * g')‖ ≤ |M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g')) :=
      hH1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) hs0)
    have hE0 : 0 ≤ Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by positivity
    rw [hnorm]
    calc Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖
        ≤ Real.exp (l.2.re * ξ (rep r * g')) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_left hH2 (Real.exp_pos _).le
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_right hexp (mul_nonneg (abs_nonneg M) hs0)
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (Real.exp A₁ * pos Δ P l₁ (rep r * g) + Real.exp A₂ * pos Δ P' l₂ (rep r * g))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) (abs_nonneg M)) hE0
      _ = _ := by ring

end GlobalTheory.CompanionTheory.EisCross
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeFnSumAe
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OpEx

open PositivityTheory.Rg.BcB.E1

theorem coeFn_sum_ae {α : Type} [MeasurableSpace α] {ν : Measure α} {ι : Type} (s : Finset ι)
    (g : ι → Lp ℂ 2 ν) :
    ((∑ j ∈ s, g j : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] fun x => ∑ j ∈ s, (g j : α → ℂ) x :=
  _root_.UpperTheory.Reformulated.B.Yxa1.main s g

theorem opExA : KerBasic → RowInt → SchurOp → OpExA := by
  intro hK hR hS X ι _ Φ hΦ
  classical
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hex : ∀ i j, ∃ T : Lp ℂ 2 X.ν →L[ℂ] Lp ℂ 2 X.ν, ∀ f, (T f : X.G → ℂ) =ᵐ[X.ν]
      fun x => ∫ y, ker X.Γ (Φ i j) x y * (f : X.G → ℂ) y ∂X.ν := by
    intro i j
    obtain ⟨A, hA, h1, h2⟩ := hR X (Φ i j) (hΦ i j)
    have hc := (hK X (Φ i j) (hΦ i j)).2.1
    exact hS X.G X.ν (ker X.Γ (Φ i j)) A hc.measurable hA h1 h2
  choose S hSop using hex
  let T : X.Hs ι →L[ℂ] X.Hs ι :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 X.ν)).symm :
        (ι → Lp ℂ 2 X.ν) →L[ℂ] X.Hs ι) ∘L
      ContinuousLinearMap.pi fun i => ∑ j, (S i j).comp (PiLp.proj 2 (fun _ : ι => Lp ℂ 2 X.ν) j)
  have hT : ∀ f i, T f i = ∑ j, S i j (f j) := by
    intro f i
    simp [T, ContinuousLinearMap.sum_apply]
  have hIs : X.IsOp Φ T := by
    intro f i
    rw [hT]
    have hall : ∀ᵐ x ∂X.ν, ∀ j, (S i j (f j) : X.G → ℂ) x =
        ∫ y, ker X.Γ (Φ i j) x y * (f j : X.G → ℂ) y ∂X.ν :=
      ae_all_iff.2 fun j => hSop i j (f j)
    filter_upwards [coeFn_sum_ae Finset.univ (fun j => S i j (f j)), hall] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => h2 j
  refine ⟨T, hIs, ?_⟩
  intro T' hT'
  ext f : 1
  refine PiLp.ext fun i => Lp.ext ?_
  exact (hT' f i).trans (hIs f i).symm

end GlobalTheory.CompanionTheory.OpEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofaceRel
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem coface_rel (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i))
    (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)) :
    (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i) := by
  have key : ∀ j : Fin n,
      (k.succAbove i).succAbove ((i.predAbove k).succAbove j) = k.succAbove (i.succAbove j) :=
    fun j => Fin.succAbove_succAbove_succAbove_predAbove k i j
  apply AlgHom.coe_ringHom_injective
  refine (hwp n).uniq (K (n + 1 + 1)) _ _ ?_ ?_
  · rw [AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]
  · intro j
    have h1 : ((δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k))).comp (ι n j)
        = ((δ (n + 1) k).comp (δ n i)).comp (ι n j) := by
      rw [AlgHom.comp_assoc, hδ, hδ, AlgHom.comp_assoc, hδ, hδ, key]
    ext x
    exact AlgHom.congr_fun h1 x

end GlobalTheory.CompanionTheory.WpCoface
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCosetRepsOpenInCompactStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_reps_open_in_compact : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (A L : AddSubgroup X), IsCompact (A : Set X) → IsOpen (L : Set X) → L ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen <;> assumption)
end

