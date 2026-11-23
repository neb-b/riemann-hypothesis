module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open MeasureTheory Set

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H] [SecondCountableTopology H] {ν : Measure H} [ν.IsHaarMeasure] {K : Subgroup H}

theorem pres_right (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) {k : H} (hk : k ∈ K) :
    MeasurePreserving (· * k) ν ν := by
  have e := Measure.isMulLeftInvariant_eq_smul (ν.map (· * k)) ν
  have m : Measurable fun x : H => x * k := measurable_mul_const k
  have e2 := congrArg (· (K : Set H)) e
  have p : (fun x : H => x * k) ⁻¹' K = K := Set.ext fun x => K.mul_mem_cancel_right hk
  simp only [Measure.map_apply m hK, p, h1, Measure.coe_nnreal_smul_apply, mul_one] at e2
  refine ⟨m, ?_⟩
  rw [e, show Measure.haarScalarFactor (ν.map (· * k)) ν = 1 by exact_mod_cast e2.symm, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G] {μ : Measure G} [μ.IsHaarMeasure]

theorem factor (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) (i : H →* G) (hi : Continuous i) (π : G → H) (hπ : Continuous π)
    (e : ∀ u g, π (i u * g) = u * π g) {f : G → ℂ} {l : H → ℂ} (hf : Integrable f μ)
    (hl : ∀ u g, π g = 1 → f (i u * g) = l u * f g) (hl1 : ∀ u ∈ K, l u = 1) {A : Set G} (hA : MeasurableSet A)
    (hAi : ∀ u g, i u * g ∈ A ↔ g ∈ A) : ∫ g in A, f g ∂μ = (∫ u, l u ∂ν) * ∫ g in A ∩ π ⁻¹' K, f g ∂μ := by
  let S : Set (H × G) := {p | p.1⁻¹ * π p.2 ∈ K}
  have hS : MeasurableSet S := (continuous_fst.inv.mul (hπ.comp continuous_snd)).measurable hK
  let Φ : H × G → ℂ := S.indicator fun p => A.indicator f p.2
  have vol : ∀ g, ν {u | u⁻¹ * π g ∈ K} = 1 := fun g => by
    rw [← h1, ← measure_preimage_mul ν (π g)⁻¹ K]
    congr 1
    ext u
    exact (K.inv_mem_iff.symm.trans (by simp))
  have mS : ∀ g, MeasurableSet {u | u⁻¹ * π g ∈ K} := fun g => (continuous_inv.mul continuous_const).measurable hK
  have sl : ∀ g, (fun u => Φ (u, g)) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => A.indicator f g := fun g => rfl
  have hfA := hf.indicator hA
  have iΦ : Integrable Φ (ν.prod μ) := by
    refine (integrable_prod_iff' (hfA.1.comp_snd.indicator hS)).2 ⟨Filter.Eventually.of_forall fun g => ?_, ?_⟩
    · rw [sl, integrable_indicator_iff (mS g)]
      exact integrableOn_const (by simp [vol])
    · refine hfA.norm.congr (Filter.Eventually.of_forall fun g => ?_)
      have : (fun u => ‖Φ (u, g)‖) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => ‖A.indicator f g‖ :=
        funext fun u => by rw [congrFun (sl g) u, norm_indicator_eq_indicator_norm]
      show _ = ∫ u, ‖Φ (u, g)‖ ∂ν
      rw [this, integral_indicator_const _ (mS g), Measure.real, vol]
      simp
  have sh : MeasurePreserving (fun p : H × G => (p.1, i p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun u g => i u * g) ((hi.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun u => map_mul_left_eq_self μ (i u))
  have i2 := sh.integrable_comp_of_integrable iΦ
  have mB : MeasurableSet (A ∩ π ⁻¹' K) := hA.inter (hπ.measurable hK)
  calc ∫ g in A, f g ∂μ = ∫ g, ∫ u, Φ (u, g) ∂ν ∂μ := by
        rw [← integral_indicator hA]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [sl]
        rw [integral_indicator_const _ (mS g), Measure.real, vol]
        simp
    _ = ∫ u, ∫ g, Φ (u, i u * g) ∂μ ∂ν := by
        rw [← integral_integral_swap (f := fun u g => Φ (u, g)) iΦ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun u =>
          (integral_mul_left_eq_self (fun g => Φ (u, g)) (i u)).symm)
    _ = ∫ g, ∫ u, Φ (u, i u * g) ∂ν ∂μ := integral_integral_swap (f := fun u g => Φ (u, i u * g)) i2
    _ = _ := by
        rw [← integral_const_mul, ← integral_indicator mB]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        by_cases hg : g ∈ A ∩ π ⁻¹' K
        · have z : π (i (π g)⁻¹ * g) = 1 := by rw [e, inv_mul_cancel]
          have w : ∀ u, f (i u * g) = l (u * π g) * f (i (π g)⁻¹ * g) := fun u => by
            rw [← hl _ _ z, ← mul_assoc, ← map_mul, mul_inv_cancel_right]
          have w1 := w 1
          rw [map_one, one_mul, one_mul, hl1 _ hg.2, one_mul] at w1
          have : ∀ u, Φ (u, i u * g) = l (u * π g) * f g := fun u => by
            simp only [Φ]
            rw [indicator_of_mem (show (u, i u * g) ∈ S by simpa [S, e] using hg.2), indicator_of_mem ((hAi u g).2 hg.1), w, w1]
          simp only [this]
          rw [indicator_of_mem hg, integral_mul_const,
            (pres_right hK h1 hg.2).integral_comp (Homeomorph.mulRight (π g)).measurableEmbedding l]
        · have : ∀ u, Φ (u, i u * g) = 0 := fun u => by
            simp only [Φ]
            by_cases h2 : π g ∈ K
            · exact indicator_apply_eq_zero.2 fun _ => indicator_of_notMem (fun h => hg ⟨(hAi u g).1 h, h2⟩) _
            · exact indicator_of_notMem (by simpa [S, e] using h2) _
          simp only [this]
          rw [indicator_of_notMem hg, integral_zero]

end GlobalTheory.ThK.Dbl.Euler

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open MeasureTheory Filter Topology

def BC {X : Type} [TopologicalSpace X] (f : X → ℂ) : Prop := Continuous f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

section

variable {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {f g : X → ℂ}

theorem BC.mul (h : BC f) (h' : BC g) : BC fun x => f x * g x := by
  obtain ⟨a, C, hC⟩ := h
  obtain ⟨b, C', hC'⟩ := h'
  exact ⟨a.mul b, C * C', fun x => (norm_mul_le _ _).trans
    (mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))⟩

theorem BC.star (h : BC f) : BC fun x => star (f x) := ⟨h.1.star, h.2.imp fun _ h x => (norm_star _).trans_le (h x)⟩

theorem BC.comp (h : BC f) {u : X' → X} (hu : Continuous u) : BC fun x => f (u x) := ⟨h.1.comp hu, h.2.imp fun _ h _ => h _⟩

theorem BC.int [MeasurableSpace X] [OpensMeasurableSpace X] (h : BC f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ :=
  .of_bound h.1.aestronglyMeasurable _ (.of_forall h.2.choose_spec)

end

variable {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (ν : Measure G) [IsFiniteMeasure ν] (ρ : Measure H) [IsFiniteMeasure ρ] {φ : G → ℂ}

theorem at_value {θ : H × G → ℂ} (hθ : BC θ) (hφ : BC φ) :
    ∫ y, (∫ g, θ (g, y.1) * star (θ (g, y.2)) ∂ρ) * (φ y.2 * star (φ y.1)) ∂ν.prod ν =
      ∫ g, (∫ h, φ h * star (θ (g, h)) ∂ν) * star (∫ h, φ h * star (θ (g, h)) ∂ν) ∂ρ := by
  simp only [← integral_mul_const]
  rw [integral_integral_swap (f := fun (y : G × G) g => θ (g, y.1) * star (θ (g, y.2)) * (φ y.2 * star (φ y.1)))
    (BC.int (((hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.1)) (by fun_prop)).mul
      (hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.2)) (by fun_prop)).star).mul
      ((hφ.comp (by fun_prop)).mul (hφ.comp (by fun_prop)).star)) _)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  simp only [integral_mul_const]
  rw [mul_comm, Complex.star_def, ← integral_conj, ← integral_prod_mul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

theorem far_right [Group G] [ContinuousMul G] (μ : Measure G) [SFinite μ] {k : G × G → ℂ} {w : G → ℂ} (hk : BC k) (hφ : BC φ)
    (hw : Integrable w μ) (h : ∀ h, ∫ h', k (h, h') * φ h' ∂ν = ∫ g, w g * φ (h * g) ∂μ) :
    ∫ y, k y * (φ y.2 * star (φ y.1)) ∂ν.prod ν = ∫ g, w g * ∫ h, φ (h * g) * star (φ h) ∂ν ∂μ := by
  rw [integral_prod _ (BC.int (hk.mul ((hφ.comp continuous_snd).mul (hφ.comp continuous_fst).star)) _)]
  simp only [← mul_assoc, integral_mul_const, h]
  simp only [← integral_mul_const, ← integral_const_mul, mul_assoc]
  obtain ⟨c, C, hC⟩ := (hφ.comp (u := fun y : G × G => y.1 * y.2) (by fun_prop)).mul (hφ.comp continuous_fst).star
  exact integral_integral_swap (f := fun h g => w g * (φ (h * g) * star (φ h)))
    ((hw.comp_snd ν).mul_bdd c.aestronglyMeasurable (.of_forall hC))

theorem ident {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {g g' : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg' : DifferentiableOn ℂ g' U) {t : ℝ} (h : ∀ s : ℂ, t < s.re → s ∈ U ∧ g s = g' s) {s : ℂ} (hs : s ∈ U) : g s = g' s := by
  have h1 : t < ((t + 1 : ℝ) : ℂ).re := by simp
  refine (hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg'.analyticOnNhd hU) hc (h _ h1).1 ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz using (h z hz).2

end GlobalTheory.ThK.Dbl.An

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HgtCount
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped NNReal ENNReal
open MeasureTheory Topology

theorem exists_cover {A : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (ν : Measure A) [ν.IsAddLeftInvariant]
    {X V Z : Set A} (hV : MeasurableSet V) (h0 : ν V ≠ 0) (hZ : ν Z ≠ ⊤) (hXZ : ∀ x ∈ X, ∀ v ∈ V, x + v ∈ Z) :
    ∃ s : Finset A, s.card * ν V ≤ ν Z ∧ ∀ x ∈ X, ∃ y ∈ s, ∃ v ∈ V, ∃ v' ∈ V, x - y = v - v' := by
  classical
  by_contra! h
  let T : A → Set A := fun x => (fun a => -x + a) ⁻¹' V
  have bd : ∀ s : Finset A, (s : Set A) ⊆ X → (s : Set A).PairwiseDisjoint T → s.card * ν V ≤ ν Z := fun s h1 h2 => by
    have := measure_biUnion_finset (μ := ν) h2 fun b _ => measurable_const_add _ hV
    simp only [T, measure_preimage_add, Finset.sum_const, nsmul_eq_mul] at this
    rw [← this]
    exact measure_mono (Set.iUnion₂_subset fun x hx a ha => by simpa using hXZ x (h1 hx) _ ha)
  obtain ⟨v₀, hv₀⟩ := nonempty_of_measure_ne_zero h0
  have key : ∀ k : ℕ, ∃ s : Finset A, s.card = k ∧ (s : Set A) ⊆ X ∧ (s : Set A).PairwiseDisjoint T := fun k => by
    induction k with
    | zero => exact ⟨∅, rfl, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨s, rfl, h1, h2⟩ := ih
      obtain ⟨x, hx, hx'⟩ := h s (bd s h1 h2)
      refine ⟨insert x s, Finset.card_insert_of_notMem fun hs => hx' x hs v₀ hv₀ v₀ hv₀ (by simp), ?_, ?_⟩
      · rw [Finset.coe_insert]; exact Set.insert_subset hx h1
      · rw [Finset.coe_insert]
        exact h2.insert fun y hy _ => Set.disjoint_left.2 fun a ha hb => hx' y hy (-y + a) hb (-x + a) ha (by rw [add_sub_add_right_eq_sub, neg_sub_neg])
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 hZ
  obtain ⟨s, rfl, h1, h2⟩ := key N
  exact hN.not_ge (bd s h1 h2)

theorem integrable_of_count {G : Type} [MeasurableSpace G] (μ : Measure G) {f : G → ℝ} (hf : Measurable f) (h0 : ∀ g, 0 < f g)
    {R : ℝ} (h1 : 1 ≤ R) (hR : ∀ g, f g ≤ R) {C : ℝ≥0∞} (hC : C ≠ ⊤) (b : ℝ≥0)
    (h : ∀ j : ℕ, μ {g | (1 / 2) ^ j ≤ f g} ≤ C * b ^ j) : ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => f g ^ t) μ := by
  classical
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (b + 1) by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, fun t ht => ⟨(hf.pow_const t).aestronglyMeasurable, ?_⟩⟩
  have t0 : 0 ≤ t := (Nat.cast_nonneg k).trans ht
  let P : ℕ → Set G := fun j => {g | (1 / 2) ^ j ≤ f g ∧ f g ≤ 2 * R * (1 / 2) ^ j}
  have hP : ⋃ j, P j = Set.univ := Set.eq_univ_of_forall fun g => by
    have ex : ∃ j : ℕ, (1 / 2 : ℝ) ^ j ≤ f g := (exists_pow_lt_of_lt_one (h0 g) (by norm_num)).imp fun _ => le_of_lt
    refine Set.mem_iUnion.2 ⟨Nat.find ex, Nat.find_spec ex, ?_⟩
    rcases e : Nat.find ex with _ | j
    · have := hR g; simp; linarith
    · have := Nat.find_min ex (m := j) (by omega)
      have p : (0 : ℝ) < (1 / 2) ^ j := by positivity
      rw [pow_succ]; nlinarith
  set ρ : ℝ≥0∞ := ENNReal.ofReal ((1 / 2) ^ t) * b
  have hρ : ρ < 1 := by
    have : ((1 / 2 : ℝ)) ^ t ≤ (1 / 2) ^ k := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht
    rw [lt_div_iff₀ (by positivity)] at hk
    have p : (0 : ℝ) < (1 / 2) ^ t := by positivity
    rw [show ρ = ENNReal.ofReal ((1 / 2) ^ t * b) by rw [ENNReal.ofReal_mul p.le, ENNReal.ofReal_coe_nnreal], ENNReal.ofReal_lt_one]
    nlinarith [b.2, show (0 : ℝ) ≤ b from b.2]
  calc ∫⁻ g, ‖f g ^ t‖ₑ ∂μ = ∫⁻ g in ⋃ j, P j, ‖f g ^ t‖ₑ ∂μ := by rw [hP, Measure.restrict_univ]
    _ ≤ ∑' j, ∫⁻ g in P j, ‖f g ^ t‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal ((2 * R) ^ t) * C * ρ ^ j := ENNReal.tsum_le_tsum fun j => by
      refine (setLIntegral_mono (g := fun _ => ENNReal.ofReal ((2 * R) ^ t) * ENNReal.ofReal ((1 / 2) ^ t) ^ j)
        measurable_const fun g hg => ?_).trans ?_
      · rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (h0 g).le _), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul_natCast (by norm_num), mul_comm t, Real.rpow_natCast_mul (by norm_num),
          ← Real.mul_rpow (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (h0 g).le hg.2 t0)
      · rw [setLIntegral_const]
        refine (mul_le_mul_right ((measure_mono fun g (hg : g ∈ P j) => hg.1).trans (h j)) _).trans_eq ?_
        simp only [ρ, mul_pow]; ring
    _ < ⊤ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.lt_top)
        (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ))

theorem count_grp {R B κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Ring B] [Algebra R B] [TopologicalSpace B]
    [IsTopologicalRing B] [T2Space B] [Fintype κ] (c : B ≃ₗ[R] (κ → R)) (hc : Continuous c) (hc' : Continuous c.symm)
    (H : Subgroup Bˣ) (hH : IsClosed (H : Set Bˣ)) {Ω : Set B} (hΩ : IsCompact Ω) {W : Set R} (hW : IsCompact W) :
    ∃ (X : Set R) (U : Set H), IsCompact X ∧ IsCompact U ∧ ∀ (l : Rˣ) (s : Finset R),
      (∀ x ∈ X, ∃ y ∈ s, ∃ w ∈ W, x - y = l * l * w) → ∀ [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant],
        μ {g | l.1 • g.1.1 ∈ Ω ∧ l.1 • (g⁻¹).1.1 ∈ Ω} ≤ (s.card : ℝ≥0∞) ^ Fintype.card κ * μ U := by
  classical
  let W' : Set ((κ → R) × (κ → R)) := (Set.univ.pi fun _ => W) ×ˢ Set.univ.pi fun _ => W
  let Ω' : Set B := (fun y : B × (κ → R) × (κ → R) => 1 + y.1 * c.symm (y.2.1 - y.2.2)) '' Ω ×ˢ W'
  have hΩ' : IsCompact Ω' := (hΩ.prod ((isCompact_univ_pi fun _ => hW).prod (isCompact_univ_pi fun _ => hW))).image (by fun_prop)
  have em : IsClosedEmbedding (fun k : H => Units.embedProduct B k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  refine ⟨⋃ k, (fun y => c y k) '' Ω, _, isCompact_iUnion fun k => hΩ.image (by fun_prop),
    em.isCompact_preimage (hΩ'.prod (hΩ'.image MulOpposite.continuous_op)), fun l s hs _ _ μ _ => ?_⟩
  let S : (κ → R) → Set H := fun y => {g | l.1 • (g⁻¹).1.1 ∈ Ω ∧ ∀ k, ∃ w ∈ W, c (l.1 • g.1.1) k - y k = l * l * w}
  have key : ∀ y, ∀ g ∈ S y, ∀ g' ∈ S y, (g⁻¹ * g').1.1 ∈ Ω' := fun y g hg g' hg' => by
    choose w hw e using hg.2
    choose w' hw' e' using hg'.2
    refine ⟨(_, w', w), ⟨hg.1, fun k _ => hw' k, fun k _ => hw k⟩, ?_⟩
    have e1 : g'.1.1 - g.1.1 = l.1 • c.symm (w' - w) := by
      refine c.injective (funext fun k => l.isUnit.mul_left_cancel ?_)
      have := e k
      have := e' k
      simp only [map_smul, map_sub, LinearEquiv.apply_symm_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
      linear_combination e' k - e k
    change 1 + l.1 • (g.1⁻¹).1 * c.symm (w' - w) = (g.1⁻¹).1 * g'.1.1
    rw [smul_mul_assoc, ← mul_smul_comm, ← e1, mul_sub, Units.inv_mul, add_sub_cancel]
  refine (measure_mono (t := ⋃ y ∈ Fintype.piFinset fun _ : κ => s, S y) fun g hg => ?_).trans
    ((measure_biUnion_finset_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (μ ((fun k : H => Units.embedProduct B k.1) ⁻¹'
      Ω' ×ˢ (MulOpposite.op '' Ω'))) fun y _ => ?_).trans_eq (by simp)))
  · choose y hy hy' using fun k => hs _ (Set.mem_iUnion.2 ⟨k, _, hg.1, rfl⟩)
    exact Set.mem_iUnion₂.2 ⟨y, Fintype.mem_piFinset.2 hy, hg.2, hy'⟩
  · rcases (S y).eq_empty_or_nonempty with e | ⟨g, hg⟩
    · simp [e]
    · refine (measure_mono ?_).trans_eq (measure_preimage_mul μ g⁻¹ _)
      exact fun g' hg' => ⟨key y g hg g' hg', _, key y g' hg' g hg, by simp⟩

end GlobalTheory.ThK.Dbl.Hgt

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldA
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open MeasureTheory Filter Topology

theorem unfold {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {f : G → ℂ} (hf : Integrable f μ) : ∫ x in D, ∑' γ : Γ, f (γ * x) ∂μ = ∫ x, f x ∂μ := by
  rw [hD.integral_eq_tsum'' f hf]
  refine integral_tsum (fun γ => ((hf.comp_mul_left (γ : G)).aestronglyMeasurable).restrict) ?_
  have := hD.lintegral_eq_tsum'' fun x => ‖f x‖ₑ
  exact (this ▸ hf.2.ne :)

theorem diffOn_integral {X : Type} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {k : ℂ → X → ℂ} (hm : ∀ s ∈ U, AEStronglyMeasurable (k s) μ) (hd : ∀ x, DifferentiableOn ℂ (k · x) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ s ∈ K, ∀ x, ‖k s x‖ ≤ C) :
    DifferentiableOn ℂ (fun s => ∫ x, k s x ∂μ) U := by
  intro s₀ h₀
  obtain ⟨r, hr, hU'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds h₀)
  obtain ⟨C, hC⟩ := hb _ hU' (isCompact_closedBall s₀ r)
  have sub : ∀ s ∈ Metric.ball s₀ (r / 2), Metric.closedBall s (r / 2) ⊆ Metric.closedBall s₀ r := fun s hs =>
    Metric.closedBall_subset_closedBall' (by have := Metric.mem_ball.1 hs; linarith)
  have da : ∀ x, ∀ s ∈ U, HasDerivAt (k · x) (deriv (k · x) s) s := fun x s hs =>
    ((hd x).differentiableAt (hU.mem_nhds hs)).hasDerivAt
  have m' : AEStronglyMeasurable (fun x => deriv (k · x) s₀) μ := by
    classical
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] s₀) (f := fun s x => if s ∈ U then slope (k · x) s₀ s else 0) (fun s => ?_)
      (.of_forall fun x => (hasDerivAt_iff_tendsto_slope.1 (da x s₀ h₀)).congr' ?_)
    · by_cases hs : s ∈ U
      · simp only [if_pos hs, slope_def_module]
        exact ((hm s hs).sub (hm s₀ h₀)).const_smul (s - s₀)⁻¹
      · simp only [if_neg hs]; exact aestronglyMeasurable_const
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h₀)] with s hs using (if_pos hs).symm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (bound := fun _ => C / (r / 2)) (F := k)
    (F' := fun s x => deriv (k · x) s) (Metric.ball_mem_nhds s₀ (half_pos hr))
    (mem_of_superset (hU.mem_nhds h₀) hm) ?_ m' (.of_forall fun x s hs => ?_) (integrable_const _)
    (.of_forall fun x s hs => da x s (hU' (sub s hs (Metric.mem_closedBall_self (half_pos hr).le))))).2.differentiableAt.differentiableWithinAt
  · exact .of_bound (hm s₀ h₀) C (.of_forall (hC s₀ (Metric.mem_closedBall_self hr.le)))
  · exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
      (((hd x).mono ((sub s hs).trans hU')).diffContOnCl_ball subset_rfl)
      fun z hz => hC z (sub s hs (Metric.sphere_subset_closedBall hz)) x

end GlobalTheory.ThK.Dbl.An

end
end

