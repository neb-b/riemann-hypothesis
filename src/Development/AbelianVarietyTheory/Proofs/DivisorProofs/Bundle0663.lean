module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0558
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmEqPSmulAddIntegral
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem exists_p_mul_of_constantCoeff_eq_zero (p : ℕ) [Fact p.Prime] {k : Type} [Field k]
    [CharP k p] [PerfectRing k p] (a : WittVector p k) (ha : WittVector.constantCoeff a = 0) :
    ∃ c : WittVector p k, a = (p : WittVector p k) * c := by
  by_cases h0 : a = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero =>
    exfalso; apply hb
    simpa using ha
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by ring⟩

theorem formalGroupLawCoboundaryOne_sub_eq {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) (f g : MvPowerSeries (Fin d) R) :
    cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  have := formalCoboundary_add h (f - g) g
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem quasiLog_eq_p_smul_add_int : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ),
    ∀ f ∈ quasiLog p h, ∀ b, Red p (cob1 (fun i => Katz.lift p (μ i)) f) (cob1 μ b) →
      RedV p (lin f) (lin b) →
      ∃ g ∈ quasiLog p h, f - (p : WittVector p k) • g ∈ intBy p k (Fin d) 1 := by
  intro p _ k _ _ _ d μ h f hf b hcf hlf
  obtain ⟨R1, -, R3, R4, -, R6, ZariskiNoetherianInduction⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d)
  obtain ⟨-, R1', -, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  obtain ⟨-, C2, -, -⟩ := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  obtain ⟨hcb, hlb⟩ := C2 (Katz.lift p b) b (R3 b)
  set f' := f - Katz.lift p b with hf'

  have hc' : cob1 (fun i => Katz.lift p (μ i)) f' ∈ intBy p k (Fin d ⊕ Fin d) (p : WittVector p k) := by
    obtain ⟨-, -, -, S4, -, S6, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
    rw [S6, hf', formalGroupLawCoboundaryOne_sub_eq hL]
    have := (S4 _ _ _ _ hcf hcb).2
    rwa [sub_self] at this
  obtain ⟨-, -, -, -, -, -, S7⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  obtain ⟨c0, hc0, hc0e⟩ := (S7 _ _).1 hc'
  have hpW : (p : WittVector p k) ≠ 0 := WittVector.p_nonzero p k
  have hpF : (p : Fr p k) ≠ 0 := by
    have : (p : Fr p k) = algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) := by simp
    rw [this]
    exact fun h0 => hpW (IsFractionRing.injective (WittVector p k) (Fr p k) (by simpa using h0))
  have hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)),
      (p : WittVector p k) • x = (p : Fr p k) • x := by
    intro σ x
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) x]
    simp
  have hcg : cob1 (fun i => Katz.lift p (μ i)) ((p : Fr p k)⁻¹ • f') ∈ intBy p k _ 1 := by
    rw [formalCoboundary_smul hL, hc0e, hsm, smul_smul, inv_mul_cancel₀ hpF, one_smul]
    exact hc0
  refine ⟨(p : Fr p k)⁻¹ • f', ⟨?_, hcg⟩, ?_⟩
  · apply _root_.GlobalTheory.Katz.quasiInt_of_cob1_int_of_lin_int p k d μ h _ _ hcg
    intro i
    obtain ⟨a, ha, ha0⟩ := hlf i
    obtain ⟨a', ha', ha0'⟩ := hlb i
    obtain ⟨c, hc⟩ := exists_p_mul_of_constantCoeff_eq_zero p (a - a') (by
      rw [map_sub, ha0, ha0', sub_self])
    refine ⟨c, ?_⟩
    have e1 : lin f' i = algebraMap (WittVector p k) (Fr p k) (a - a') := by
      simp only [lin, hf', map_sub] at ha ha' ⊢
      rw [ha, ha']
    have e2 : lin ((p : Fr p k)⁻¹ • f') i = (p : Fr p k)⁻¹ * lin f' i := by
      simp [lin]
    rw [e2, e1, hc, map_mul]
    simp [hpF]
  · rw [hsm, smul_smul, mul_inv_cancel₀ hpF, one_smul, hf', sub_sub_cancel]
    exact (R1 _).2 ⟨b, R3 b⟩

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmGenerationOfDivisionStepPadic
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.Conv

section SlopeTestRemainingChoices

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem exists_lim {p : ℕ} (h : IsFrame p E (RingHom.id O)) (a : ℕ → O) :
    ∃ L : O, ∀ N : ℕ, ∃ c : O,
      L = ∑ n ∈ Finset.range N, (p : O) ^ n * a n + (p : O) ^ N * c := by
  obtain ⟨L, hL⟩ := h.complete.toIsPrecomplete.prec
    (f := fun N => ∑ n ∈ Finset.range N, (p : O) ^ n * a n) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left]
      exact dvd_neg.2 (Finset.dvd_sum fun k hk => dvd_mul_of_dvd_left
        (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _))
  refine ⟨L, fun N => ?_⟩
  have hN : (∑ n ∈ Finset.range N, (p : O) ^ n * a n) ≡ L
      [SMOD (Ideal.span {(p : O)}) ^ N • (⊤ : Submodule O O)] := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hN
  obtain ⟨c, hc⟩ := hN
  exact ⟨-c, by linear_combination -hc⟩

theorem eq_zero_of_forall {p : ℕ} (h : IsFrame p E (RingHom.id O)) {x : E}
    (hx : ∀ N : ℕ, ∃ b : O, x = algebraMap O E ((p : O) ^ N * b)) : x = 0 := by
  obtain ⟨b, hb⟩ := hx 0
  have h0 : (p : O) ^ 0 * b = 0 := h.eq_zero_of_forall_pow_dvd fun N => by
    obtain ⟨c, hc⟩ := hx N
    exact ⟨c, h.inj (hb.symm.trans hc)⟩
  rw [hb, h0, map_zero]

theorem comb_add_mul {ι : Type} [Fintype ι] (x y : ι → O) (c : O)
    (e : ι → MvPowerSeries (Fin d) E) :
    comb (fun i => x i + c * y i) e = comb x e + algebraMap O E c • comb y e := by
  unfold comb
  simp only [map_add (f := _), map_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

def IntD (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (g : MvPowerSeries (Fin d) E) : Prop :=
  (∀ i, ∃ b : O, lin g i = algebraMap O E b) ∧ In (⊤ : Ideal O) (cob1 (up E μ) g)

variable {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}

theorem up_const (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp [up, hμ]

theorem IntD.ofQL {g : MvPowerSeries (Fin d) E} (hg : QL μ ⊤ g) : IntD μ g :=
  ⟨fun i => (hg.2.1 i).imp fun _ hb => hb.2, hg.2.2⟩

theorem IntD.zero (hμ : ∀ i, constantCoeff (μ i) = 0) : IntD μ (0 : MvPowerSeries (Fin d) E) := by
  have h0 : cob1 (up E μ) (0 : MvPowerSeries (Fin d) E) = 0 := by
    simpa using formalCoboundary_smul (up_const hμ) (0 : E) (0 : MvPowerSeries (Fin d) E)
  refine ⟨fun i => ⟨0, by simp [lin]⟩, fun α => ⟨0, trivial, by simp [h0]⟩⟩

theorem IntD.add (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g + g') := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    obtain ⟨b', hb'⟩ := hg'.1 i
    refine ⟨b + b', ?_⟩
    simp only [lin, map_add (f := _)] at hb hb' ⊢
    rw [hb, hb']
  · obtain ⟨b, -, hb⟩ := hg.2 α
    obtain ⟨b', -, hb'⟩ := hg'.2 α
    exact ⟨b + b', trivial, by rw [formalCoboundary_add (up_const hμ), map_add (f := _), hb, hb', map_add (f := _)]⟩

theorem IntD.smul (hμ : ∀ i, constantCoeff (μ i) = 0) (c : O) {g : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) : IntD μ (algebraMap O E c • g) := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    refine ⟨c * b, ?_⟩
    simp only [lin, coeff_smul] at hb ⊢
    rw [hb, map_mul]
  · obtain ⟨b, -, hb⟩ := hg.2 α
    exact ⟨c * b, trivial, by rw [formalCoboundary_smul (up_const hμ), coeff_smul, hb, map_mul]⟩

theorem IntD.sub (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g - g') := by
  have : g - g' = g + algebraMap O E (-1) • g' := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [this]
  exact hg.add hμ (hg'.smul hμ _)

theorem IntD.comb (hμ : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι] (b : ι → O)
    {e : ι → MvPowerSeries (Fin d) E} (he : ∀ i, IntD μ (e i)) : IntD μ (comb b e) :=
  Finset.sum_induction _ (IntD μ) (fun _ _ h1 h2 => h1.add hμ h2) (IntD.zero hμ)
    fun i _ => (he i).smul hμ (b i)

theorem IntD.map (hμ : ∀ i, constantCoeff (μ i) = 0) (s : MvPowerSeries (Fin d) O) :
    IntD μ (MvPowerSeries.map (algebraMap O E) s) := by
  refine ⟨fun i => ⟨coeff (Finsupp.single i 1) s, by simp [lin, coeff_map]⟩, ?_⟩
  have := ((map_cob_swap_pull O d μ hμ E (algebraMap O E)).1 s).symm
  rw [show cob1 (up E μ) (MvPowerSeries.map (algebraMap O E) s) =
      MvPowerSeries.map (algebraMap O E) (cob1 μ s) from this]
  exact In.top_iff.2 ⟨_, rfl⟩

end SlopeTestRemainingChoices

theorem generate_of_step : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  intro p _ O E _ _ _ h d μ hμ ι _ e he H f hf
  have hc := hμ.const
  choose! bf sf ff hQ hff using H
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → MvPowerSeries (Fin d) E, F 0 = f ∧ ∀ n, F (n + 1) = ff (F n) :=
    ⟨fun n => ff^[n] f, rfl, fun n => Function.iterate_succ_apply' ff n f⟩
  have hFQ : ∀ n, QL μ ⊤ (F n) := by
    intro n
    induction n with
    | zero => rw [hF0]; exact hf
    | succ n ih => rw [hFs]; exact hQ _ ih
  have step : ∀ n, F n = comb (bf (F n)) e + map (algebraMap O E) (sf (F n)) + (p : E) • F (n + 1) :=
    fun n => by rw [hFs]; exact hff _ (hFQ n)
  have hpE : ∀ N : ℕ, (p : E) ^ N = algebraMap O E ((p : O) ^ N) := fun N => by
    rw [map_pow, map_natCast]
  have tele : ∀ N : ℕ, f = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
      ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) + (p : E) ^ N • F N := by
    intro N
    induction N with
    | zero =>
      have : comb (fun _ : ι => (0 : O)) e = 0 := by simp [comb]
      simp only [Finset.range_zero, Finset.sum_empty, this, pow_zero, one_smul, zero_add, hF0]
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [comb_add_mul, ← hpE]
      have hs := step N
      rw [ih] at *
      linear_combination (norm := module) ((p : E) ^ N) • hs
  choose Bv hB using fun i => exists_lim h (fun n => bf (F n) i)
  choose Sc hS using fun α => exists_lim h (fun n => coeff α (sf (F n)))
  obtain ⟨S, hSd⟩ : ∃ S : MvPowerSeries (Fin d) O, ∀ α, coeff α S = Sc α := ⟨Sc, fun _ => rfl⟩
  have key : ∀ N : ℕ, ∃ g, Conv.IntD μ g ∧
      f - comb Bv e - map (algebraMap O E) S = (p : E) ^ N • g := by
    intro N
    choose cB hcB using fun i => hB i N
    choose cS hcS using fun α => hS α N
    obtain ⟨T, hTd⟩ : ∃ T : MvPowerSeries (Fin d) O, ∀ α, coeff α T = cS α := ⟨cS, fun _ => rfl⟩
    refine ⟨F N - comb cB e - map (algebraMap O E) T, ?_, ?_⟩
    · exact ((IntD.ofQL (hFQ N)).sub hc (IntD.comb hc cB fun i => IntD.ofQL (he i))).sub hc
        (IntD.map hc T)
    · have h1 : comb Bv e = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
          (p : E) ^ N • comb cB e := by
        rw [hpE, ← comb_add_mul]
        congr 1
        funext i
        exact hcB i
      have h2 : map (algebraMap O E) S =
          ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) +
            (p : E) ^ N • map (algebraMap O E) T := by
        ext α
        set_option synthInstance.maxHeartbeats 100000 in
          rw [coeff_map, hSd, hcS α, map_add (f := _), map_add (f := _), coeff_smul, coeff_map, hTd, map_sum (coeff α)]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [coeff_smul, coeff_map, map_sum, map_mul, map_pow, map_natCast]
      rw [h1, h2]
      linear_combination (norm := module) tele N
  have hR : f - comb Bv e - map (algebraMap O E) S = 0 := by
    refine _root_.GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions p O E h d μ hμ _ ?_ ?_
    · funext i
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, hb⟩ := hg.1 i
      refine ⟨b, ?_⟩
      rw [hgN]
      simp only [lin, coeff_smul] at hb ⊢
      rw [hb, hpE, map_mul]
    · ext α
      rw [coeff_zero]
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, -, hb⟩ := hg.2 α
      refine ⟨b, ?_⟩
      rw [hgN, formalCoboundary_smul (up_const hc), coeff_smul, hb, hpE, map_mul]
  exact ⟨Bv, In.top_iff.2 ⟨S, (sub_eq_zero.1 hR).symm⟩⟩

end GlobalTheory.QLog.Conv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientHolomorphicMeasurable
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.TwEst.quot_holo_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω →
    A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) →
    (∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧
    Measurable (_root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y)) ∧
    ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * _root_.GlobalTheory.OTY.TwEst.quot A h β y := by
  intro n Y _ _ _ _ _ ι La _ A la U Ω β h hU hΩ hβ hh h0
  classical
  obtain ⟨⟨hβhol, hβcoc⟩, hβne⟩ := hβ
  obtain ⟨hhhol, hhcoc⟩ := hh
  have hq : ∀ y, _root_.GlobalTheory.OTY.TwEst.quot A h β y = h (A.pick y) y / β (A.pick y) y := fun y => by
    unfold _root_.GlobalTheory.OTY.TwEst.quot; rfl
  have hβi : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U → β i y ≠ 0 := by
    intro i y hy hyU hzero
    apply hβne y hyU
    rw [hβcoc (A.pick y) i y hyU (A.mem_pick y) hy, hzero, mul_zero]
  have hqe : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U →
      _root_.GlobalTheory.OTY.TwEst.quot A h β y = h i y / β i y := by
    intro i y hy hyU
    rw [hq]
    by_cases hyΩ : y ∈ Ω
    · rw [hhcoc (A.pick y) i y hyΩ (A.mem_pick y) hy, hβcoc (A.pick y) i y hyU (A.mem_pick y) hy,
        mul_div_mul_left _ _ (A.g_ne la _ _ y (A.mem_pick y) hy)]
    · rw [h0 _ _ hyΩ, h0 _ _ hyΩ, zero_div, zero_div]
  have hdiff : ∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) := by
    intro i
    set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) with hS
    have h1 : DifferentiableOn ℂ (h i ∘ (A.chart i).symm) S :=
      (hhhol i).mono fun v hv => ⟨hv.1, hv.2.2⟩
    have h2 : DifferentiableOn ℂ (β i ∘ (A.chart i).symm) S :=
      (hβhol i).mono fun v hv => ⟨hv.1, hv.2.1⟩
    have h3 : ∀ v ∈ S, (β i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
      hβi i _ ((A.chart i).map_target hv.1) hv.2.1
    have hd : DifferentiableOn ℂ
        (fun v => (h i ∘ (A.chart i).symm) v * ((β i ∘ (A.chart i).symm) v)⁻¹) S :=
      h1.mul (h2.inv h3)
    refine hd.congr fun v hv => ?_
    simp only [Function.comp_apply, ← div_eq_mul_inv]
    exact hqe i _ ((A.chart i).map_target hv.1) hv.2.1
  refine ⟨hdiff, ?_, fun y hy => ?_⟩
  · have hopen : IsOpen (U ∩ Ω) := hU.inter hΩ
    have hcont : ContinuousOn (_root_.GlobalTheory.OTY.TwEst.quot A h β) (U ∩ Ω) := by
      intro y hy
      set i := A.pick y
      have hys : y ∈ (A.chart i).source := A.mem_pick y
      have hset : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) :=
        (A.chart i).isOpen_inter_preimage_symm hopen
      have hmem : A.chart i y ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) :=
        ⟨(A.chart i).map_source hys, by
          simp only [Set.mem_preimage, (A.chart i).left_inv hys]; exact hy⟩
      have hca : ContinuousAt (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) (A.chart i y) :=
        ((hdiff i).continuousOn).continuousAt (hset.mem_nhds hmem)
      have hcomp : ContinuousAt ((_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ∘ A.chart i) y :=
        hca.comp ((A.chart i).continuousAt hys)
      refine (hcomp.congr ?_).continuousWithinAt
      filter_upwards [(A.chart i).open_source.mem_nhds hys] with w hw
      simp [(A.chart i).left_inv hw]
    have heq : _root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y) =
        (U ∩ Ω).piecewise (_root_.GlobalTheory.OTY.TwEst.quot A h β) 0 := by
      funext y
      unfold _root_.GlobalTheory.OTY.TwEst.ext0
      by_cases hyU : y ∈ U
      · by_cases hyΩ : y ∈ Ω
        · simp [hyU, hyΩ, Set.piecewise]
        · simp [hyU, hyΩ, Set.piecewise, hq, h0 _ _ hyΩ]
      · simp [hyU, Set.piecewise]
    rw [heq]
    exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet
  · rw [hq, mul_div_cancel₀ _ (hβne y hy)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryNearOneEqChartMul
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory

theorem eq_chart_mul_of_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  intro E _ _ _ r X x σ t ρ hx hρ hσ0 hσc hσB ht _ _ hstab δ hδ
  obtain ⟨η, hη, hB⟩ := _root_.GlobalTheory.RiemConst.phaseFrame_small_angles E X.Ψ r δ hδ
  have hσa : ContinuousAt σ 0 := hσc.continuousAt (Metric.ball_mem_nhds 0 hρ)
  obtain ⟨ε1, hε1, κ, hκ, hC⟩ := _root_.GlobalTheory.SUVol.conj_inv_section_mul_entries_near_one E r X x σ hx hσ0 hσa η hη
  obtain ⟨ε2, hε2, hA⟩ := _root_.GlobalTheory.LUNear.lmulC_split_near_one E r X x hx (min (min δ ρ) κ) (lt_min (lt_min hδ hρ) hκ)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun g hg => ?_⟩
  have hg1 : g ∈ grpBall (realSU X.Ψ X.Gm) ε1 := fun τ a b => lt_of_lt_of_le (hg τ a b) (min_le_left _ _)
  obtain ⟨z, hz, b, hb, hgx⟩ := hA (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
    (fun τ a c => lt_of_lt_of_le (hg τ a c) (min_le_right _ _))
  have hz1 : ‖z‖ < δ := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : z ∈ Metric.ball (0 : V (nd X)) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
  have hz3 : ‖z‖ < κ := lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨b', hb', hσx⟩ := hσB z hz2
  have hxu : ∀ τ, IsUnit (mat x τ) := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ))

  have hstep : ∃ b'' ∈ Bor X.Ψ r, X.lmulC (fun τ => (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b'' := by
    refine ⟨fun τ => ((mat b' τ)⁻¹ * mat b τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_, ?_⟩
    · have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      refine ⟨?_, fun a c hca => ?_⟩
      · show ((mat b' τ)⁻¹ * mat b τ).det ≠ 0
        rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
        exact mul_ne_zero (inv_ne_zero (hb' τ).1) (hb τ).1
      · show ((mat b' τ)⁻¹ * mat b τ) a c = 0
        letI := Matrix.invertibleOfIsUnitDet _ hb'u
        have h1 : (mat b' τ)⁻¹.BlockTriangular id :=
          Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => (hb' τ).2 a c h)
        have h2 : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
        exact (h1.mul h2) hca
    · funext τ
      have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      set S : GL (Fin r) ℂ := ((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hS
      set G : GL (Fin r) ℂ := ((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hG
      have eM : ((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ) = S⁻¹ * G := rfl
      have e1 : (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b' τ := congrFun hσx τ
      have e2 : (G : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b τ := congrFun hgx τ
      have e3 : mat x τ * mat (nmat X z) τ = (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ * (mat b' τ)⁻¹ := by
        rw [e1, Matrix.mul_assoc (mat x τ * mat (nmat X z) τ), Matrix.mul_nonsing_inv _ hb'u, Matrix.mul_one]
      show (((S⁻¹ * G : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) =
        mat x τ * ((mat b' τ)⁻¹ * mat b τ)
      rw [Units.val_mul, Matrix.mul_assoc, e2, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc]
  obtain ⟨θ, hθ⟩ := hstab _ hstep
  have hP : ∀ θ₀, ∀ τ, (mat x τ)⁻¹ * ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat (phaseFrame θ₀) τ := by
    intro θ₀ τ
    have h1 : ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (phaseFrame θ₀) τ := congrFun (ht θ₀) τ
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hxu τ)), Matrix.one_mul]
  have hph : ∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η := by
    intro τ a
    have h := hC z hz3 g hg1 τ a a
    rw [hθ, hP θ τ] at h
    simpa [mat] using h
  obtain ⟨θ', hθ', hPP⟩ := hB θ hph
  have htt : t θ' = t θ := by
    apply Subtype.ext; funext τ; apply Units.ext
    have h1 := congrFun ((ht θ').trans ((congrArg (rmul x) hPP).trans (ht θ).symm)) τ
    exact (hxu τ).mul_left_injective h1
  refine ⟨(z, θ'), ?_, ?_⟩
  · rw [Prod.norm_def]; exact max_lt hz1 hθ'
  · show σ z * t θ' = g
    rw [htt, ← hθ, mul_inv_cancel_left]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacterStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) → subst c.μ u = inL u * inR u := by
  first | exact @GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | exact GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | (intros; apply GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_subgroup_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (exact GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (intros; apply GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial <;> assumption)
end

