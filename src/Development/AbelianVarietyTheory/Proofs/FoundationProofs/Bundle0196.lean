module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StepRatioAbsVwProd
section
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem stepRatio_vw_pow (w : Pl K) {x : K} (hx : x ≠ 0) (c : ℕ) : vw w (x ^ c) = c * vw w x := by
  induction c with
  | zero =>
    have h := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (1 : K) 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    rw [pow_zero]
    push_cast
    omega
  | succ c ih =>
    rw [pow_succ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero c hx) hx, ih]
    push_cast
    ring

theorem stepRatio_vw_of_dvd (w : Pl K) {q c : ℕ} (hq : 0 < q) {g : 𝓞 K} (hg : g ∣ (q : 𝓞 K) ^ c) :
    (g : K) ≠ 0 ∧ 0 ≤ vw w (g : K) ∧ vw w (g : K) ≤ c * vw w (q : K) := by
  obtain ⟨b, hb⟩ := hg
  have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have h : (q : K) ^ c = (g : K) * (b : K) := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hb
    simpa using this
  have hne : (g : K) * (b : K) ≠ 0 := h ▸ pow_ne_zero c hq0
  have hg0 := left_ne_zero_of_mul hne
  have hb0 := right_ne_zero_of_mul hne
  refine ⟨hg0, Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w g, ?_⟩
  rw [← stepRatio_vw_pow w hq0, h, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hg0 hb0]
  have := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w b
  omega

theorem stepRatio_abs_vw_prod (w : Pl K) {T : Type} (S : Finset T) (f : T → K) (r : T → ℝ)
    (h : ∀ v ∈ S, f v ≠ 0 ∧ |(vw w (f v) : ℝ)| ≤ r v) :
    |(vw w (∏ v ∈ S, f v) : ℝ)| ≤ ∑ v ∈ S, r v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := stepRatio_vw_pow w (one_ne_zero : (1 : K) ≠ 0) 0
    rw [pow_zero, Nat.cast_zero, zero_mul] at this
    rw [Finset.prod_empty, Finset.sum_empty, this]
    simp
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := fun v hv => h v (Finset.mem_insert_of_mem hv)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h1.1 (Finset.prod_ne_zero_iff.2 fun v hv => (h2 v hv).1)]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add h1.2 (ih h2))

theorem stepRatio_vw_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ),
    (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (T : Type) (S0 : Finset T) (cc qq : T → ℕ), (∀ v ∈ S0, 0 < qq v) → ∀ u1 u0 : ℂ,
    StepRatio σ₀ Qn S0 cc qq u1 u0 → ∃ t : K, t ≠ 0 ∧ u1 = σ₀ t * u0 ∧
      |(vw w t : ℝ)| ≤ 2 * ∑ v ∈ S0, (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by
  intro K _ _ _ σ₀ w Qn hQ T S0 cc qq hq u1 u0 h
  obtain ⟨b, g, g', hb, hg, hu⟩ := h
  have vz : ∀ {a : 𝓞 K}, a ∉ w.asIdeal → vw w (a : K) = 0 := by
    intro a ha
    classical
    have ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
      rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      rintro rfl
      exact ha w.asIdeal.zero_mem
    unfold vw
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]
    by_contra h
    have h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
      intro h0
      exact h (by rw [h0]; rfl)
    exact ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))
  have ⟨hb0, hbv⟩ : b ≠ 0 ∧ vw w b = 0 := by
    obtain ⟨a, k, k', ⟨d, hd⟩, he⟩ := hb
    have hpow : ∀ j : ℕ, (Qn : 𝓞 K) ^ j ∉ w.asIdeal :=
      fun j hj => hQ (w.isPrime.mem_of_pow_mem j hj)
    have ha : a ∉ w.asIdeal := fun h => hpow k' (hd ▸ w.asIdeal.mul_mem_right d h)
    have ha0 : (a : K) ≠ 0 := by
      intro h
      have : a = 0 := by exact_mod_cast h
      exact ha (this ▸ w.asIdeal.zero_mem)
    have hb0 : b ≠ 0 := by rintro rfl; rw [zero_mul] at he; exact ha0 he.symm
    have hk0 : (Qn : K) ^ k ≠ 0 := by intro h; rw [h, mul_zero] at he; exact ha0 he.symm
    refine ⟨hb0, ?_⟩
    have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w b _ hb0 hk0
    have h2 := vz ha
    have h3 := vz (hpow k)
    have h4 : ((((Qn : 𝓞 K) ^ k : 𝓞 K)) : K) = (Qn : K) ^ k := by simp
    rw [h4] at h3
    rw [he, h2, h3] at h1
    omega
  have key : ∀ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 ∧
      |(vw w ((g v : K) / (g' v : K)) : ℝ)| ≤ 2 * ((cc v : ℝ) * (vw w (qq v : K) : ℝ)) := by
    intro v hv
    obtain ⟨a0, a1, a2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).1
    obtain ⟨b0, b1, b2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).2
    refine ⟨div_ne_zero a0 b0, ?_⟩
    rw [div_eq_mul_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ a0 (inv_ne_zero b0), Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    have a1' : (0 : ℝ) ≤ (vw w (g v : K) : ℝ) := by exact_mod_cast a1
    have a2' : (vw w (g v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast a2
    have b1' : (0 : ℝ) ≤ (vw w (g' v : K) : ℝ) := by exact_mod_cast b1
    have b2' : (vw w (g' v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast b2
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hp : ∏ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (key v hv).1
  refine ⟨_, mul_ne_zero hb0 hp, hu, ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hb0 hp, hbv, zero_add, Finset.mul_sum]
  exact stepRatio_abs_vw_prod w S0 _ _ key

end GlobalTheory.Square
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCompLeSumOfInjOn
section
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square

theorem sum_comp_le_sum_of_injOn {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S) (hg : ∀ s ∈ S, 0 ≤ g s) :
    ∑ t ∈ T, g (f t) ≤ ∑ s ∈ S, g s := by
  rw [← Finset.sum_image (g := f) (f := g) hf]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hg s hs)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
  exact hS t ht

theorem sum_le_sum_add_card_mul {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (u : ι → ℝ) (c : ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S)
    (hg : ∀ s ∈ S, 0 ≤ g s) (hu : ∀ t ∈ T, u t ≤ g (f t) + c) :
    ∑ t ∈ T, u t ≤ ∑ s ∈ S, g s + (T.card : ℝ) * c := by
  have h1 := Finset.sum_le_sum hu
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 := sum_comp_le_sum_of_injOn T S f g hf hS hg
  linarith

theorem count_factors : ∀ (e p q e0 h0 : ℕ), e0 + p = e + q → e0 ≤ h0 → ∀ (v a n0 : ℤ → ℝ) (er : ℝ), 0 ≤ er → (∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q → 0 ≤ a s ∧ 0 ≤ n0 s ∧ v s ≤ a s + er ∧ -(v s) ≤ a s + n0 s) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → v s = v (1 - s)) → (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s) + (∑ k ∈ range p, v ((e : ℤ) + q - k)) - (∑ k ∈ range q, v ((e : ℤ) + k + 1)) ≤ 4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) + ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
  intro e p q e0 h0 he hle v a n0 er her H hsym
  set S : Finset ℤ := Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ) with hS
  have hmem : ∀ s : ℤ, s ∈ S ↔ 1 ≤ s ∧ s ≤ (h0 : ℤ) + p + q := by
    intro s; simp [hS]
  have ha : ∀ s ∈ S, 0 ≤ a s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).1
  have hn : ∀ s ∈ S, 0 ≤ n0 s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).2.1
  have hsplit : ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s
      = ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s + ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s := by
    rw [← Finset.sum_union]
    · congr 1
      ext s
      simp only [mem_union, mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro s h1 h2
      simp only [mem_Icc] at h1 h2
      omega
  have b1 : ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s ≤ ∑ s ∈ S, a s + (e0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 - (e0 : ℤ)) 0) S (fun s => 1 - s) a v er
      (fun x _ y _ h => by simpa using h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        rw [hsym t ht.1 ht.2]
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 - (e0 : ℤ)) 0).card = e0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b2 : ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s ≤ ∑ s ∈ S, a s + (h0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 : ℤ) (h0 : ℤ)) S (fun s => s) a v er
      (fun x _ y _ h => h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 : ℤ) (h0 : ℤ)).card = h0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b3 : ∑ k ∈ range p, v ((e : ℤ) + q - k) ≤ ∑ s ∈ S, a s + (p : ℝ) * er := by
    have := sum_le_sum_add_card_mul (range p) S (fun k : ℕ => (e : ℤ) + q - k) a
      (fun k : ℕ => v ((e : ℤ) + q - k)) er
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega) ha
      (fun t ht => by
        simp only [mem_range] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    rwa [card_range] at this
  have b4 : ∑ k ∈ range q, -v ((e : ℤ) + k + 1) ≤ ∑ s ∈ S, (a s + n0 s) + (q : ℝ) * 0 := by
    have := sum_le_sum_add_card_mul (range q) S (fun k : ℕ => (e : ℤ) + k + 1)
      (fun s => a s + n0 s) (fun k : ℕ => -v ((e : ℤ) + k + 1)) 0
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega)
      (fun s hs => add_nonneg (ha s hs) (hn s hs))
      (fun t ht => by
        simp only [mem_range] at ht
        rw [add_zero]
        exact (H _ (by omega) (by omega)).2.2.2)
    rwa [card_range] at this
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at b4
  have hN : 0 ≤ ∑ s ∈ S, n0 s := Finset.sum_nonneg hn
  have hA : 0 ≤ ∑ s ∈ S, a s := Finset.sum_nonneg ha
  have hcount : ((e0 : ℝ) + h0 + p) * er ≤ ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
    refine mul_le_mul_of_nonneg_right ?_ her
    have : e0 + h0 + p ≤ 2 * (h0 + p + q) := by omega
    exact_mod_cast this
  rw [hsplit]
  linarith

end GlobalTheory.Square
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateH2IffAllFiniteExtensions
section
noncomputable section

namespace GlobalTheory.TateTopCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

section Transport

variable {O O' G M M' : Type} [CommRing O] [CommRing O'] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O' M']
  {σ : O →+* O'} {σ' : O' →+* O} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (π : Representation O G M) (ρ : Representation O' G M') (e : M ≃ₛₗ[σ] M')

variable (he : ∀ g x, e (π g x) = ρ g (e x))
include he


end Transport

section Integers

variable {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [CommRing O] [Algebra O LL]

theorem mem_range_of_norm_le (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) (hx : ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1) :
    x ∈ Set.range (algebraMap O LL) := by
  obtain ⟨⟨hO, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := h
  obtain ⟨-, -, hmt', -, -⟩ := (GlobalTheory.LocalIntegers.good_integers l L').1
  have hcont : Continuous φ.symm :=
    IsModuleTopology.continuous_of_linearMap φ.symm.toLinearEquiv.toLinearMap
  have hU : IsOpen (φ.symm ⁻¹' Set.range (algebraMap O LL)) := hop.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 ⟨0, by simp⟩
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt ℚ_[l] hε
  have hc0' : c ≠ 0 := norm_pos_iff.1 hc0
  have hk : ∀ k : ℕ, ∃ b : O, algebraMap O LL b = algebraMap ℚ_[l] LL c * x ^ k := by
    intro k
    have : φ (algebraMap ℚ_[l] LL c * x ^ k) ∈ Metric.ball (0 : ↥L'.1) ε := by
      rw [mem_ball_zero_iff]
      change ‖((φ (algebraMap ℚ_[l] LL c * x ^ k) : ↥L'.1) : Om l)‖ < ε
      rw [map_mul, map_pow, AlgEquiv.commutes]
      push_cast
      rw [norm_mul, norm_pow]
      have h1 : ‖((algebraMap ℚ_[l] ↥L'.1 c : ↥L'.1) : Om l)‖ = ‖c‖ := PadicAlgCl.norm_extends l c
      calc _ ≤ ‖c‖ * 1 := by
            gcongr
            · exact h1.le
            · exact pow_le_one₀ (norm_nonneg _) hx
        _ < ε := by simpa using hc
    simpa using hball this
  rcases ValuationRing.isInteger_or_isInteger O x with h | ⟨y, hy⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  by_cases hu : IsUnit y
  · obtain ⟨z, hz⟩ := hu.exists_right_inv
    refine ⟨z, ?_⟩
    have := congrArg (algebraMap O LL) hz
    rw [map_mul, hy, map_one] at this
    field_simp at this
    exact this
  · exfalso
    obtain ⟨a, ha⟩ := hk 0
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hc0' (by simpa using ha.symm)
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hu ha0
    obtain ⟨b, hb⟩ := hk (n + 1)
    refine hn ⟨b, IsFractionRing.injective O LL ?_⟩
    rw [map_mul, map_pow, hy, hb, ha, inv_pow]
    field_simp

theorem mem_range_iff (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) :
    x ∈ Set.range (algebraMap O LL) ↔ φ x ∈ OL L' := by
  have hO : φ x ∈ OL L' ↔ ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1 := mem_integralClosure_padicInt_iff L'.1 _
  rw [hO]
  refine ⟨?_, mem_range_of_norm_le h L' φ x⟩
  rintro ⟨a, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  have hsurj : Function.Surjective (algebraMap O LL) := by
    intro w
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖((φ w : ↥L'.1) : Om l)‖ hlt
    have hpos : 0 < ‖((φ (algebraMap O LL a) : ↥L'.1) : Om l)‖ ^ k := by positivity
    have ha : algebraMap O LL a ≠ 0 := by
      intro h0
      rw [h0] at hlt
      norm_num at hlt
    obtain ⟨b, hb⟩ := mem_range_of_norm_le h L' φ (w / algebraMap O LL a ^ k) (by
      rw [map_div₀, map_pow]
      push_cast
      rw [norm_div, norm_pow, div_le_one hpos]
      exact hk.le)
    exact ⟨b * a ^ k, by rw [map_mul, map_pow, hb]; field_simp⟩
  obtain ⟨⟨hO, hdvr, hfr⟩, -⟩ := h
  exact IsDiscreteValuationRing.not_isField O
    ((RingEquiv.ofBijective (algebraMap O LL)
      ⟨IsFractionRing.injective O LL, hsurj⟩).toMulEquiv.isField (Field.toIsField LL))

theorem exists_finExt (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ L' : FinExt l, Nonempty (LL ≃ₐ[ℚ_[l]] ↥L'.1) := by
  let ψ : LL →ₐ[ℚ_[l]] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨⟨ψ.fieldRange, (AlgEquiv.ofInjectiveField ψ).toLinearEquiv.finiteDimensional⟩,
    ⟨AlgEquiv.ofInjectiveField ψ⟩⟩

end Integers

section Quotients

variable {G LL O LL' O' M' : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O]
  [Algebra O LL] [Field LL'] [CommRing O'] [Algebra O' LL'] [AddCommGroup M'] [Module O' M']
  [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalAddGroup M']
  [ContinuousConstSMul O' M']


omit [TopologicalSpace G] in
def rangeLattice (hinj : Function.Injective (algebraMap O LL)) (χ : G →* LLˣ)
    (hχ : ∀ g, ((χ g : LLˣ) : LL) ∈ Set.range (algebraMap O LL)) :
    Lattice (O := O) (charRep χ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hχ g
    exact ⟨a * y, by simp [charRep, ha]⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) :
        Submodule O LL) : Set LL) := Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x this

end Quotients

section Compare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

end Compare

end GlobalTheory.TateTopCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTheoremModule
section
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Hyp

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime] (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem actVB_res (Y : Lat K LL) (g : ↥(GK K)) (g' : ↥(GK (levelField K s))) (hg : (g : GQ l) = g') :
    actVB ((LT l).PD K) Y.ρ g = actVB ((LT l).PD (levelField K s)) (resKs h Y) g' := by
  have h2 : Y.ρ g = resKs h Y g' := congrArg Y.ρ (Subtype.ext hg)
  have h3 : (((LT l).PD K).actB g).toAlgHom.toLinearMap.restrictScalars ℚ_[l] =
      (((LT l).PD (levelField K s)).actB g').toAlgHom.toLinearMap.restrictScalars ℚ_[l] :=
    LinearMap.ext fun b => (((LT l).PD_actB K g b).trans (by rw [hg])).trans
      ((LT l).PD_actB (levelField K s) g' b).symm
  unfold actVB
  rw [h2, h3]

theorem iInf_eq_of {α β γ : Type} [CompleteLattice γ] (f : α → γ) (g : β → γ)
    (h1 : ∀ a, ∃ b, f a = g b) (h2 : ∀ b, ∃ a, f a = g b) : ⨅ a, f a = ⨅ b, g b :=
  le_antisymm (le_iInf fun b => by obtain ⟨a, ha⟩ := h2 b; exact ha ▸ iInf_le f a)
    (le_iInf fun a => by obtain ⟨b, hb⟩ := h1 a; exact hb ▸ iInf_le g b)

theorem finrank_congr {R M : Type} [Field R] [AddCommGroup M] [Module R M] {X X' : Submodule R M}
    (e : X = X') : Module.finrank R ↥X = Module.finrank R ↥X' := by rw [e]

theorem fixed_eq (Y : Lat K LL) : (⨅ g : ((HW l).W K s LL h).GKs,
      LinearMap.ker (actVB ((LT l).PD K) Y.ρ (g : ↥(GK K)) - LinearMap.id)) =
      Dcris ((LT l).PD (levelField K s)) (resKs h Y) := by
  refine iInf_eq_of _ _ (fun g => ?_) fun g' => ?_
  · have hg : (g.1.1 : GQ l) ∈ GK (levelField K s) := (mem_GKs ((HW l).W_s K s LL h) g.1).mp g.2
    exact ⟨⟨g.1.1, hg⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y g.1 ⟨g.1.1, hg⟩ rfl)⟩
  · exact ⟨⟨⟨g'.1, GK_le (K := K) (K' := levelField K s) h.2.2.1 g'.2⟩,
      (mem_GKs ((HW l).W_s K s LL h) _).mpr g'.2⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y _ _ rfl)⟩

theorem crys_iff (Y : Lat K LL) :
    IsCrysOn (sit LT HW l AI K s LL h) (sit LT HW l AI K s LL h).W.GKs Y ↔
      IsCrys ((LT l).PD (levelField K s)) (resKs h Y) := by
  have h1 := finrank_congr (fixed_eq LT HW h Y)
  have h2 := congrArg (· * Module.finrank ↥LL.1 Y.V) (finrank_maxUnramified_levelFieldFiniteExtension K s h.1).symm
  exact iff_of_eq (congrArg₂ Eq h1 h2)

end Hyp

section Final

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

variable (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

variable (D : Formalism.BasicNotions.D7) (H : HWOf D.loc) (F : FonOf D.loc D.locA H)

end Final

end GlobalTheory.TorsionBoundCompare
end
end

