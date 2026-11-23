module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactors
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricH1ZetaSubOneKillsStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_h1_zeta_sub_one_kills : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  intro p _ hp2 Ω _ _ hΩ T k j hj c hc hcoc
  classical
  let H := Ggeo p Ω ⊓ ⨅ n, Gn T n
  have uniform : ∃ S : Finset Ω, ∀ g ∈ H, ∀ h ∈ H,
      (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g) := by
    have localTests : ∀ g : Gal p Ω, ∃ S : Finset Ω,
        (g ∈ H → ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g)) ∧
        (g ∉ H → ∀ h ∈ H, ¬ ∀ x ∈ S, h x = g x) := by
      intro g
      by_cases hg : g ∈ H
      · obtain ⟨S, hS⟩ := hc.2 g hg
        exact ⟨S, fun _ => hS, fun h => (h hg).elim⟩
      · obtain ⟨a, hga, ha⟩ := TateGeo.exists_moved T hg
        refine ⟨{a}, fun h => (hg h).elim, fun _ h hh agree => hga ?_⟩
        exact (agree a (Finset.mem_singleton_self a)).symm.trans (ha h hh)
    choose S hlocal hsep using localTests
    obtain ⟨F, hF⟩ := _root_.GlobalTheory.K5.gal_finite_subcover p Ω hΩ S
    refine ⟨F.biUnion S, fun g hg h hh agree => ?_⟩
    obtain ⟨g₀, hg₀F, hg₀⟩ := hF g
    have hg₀H : g₀ ∈ H := by
      by_contra h
      exact hsep g₀ h g hg hg₀
    have hg' := hlocal g₀ hg₀H g hg hg₀
    have hh' := hlocal g₀ hg₀H h hh (fun x hx =>
      (agree x (Finset.mem_biUnion.mpr ⟨g₀, hg₀F, hx⟩)).trans (hg₀ x hx))
    simpa [Cong] using Basic.cong_sub hh' hg'
  obtain ⟨S, hS⟩ := uniform
  obtain ⟨y, E, hy, hEH, hu, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hΩ T H inf_le_right S j hj
  let x : Ω := ∑ g ∈ E, g y * c g
  have hx : IsInt (p := p) x := by
    refine IsIntegral.sum _ fun g hg => ?_
    exact (IsIntegral.map g.toAlgHom hy).mul (hc.1 g (hEH g hg))
  refine ⟨-x, hx.neg, fun h hh => ?_⟩
  have hσ : ∀ g ∈ E, ∃ g' ∈ E, h (g y) = g' y ∧ ∀ s ∈ S, h (g s) = g' s := by
    intro g hg
    obtain ⟨g', ⟨hg', hy', hs'⟩, -⟩ := hu (h * g) (H.mul_mem hh (hEH g hg))
    exact ⟨g', hg', hy', hs'⟩
  choose! σ hσE hσy hσS using hσ
  have hσinj : Set.InjOn σ E := by
    intro g₁ hg₁ g₂ hg₂ e
    apply (hu g₁ (hEH g₁ hg₁)).unique ⟨hg₁, rfl, fun _ _ => rfl⟩
    refine ⟨hg₂, h.injective ?_, fun s hs => h.injective ?_⟩
    · rw [hσy g₁ hg₁, hσy g₂ hg₂, e]
    · rw [hσS g₁ hg₁ s hs, hσS g₂ hg₂ s hs, e]
  have himage : E.image σ = E :=
    Finset.eq_of_subset_of_card_le (by simpa only [Finset.image_subset_iff] using hσE)
      (by rw [Finset.card_image_of_injOn hσinj])
  have hperm : ∑ g ∈ E, σ g y * c (σ g) = x := by
    rw [← Finset.sum_image (f := fun g' => g' y * c g') hσinj, himage]
  have hhx : h x = ∑ g ∈ E, h (g y) * h (c g) := by
    simp only [x, map_sum, map_mul]
  have hζ : h (T.ζ j) = T.ζ j := (((TateGeo.mem_geoTop_iff T h).mp hh).2 j).1
  have hsumh : ∑ g ∈ E, h (g y) = T.ζ j - 1 := by
    rw [← map_sum, hsum, map_sub, map_one, hζ]
  have termCong : ∀ g ∈ E, Cong (p := p) k (h (g y) * h (c g))
      (σ g y * c (σ g) - h (g y) * c h) := by
    intro g hg
    have hgH := hEH g hg
    obtain ⟨a, ha, ea⟩ := hcoc h hh g hgH
    obtain ⟨b, hb, eb⟩ := hS (σ g) (hEH _ (hσE g hg)) (h * g) (H.mul_mem hh hgH) (hσS g hg)
    refine ⟨h (g y) * (b - a), (IsIntegral.map h.toAlgHom (IsIntegral.map g.toAlgHom hy)).mul (hb.sub ha), ?_⟩
    rw [← hσy g hg]
    linear_combination h (g y) * (eb - ea)
  have sumCong (s : Finset (Gal p Ω)) (f f' : Gal p Ω → Ω)
      (hs : ∀ g ∈ s, Cong (p := p) k (f g) (f' g)) :
      Cong (p := p) k (∑ g ∈ s, f g) (∑ g ∈ s, f' g) := by
    induction s using Finset.induction_on with
    | empty => simpa using Basic.cong_refl (p := p) k (0 : Ω)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact Basic.cong_add (hs a (Finset.mem_insert_self a s))
        (ih fun g hg => hs g (Finset.mem_insert_of_mem hg))
  have total := sumCong E _ _ termCong
  rw [← hhx, Finset.sum_sub_distrib, hperm, ← Finset.sum_mul, hsumh] at total
  obtain ⟨z, hz, e⟩ := total
  refine ⟨z, hz, ?_⟩
  show (T.ζ j - 1) * c h - (h (-x) - -x) = _
  rw [map_neg]
  linear_combination e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeff
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem tendsto_eulerProduct_LSeries_of_sq : ∀ (b : ℕ → ℂ) (s : ℝ), 0 < s → b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)) atTop (𝓝 (LSeries b ((1 + s : ℝ) : ℂ))) := by
  intro b s hs hb1 hmul hsum
  have hn : Summable (fun n : ℕ => ‖LSeries.term b ((1 + s : ℝ) : ℂ) n‖) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) :=
      Real.summable_one_div_nat_rpow.2 (by linarith)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hsum.add h1)
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · positivity
    · rw [Complex.ofReal_re, ← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (‖b n‖ - 1), norm_nonneg (b n)]
  refine EulerProduct.eulerProduct (f := LSeries.term b ((1 + s : ℝ) : ℂ)) ?_ ?_ hn ?_
  · simp [LSeries.term, hb1]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn0,
      LSeries.term_of_ne_zero (mul_ne_zero hm hn0), hmul m n hmn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, div_mul_div_comm]
  · simp

theorem prod_primesBelow_sq_le_tsum : ∀ (b : ℕ → ℂ) (s : ℝ), b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) ≤ ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro b s hb1 hmul hsum N
  have h0 : ∀ n : ℕ, 0 ≤ ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := fun n => by positivity
  have key := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) (by simp [hb1])
    (fun {m n} hmn => by
      simp only [hmul m n hmn, norm_mul, mul_pow, Nat.cast_mul]
      rw [Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm])
    (by simpa only [Real.norm_of_nonneg (h0 _)] using hsum) N
  rw [key]
  exact hsum.tsum_subtype_le _ _ h0

theorem global_positivity_ineq : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro M b ω s C hs hb1 hb0 hmul hbM hrec hC hsum X
  set f : ℕ → ℝ := fun n => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hf
  set Ssum := ∑' n : ℕ, f n
  set Lp : ℕ → ℂ := fun p => ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) with hLp
  set Rp : ℕ → ℝ := fun p => ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) with hRp
  set α : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ with hα
  set β : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ with hβ
  set A : ℕ → ℝ := fun p => if ¬ p ∣ M then ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) else 0 with hA
  have hA0 : ∀ p, 0 ≤ A p := fun p => by
    simp only [hA]; split_ifs <;> positivity

  have hα1 : ∀ p : ℕ, p.Prime → 1 ≤ α p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
    have h3 : 1 / (p : ℝ) ^ (1 + s) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hα]
    rw [one_le_inv₀ (by linarith)]; linarith
  have hβ1 : ∀ p : ℕ, p.Prime → 1 ≤ β p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (2 * (1 + s)) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (2 * (1 + s)) := by positivity
    have h3 : 1 / (p : ℝ) ^ (2 * (1 + s)) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hβ]
    rw [one_le_inv₀ (by linarith)]; linarith

  have hdiv : ∀ p : ℕ, p.Prime → p ∣ M → Lp p = 1 ∧ Rp p = 1 := by
    intro p hp hpM
    have hz : ∀ e : ℕ, e ≠ 0 → b (p ^ e) = 0 := by
      intro e he
      apply hbM
      intro hc
      have : p ∣ Nat.gcd (p ^ e) M := Nat.dvd_gcd (dvd_pow_self p he) hpM
      rw [hc] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    constructor
    · simp only [hLp]
      rw [tsum_eq_single 0]
      · simp [LSeries.term, hb1]
      · intro e he; simp [LSeries.term, hz e he]
    · simp only [hRp]
      rw [tsum_eq_single 0]
      · simp [hb1]
      · intro e he; simp [hz e he]
  have hRp0 : ∀ p, 0 ≤ Rp p := fun p => tsum_nonneg (fun e => by positivity)
  have hα0 : ∀ p : ℕ, p.Prime → 0 ≤ α p := fun p hp => le_trans zero_le_one (hα1 p hp)
  have hβ0 : ∀ p : ℕ, p.Prime → 0 ≤ β p := fun p hp => le_trans zero_le_one (hβ1 p hp)

  have hloc : ∀ p : ℕ, p.Prime → Real.exp (A p) ≤ α p * ‖Lp p‖ ^ 2 * Rp p * β p := by
    intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨h1, h2⟩ := hdiv p hp hpM
      simp only [hA, hpM, not_true_eq_false, if_false, Real.exp_zero, h1, h2, norm_one, one_pow, mul_one]
      nlinarith [hα1 p hp, hβ1 p hp]
    · have := _root_.GlobalTheory.LocIneq.local_positivity_eulerFactor b ω s C p hs hp hb1 (hrec p 1 hp hpM).1 (fun r => (hrec p r hp hpM).2) hC
      simpa only [hA, hpM, not_false_eq_true, if_true] using this

  have hfin : ∀ N : ℕ, X ≤ N → Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by
    intro N hN
    have e1 : ∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) = ∑ p ∈ X.primesBelow, A p := by
      rw [Nat.primesBelow, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : p.Prime <;> by_cases h2 : p ∣ M <;> simp [hA, h1, h2]
    have e2 : ∑ p ∈ X.primesBelow, A p ≤ ∑ p ∈ N.primesBelow, A p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesBelow_mono hN) (fun p _ _ => hA0 p)
    rw [e1]
    calc Real.exp (∑ p ∈ X.primesBelow, A p) ≤ Real.exp (∑ p ∈ N.primesBelow, A p) := Real.exp_le_exp.mpr e2
      _ = ∏ p ∈ N.primesBelow, Real.exp (A p) := Real.exp_sum _ _
      _ ≤ ∏ p ∈ N.primesBelow, (α p * ‖Lp p‖ ^ 2 * Rp p * β p) :=
          Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => hloc p (Nat.prime_of_mem_primesBelow hp))
      _ = (∏ p ∈ N.primesBelow, α p) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * (∏ p ∈ N.primesBelow, Rp p) * (∏ p ∈ N.primesBelow, β p) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, norm_prod, Finset.prod_pow]
      _ ≤ (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum * 2 := by
          have a1 := _root_.GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le s hs N
          have a2 := _root_.GlobalTheory.prod_primesBelow_zeta_two_add_le_two s hs.le N
          have a3 := prod_primesBelow_sq_le_tsum b s hb1 hmul hsum N
          have p1 : 0 ≤ ∏ p ∈ N.primesBelow, α p := Finset.prod_nonneg (fun p hp => hα0 p (Nat.prime_of_mem_primesBelow hp))
          have p2 : 0 ≤ ∏ p ∈ N.primesBelow, Rp p := Finset.prod_nonneg (fun p _ => hRp0 p)
          have p3 : 0 ≤ ∏ p ∈ N.primesBelow, β p := Finset.prod_nonneg (fun p hp => hβ0 p (Nat.prime_of_mem_primesBelow hp))
          gcongr
      _ = 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by ring
  have hlim := tendsto_eulerProduct_LSeries_of_sq b s hs hb1 hmul hsum
  have hcont : Tendsto (fun N : ℕ => 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum) atTop (𝓝 (2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * Ssum)) :=
    ((hlim.norm.pow 2).const_mul _).mul_const _
  exact ge_of_tendsto hcont (Filter.eventually_atTop.mpr ⟨X, hfin⟩)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumInvariantOfStable
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem GlobalTheory.EisM.hsum_inv_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  intro k L L' N ε Δ ι _ β f hk hNL hNL' hΔ hΔγ hβ hf
  have hcoc := (_root_.GlobalTheory.EisM.slz_props k f hk).1
  rw [(_root_.GlobalTheory.EisM.slz_props k (hsum k (ch ε) β f) hk).2.2.1 L' (ch ε)]
  intro γ hγ
  have hNγ : (N : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hNL').trans hγ
  have hβmem : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  have hγγ : (γ : M2) * ((γ⁻¹ : SL(2,ℤ)) : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγγ' : ((γ⁻¹ : SL(2,ℤ)) : M2) * (γ : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγinv : (L' : ℤ) ∣ (γ⁻¹ : SL(2,ℤ)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hγ.neg_right
  set β' : ι → M2 := fun i => β i * (γ : M2) with hβ'
  have hβ'rep : LRep L Δ β' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨g, i⟩ -
      have := hβ.mapsTo (Set.mem_univ (g, i))
      simp only [β', ← mul_assoc]
      exact hΔγ _ this γ hγ
    · rintro ⟨g, i⟩ - ⟨g', j⟩ - h
      have h' := congrArg (· * ((γ⁻¹ : SL(2,ℤ)) : M2)) h
      simp only [β', mul_assoc, hγγ, mul_one] at h'
      exact hβ.injOn (Set.mem_univ _) (Set.mem_univ _) h'
    · intro δ hδ
      have h1 := hΔγ δ hδ γ⁻¹ hγinv
      obtain ⟨⟨g, i⟩, -, hgi⟩ := hβ.surjOn h1
      refine ⟨(g, i), Set.mem_univ _, ?_⟩
      simp only at hgi ⊢
      rw [← mul_assoc, hgi, mul_assoc, hγγ', mul_one]
  have hsumeq := _root_.GlobalTheory.EisM.RepInd.hsum_indep k L N ε Δ ι ι β β' f hk hNL hΔ hβ hβ'rep hf
  have hdetγ : (0 : ℤ) < (γ : M2).det := by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num
  have hch : ∀ i, ch ε (β' i 0 0) = ch ε (β i 0 0) * ch ε (γ 0 0) := by
    intro i
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    simp only [ch, β', Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hz, mul_zero, add_zero, map_mul]
  have hγd : ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hd
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    have h2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod N)) hd
      push_cast at this
      rw [hz, mul_zero, sub_zero] at this
      exact this
    simp only [ch]
    rw [← map_mul, h2, map_one]
  funext τ
  have hlin : slz k (γ : M2) (hsum k (ch ε) β f) τ = ∑ i, ch ε (β i 0 0) * slz k (γ : M2) (slz k (β i) f) τ := by
    simp only [slz, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hlin, hsumeq]
  simp only [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcoc (β i) γ (hΔ _ (hβmem i)).1 hdetγ, hch i]
  calc ch ε (β i 0 0) * slz k (β i * ↑γ) f τ
      = ch ε (β i 0 0) * (ch ε (γ 0 0) * ch ε (γ 1 1)) * slz k (β i * ↑γ) f τ := by rw [hγd, mul_one]
    _ = _ := by simp only [β']; ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLe
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem im_ofComplex_xy (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  change ((x : ℂ) + (y : ℂ) * Complex.I).im = y
  simp

theorem integrableOn_rpow_sub_two_mul_exp_Ioi_one (r c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (r - 2) * Real.exp (-c * y)) (Set.Ioi 1) := by
  have hI : IntegrableOn (fun y : ℝ => y ^ (max (r - 2) 0) * Real.exp (-c * y ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have := le_max_right (r - 2) 0; linarith)
      one_pos hc
  have hI' := hI.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hI' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (Real.exp_pos _).le), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)) (Real.exp_pos _).le

theorem integrableOn_im_rpow_mul_exp_strip_one_le :
    ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im))
      {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  intro r c hc
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmeas : Measurable (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) :=
    (hmim.pow_const r).mul (Real.measurable_exp.comp (measurable_const.mul hmim))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hmT : MeasurableSet {τ : ℍ | 1 ≤ τ.im} := measurableSet_le measurable_const hmim
  have hS : {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} = {τ : ℍ | 1 ≤ τ.im} ∩ strip := by
    ext τ; simp [and_comm]
  show ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im}, ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ < ⊤
  rw [hS, ← Measure.restrict_restrict hmT, ← lintegral_indicator hmT,
    (_root_.GlobalTheory.EisM.strip_iterated).1 _ ((hmeas.enorm).indicator hmT)]
  have hinner : Set.EqOn
      (fun y : ℝ => (∫⁻ x in Set.Ico (0 : ℝ) 1, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I))) *
          ENNReal.ofReal (1 / y ^ 2))
      (fun y : ℝ => (Set.Ici (1 : ℝ)).indicator
        (fun y => ENNReal.ofReal (y ^ (r - 2) * Real.exp (-c * y))) y) (Set.Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hpt : ∀ x : ℝ, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I)) =
        (Set.Ici (1 : ℝ)).indicator
          (fun y => ENNReal.ofReal (y ^ r * Real.exp (-c * y))) y := by
      intro x
      by_cases h1 : (1 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_mem (by simpa using h1), im_ofComplex_xy x y hy0,
          Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      · rw [Set.indicator_of_notMem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_notMem (by simpa using h1)]
    simp only [hpt]
    rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h1 : (1 : ℝ) ≤ y
    · rw [Set.indicator_of_mem (by simpa using h1), Set.indicator_of_mem (by simpa using h1),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      congr 1
      rw [Real.rpow_sub hy0, Real.rpow_two]
      field_simp
    · rw [Set.indicator_of_notMem (by simpa using h1), Set.indicator_of_notMem (by simpa using h1),
        zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ioi.2 one_pos)]
  have hfin := ((integrableOn_Ici_iff_integrableOn_Ioi).2
    (integrableOn_rpow_sub_two_mul_exp_Ioi_one r c hc)).hasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hfin

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCocycleCoboundaryOfNormsStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  first | exact @GlobalTheory.NeedB.NormCob.carry_coboundary | exact GlobalTheory.NeedB.NormCob.carry_coboundary | (intros; apply GlobalTheory.NeedB.NormCob.carry_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeFunctionDivisibleFirstSubstitution
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory

theorem latF_rows_subst : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  intro N l ν φ a b c d hdet hN hl y
  obtain ⟨y1, y2⟩ := y
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcop : IsCoprime ((N : ℤ) * d) (l : ℤ) := ⟨a, -(b * c), by linear_combination hdet⟩
  simp only [latF]
  by_cases h1 : (N : ℤ) ∣ y1
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right _ _)]
    have hdiv : (N : ℤ) * m / N = m := Int.mul_ediv_cancel_left m hNz
    simp only [hdiv]
    have key : ((N : ℤ) * l ∣ N * m) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h; exact (mul_dvd_mul_iff_left hNz).mp h
      · intro h; exact mul_dvd_mul_left _ h
    have key2 : ((l : ℤ) ∣ m * (N * d) - y2 * (l * c)) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h
        have h' : (l : ℤ) ∣ m * (N * d) := by
          have := dvd_add h (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
          simpa using this
        exact hcop.symm.dvd_of_dvd_mul_right h'
      · intro h
        exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
    push_cast
    by_cases h2 : (l : ℤ) ∣ m
    · obtain ⟨m2, rfl⟩ := h2
      rw [if_pos ((key2).mpr (dvd_mul_right _ _)), if_pos (key.mpr (dvd_mul_right _ _))]
      have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      have e1 : (l : ℤ) * m2 * (N * d) - y2 * (l * c) = l * (m2 * N * d - y2 * c) := by ring
      rw [e1, Int.mul_ediv_cancel_left _ hlz]
      simp only [ch, one_mul, map_intCast]
      congr 2
      · push_cast
        simp [mul_comm]
      · push_cast
        simp [mul_comm]
    · rw [if_neg (fun h => h2 (key2.mp h)), if_neg (fun h => h2 (key.mp h))]
  · rw [if_neg h1, if_neg]
    intro h
    push_cast at h
    exact h1 (dvd_trans (dvd_mul_right _ _) h)

end GlobalTheory
end

