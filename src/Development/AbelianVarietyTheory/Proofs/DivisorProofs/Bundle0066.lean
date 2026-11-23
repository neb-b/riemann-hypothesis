module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConvolutionEq
section
open MeasureTheory Pointwise

namespace GlobalTheory

theorem integral_mul_convolution_eq (H : Type) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) (hμ : μ.IsHaarMeasure)
    (K : Set H) (hK : IsCompact K) (κ a : H → ℂ) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (ha : Measurable a) (hai : Integrable a μ)
    (haK : ∀ x ∉ K, a x = 0) (f : H → ℂ) (hf : Continuous f) :
    ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  haveI := hμ
  have hC : IsCompact (tsupport κ) := hκc
  obtain ⟨M, hM⟩ : ∃ M, ∀ w ∈ tsupport κ * K, ‖f w‖ ≤ M :=
    (hC.mul hK).exists_bound_of_continuousOn hf.continuousOn
  set G : H × H → ℂ := fun p => κ p.1 * (f p.2 * a (p.1⁻¹ * p.2)) with hG
  have hGm : AEStronglyMeasurable G (μ.prod μ) := by
    have h1 : Measurable fun p : H × H => a (p.1⁻¹ * p.2) :=
      ha.comp (measurable_fst.inv.mul measurable_snd)
    exact (hκ.comp continuous_fst).aestronglyMeasurable.mul
      ((hf.comp continuous_snd).aestronglyMeasurable.mul h1.aestronglyMeasurable)
  have hbound : Integrable (fun p : H × H => (‖κ p.1‖ * M) * ‖a p.2‖) (μ.prod μ) :=
    Integrable.mul_prod ((hκ.integrable_of_hasCompactSupport hκc).norm.mul_const M) hai.norm
  have hGs : Integrable (G ∘ fun p : H × H => (p.1, p.1 * p.2)) (μ.prod μ) := by
    refine hbound.mono' (hGm.comp_measurePreserving (measurePreserving_prod_mul μ μ)) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [Function.comp, G, inv_mul_cancel_left]
    by_cases h1 : κ p.1 = 0
    · simp only [h1, zero_mul, norm_zero, mul_zero]; positivity
    by_cases h2 : a p.2 = 0
    · simp only [h2, mul_zero, norm_zero]; rfl
    have hx : p.1 ∈ tsupport κ := subset_tsupport _ h1
    have hy : p.2 ∈ K := by
      by_contra h; exact h2 (haK _ h)
    have hfM := hM _ (Set.mul_mem_mul hx hy)
    rw [norm_mul, norm_mul]
    calc ‖κ p.1‖ * (‖f (p.1 * p.2)‖ * ‖a p.2‖) ≤ ‖κ p.1‖ * (M * ‖a p.2‖) := by gcongr
      _ = ‖κ p.1‖ * M * ‖a p.2‖ := by ring
  have hGi : Integrable G (μ.prod μ) :=
    ((measurePreserving_prod_mul μ μ).integrable_comp hGm).1 hGs
  have hF : Integrable (Function.uncurry fun z x => f z * (κ x * a (x⁻¹ * z))) (μ.prod μ) := by
    refine hGi.swap.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, G, Prod.fst_swap, Prod.snd_swap, Function.uncurry]
    ring
  calc ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ
      = ∫ z, ∫ x, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := by
        congr 1; funext z; exact (integral_const_mul _ _).symm
    _ = ∫ x, ∫ z, f z * (κ x * a (x⁻¹ * z)) ∂μ ∂μ := integral_integral_swap hF
    _ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_mul_left_eq_self (fun z => f z * (κ x * a (x⁻¹ * z))) x,
          ← integral_const_mul]
        congr 1; funext y
        simp only [inv_mul_cancel_left]
        ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem inv_mem_connectedComponentIn_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left)
    (hy : y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hw : ∀ z : G.left, G.hom ((ι[G]).left z) = G.hom z := by
    intro z
    have h := Over.w (ι[G])
    rw [← Scheme.Hom.comp_apply, h]
  have hη : ∀ s : S, (ι[G]).left ((η[G]).left s) = (η[G]).left s := by
    intro s
    have h : (η[G] ≫ ι[G]).left = (η[G]).left := by rw [GrpObj.one_inv]
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rw [hw]
  set F := G.hom ⁻¹' {G.hom y}
  set e := (η[G]).left (G.hom y)
  have heF : e ∈ F := (connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩)
  have hsub : (ι[G]).left '' connectedComponentIn F e ⊆ connectedComponentIn F e := by
    refine (isPreconnected_connectedComponentIn.image _ (ι[G]).left.continuous.continuousOn).subset_connectedComponentIn
      ⟨e, mem_connectedComponentIn heF, hη _⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzF : z ∈ F := connectedComponentIn_subset _ _ hz
    simp only [F, Set.mem_preimage, Set.mem_singleton_iff] at hzF ⊢
    rw [hw, hzF]
  exact hsub ⟨y, hy, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionNormClassRemoveRationalFactor
section
open scoped TensorProduct Classical

namespace GlobalTheory.RatRed

def LUnit (ℓ : ℕ) (r : ℚ) : Prop :=
  ∃ N : ℕ, ¬ ℓ ∣ N ∧ (∃ m : ℤ, (N : ℚ) * r = m) ∧ ∃ m : ℤ, (N : ℚ) * r⁻¹ = m

theorem lunit_one (ℓ : ℕ) (hℓ : ℓ.Prime) : LUnit ℓ 1 :=
  ⟨1, hℓ.not_dvd_one, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

theorem lunit_mul {ℓ : ℕ} (hℓ : ℓ.Prime) {r s : ℚ} (hr : LUnit ℓ r) (hs : LUnit ℓ s) :
    LUnit ℓ (r * s) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  obtain ⟨M, hM, ⟨k₁, g₁⟩, ⟨k₂, g₂⟩⟩ := hs
  refine ⟨N * M, fun h => (hℓ.dvd_mul.1 h).elim hN hM, ⟨m₁ * k₁, ?_⟩, ⟨m₂ * k₂, ?_⟩⟩
  · push_cast; rw [← h₁, ← g₁]; ring
  · push_cast; rw [← h₂, ← g₂, mul_inv]; ring

theorem lunit_inv {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ r⁻¹ := by
  obtain ⟨N, hN, h₁, h₂⟩ := hr
  exact ⟨N, hN, h₂, by simpa using h₁⟩

theorem lunit_neg {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ (-r) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨N, hN, ⟨-m₁, ?_⟩, ⟨-m₂, ?_⟩⟩
  · push_cast; rw [← h₁]; ring
  · push_cast; rw [← h₂, inv_neg]; ring

theorem lunit_nat {ℓ : ℕ} {n : ℕ} (hn : ¬ ℓ ∣ n) : LUnit ℓ (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by
    rintro h; exact hn (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨n, hn, ⟨(n : ℤ) * n, by push_cast; ring⟩, ⟨1, by rw [mul_inv_cancel₀ hn0]; simp⟩⟩

theorem lunit_pow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℕ) : LUnit ℓ (r ^ k) := by
  induction k with
  | zero => simpa using lunit_one ℓ hℓ
  | succ k ih => rw [pow_succ]; exact lunit_mul hℓ ih hr

theorem lunit_zpow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℤ) : LUnit ℓ (r ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using lunit_pow hℓ hr n
  · simpa [zpow_neg] using lunit_inv (lunit_pow hℓ hr n)

theorem lunit_prime {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ) : LUnit ℓ (p : ℚ) :=
  lunit_nat (fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h).symm)

theorem lunit_decomp {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℚ} (hc : c ≠ 0) :
    ∃ k : ℤ, LUnit ℓ (c / (ℓ : ℚ) ^ k) := by
  have hnum : c.num.natAbs ≠ 0 := by simpa using Rat.num_ne_zero.2 hc
  obtain ⟨e₁, n, hn, hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hnum ℓ hℓ.ne_one
  obtain ⟨e₂, m, hm, hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd c.den_nz ℓ hℓ.ne_one
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    rintro h; exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hden : (c.den : ℚ) = (ℓ : ℚ) ^ e₂ * m := by rw [hme]; push_cast; ring
  have key : c * ((ℓ : ℚ) ^ e₂ * m) = (c.num : ℚ) := by rw [← hden]; exact Rat.mul_den_eq_num c
  rw [zpow_sub₀ hℓ0, zpow_natCast, zpow_natCast]
  rcases Int.natAbs_eq c.num with h | h
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = (n : ℚ) * (m : ℚ)⁻¹ := by
      have : (c.num : ℚ) = (ℓ : ℚ) ^ e₁ * n := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm))
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = -((n : ℚ) * (m : ℚ)⁻¹) := by
      have : (c.num : ℚ) = -((ℓ : ℚ) ^ e₁ * n) := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_neg (lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm)))

theorem lunit_integral {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ}
    (hr : LUnit ℓ r) {d : ℕ} (hd : ¬ ℓ ∣ d) {x y : E} (hx : IsIntegral ℤ ((d : E) * x))
    (hy : IsIntegral ℤ ((d : E) * y)) :
    ∃ d' : ℕ, ¬ ℓ ∣ d' ∧ IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r * x)) ∧
      IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r⁻¹ * y)) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨d * N, fun h => (hℓ.dvd_mul.1 h).elim hd hN, ?_, ?_⟩
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r * x) = (m₁ : E) * ((d : E) * x) := by
      have : (m₁ : E) = algebraMap ℚ E ((N : ℚ) * r) := by rw [h₁]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₁).mul hx
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r⁻¹ * y) = (m₂ : E) * ((d : E) * y) := by
      have : (m₂ : E) = algebraMap ℚ E ((N : ℚ) * r⁻¹) := by rw [h₂]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₂).mul hy

theorem exists_nat_mul_integral {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (z : E) : ∃ D : ℕ, D ≠ 0 ∧ IsIntegral ℤ ((D : E) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_natCast] at this
    rwa [this] at hint
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_neg, Int.cast_natCast] at this
    rw [this, neg_mul] at hint
    simpa using hint.neg

theorem ratred : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E ≃ₐ[ℚ] E) (S : Finset ℕ) (A : Finset E),
    (∀ a : E, IsUnit a → τ a = a →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
        ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
      ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e) →
    ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  intro E _ _ _ τ S A hA a ha hτa hloc
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨D₁, hD₁, hi₁⟩ := exists_nat_mul_integral (u : E)
  obtain ⟨D₂, hD₂, hi₂⟩ := exists_nat_mul_integral ((u⁻¹ : Eˣ) : E)
  have hD0 : D₁ * D₂ ≠ 0 := mul_ne_zero hD₁ hD₂
  have hDu : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * u) := by
    have e : (((D₁ * D₂ : ℕ) : E) * u) = (D₂ : E) * ((D₁ : E) * u) := by push_cast; ring
    rw [e]; exact (isIntegral_natCast D₂).mul hi₁
  have hDu' : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) := by
    have e : (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) = (D₁ : E) * ((D₂ : E) * ((u⁻¹ : Eˣ) : E)) := by
      push_cast; ring
    rw [e]; exact (isIntegral_natCast D₁).mul hi₂
  choose! c b x y hc hb h₁ h₂ d hd hix hiy using hloc
  have hk : ∀ ℓ, ℓ.Prime → ℓ ∉ S → ∃ k : ℤ, LUnit ℓ (c ℓ / (ℓ : ℚ) ^ k) :=
    fun ℓ hℓ hS => lunit_decomp hℓ (hc ℓ hℓ hS)
  choose! k hk using hk
  let T : Finset ℕ := (D₁ * D₂).primeFactors.filter (· ∉ S)
  have hTmem : ∀ p, p ∈ T ↔ p.Prime ∧ p ∣ D₁ * D₂ ∧ p ∉ S := by
    intro p
    simp only [T, Finset.mem_filter, Nat.mem_primeFactors]
    tauto
  let q : ℚ := ∏ p ∈ T, (p : ℚ) ^ (k p)
  have hq0 : q ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p hp => zpow_ne_zero _ ?_
    exact_mod_cast ((hTmem p).1 hp).1.ne_zero
  have hqU : ∀ ℓ, ℓ.Prime → ℓ ∉ T → LUnit ℓ q := by
    intro ℓ hℓ hT
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hp).1 (fun h => hT (h ▸ hp))) _
  have hcqU : ∀ ℓ ∈ T, LUnit ℓ (c ℓ / q) := by
    intro ℓ hℓT
    obtain ⟨hℓ, -, hS⟩ := (hTmem ℓ).1 hℓT
    have e : c ℓ / q = c ℓ / (ℓ : ℚ) ^ (k ℓ) * (∏ p ∈ T.erase ℓ, (p : ℚ) ^ (k p))⁻¹ := by
      simp only [q]
      rw [← Finset.mul_prod_erase T (fun p => (p : ℚ) ^ (k p)) hℓT, div_mul_eq_div_div, div_eq_mul_inv]
    rw [e]
    refine lunit_mul hℓ (hk ℓ hℓ hS) (lunit_inv ?_)
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    obtain ⟨hpl, hpT⟩ := Finset.mem_erase.1 hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hpT).1 hpl) _
  have hq1 : algebraMap ℚ E q * algebraMap ℚ E q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have ha' : IsUnit (algebraMap ℚ E q⁻¹ * (u : E)) :=
    ((isUnit_iff_ne_zero.2 (inv_ne_zero hq0)).map (algebraMap ℚ E)).mul u.isUnit
  have hτ' : τ (algebraMap ℚ E q⁻¹ * (u : E)) = algebraMap ℚ E q⁻¹ * (u : E) := by
    rw [map_mul, AlgEquiv.commutes, hτa]
  obtain ⟨a₀, ha₀, e, he⟩ := hA _ ha' hτ' (by
    intro ℓ hℓ hS
    by_cases hT : ℓ ∈ T
    · obtain ⟨d', hd', hx', hy'⟩ :=
        lunit_integral hℓ (hcqU ℓ hT) (hd ℓ hℓ hS) (hix ℓ hℓ hS) (hiy ℓ hℓ hS)
      refine ⟨b ℓ, _, _, hb ℓ hℓ hS, ?_, ?_, d', hd', hx', hy'⟩
      · rw [div_eq_mul_inv, map_mul, h₁ ℓ hℓ hS]; ring
      · have hc1 : algebraMap ℚ E (c ℓ) * algebraMap ℚ E (c ℓ)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ (hc ℓ hℓ hS), map_one]
        rw [inv_div, div_eq_mul_inv, map_mul]
        linear_combination (-(b ℓ * τ (b ℓ))) * hc1 + algebraMap ℚ E (c ℓ)⁻¹ * h₂ ℓ hℓ hS -
          (algebraMap ℚ E (c ℓ)⁻¹ * y ℓ * (u : E)) * hq1
    · have hD : ¬ ℓ ∣ D₁ * D₂ := fun h => hT ((hTmem ℓ).2 ⟨hℓ, h, hS⟩)
      obtain ⟨d', hd', hx', hy'⟩ := lunit_integral hℓ (lunit_inv (hqU ℓ hℓ hT)) hD hDu hDu'
      refine ⟨1, _, _, isUnit_one, ?_, ?_, d', hd', hx', hy'⟩
      · simp
      · rw [inv_inv, map_one, mul_one]
        linear_combination (-((u : E) * ((u⁻¹ : Eˣ) : E))) * hq1 - u.mul_inv)
  refine ⟨a₀, ha₀, Units.mk0 q hq0, e, ?_⟩
  rw [← he, Units.val_mk0, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end GlobalTheory.RatRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleDvdOfDvdCharpolyOfAevalMatrix
section
open Matrix Polynomial

namespace GlobalTheory

theorem irreducible_dvd_of_dvd_charpoly_of_aeval_matrix {K : Type} [Field K] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) K) (p q : K[X]) (hp : Irreducible p)
    (hd : p ∣ M.charpoly) (hq : aeval M q = 0) : p ∣ q := by
  classical
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let M' := M.map (algebraMap K L)
  have hM' : aeval M' q = 0 := by
    have := Polynomial.aeval_algHom_apply ((Algebra.ofId K L).mapMatrix (m := Fin h)) M q
    rw [hq, map_zero] at this
    exact this
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (q.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap, hM'] at h2
  have hnt : Nontrivial (Matrix (Fin h) (Fin h) L) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (spectrum.mem_iff.1 hs) (isUnit_of_subsingleton _)
  rw [spectrum.zero_eq, Set.mem_singleton_iff] at h2
  simp only [eval_map, ← aeval_def] at h2
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h2
  exact h2

theorem charpoly_eq_pow_of_aeval_irreducible_eq_zero :
    ∀ (K : Type) [Field K] (h N : ℕ) (M : Matrix (Fin h) (Fin h) K) (f : K[X]), f.Monic →
      Irreducible f → Polynomial.aeval M f = 0 → h = f.natDegree * N → M.charpoly = f ^ N := by
  intro K _ h N M f hfm hfi hf hh
  classical
  have hc0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hmem : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors M.charpoly, b = f := by
    intro b hb
    have hbi := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb
    have hbd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb
    have hbn := UniqueFactorizationMonoid.normalize_normalized_factor b hb
    have hbm : b.Monic := by
      rw [← hbn]; exact Polynomial.monic_normalize hbi.ne_zero
    have hbf := irreducible_dvd_of_dvd_charpoly_of_aeval_matrix M b f hbi hbd hf
    exact eq_of_monic_of_associated hbm hfm (hbi.associated_of_dvd hfi hbf)
  set n := Multiset.card (UniqueFactorizationMonoid.normalizedFactors M.charpoly)
  have hrep : UniqueFactorizationMonoid.normalizedFactors M.charpoly = Multiset.replicate n f :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hass := UniqueFactorizationMonoid.prod_normalizedFactors hc0
  rw [hrep, Multiset.prod_replicate] at hass
  have hcp : M.charpoly = f ^ n :=
    (eq_of_monic_of_associated (hfm.pow n) (Matrix.charpoly_monic M) hass).symm
  have hdeg : f.natDegree * n = f.natDegree * N := by
    have := congrArg Polynomial.natDegree hcp
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hfm.natDegree_pow] at this
    rw [← hh]; linarith
  have hpos : 0 < f.natDegree := Irreducible.natDegree_pos hfi
  rw [hcp, Nat.eq_of_mul_eq_mul_left hpos hdeg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing
section
namespace GlobalTheory

theorem isAdicComplete_of_le_of_isNoetherianRing (R : Type) [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hIJ : I ≤ J) (hJ : IsAdicComplete J R) : IsAdicComplete I R := by
  have hle : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff I R :=
    ⟨fun x hx => hJ.toIsHausdorff.haus x fun n => (hx n).mono (hle n)⟩
  have hP : IsPrecomplete I R := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hJ.toIsPrecomplete.prec (f := f) fun {m n} h => (hf h).mono (hle m)
    refine ⟨L, fun n => ?_⟩
    set N : Submodule R R := I ^ n • ⊤ with hN
    have hK : (⨅ m : ℕ, J ^ m • ⊤ : Submodule R (R ⧸ N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J (by
        simpa only [Ideal.jacobson_bot] using IsAdicComplete.le_jacobson_bot J)
    rw [SModEq.sub_mem, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot R, ← hK,
      Submodule.mem_iInf]
    intro m
    have h1 : f n - f (max n m) ∈ N := SModEq.sub_mem.1 (hf (le_max_left n m))
    have h2 : f (max n m) - L ∈ (J ^ m • ⊤ : Submodule R R) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right n m))
        (SModEq.sub_mem.1 (hL (max n m)))
    have h3 : N.mkQ (f (max n m) - L) ∈ (J ^ m • ⊤ : Submodule R (R ⧸ N)) := by
      have := Submodule.mem_map_of_mem (f := N.mkQ) h2
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have h4 : (Submodule.Quotient.mk (f n - L) : R ⧸ N) = N.mkQ (f (max n m) - L) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      convert h1 using 1
      ring
    rw [h4]
    exact h3
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
section
namespace GlobalTheory.FinProjComplete

theorem mem_smul_top_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R) (x : ι → R) :
    x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => R) i) h
    rw [Submodule.map_smul''] at this
    simpa using Submodule.smul_mono le_rfl le_top this
  · have hx : x = ∑ i, x i • Pi.single i (1 : R) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

theorem isAdicComplete_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R)
    [IsAdicComplete J R] : IsAdicComplete J (ι → R) := by
  have hR : ∀ (x : R) n, x ≡ 0 [SMOD (J ^ n • ⊤ : Submodule R R)] ↔ x ∈ J ^ n := by
    intro x n; simp [SModEq.sub_mem]
  suffices h : IsHausdorff J (ι → R) ∧ IsPrecomplete J (ι → R) from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩,
    ⟨fun u hu => ?_⟩⟩
  · rw [hR]
    have := SModEq.sub_mem.1 (hx n)
    simpa using (mem_smul_top_pi (J ^ n) _).1 this j
  · have h1 : ∀ i, ∃ L : R, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R R)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (mem_smul_top_pi (J ^ a) _).1 (SModEq.sub_mem.1 (hu hab)) i
    choose L hL using h1
    refine ⟨L, fun k => SModEq.sub_mem.2 ((mem_smul_top_pi (J ^ k) _).2 fun i => ?_)⟩
    have := SModEq.sub_mem.1 (hL i k)
    rw [smul_eq_mul, Ideal.mul_top] at this
    simpa using this

theorem map_mem_pow_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) {x y : M} {n : ℕ}
    (h : x ≡ y [SMOD (J ^ n • ⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD (J ^ n • ⊤ : Submodule R N)] := by
  rw [SModEq.sub_mem] at h ⊢
  have := Submodule.mem_map_of_mem (f := f) h
  rw [Submodule.map_smul'', map_sub] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem isAdicComplete_of_retract {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (π : N →ₗ[R] M) (s : M →ₗ[R] N)
    (hs : ∀ x, π (s x) = x) [IsAdicComplete J N] : IsAdicComplete J M := by
  suffices h : IsHausdorff J M ∧ IsPrecomplete J M from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => ?_⟩, ⟨fun u hu => ?_⟩⟩
  · have : s x = 0 := IsHausdorff.haus' (I := J) (s x) fun n => by
      simpa using map_mem_pow_smul_top J s (hx n)
    rw [← hs x, this, map_zero]
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => s (u k))
      fun hab => map_mem_pow_smul_top J s (hu hab)
    exact ⟨π L, fun n => by simpa [hs] using map_mem_pow_smul_top J π (hL n)⟩

theorem isAdicComplete_span_natCast_of_finite_projective (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O] : IsAdicComplete (Ideal.span {(p : A)}) A := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have : IsAdicComplete (Ideal.span {(p : O)}) (Fin r → O) := isAdicComplete_pi _
  have hO : IsAdicComplete (Ideal.span {(p : O)}) A :=
    isAdicComplete_of_retract _ π s fun x => by simpa using LinearMap.congr_fun hs x
  have hmap : (Ideal.span {(p : O)}).map (algebraMap O A) = Ideal.span {(p : A)} := by
    simp [Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).2 hO

end GlobalTheory.FinProjComplete
end

