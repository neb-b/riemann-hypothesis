module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DyadicSummationWithDecay
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem dyad_cauchySchwarz {X : Type} [MeasurableSpace X] (μ : Measure X) (A B : X → ℝ)
    (hA : Measurable A) (hB : Measurable B) (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (h1 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ ≤ ENNReal.ofReal (P ^ 2))
    (h2 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ ≤ ENNReal.ofReal (Q ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ ≤ ENNReal.ofReal (P * Q) := by
  have hc : 0 < Q / (2 * P) := by positivity
  have hd : 0 < P / (2 * Q) := by positivity
  have hpt : ∀ x, ENNReal.ofReal (A x * B x) ≤
      ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (A x ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (B x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : Q / (2 * P) * A x ^ 2 + P / (2 * Q) * B x ^ 2 - A x * B x
        = (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by
      field_simp; ring
    have h0 : 0 ≤ (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by positivity
    linarith
  have mA : Measurable fun x => ENNReal.ofReal (A x ^ 2) := by fun_prop
  have mB : Measurable fun x => ENNReal.ofReal (B x ^ 2) := by fun_prop
  calc _ ≤ _ := lintegral_mono hpt
    _ = ENNReal.ofReal (Q / (2 * P)) * ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ
        + ENNReal.ofReal (P / (2 * Q)) * ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ := by
      rw [lintegral_add_left (mA.const_mul _), lintegral_const_mul _ mA, lintegral_const_mul _ mB]
    _ ≤ ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (P ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (Q ^ 2) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp; ring

theorem dyad_exists_shell (H s : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H ∧ (i = 0 ∨ 2 ^ i * H < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hH] at hn
    have : (0:ℝ) < 2 ^ n * H := by positivity
    rw [pow_succ]; linarith
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := k) (by omega)
    exact not_le.mp this

theorem dyad_exists_down (M y : ℝ) (hy : 0 < y) (hM : y ≤ M) :
    ∃ a : ℕ, M / 2 ^ (a + 1) < y ∧ y ≤ 2 * (M / 2 ^ (a + 1)) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := M / y) (y := 2)
    (by rw [le_div_iff₀ hy]; linarith) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hy] at h2; linarith
  · rw [le_div_iff₀ hy] at h1
    have : 2 * (M / 2 ^ (n + 1)) = M / 2 ^ n := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]; linarith

theorem dyad_piece_real (r k e n : ℕ) (H De N sg u v w : ℝ) (hr : 1 ≤ r) (hH : 0 < H)
    (hDe : 0 < De) (hN : 0 < N) (hsg : 1 ≤ sg) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hwN : w ≤ N) (hwM : w ≤ ((u * (2 * H)) ^ r * De) ^ 2 * v)
    (hNR : 1 ≤ N * (u * (2 * H)) ^ (2 * r)) (hsu : sg ≤ u ^ r) :
    (u * (2 * H)) ^ e * w ^ (k + 1) * (u ^ (e + 4 * r + 1 + n))⁻¹ ≤
      (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * sg ^ (-((n : ℝ) / r)) * (u⁻¹ * v) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have h1 : (u ^ n)⁻¹ ≤ sg ^ (-((n : ℝ) / r)) := by
    rw [Real.rpow_neg (by linarith)]
    apply inv_anti₀ (by positivity)
    calc sg ^ ((n : ℝ) / r) ≤ (u ^ r) ^ ((n : ℝ) / r) := by gcongr
      _ = u ^ n := by
        rw [← Real.rpow_natCast u r, ← Real.rpow_mul hu.le, ← Real.rpow_natCast u n]
        congr 1; field_simp
  have h2 : w ^ (k + 1) ≤ N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v := by
    calc w ^ (k + 1) = w ^ k * w * 1 := by ring
      _ ≤ N ^ k * (((u * (2 * H)) ^ r * De) ^ 2 * v) * (N * (u * (2 * H)) ^ (2 * r)) := by
        gcongr
      _ = _ := by ring
  calc _ ≤ (u * (2 * H)) ^ e * (N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v)
        * (u ^ (e + 4 * r + 1 + n))⁻¹ := by gcongr
    _ = (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * (u ^ n)⁻¹ * (u⁻¹ * v) := by
      rw [mul_pow u, mul_pow u]
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem dyad_tsum_four (c : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, c * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = 16 * c := by
  have g : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
    rw [ENNReal.tsum_geometric]; simp
  rw [ENNReal.tsum_mul_left]
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, g]
  ring

theorem dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  intro X _ ν A B S S' Y Y' r j kk e q H₁ De D K K' sg hA hB _ _ _ _ hr hkk hq hH hDe hD hK hK'
    hsg hae h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, kk = k + 1 := ⟨kk - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = e + 4 * r + 1 + n := ⟨q - (e + 4 * r + 1), by omega⟩
  have hexp : ((e + 4 * r + 1 + n : ℕ) : ℝ) - e - 4 * r - 1 = n := by push_cast; ring
  rw [hexp]
  have hH0 : 0 < H₁ := by linarith
  have hDe0 : 0 < De := by linarith
  set C : ℝ := Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
    * sg ^ (-((n : ℝ) / r))) with hC
  have hC0 : 0 ≤ C := by positivity
  let M : ℕ → ℕ → ℝ := fun i i' => (2 ^ (i + i' + 1) * H₁) ^ r * De
  have hM0 : ∀ i i', 0 < M i i' := fun i i' => by positivity
  let P : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x |
    (0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) ∧
    (S x ≤ 2 ^ (p.1 + 1) * H₁ ∧ (p.1 = 0 ∨ 2 ^ p.1 * H₁ < S x)) ∧
    (S' x ≤ 2 ^ (p.2.1 + 1) * H₁ ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H₁ < S' x)) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, P p := by
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := dyad_exists_shell H₁ (S x) hH0
    obtain ⟨i', hi'⟩ := dyad_exists_shell H₁ (S' x) hH0
    have hmax : max (S x) (S' x) ^ r * De ≤ M i i' := by
      have a1 : (2:ℝ) ^ (i + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a2 : (2:ℝ) ^ (i' + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a3 : max (S x) (S' x) ≤ 2 ^ (i + i' + 1) * H₁ :=
        max_le (hi.1.trans (by gcongr)) (hi'.1.trans (by gcongr))
      have a4 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith [hx.2.2.1])
      show _ ≤ (2 ^ (i + i' + 1) * H₁) ^ r * De
      gcongr
    obtain ⟨a, ha⟩ := dyad_exists_down (M i i') (Y x) hx.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.1.trans hmax)
    obtain ⟨b, hb⟩ := dyad_exists_down (M i i') (Y' x) hx.2.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.2.1.trans hmax)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b), hx, hi, hi', ha, hb⟩
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in P p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (P (i, i', a, b)).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]; simp
    obtain ⟨⟨-, -, s1, s2, y1, y2, g1, g2, -, -, g3⟩, ⟨b1, -⟩, ⟨b2, -⟩, ⟨c1, -⟩, ⟨c2, -⟩⟩ := hx
    simp only at b1 b2 c1 c2 ⊢
    have hm := hM0 i i'
    set y : ℝ := M i i' / 2 ^ (a + 1) with hy
    set y' : ℝ := M i i' / 2 ^ (b + 1) with hy'
    have hy0 : 0 < y := by positivity
    have hy0' : 0 < y' := by positivity
    set R : ℝ := 2 ^ (i + i' + 1) * H₁ with hR
    have hR0 : 0 < R := by positivity
    set q := e + 4 * r + 1 + n with hqdef
    have i1 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (A x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K * Real.sqrt (R ^ e) * y ^ (k + 1) * (((2:ℝ) ^ i) ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h1 i i' y hy0).trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.1.1, hz.2.1.2, hz.2.2.1.1, hz.2.2.2.1.1, hz.2.2.2.1.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y, ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    have i2 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (B x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K' * Real.sqrt (R ^ e) * y' ^ (k + 1) * (((2:ℝ) ^ i') ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h2 i i' y' hy0').trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.2.1.1, hz.2.2.1.2, hz.2.1.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK'.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y', ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    refine (dyad_cauchySchwarz _ A B hA hB _ _ (by positivity) (by positivity) i1 i2).trans ?_
    have hrhs : ENNReal.ofReal C * (2⁻¹ ^ i * (2⁻¹ ^ i' * (2⁻¹ ^ a * 2⁻¹ ^ b))) =
        ENNReal.ofReal (C * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
      have e2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ : ℝ) := by
        rw [ENNReal.ofReal_inv_of_pos two_pos]; simp
      rw [ENNReal.ofReal_mul hC0, e2]
      congr 1
      simp only [← ENNReal.ofReal_pow (show (0:ℝ) ≤ 2⁻¹ by norm_num)]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_add, pow_add]; simp only [inv_pow]; field_simp
    rw [hrhs]
    apply ENNReal.ofReal_le_ofReal
    have hRu : R = 2 ^ (i + i') * (2 * H₁) := by rw [hR]; ring
    have hu1 : (1:ℝ) ≤ 2 ^ (i + i') := one_le_pow₀ one_le_two
    have hSS : S x * S' x ≤ 2 ^ (i + i') * (2 * H₁) ^ 2 := by
      calc S x * S' x ≤ (2 ^ (i + 1) * H₁) * (2 ^ (i' + 1) * H₁) := by
            apply mul_le_mul b1 b2 (by linarith) (by positivity)
        _ = _ := by ring
    have hSS0 : 0 ≤ S x * S' x := mul_nonneg (by linarith) (by linarith)
    have hSSr : (S x * S' x) ^ r ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := by
      rw [pow_mul, ← mul_pow]; gcongr
    have key := dyad_piece_real r k e n H₁ De (2 ^ j / D) sg (2 ^ (i + i')) ((2 ^ (a + b))⁻¹)
      (y * y') hr hH0 hDe0 (by positivity) hsg (by positivity) (by positivity) (by positivity)
      (by
        rw [le_div_iff₀ hD]
        refine le_trans ?_ g1
        gcongr)
      (by
        rw [← hRu]
        have : y * y' = (R ^ r * De) ^ 2 * (2 ^ (a + b))⁻¹ / 4 := by
          rw [hy, hy']
          show (R ^ r * De) / _ * ((R ^ r * De) / _) = _
          field_simp; ring
        rw [this]
        have : 0 ≤ (R ^ r * De) ^ 2 * ((2:ℝ) ^ (a + b))⁻¹ := by positivity
        linarith)
      (by
        rw [div_mul_eq_mul_div, le_div_iff₀ hD, one_mul]
        have j1 : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
        have : ((2:ℝ) ^ (i + i')) ^ r ≤ (2 ^ (i + i')) ^ (2 * r) :=
          pow_le_pow_right₀ hu1 (by omega)
        calc D ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := g2.trans hSSr
          _ ≤ (2 ^ (i + i')) ^ (2 * r) * (2 * H₁) ^ (2 * r) := by gcongr
          _ = 1 * (2 ^ (i + i') * (2 * H₁)) ^ (2 * r) := by rw [mul_pow _ (2 * H₁), one_mul]
          _ ≤ _ := by gcongr)
      (by
        refine g3.trans (max_le (one_le_pow₀ hu1) ?_)
        rw [div_le_iff₀ (by positivity)]
        exact hSSr)
    rw [← hRu, ← hqdef] at key
    have hsq : Real.sqrt (R ^ e) * Real.sqrt (R ^ e) = R ^ e := Real.mul_self_sqrt (by positivity)
    calc _ = Real.sqrt (K * K') * ((Real.sqrt (R ^ e) * Real.sqrt (R ^ e)) * (y * y') ^ (k + 1)
            * (((2:ℝ) ^ (i + i')) ^ q)⁻¹) := by
          rw [Real.sqrt_mul hK.le, mul_pow y, pow_add 2 i i', mul_pow _ _ q, mul_inv]; ring
      _ ≤ Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
            * sg ^ (-((n : ℝ) / r)) * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
          rw [hsq]; gcongr
      _ = _ := by rw [hC]; ring
  calc _ = ∫⁻ x in ⋃ p, P p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = 16 * ENNReal.ofReal C := dyad_tsum_four _
    _ = ENNReal.ofReal (16 * C) := by
        rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 16 by norm_num), ENNReal.ofReal_ofNat]
    _ = _ := by rw [hC]; congr 1; ring

end GlobalTheory.Amp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProjector
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.WittInt

theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ z ∈ Λ, P z ∈ Λ) ∧ (∀ z, P z ∈ W) ∧ ∀ z ∈ W, P z = z := by
  have hmul : ∀ y : V, ∃ s : nonZeroDivisors O, s • y ∈ Λ := fun y => by
    have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
    rw [Submodule.span_eq] at hs
    exact ⟨s, hs⟩
  have hunit : ∀ s : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) s) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hunit
      surj := fun y => by
        obtain ⟨s, hs⟩ := hmul y
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hne : ∀ s : nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hsat : ∀ (s : nonZeroDivisors O) (v : V), (s : O) • v ∈ W → v ∈ W := fun s v h => by
    rw [← algebraMap_smul K] at h
    exact (W.smul_mem_iff (hne s)).1 h
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := (W.restrictScalars O).comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c v h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hunit)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hunit y
  refine ⟨g, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact (π _).2
  · obtain ⟨c, hc⟩ := hmul z
    refine hsat c _ ?_
    rw [← LinearMap.map_smul_of_tower]
    have := hg ⟨_, hc⟩
    rw [show g ((c : O) • z) = _ from this]
    exact hπ _
  · obtain ⟨c, hc⟩ := hmul z
    have h1 := hg ⟨_, hc⟩
    rw [hπ' ⟨_, hc⟩ ((W.restrictScalars O).smul_mem (c : O) hz)] at h1
    have h2 : g (algebraMap O K c • z) = algebraMap O K c • z := by
      rw [algebraMap_smul]; exact h1
    rw [map_smul] at h2
    exact smul_right_injective V (hne c) h2

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem form_star {J : Matrix (Fin n) (Fin n) E} (hJ : Jᴴ = J) (x y : Fin n → E) :
    star (star x ⬝ᵥ (J *ᵥ y)) = star y ⬝ᵥ (J *ᵥ x) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec, dotProduct_comm]

theorem form_adj {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) :
    star (M *ᵥ x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ ((J⁻¹ * Mᴴ * J) *ᵥ y)) := by
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.one_mul, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_nondeg {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (y : Fin n → E)
    (h : ∀ x : Fin n → E, star x ⬝ᵥ (J *ᵥ y) = 0) : y = 0 := by
  apply eq_zero_of_mulVec_eq_zero hd
  funext i
  have := h (Pi.single i 1)
  simpa [← Pi.single_star] using this

theorem exists_adjoint {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0)
    (P : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ Q : (Fin n → E) →ₗ[E] (Fin n → E),
      (∀ x y, star (P x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ Q y)) ∧
      LinearMap.trace E _ Q = star (LinearMap.trace E _ P) := by
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective P
  refine ⟨Matrix.toLin' (J⁻¹ * Mᴴ * J), fun x y => form_adj hd M x y, ?_⟩
  rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_mul_cycle,
    mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, trace_conjTranspose]

end Form

theorem split_of_trace (E : Type) [Field E] [NumberField E] [StarRing E] (w : 𝓞 E)
    (hw : (w : E) + star (w : E) = 1) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (hd : J.det ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hself : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (W : Submodule E (Fin n → E)) (hW : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) :
    ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧
      Module.finrank E W' = Module.finrank E W ∧
      (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧
      ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧
        ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  have hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
    let U := Submodule.span E (Λ : Set (Fin n → E))
    change U = ⊤
    by_contra hU
    let g : (Fin n → E) →ₗ[E] Module.Dual E U :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin J)).domRestrict₂ U
    have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hU
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := star z
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      have := congrArg star hy
      simpa [y] using this
    have hline (a : E) : a • y ∈ Λ := (hself _).2 fun x hx => by
      have hz' : z ⬝ᵥ (J *ᵥ x) = 0 :=
        congrArg (fun f : Module.Dual E U => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have horth : star x ⬝ᵥ (J *ᵥ y) = 0 := by
        rw [← form_star hJ y x]
        simp [y, hz']
      simp only [Matrix.mulVec_smul, dotProduct_smul, horth, smul_zero]
      exact ⟨0, map_zero _⟩
    let i : E →ₗ[𝓞 E] Λ :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict Λ hline
    let : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨P, hPΛ, hPW, hPid⟩ := exists_projector Λ hΛ.fg hspan W
  obtain ⟨Q, hPQ, htr⟩ := exists_adjoint hd P
  have hQP : ∀ x y, star (Q x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ P y) := fun x y => by
    rw [← form_star hJ, ← hPQ, form_star hJ]
  have hQΛ : ∀ z ∈ Λ, Q z ∈ Λ := fun z hz => (hself _).2 fun y hy => by
    rw [← hPQ]; exact (hself z).1 hz _ (hPΛ y hy)
  have hQ0 : ∀ y, (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → Q y = 0 := fun y hy =>
    form_nondeg hd _ fun x => by rw [← hPQ]; exact hy _ (hPW x)
  have hQW : ∀ y ∈ W, Q y = 0 := fun y hy => hQ0 y fun x hx => hW x hx y hy
  have hPP : ∀ y, P (P y) = P y := fun y => hPid _ (hPW y)
  have hQQ : ∀ y, Q (Q y) = Q y := fun y => by
    rw [← sub_eq_zero]
    refine form_nondeg hd _ fun x => ?_
    rw [mulVec_sub, dotProduct_sub, ← hPQ, ← hPQ, hPP, hPQ, sub_self]
  have hQPz : ∀ y, Q (P y) = 0 := fun y => hQW _ (hPW y)
  let T : (Fin n → E) →ₗ[E] (Fin n → E) := Q - (w : E) • (P ∘ₗ Q)
  have hT : ∀ y, T y = Q y - (w : E) • P (Q y) := fun y => rfl
  have hQT : ∀ y, Q (T y) = Q y := fun y => by
    rw [hT, map_sub, map_smul, hQPz, hQQ, smul_zero, sub_zero]
  have hTT : ∀ y, T (T y) = T y := fun y => by rw [hT (T y), hQT, hT]
  have hWT : ∀ x ∈ W, ∀ y, star x ⬝ᵥ (J *ᵥ T y) = star x ⬝ᵥ (J *ᵥ y) := fun x hx y => by
    rw [hT, mulVec_sub, dotProduct_sub, hW x hx _ (W.smul_mem _ (hPW _)), sub_zero, ← hPQ, hPid x hx]
  have hTl : ∀ x y, star (T x) ⬝ᵥ (J *ᵥ y) =
      star x ⬝ᵥ (J *ᵥ (P y - star (w : E) • P (Q y))) := fun x y => by
    rw [hT, star_sub, star_smul, sub_dotProduct, smul_dotProduct, hPQ, hQP, hQP, mulVec_sub,
      dotProduct_sub, mulVec_smul, dotProduct_smul]
  refine ⟨LinearMap.range T, ?_, ?_, ?_, fun z hz => ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hTl, hQT, hT, map_sub, map_smul, hPP, sub_sub, ← add_smul, hw, one_smul, sub_self, mulVec_zero,
      dotProduct_zero]
  · have h1 : LinearMap.IsProj W P := ⟨hPW, hPid⟩
    have h2 : LinearMap.IsProj (LinearMap.range T) T :=
      ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hTT x⟩
    have h3 : Q ∘ₗ P = 0 := LinearMap.ext hQPz
    have h4 : LinearMap.trace E _ T = LinearMap.trace E _ Q := by
      simp only [T]
      rw [map_sub, map_smul, LinearMap.trace_comp_comm', h3, map_zero, smul_zero, sub_zero]
    rw [h2.trace, htr, h1.trace, star_natCast] at h4
    exact_mod_cast h4
  · rintro _ ⟨y, rfl⟩ hy
    have h0 : Q y = 0 := hQ0 y fun x hx => by rw [← hWT x hx]; exact hy x hx
    rw [hT, h0, map_zero, smul_zero, sub_zero]
  · have hTz : T z ∈ Λ := Λ.sub_mem (hQΛ z hz) (Λ.smul_mem w (hPΛ _ (hQΛ z hz)))
    have hu : z - T z ∈ Λ := Λ.sub_mem hz hTz
    have hxW : P (z - T z) ∈ W := hPW _
    have hQu : Q (z - T z) = 0 := by rw [map_sub, hQT, sub_self]
    refine ⟨P (z - T z), hPΛ _ hu, T z, hTz, hxW, ⟨z, rfl⟩, fun t ht => ?_⟩
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ht
    rw [star_add, add_dotProduct, hTl, sub_right_comm, map_sub P (z - T z), map_sub Q (z - T z), hQu, hQPz, hPP, sub_self,
      sub_self, map_zero, smul_zero, sub_self, mulVec_zero, dotProduct_zero, add_zero, mulVec_sub,
      mulVec_sub, dotProduct_sub, dotProduct_sub, hWT a ha, hW a ha _ hxW, sub_self, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ W : Submodule E (Fin n → E), (∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧ Module.finrank E W' = Module.finrank E W ∧ (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧ ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  intro E _ _ _ hE n J hJ hd Λ hΛ hs W hW
  obtain ⟨w, hw⟩ := GlobalTheory.TraceOnto.exists_trace_one E hE
  exact split_of_trace E w hw n J hJ hd Λ hΛ hs W hW

end GlobalTheory.WittInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarOnBesselSubgroupProdMap
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.ProdHaarS

theorem isHaarOn_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN →
    IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨-, -, h, -⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  exact h

end GlobalTheory.SgInf.ProdHaarS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitaryStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_map_mul_right_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (M : Set (Formalism.REAL.UJ ε)) → IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ → ∀ l ∈ M, l ∈ maxK ε → μ.map (fun g => g * l) = μ := by
  first | exact @GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | exact GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | (intros; apply GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right <;> assumption)
end

