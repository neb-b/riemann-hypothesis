module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.Dyadic

theorem lintegral_mul_le_of_sq {X : Type} [MeasurableSpace X] (μ : Measure X) (A B : X → ℝ)
    (hA : Measurable A) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (h1 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ ≤ ENNReal.ofReal (α ^ 2))
    (h2 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ ≤ ENNReal.ofReal (α * β) := by
  have hc : 0 ≤ β / (2 * α) := by positivity
  have hd : 0 ≤ α / (2 * β) := by positivity
  calc ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (β / (2 * α)) * ENNReal.ofReal (A x ^ 2)
          + ENNReal.ofReal (α / (2 * β)) * ENNReal.ofReal (B x ^ 2)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : β / (2 * α) * A x ^ 2 + α / (2 * β) * B x ^ 2 - A x * B x
            = (β * A x - α * B x) ^ 2 / (2 * α * β) := by
          field_simp; ring
        have h3 : 0 ≤ (β * A x - α * B x) ^ 2 / (2 * α * β) := by positivity
        linarith
    _ = ENNReal.ofReal (β / (2 * α)) * ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ
          + ENNReal.ofReal (α / (2 * β)) * ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (β / (2 * α)) * ENNReal.ofReal (α ^ 2)
          + ENNReal.ofReal (α / (2 * β)) * ENNReal.ofReal (β ^ 2) := by gcongr
    _ = ENNReal.ofReal (α * β) := by
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp; ring

theorem exists_shell (s H : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ i * H ∧ (i = 0 ∨ 2 ^ i * H / 2 < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ i * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    exact ⟨n, ((div_lt_iff₀ hH).1 hn).le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | j
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := j) (by omega)
    push Not at this
    rw [pow_succ]; linarith

theorem exists_shell_down (y T : ℝ) (hy : 0 < y) (hT : y ≤ T) :
    ∃ a : ℕ, T / 2 ^ (a + 1) < y ∧ y ≤ 2 * (T / 2 ^ (a + 1)) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := T / y) (y := (2 : ℝ))
    ((one_le_div hy).2 hT) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hy] at h2; linarith
  · rw [le_div_iff₀ hy] at h1
    have : 2 * (T / 2 ^ (n + 1)) = T / 2 ^ n := by rw [pow_succ]; field_simp
    rw [this, le_div_iff₀ (by positivity)]; linarith

theorem piece_bound (r kk : ℕ) (H De D l l' u v : ℝ) (hr : 1 ≤ r) (hkk : 1 ≤ kk) (hH : 1 ≤ H)
    (hDe : 1 ≤ De) (hD : 0 < D) (hl : 1 ≤ l) (hl' : 1 ≤ l') (hu : 0 < u) (hv : 0 < v)
    (h1 : (r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u *
      ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) * D ≤ 2 ^ r)
    (h2 : D ≤ (l * l' * H) ^ (2 * r)) :
    ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u) ^ kk *
        (l ^ (24 * r ^ 3 + 1))⁻¹) *
      ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) ^ kk *
        (l' ^ (24 * r ^ 3 + 1))⁻¹) ≤
      (r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk *
        (l⁻¹ * l'⁻¹ * u⁻¹ * v⁻¹) := by
  have hR : 1 ≤ l * l' * H := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hl hl') hH
  have hRe : (l * l' * H) ^ (24 * r ^ 3) = l ^ (24 * r ^ 3) * l' ^ (24 * r ^ 3) * H ^ (24 * r ^ 3) := by
    rw [mul_pow, mul_pow]
  generalize l * l' * H = R at *
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hT2 : (r * R ^ (2 * r - 1) * De) ^ r * (r * R ^ (2 * r - 1) * De) ^ r * R ^ (2 * r)
      = (r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [this]
    generalize ((m + 1 : ℕ) : ℝ) = c
    ring
  have hTpos : 0 < (r * R ^ (2 * r - 1) * De) ^ r := by positivity
  generalize (r * R ^ (2 * r - 1) * De) ^ r = T at *
  set P : ℝ := 2 ^ r / D with hP
  have hPpos : 0 < P := by positivity
  set w : ℝ := T / u * (T / v) with hw
  have hwpos : 0 < w := by positivity
  have hwP : w ≤ P := by rw [hP, le_div_iff₀ hD]; exact h1
  have h3 : w ^ kk ≤ P ^ kk * (T * T * R ^ (2 * r) * (u⁻¹ * v⁻¹)) := by
    obtain ⟨m, rfl⟩ : ∃ m, kk = m + 1 := ⟨kk - 1, by omega⟩
    have h4 : w ^ m ≤ P ^ m := pow_le_pow_left₀ hwpos.le hwP m
    have h5 : 1 ≤ P * R ^ (2 * r) := by
      have : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ one_le_two
      calc (1 : ℝ) ≤ 2 ^ r := this
        _ = P * D := by rw [hP]; field_simp
        _ ≤ P * R ^ (2 * r) := by gcongr
    calc w ^ (m + 1) = w ^ m * w * 1 := by ring
      _ ≤ P ^ m * w * (P * R ^ (2 * r)) := by gcongr
      _ = _ := by rw [hw]; ring
  rw [hT2] at h3
  have h6 : R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2) ≤ R ^ (24 * r ^ 3) := by
    rw [← pow_add, ← pow_add]
    refine pow_le_pow_right₀ hR ?_
    have : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    omega
  have hl0 : 0 < l := by linarith
  have hl0' : 0 < l' := by linarith
  have hR0 : 0 < R := by linarith
  have hDe0 : 0 < De := by linarith
  calc _ = R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * w ^ kk *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by
          rw [hw, mul_pow]; ring
    _ ≤ R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = (R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2)) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by ac_rfl
    _ ≤ R ^ (24 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = _ := by
      rw [hRe, pow_succ l, pow_succ l']
      have e1 : 0 < l ^ (24 * r ^ 3) := by positivity
      have e2 : 0 < l' ^ (24 * r ^ 3) := by positivity
      generalize l ^ (24 * r ^ 3) = a at *
      generalize l' ^ (24 * r ^ 3) = b at *
      generalize H ^ (24 * r ^ 3) = c
      generalize P ^ kk = d
      generalize (r : ℝ) ^ (2 * r) = e
      generalize De ^ (2 * r) = f
      field_simp

theorem tsum_four (C : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = C * 16 := by
  have h : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
    rw [ENNReal.tsum_geometric]; simp
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, h]
  norm_num

theorem dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r kk : ℕ) (H₁ De D K K' : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧ D ≤ max (S x) (S' x) ^ (2 * r) ∧ Y x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ∧ Y' x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ i * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < S x) ∧ S' x ≤ 2 ^ i' * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < S' x) ∧ S x ≤ 2 ^ i * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (Real.sqrt (K * K') * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk) := by
  intro X _ ν A B S S' Y Y' r kk H De D K K' hA hB hS hS' hY hY' hr hkk hH hDe hD hK hK' hae h1 h2
  have hH0 : 0 < H := by linarith
  have hDe0 : 0 < De := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  let T : ℕ → ℕ → ℝ := fun i i' => (r * ((2 : ℝ) ^ i * 2 ^ i' * H) ^ (2 * r - 1) * De) ^ r
  have hT : ∀ i i', 0 < T i i' := fun i i' => by positivity
  let Q : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x | (0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧
      D ≤ ((2 : ℝ) ^ p.1 * 2 ^ p.2.1 * H) ^ (2 * r)) ∧
      S x ≤ 2 ^ p.1 * H ∧ (p.1 = 0 ∨ 2 ^ p.1 * H / 2 < S x) ∧
      S' x ≤ 2 ^ p.2.1 * H ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H / 2 < S' x) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
      (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (T p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, Q p := by
    filter_upwards [hae] with x ⟨_, _, s1, s2, y1, y2, hyy, hd, t1, t2⟩
    obtain ⟨i, hi, hi2⟩ := exists_shell (S x) H hH0
    obtain ⟨i', hi', hi2'⟩ := exists_shell (S' x) H hH0
    have a1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    have a2 : (1 : ℝ) ≤ 2 ^ i' := one_le_pow₀ one_le_two
    have hm : max (S x) (S' x) ≤ (2 : ℝ) ^ i * 2 ^ i' * H := by
      refine max_le (hi.trans ?_) (hi'.trans ?_)
      · gcongr; exact le_mul_of_one_le_right (by positivity) a2
      · gcongr; exact le_mul_of_one_le_left (by positivity) a1
    have hm0 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith)
    have hmT : (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ≤ T i i' := by
      simp only [T]; gcongr
    obtain ⟨a, ha⟩ := exists_shell_down (Y x) (T i i') y1 (t1.trans hmT)
    obtain ⟨b, hb⟩ := exists_shell_down (Y' x) (T i i') y2 (t2.trans hmT)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b),
      ⟨y1, y2, hyy, hd.trans (pow_le_pow_left₀ hm0 hm _)⟩, hi, hi2, hi', hi2', ha, hb⟩
  set C : ℝ := Real.sqrt (K * K') * ((r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) *
    (2 ^ r / D) ^ kk) with hC
  have hC0 : 0 ≤ C := by positivity
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (Q (i, i', a, b)).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
    · rw [h]; simp
    obtain ⟨⟨y1, y2, hyy, hd⟩, -, -, -, -, ⟨ha, -⟩, ⟨hb, -⟩⟩ := hx0
    dsimp only at hd ha hb ⊢
    have hTi := hT i i'
    have hyy' : T i i' / 2 ^ (a + 1) * (T i i' / 2 ^ (b + 1)) * D ≤ 2 ^ r := by
      refine le_trans ?_ hyy
      gcongr
    have key := piece_bound r kk H De D (2 ^ i) (2 ^ i') (2 ^ (a + 1)) (2 ^ (b + 1)) hr hkk hH hDe hD
      (one_le_pow₀ one_le_two) (one_le_pow₀ one_le_two) (by positivity) (by positivity) hyy' hd
    have cs := lintegral_mul_le_of_sq (ν.restrict (Q (i, i', a, b))) A B hA
      (Real.sqrt K * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (a + 1)) ^ kk *
        (((2 : ℝ) ^ i) ^ (24 * r ^ 3 + 1))⁻¹))
      (Real.sqrt K' * (((2 : ℝ) ^ i * 2 ^ i' * H) ^ (10 * r ^ 3) * (T i i' / 2 ^ (b + 1)) ^ kk *
        (((2 : ℝ) ^ i') ^ (24 * r ^ 3 + 1))⁻¹)) (by positivity) (by positivity)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h1 i i' (T i i' / 2 ^ (a + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, q2, q3, -, ⟨q4, q5⟩, -⟩
          exact ⟨q1, q2, q3, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K), Real.sq_sqrt hK.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (a + 1) = y
          generalize (2 : ℝ) ^ i = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
      (by
        refine (lintegral_mono_set ?_).trans
          ((h2 i i' (T i i' / 2 ^ (b + 1)) (by positivity)).trans (le_of_eq ?_))
        · rintro x ⟨-, q1, -, q2, q3, -, ⟨q4, q5⟩⟩
          exact ⟨q2, q3, q1, q4, q5⟩
        · congr 1
          rw [mul_pow (Real.sqrt K'), Real.sq_sqrt hK'.le, pow_add (2 : ℝ) i i']
          generalize (2 : ℝ) ^ i * 2 ^ i' * H = R
          generalize T i i' / 2 ^ (b + 1) = y
          generalize (2 : ℝ) ^ i' = l
          generalize 24 * r ^ 3 + 1 = q
          ring)
    refine cs.trans ?_
    have e : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 ^ n)⁻¹) := fun n => by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.inv_pow]
      simp
    rw [e, e, e, e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_mul_mul_comm, ← Real.sqrt_mul hK.le, hC, mul_assoc (Real.sqrt (K * K'))]
    refine mul_le_mul_of_nonneg_left (key.trans ?_) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_assoc, mul_assoc]
    gcongr <;> simp
  calc ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν
      = ∫⁻ x in ⋃ p, Q p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ ∑' p, ∫⁻ x in Q p, ENNReal.ofReal (A x * B x) ∂ν := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal C * 16 := tsum_four _
    _ = ENNReal.ofReal (C * 16) := by rw [ENNReal.ofReal_mul hC0]; simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C * 16 ≤ C * 24 := by gcongr; norm_num
          _ = _ := by rw [hC]; ring

end GlobalTheory.Dyadic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalGen
section
namespace GlobalTheory.LocalGenerators

theorem local_gen {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ (0 : R) ∧ ∃ s ∉ P.asIdeal, ∀ y ∈ J, ∃ o : R, s * y = o * d := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : ¬ J ≤ J * P.asIdeal := by
    intro h
    have heq : J * P.asIdeal = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h
    exact hP (mul_left_cancel₀ hJ heq)
  obtain ⟨d, hdJ, hdn⟩ := SetLike.not_le_iff_exists.mp hlt
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hdn (Submodule.zero_mem _)
  have hdvd : J ∣ Ideal.span {d} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  obtain ⟨K, hK⟩ := hdvd
  have hKP : ¬ K ≤ P.asIdeal := by
    intro h
    apply hdn
    have : Ideal.span {d} ≤ J * P.asIdeal := hK ▸ Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self d)
  obtain ⟨s, hsK, hsP⟩ := SetLike.not_le_iff_exists.mp hKP
  refine ⟨d, hdJ, hd0, s, hsP, ?_⟩
  intro y hy
  have hm : s * y ∈ Ideal.span {d} := by
    rw [hK, mul_comm s y]; exact Ideal.mul_mem_mul hy hsK
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨o, ho.symm⟩

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (J : Ideal (NumberField.RingOfIntegers E)), J ≠ ⊥ →
    ∃ d ∈ J, d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∃ s ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal P, ∀ y ∈ J,
        ∃ (o : NumberField.RingOfIntegers E), s * y = o * d := by
  intro E _ _ P J hJ
  exact local_gen P J hJ

end GlobalTheory.LocalGenerators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MainTheorem
section
namespace GlobalTheory.DenominatorTheorem

open NumberField

theorem main_theorem : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (G : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑G : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E),
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ G := by
  intro E _ _ n G hG y
  have hy : y ∈ Submodule.span E (G : Set (Fin n → E)) := hG ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using G.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine G.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact G.smul_mem d hcx
    · rw [mul_smul]; exact G.smul_mem c hdz
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    simp only at hpq
    refine ⟨(q : RingOfIntegers E) * c, mul_ne_zero (nonZeroDivisors.ne_zero q.2) hc, ?_⟩
    have key : ((q : RingOfIntegers E) * c) • (a • x) = p • (c • x) := by
      rw [← algebraMap_smul E ((q : RingOfIntegers E) * c) (a • x), smul_smul,
        ← algebraMap_smul E p (c • x), ← algebraMap_smul E c x, smul_smul, map_mul,
        mul_comm (algebraMap _ E (q : RingOfIntegers E)), mul_assoc, mul_comm _ a, hpq, mul_comm]
    rw [key]
    exact G.smul_mem p hcx

end GlobalTheory.DenominatorTheorem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffIdempotentOfOrthogonality
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_isometricRep_inv {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (g : G) (u v : H) : ⟪u, σ g⁻¹ v⟫_ℂ = ⟪σ g u, v⟫_ℂ := by
  have hv : σ g (σ g⁻¹ v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  have hf : ∀ x, f x = σ g x := fun _ => rfl
  calc ⟪u, σ g⁻¹ v⟫_ℂ = ⟪f u, f (σ g⁻¹ v)⟫_ℂ := (f.inner_map_map _ _).symm
    _ = ⟪σ g u, v⟫_ℂ := by rw [hf, hf, hv]

theorem matrixCoeff_idempotent_of_orthogonality : ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), 0 < d → (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ v w v' w' : H, ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) → ∀ w : H, ‖w‖ = 1 → (∀ g : G, star ((d : ℂ) * star ⟪w, σ g⁻¹ w⟫_ℂ) = (d : ℂ) * star ⟪w, σ g w⟫_ℂ) ∧ (∀ x y : G, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ)) ∧ (∀ u u' : H, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) ∧ ∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0 := by
  intro G _ _ μ H _ _ _ σ d hd hσ hS w hw
  have adj : ∀ (g : G) (a b : H), ⟪a, σ g⁻¹ b⟫_ℂ = ⟪σ g a, b⟫_ℂ :=
    fun g a b => inner_isometricRep_inv σ hσ g a b
  have hc : ∀ a b : H, star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := fun a b => by
    rw [← starRingEnd_apply, inner_conj_symm]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdc : star (d : ℂ) = d := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    rw [star_mul', star_star, hdc, adj, hc]
  · intro x y
    have key : ∀ g : G, star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ y w, σ g (σ x w)⟫_ℂ := by
      intro g
      rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
        adj, adj, hc]
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ
        = ∫ g, ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; rw [key]; ring
      _ = ((d : ℂ) * d) * (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ / d) := by
          rw [integral_const_mul, hS]
      _ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ) := by
          rw [hc]; field_simp
  · intro u u'
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ
        = ∫ g, (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; ring
      _ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ := by
          rw [integral_const_mul, hS]; field_simp
  · intro y hy
    have h0 := hS w y w y
    simp only [hy, zero_mul, integral_zero] at h0
    have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    rw [hww, one_mul] at h0
    have hyy : ⟪y, y⟫_ℂ = 0 := (div_eq_zero_iff.mp h0.symm).resolve_right hd0
    exact inner_self_eq_zero.mp hyy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetIwasawaSliceOfTransversal
section
open MeasureTheory

namespace GlobalTheory

theorem exists_measurableSet_slice_of_transversal
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G)
    (hN : MeasurableSet (N : Set G)) (hM : MeasurableSet (M : Set G))
    (hK : MeasurableSet (K : Set G)) (hσ : Measurable σ)
    (h1 : ∀ x, σ x * x⁻¹ ∈ K ⊓ M) (h2 : ∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x)
    (h3 : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (h4 : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1)
    (DN DM : Set G) (hDN : MeasurableSet DN) (hDM : MeasurableSet DM) :
    ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K,
      (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  have uniq : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, σ k = k → ∀ u' ∈ N, ∀ m' ∈ M, ∀ k' ∈ K, σ k' = k' →
      u * m * k = u' * m' * k' → u = u' ∧ m = m' ∧ k = k' := by
    intro u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    have e : k = m⁻¹ * u⁻¹ * (u' * m' * k') := by rw [← h]; group
    have e1 : (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * (m⁻¹ * m') = k * k'⁻¹ := by rw [e]; group
    have hkk : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
    have hmm : m⁻¹ * m' ∈ M := M.mul_mem (M.inv_mem hm) hm'
    have e2 := h4 _ (h3 _ (M.inv_mem hm) _ (N.mul_mem (N.inv_mem hu) hu')) _ hmm (e1 ▸ hkk)
    have huu : u = u' := by
      have : u' = u * (m * (m⁻¹ * (u⁻¹ * u') * m⁻¹⁻¹) * m⁻¹) := by group
      rw [this, e2]; group
    rw [e2, one_mul] at e1
    have e3 := h2 (k * k'⁻¹) ⟨hkk, e1 ▸ hmm⟩ k'
    rw [inv_mul_cancel_right, hs, hs'] at e3
    subst huu e3
    exact ⟨rfl, mul_left_cancel (mul_right_cancel h), rfl⟩
  let X : Set (G × G × G) := (DN ∩ N) ×ˢ ((DM ∩ M) ×ˢ ((K : Set G) ∩ {k | σ k = k}))
  have hX : MeasurableSet X :=
    (hDN.inter hN).prod ((hDM.inter hM).prod
      (hK.inter (measurableSet_eq_fun hσ measurable_id)))
  let f : G × G × G → G := fun p => p.1 * p.2.1 * p.2.2
  have hf : Continuous f := by fun_prop
  have hinj : Set.InjOn f X := by
    rintro ⟨u, m, k⟩ ⟨⟨_, hu⟩, ⟨_, hm⟩, hk, hs⟩ ⟨u', m', k'⟩ ⟨⟨_, hu'⟩, ⟨_, hm'⟩, hk', hs'⟩ h
    obtain ⟨a, b, c⟩ := uniq u hu m hm k hk hs u' hu' m' hm' k' hk' hs' h
    rw [a, b, c]
  refine ⟨f '' X, hX.image_of_continuousOn_injOn hf.continuousOn hinj, ?_⟩
  intro u hu m hm k hk
  have hl := h1 k
  have hl' : k * (σ k)⁻¹ ∈ K ⊓ M := by
    have := (K ⊓ M).inv_mem hl
    simpa using this
  have hσK : σ k ∈ K := by
    have := K.mul_mem hl.1 hk
    simpa using this
  have hσσ : σ (σ k) = σ k := by
    have := h2 _ hl k
    simpa using this
  have hm2 : m * (k * (σ k)⁻¹) ∈ M := M.mul_mem hm hl'.2
  have e : u * m * k = u * (m * (k * (σ k)⁻¹)) * σ k := by group
  constructor
  · rintro ⟨⟨u', m', k'⟩, ⟨⟨hdu, hu'⟩, ⟨hdm, hm'⟩, hk', hs'⟩, h⟩
    obtain ⟨a, b, _⟩ := uniq u hu _ hm2 _ hσK hσσ u' hu' m' hm' k' hk' hs' (e.symm.trans h.symm)
    rw [b, a]
    exact ⟨hdu, hdm⟩
  · rintro ⟨hdu, hdm⟩
    exact ⟨(u, m * (k * (σ k)⁻¹), σ k), ⟨⟨hdu, hu⟩, ⟨hdm, hm2⟩, hσK, hσσ⟩, e.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowApplyEqZeroOfStrictUpper
section
namespace GlobalTheory.StrictUpperNilpotentFlagMeasures

theorem pow_apply_eq_zero_of_strictUpper {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ}
    (hX : ∀ i j : Fin m, (j : ℕ) ≤ (i : ℕ) → X i j = 0) (n : ℕ) :
    ∀ i j : Fin m, (j : ℕ) < (i : ℕ) + n → (X ^ n) i j = 0 := by
  induction n with
  | zero =>
    intro i j h
    rw [pow_zero]
    apply Matrix.one_apply_ne
    rintro rfl
    omega
  | succ n ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < (i : ℕ) + n
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]

end GlobalTheory.StrictUpperNilpotentFlagMeasures
end

