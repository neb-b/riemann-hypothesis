module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAdditive
section
namespace GlobalTheory.PMonE

theorem window_additive (q : ℝ) (hq : 2 ≤ q) (r : ℤ) (α f : ℤ → ℝ) (hα : Antitone α)
    (hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * (q ^ (r - J) - 1)) :
    (∀ J, J ≤ r → f J + α J ≤ f r + α r) ∧
    (∀ J, r + 1 ≤ J → f J - α J / 2 ≤ f r - α (r + 1) / 2) := by
  have hd : ∀ J, 0 ≤ α J - α (J + 1) := fun J => sub_nonneg.2 (hα (by omega))
  have hq1 : (1 : ℝ) ≤ q := by linarith
  constructor
  · intro J hJ
    induction J, hJ using Int.leInductionDown with
    | base => exact le_rfl
    | pred n hn ih =>
      have h1 := hf (n - 1)
      have h2 := hd (n - 1)
      rw [sub_add_cancel] at h1 h2
      have h3 : q ^ (1 : ℤ) ≤ q ^ (r - (n - 1)) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_one] at h3
      nlinarith [mul_nonneg h2 (show 0 ≤ q ^ (r - (n - 1)) - 2 by linarith)]
  · intro J hJ
    induction J, hJ using Int.leInduction with
    | base =>
      have h1 := hf r
      rw [sub_self, zpow_zero, sub_self, mul_zero] at h1
      linarith
    | succ n hn ih =>
      have h1 := hf n
      have h2 := hd n
      have h3 : q ^ (r - n) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_neg_one] at h3
      have h4 : q⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
      nlinarith [mul_nonneg h2 (show 0 ≤ 2⁻¹ - q ^ (r - n) by linarith)]

theorem window_ineq : ∀ (p h : ℕ), 1 < p → 0 < h → ∀ a ρ : ℤ → ℝ, (∀ J, 0 < a J) → (∀ J, 0 < ρ J) → Antitone a → a 0 < p * a ((h : ℤ) - 1) → (∀ J, a (J + h) = a J / p) → (∀ J, ρ (J + h) = ρ J ^ ((p : ℝ) ^ h)⁻¹) → (∀ J, a (J + 1) * ρ (J + 1) ^ ((p : ℝ) ^ J) = a J * ρ J ^ ((p : ℝ) ^ J)) → ∀ r : ℕ, r < h → ∀ J : ℤ, a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) ∧ (J < 0 → a J * ρ J ^ ((p : ℝ) ^ r) < a r * ρ r ^ ((p : ℝ) ^ r)) ∧ (J ≤ -(h : ℤ) → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) ∧ (3 * (h : ℤ) ≤ J → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) := by
  intro p h hp hh a ρ ha hρ hanti hlt hper _ hrel r hr J
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set α : ℤ → ℝ := fun J => Real.log (a J) with hαdef
  set f : ℤ → ℝ := fun J => Real.log (a J * ρ J ^ ((p : ℝ) ^ r)) with hfdef
  have hα : Antitone α := fun i j hij => Real.log_le_log (ha j) (hanti hij)
  have hpos : ∀ J, 0 < a J * ρ J ^ ((p : ℝ) ^ r) := fun J =>
    mul_pos (ha J) (Real.rpow_pos_of_pos (hρ J) _)
  have hlog : ∀ (J : ℤ) (e : ℝ), Real.log (a J * ρ J ^ e) = α J + e * Real.log (ρ J) := by
    intro J e
    rw [Real.log_mul (ha J).ne' (Real.rpow_pos_of_pos (hρ J) _).ne', Real.log_rpow (hρ J)]
  have hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * ((p : ℝ) ^ ((r : ℤ) - J) - 1) := by
    intro J
    have h1 := congrArg Real.log (hrel J)
    rw [hlog, hlog] at h1
    have h2 : (p : ℝ) ^ r = (p : ℝ) ^ ((r : ℤ) - J) * (p : ℝ) ^ J := by
      rw [← zpow_add₀ hp0.ne', sub_add_cancel, zpow_natCast]
    simp only [hfdef, hlog]
    rw [h2]
    linear_combination (p : ℝ) ^ ((r : ℤ) - J) * h1
  obtain ⟨hL, hR⟩ := window_additive p hp2 r α f hα hf
  have hαper : ∀ J, α (J + h) = α J - Real.log p := by
    intro J
    simp only [hαdef]
    rw [hper, Real.log_div (ha J).ne' hp0.ne']
  have hdiv : f J ≤ f r - Real.log p →
      a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p := by
    intro H
    rw [← Real.log_le_log_iff (hpos J) (div_pos (hpos r) hp0),
      Real.log_div (hpos r).ne' hp0.ne']
    exact H
  have hr0 : α r ≤ α 0 := hα (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.log_le_log_iff (hpos J) (hpos r)]
    change f J ≤ f r
    rcases le_or_gt J r with hJ | hJ
    · have := hL J hJ
      have := hα hJ
      linarith
    · have := hR J hJ
      have := hα (show (r : ℤ) + 1 ≤ J from hJ)
      linarith
  · intro hJ
    rw [← Real.log_lt_log_iff (hpos J) (hpos r)]
    change f J < f r
    have h1 := hL J (by omega)
    have h2 : α (-1) ≤ α J := hα (by omega)
    have h3 : α 0 < α (-1) := by
      apply Real.log_lt_log (ha 0)
      have h4 := hlt
      have h5 := hper (-1)
      rw [show (-1 : ℤ) + h = (h : ℤ) - 1 by ring] at h5
      rw [h5, mul_div_cancel₀ _ hp0.ne'] at h4
      exact h4
    linarith
  · intro hJ
    apply hdiv
    have h1 := hL J (by omega)
    have h2 : α (-h) ≤ α J := hα hJ
    have h3 := hαper (-h)
    rw [neg_add_cancel] at h3
    linarith
  · intro hJ
    apply hdiv
    have h1 := hR J (by omega)
    have h2 : α J ≤ α (h + h + h) := hα (by omega)
    have h3 := hαper (h + h)
    have h4 := hαper h
    have h5 : α h ≤ α (r + 1) := hα (by omega)
    linarith

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittMatrixCoeffMemOfFrobenius
section
open scoped PowerSeries Pointwise

namespace GlobalTheory

namespace WittIntegrality

open WittVector

variable {C : Type} [Field C] (A : ValuationSubring C)

lemma mem_of_pow_mem {c : C} {k : ℕ} (hk : 1 ≤ k) (h : c ^ k ∈ A) : c ∈ A := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases A.mem_or_inv_mem c with hc | hc
  · exact hc
  · by_cases h0 : c = 0
    · rw [h0]; exact A.zero_mem
    · have e : c = c ^ (m + 1) * c⁻¹ ^ m := by
        rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, mul_one]
      rw [e]; exact mul_mem h (pow_mem hc _)

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def S : Subring (WittVector p C) := (WittVector.map (p := p) A.subtype).range

variable {p}

lemma mem_S (x : WittVector p C) : x ∈ S A p ↔ ∀ k, x.coeff k ∈ A := by
  constructor
  · rintro ⟨y, rfl⟩ k
    rw [WittVector.map_coeff]
    exact (y.coeff k).2
  · intro h
    refine ⟨WittVector.mk p fun k => ⟨x.coeff k, h k⟩, ?_⟩
    ext k
    rw [WittVector.map_coeff]
    rfl

lemma teich_mem {c : C} (hc : c ∈ A) : teichmuller p c ∈ S A p := by
  rw [mem_S]
  intro k
  cases k with
  | zero => rwa [teichmuller_coeff_zero]
  | succ k => rw [teichmuller_coeff_pos p c _ (Nat.succ_pos k)]; exact A.zero_mem

variable [CharP C p]

lemma frob_mem {x : WittVector p C} (hx : x ∈ S A p) : frobenius x ∈ S A p := by
  rw [mem_S] at hx ⊢
  intro k
  rw [coeff_frobenius_charP]
  exact pow_mem (hx k) _

lemma mem_of_mul_p_mem {x : WittVector p C} (hx : x * (p : WittVector p C) ∈ S A p) :
    x ∈ S A p := by
  rw [mem_S] at hx ⊢
  intro k
  have := hx (k + 1)
  rw [mul_charP_coeff_succ] at this
  exact mem_of_pow_mem A hp.out.one_lt.le this

variable [PerfectRing C p]

noncomputable def tail (x : WittVector p C) : WittVector p C :=
  WittVector.mk p fun k => (frobeniusEquiv C p).symm (x.coeff (k + 1))

lemma tail_coeff (x : WittVector p C) (k : ℕ) : x.coeff (k + 1) = (tail x).coeff k ^ p := by
  simp only [tail, WittVector.coeff_mk, frobeniusEquiv_symm_pow_p]

lemma decomp (x : WittVector p C) : x = teichmuller p (x.coeff 0) + tail x * p := by
  ext k
  rw [coeff_add_of_disjoint]
  · cases k with
    | zero => rw [teichmuller_coeff_zero, mul_charP_coeff_zero, add_zero]
    | succ k =>
      rw [teichmuller_coeff_pos p _ _ (Nat.succ_pos k), mul_charP_coeff_succ, zero_add, tail_coeff]
  · intro k
    cases k with
    | zero => exact Or.inr (mul_charP_coeff_zero _)
    | succ k => exact Or.inl (teichmuller_coeff_pos p _ _ (Nat.succ_pos k))

lemma key0 {n : Type} [Fintype n] (Y Z B : Matrix n n (WittVector p C))
    (hY : ∀ i j, Y i j ∈ S A p) (hB : ∀ i j, B i j ∈ S A p)
    (h : ∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) :
    ∀ i j, (Z i j).coeff 0 ∈ A := by
  classical
  have he : ∀ i j, (Z i j).coeff 0 ^ p =
      ∑ a, (Y i a).coeff 0 * (Z a j).coeff 0 + (B i j).coeff 0 := by
    intro i j
    have := congrArg (WittVector.constantCoeff (p := p) (R := C)) (h i j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_mul, WittVector.constantCoeff_apply,
      coeff_frobenius_charP] at this
    exact this
  by_contra hne
  push_neg at hne
  obtain ⟨i0, j0, hij⟩ := hne
  obtain ⟨⟨i1, j1⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n))
    (fun q => A.valuation ((Z q.1 q.2).coeff 0)) ⟨(i0, j0), Finset.mem_univ _⟩
  set z1 := (Z i1 j1).coeff 0 with hz1
  have h1 : 1 < A.valuation z1 := by
    have a := hmax (i0, j0) (Finset.mem_univ _)
    have b : ¬ A.valuation ((Z i0 j0).coeff 0) ≤ 1 := by rwa [A.valuation_le_one_iff]
    exact lt_of_lt_of_le (not_le.mp b) a
  have hz1A : z1 ∉ A := by
    rw [← A.valuation_le_one_iff]; exact not_le.mpr h1
  have hz0 : z1 ≠ 0 := fun e => hz1A (e ▸ A.zero_mem)
  have hle : A.valuation (z1 ^ p) ≤ A.valuation z1 := by
    rw [hz1, he i1 j1]
    refine Valuation.map_add_le _ ?_ ?_
    · refine Valuation.map_sum_le _ fun a _ => ?_
      rw [map_mul]
      calc A.valuation ((Y i1 a).coeff 0) * A.valuation ((Z a j1).coeff 0)
          ≤ 1 * A.valuation ((Z a j1).coeff 0) :=
            by gcongr; exact (A.valuation_le_one_iff _).2 ((mem_S A _).1 (hY i1 a) 0)
        _ ≤ A.valuation z1 := by rw [one_mul]; exact hmax (a, j1) (Finset.mem_univ _)
    · exact ((A.valuation_le_one_iff _).2 ((mem_S A _).1 (hB i1 j1) 0)).trans h1.le
  have hpm : z1 ^ (p - 1) ∈ A := by
    rw [← A.valuation_le_one_iff]
    have e : z1 ^ (p - 1) = z1 ^ p * z1⁻¹ := by
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    rw [e, map_mul]
    calc A.valuation (z1 ^ p) * A.valuation z1⁻¹ ≤ A.valuation z1 * A.valuation z1⁻¹ :=
          by gcongr
      _ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
  exact hz1A (mem_of_pow_mem A (by have := hp.out.two_le; omega) hpm)

lemma key {n : Type} [Fintype n] (Y : Matrix n n (WittVector p C)) (hY : ∀ i j, Y i j ∈ S A p) :
    ∀ (k : ℕ) (Z B : Matrix n n (WittVector p C)), (∀ i j, B i j ∈ S A p) →
    (∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) →
    ∀ i j, (Z i j).coeff k ∈ A := by
  intro k
  induction k with
  | zero => exact fun Z B hB h => key0 A Y Z B hY hB h
  | succ k ih =>
    intro Z B hB h
    have h0 := key0 A Y Z B hY hB h
    let U : Matrix n n (WittVector p C) := fun i j => tail (Z i j)
    let D : Matrix n n (WittVector p C) :=
      fun i j => frobenius (U i j) - ∑ a, Y i a * U a j
    have hD : ∀ i j, D i j * p = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0) + B i j
        - frobenius (teichmuller p ((Z i j).coeff 0)) := by
      intro i j
      have e1 : frobenius (Z i j) = frobenius (teichmuller p ((Z i j).coeff 0))
          + frobenius (U i j) * p := by
        conv_lhs => rw [decomp (Z i j)]
        rw [map_add (f := _), map_mul, map_natCast]
      have e2 : ∑ a, Y i a * Z a j = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0)
          + (∑ a, Y i a * U a j) * p := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [decomp (Z a j)]
        ring
      have e4 := h i j
      rw [e1, e2] at e4
      simp only [D]
      linear_combination e4
    have hDm : ∀ i j, D i j ∈ S A p := by
      intro i j
      refine mem_of_mul_p_mem A ?_
      rw [hD]
      exact Subring.sub_mem _ (Subring.add_mem _ (Subring.sum_mem _ fun a _ =>
        Subring.mul_mem _ (hY i a) (teich_mem A (h0 a j))) (hB i j))
        (frob_mem A (teich_mem A (h0 i j)))
    have hU := ih U D hDm (fun i j => by simp only [D]; ring)
    intro i j
    rw [tail_coeff]
    exact pow_mem (hU i j) _

end WittIntegrality

open WittIntegrality in
theorem witt_matrix_coeff_mem_of_frobenius : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [CharP C p] [PerfectRing C p] (A : ValuationSubring C) {n : Type} [Fintype n] (Z : Matrix n n (WittVector p C)) (Y : Matrix n n (WittVector p A)), (Z.map WittVector.frobenius = Y.map (WittVector.map A.subtype) * Z ∨ Z.map WittVector.frobenius = Z * Y.map (WittVector.map A.subtype)) → ∀ i j m, (Z i j).coeff m ∈ A := by
  intro p _ C _ _ _ A n _ Z Y h i j m
  rcases h with h | h
  · refine key A (Y.map (WittVector.map A.subtype)) (fun i j => ⟨Y i j, rfl⟩) m Z 0
      (fun _ _ => Subring.zero_mem _) ?_ i j
    intro i j
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this, Matrix.zero_apply, add_zero]
  · refine key A (Y.map (WittVector.map A.subtype)).transpose (fun i j => ⟨Y j i, rfl⟩) m
      Z.transpose 0 (fun _ _ => Subring.zero_mem _) ?_ j i
    intro i j
    have := congrFun (congrFun h j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [Matrix.transpose_apply, this, Matrix.zero_apply, add_zero]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorDvdOfSaturatedIdeal
section
namespace GlobalTheory

open WittVector

theorem wittVector_coeff_pow_mul_eq_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] : ∀ (m : ℕ) (t : WittVector l R) (j : ℕ), j < m →
      ((l : WittVector l R) ^ m * t).coeff j = 0 := by
  intro m
  induction m with
  | zero => intro t j hj; omega
  | succ m ih =>
    intro t j hj
    have h : (l : WittVector l R) ^ (m + 1) * t
        = verschiebung (frobenius ((l : WittVector l R) ^ m * t)) := by
      rw [verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact verschiebung_coeff_zero _
    | succ j =>
      rw [verschiebung_coeff_succ, coeff_frobenius_charP, ih t j (by omega)]
      exact zero_pow hl.out.ne_zero

theorem wittVector_coeff_add_pow_mul {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] (x t : WittVector l R) (m j : ℕ) (hj : j < m) :
    (x + (l : WittVector l R) ^ m * t).coeff j = x.coeff j := by
  have h0 : truncate m ((l : WittVector l R) ^ m * t) = 0 := by
    ext i
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
    exact wittVector_coeff_pow_mul_eq_zero m t i i.2
  have h1 : truncate m (x + (l : WittVector l R) ^ m * t) = truncate m x := by
    rw [map_add (f := _), h0, add_zero]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨j, hj⟩ y) h1
  simpa only [WittVector.coeff_truncate] using this

theorem wittVector_dvd_of_coeff_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] [PerfectRing R l] (x : WittVector l R) (hx : x.coeff 0 = 0) :
    ∃ y, x = (l : WittVector l R) * y := by
  by_cases h : x = 0
  · exact ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨m, b, hb, hxb⟩ := exists_eq_pow_p_mul x h
  cases m with
  | zero => rw [pow_zero, one_mul] at hxb; exact absurd (hxb ▸ hx) hb
  | succ m => exact ⟨(l : WittVector l R) ^ m * b, by rw [hxb]; ring⟩

theorem wittVector_dvd_of_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J →
    (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) →
    ∀ a ∈ J, μ ∣ a := by
  intro l _ R _ _ _ J μ hμ hsat hdiv a ha

  have step : ∀ d : J, ∃ c : WittVector l R, ∃ d' : J,
      (d : WittVector l R) = μ * c + (l : WittVector l R) * d' := by
    intro d
    obtain ⟨c₀, hc₀⟩ := hdiv d d.2
    set x := (d : WittVector l R) - μ * teichmuller l c₀ with hxdef
    have hx0 : x.coeff 0 = 0 := by
      have e : (d : WittVector l R) = x + μ * teichmuller l c₀ := by rw [hxdef]; ring
      have h2 := congrArg (fun y : WittVector l R => y.coeff 0) e
      simp only [add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero] at h2
      rw [hc₀] at h2
      linear_combination -h2
    obtain ⟨y, hy⟩ := wittVector_dvd_of_coeff_zero x hx0
    have hyJ : y ∈ J := by
      apply hsat
      rw [← hy, hxdef]
      exact J.sub_mem d.2 (J.mul_mem_right _ hμ)
    refine ⟨teichmuller l c₀, ⟨y, hyJ⟩, ?_⟩
    rw [← hy, hxdef]; ring
  choose cf df hcd using step
  let seq : ℕ → J := fun n => Nat.rec ⟨a, ha⟩ (fun _ d => df d) n
  let s : ℕ → WittVector l R := fun n =>
    ∑ k ∈ Finset.range n, (l : WittVector l R) ^ k * cf (seq k)
  have hs_succ : ∀ n, s (n + 1) = s n + (l : WittVector l R) ^ n * cf (seq n) := by
    intro n; simp only [s, Finset.sum_range_succ]
  have hmain : ∀ n, a = μ * s n + (l : WittVector l R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : (seq (n + 1)).1 = (df (seq n)).1 := rfl
      rw [hs_succ, e]
      have := hcd (seq n)
      rw [ih, this]; ring
  have hstab : ∀ n m, n ≤ m → ∃ t, s m = s n + (l : WittVector l R) ^ n * t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨0, by ring⟩
    | succ m hnm ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (l : WittVector l R) ^ (m - n) * cf (seq m), ?_⟩
      rw [hs_succ, ht, mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]; ring
  let c : WittVector l R := WittVector.mk l (fun k => (s (k + 1)).coeff k)
  refine ⟨c, ?_⟩
  ext k

  have htc : truncate (k + 1) c = truncate (k + 1) (s (k + 1)) := by
    ext i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate]
    obtain ⟨t, ht⟩ := hstab ((i : ℕ) + 1) (k + 1) (by omega)
    show (s ((i : ℕ) + 1)).coeff i = _
    rw [ht, wittVector_coeff_add_pow_mul _ _ _ _ (by omega)]
  have hta : truncate (k + 1) a = truncate (k + 1) (μ * c) := by
    have e := hmain (k + 1)
    have h0 : truncate (k + 1) ((l : WittVector l R) ^ (k + 1) * (seq (k + 1)).1)
        = 0 := by
      ext i
      rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      exact wittVector_coeff_pow_mul_eq_zero _ _ i i.2
    conv_lhs => rw [e]
    rw [map_add (f := _), h0, add_zero, map_mul, map_mul, htc]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨k, Nat.lt_succ_self k⟩ y) hta
  simpa only [WittVector.coeff_truncate] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqMapOfCoeffZero
section
open scoped NNReal

namespace GlobalTheory.WittMapUniq

open WittVector

theorem exists_pow_pow_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] : ∀ (n : ℕ) (r : R), ∃ s : R, s ^ l ^ n = r := by
  intro n
  induction n with
  | zero => intro r; exact ⟨r, by simp⟩
  | succ n ih =>
    intro r
    obtain ⟨t, ht⟩ := surjective_frobenius R l r
    obtain ⟨s, hs⟩ := ih t
    refine ⟨s, ?_⟩
    rw [pow_succ, pow_mul, hs, ← ht, frobenius_def]

theorem eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l]
    (F : WittVector l R →+* WittVector l O) (ψ : R →+* O),
    (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  intro l _ R O _ _ _ _ _ _ F ψ hF
  have hdiff : ∀ x : WittVector l R, (l : WittVector l O) ∣ F x - WittVector.map ψ x := by
    intro x
    rw [← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]
    have h := (WittVector.constantCoeff : WittVector l O →+* O).map_sub (F x) (WittVector.map ψ x)
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hF, WittVector.map_coeff, sub_self]
  have hteich : ∀ (n : ℕ) (r : R),
      (l : WittVector l O) ^ (n + 1) ∣ F (teichmuller l r) - teichmuller l (ψ r) := by
    intro n r
    obtain ⟨s, rfl⟩ := exists_pow_pow_eq l R n r
    have h1 : (l : WittVector l O) ∣ F (teichmuller l s) - teichmuller l (ψ s) := by
      have := hdiff (teichmuller l s)
      rwa [WittVector.map_teichmuller] at this
    have h2 := dvd_sub_pow_of_dvd_sub h1 n
    rw [map_pow, map_pow, map_pow, map_pow]
    exact h2
  ext x m
  have key : ∀ n : ℕ, F x - WittVector.map ψ x ∈ Ideal.span {((l : WittVector l O) ^ n)} := by
    intro n
    let I : Ideal (WittVector l O) := Ideal.span {((l : WittVector l O) ^ n)}
    have hfg : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp (WittVector.map ψ) := by
      refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ ?_
      · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      · intro r
        simp only [RingHom.comp_apply, WittVector.map_teichmuller]
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact dvd_trans (pow_dvd_pow _ n.le_succ) (hteich n r)
    have := congrArg (fun f => f x) hfg
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.mp this
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).mp (key (m + 1))
  have h' := (le_coeff_eq_iff_le_sub_coeff_eq_zero (n := m + 1)).mpr h
  exact h' m (Nat.lt_succ_self m)

end GlobalTheory.WittMapUniq
end

