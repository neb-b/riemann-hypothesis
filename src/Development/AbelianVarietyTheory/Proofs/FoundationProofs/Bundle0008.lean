module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FromBlocksMulInv
section
noncomputable section

open Matrix

namespace GlobalTheory.SingleBlock

variable {k : Type} [Field k] {r t : ℕ}

theorem fromBlocks_mul_inv (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) *
      fromBlocks ((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        (-(((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * b *
          ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))) 0
        ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = 1 := by
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, neg_add_cancel, neg_zero, fromBlocks_one]

def blockUnit (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    GL (Fin r ⊕ Fin t) k :=
  ⟨_, _, fromBlocks_mul_inv p b d, mul_eq_one_comm.1 (fromBlocks_mul_inv p b d)⟩

def blockPar (t : ℕ) (Q : Subgroup (GL (Fin r) k)) : Subgroup (GL (Fin r ⊕ Fin t) k) where
  carrier := {h | ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
    (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
      fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k)}
  one_mem' := ⟨1, Q.one_mem, 0, 1, by simp⟩
  mul_mem' := by
    rintro x y ⟨p, hp, b, d, e⟩ ⟨p', hp', b', d', e'⟩
    refine ⟨p * p', Q.mul_mem hp hp', (p : Matrix (Fin r) (Fin r) k) * b' +
      b * (d' : Matrix (Fin t) (Fin t) k), d * d', ?_⟩
    rw [Units.val_mul, e, e', fromBlocks_multiply]
    simp
  inv_mem' := by
    rintro x ⟨p, hp, b, d, e⟩
    exact ⟨p⁻¹, Q.inv_mem hp, _, d⁻¹,
      Units.inv_eq_of_mul_eq_one_right (e ▸ fromBlocks_mul_inv p b d)⟩

private theorem mem_blockPar_iff' (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔ ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) :=
  Iff.rfl

theorem mem_blockPar_iff (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔
      (∃ p ∈ Q, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₁ =
        (p : Matrix (Fin r) (Fin r) k)) ∧
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₁ = 0 := by
  rw [mem_blockPar_iff']
  constructor
  · rintro ⟨p, hp, b, d, e⟩
    exact ⟨⟨p, hp, by rw [e, toBlocks_fromBlocks₁₁]⟩, by rw [e, toBlocks_fromBlocks₂₁]⟩
  · rintro ⟨⟨p, hp, h11⟩, h21⟩
    have hM : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k)
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₂ 0
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂ := by
      rw [← h11, ← h21, fromBlocks_toBlocks]
    have hdet : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂.det ≠ 0 := by
      intro h0
      have hu := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h)).ne_zero
      rw [hM, det_fromBlocks_zero₂₁, h0, mul_zero] at hu
      exact hu rfl
    exact ⟨p, hp, _, Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), hM⟩

theorem card_blockPar (Q : Subgroup (GL (Fin r) k)) :
    Nat.card (blockPar t Q) =
      Nat.card Q * (Nat.card k ^ (r * t) * Nat.card (GL (Fin t) k)) := by
  let φ : Q × (Matrix (Fin r) (Fin t) k × GL (Fin t) k) → blockPar t Q := fun x =>
    ⟨blockUnit x.1.1 x.2.1 x.2.2, (mem_blockPar_iff' Q _).mpr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨p, hp⟩, b, d⟩ ⟨⟨p', hp'⟩, b', d'⟩ h
      have h1 : fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) =
          fromBlocks (p' : Matrix (Fin r) (Fin r) k) b' 0 (d' : Matrix (Fin t) (Fin t) k) :=
        congrArg (fun z : blockPar t Q =>
          ((z : GL (Fin r ⊕ Fin t) k) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k)) h
      obtain ⟨e1, e2, -, e4⟩ := Matrix.fromBlocks_inj.mp h1
      have hp_eq : p = p' := Units.ext e1
      have hd_eq : d = d' := Units.ext e4
      subst hp_eq hd_eq e2
      rfl
    · rintro ⟨h, hh⟩
      obtain ⟨p, hp, b, d, e⟩ := (mem_blockPar_iff' Q h).mp hh
      exact ⟨(⟨p, hp⟩, b, d), Subtype.ext (Units.ext e.symm)⟩
  have hM : Nat.card (Matrix (Fin r) (Fin t) k) = Nat.card k ^ (r * t) := by
    show Nat.card (Fin r → Fin t → k) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card (α := Fin t), Nat.card_eq_fintype_card (α := Fin r),
      Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm t r]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_prod, hM]

theorem card_GL_real [Finite k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Nat.card k : ℝ) ^ (n * n) *
      ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  classical
  have := Fintype.ofFinite k
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ)) n]
  have step : ∀ i ∈ Finset.range n, ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ) =
      (Nat.card k : ℝ) ^ n * (1 - ((Nat.card k : ℝ) ^ (n - i))⁻¹) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) hin.le)]
    push_cast
    have hsplit : (Nat.card k : ℝ) ^ n = (Nat.card k : ℝ) ^ i * (Nat.card k : ℝ) ^ (n - i) := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : (Nat.card k : ℝ) ^ n * ((Nat.card k : ℝ) ^ (n - i))⁻¹ = (Nat.card k : ℝ) ^ i := by
      rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq.ne'), mul_one]
    rw [mul_sub, mul_one, h2]
  rw [Finset.prod_congr rfl step, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul]
  congr 1
  apply Finset.prod_nbij' (fun i => n - i) (fun i => n - i)
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Ioc] at ha
    omega
  · intro a _
    rfl

theorem card_GL_sum : Nat.card (GL (Fin r ⊕ Fin t) k) = Nat.card (GL (Fin (r + t)) k) :=
  Nat.card_congr
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toMulEquiv).toEquiv

private theorem mul_inv_eq_of_mul_eq_mul {I A a b c P P' : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hP : P ≠ 0) (h : I * (A * (b * (c * P))) = a * b * b * c * (P * P')) :
    I * (A * a⁻¹ * b⁻¹) = P' := by
  have key : I * A = a * b * P' := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hb hc) hP)
    linear_combination h
  calc I * (A * a⁻¹ * b⁻¹) = (I * A) * (a⁻¹ * b⁻¹) := by ring
    _ = P' * (a * a⁻¹) * (b * b⁻¹) := by rw [key]; ring
    _ = P' := by rw [mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_one, mul_one]

theorem index_blockPar [Finite k] (Q : Subgroup (GL (Fin r) k)) :
    ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r ^ 2))⁻¹ *
      ((Nat.card k : ℝ) ^ (r * t))⁻¹) =
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  have hq' : (1 : ℝ) < Nat.card k := by exact_mod_cast hq1
  have hpos : ∀ m : ℕ, 0 < ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
    intro m
    apply Finset.prod_pos
    intro i hi
    have hi0 : i ≠ 0 := by
      simp only [Finset.mem_Ioc] at hi
      omega
    have : ((Nat.card k : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq' hi0)
    linarith
  have hidx := (blockPar t Q).index_mul_card
  rw [card_blockPar, card_GL_sum] at hidx
  have hR : ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r * t) *
      (Nat.card (GL (Fin t) k) : ℝ))) = (Nat.card (GL (Fin (r + t)) k) : ℝ) := by
    exact_mod_cast hidx
  rw [card_GL_real, card_GL_real,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (Nat.le_add_left t r)] at hR
  have he : (Nat.card k : ℝ) ^ ((r + t) * (r + t)) = (Nat.card k : ℝ) ^ (r ^ 2) *
      (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (t * t) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [he] at hR
  exact mul_inv_eq_of_mul_eq_mul (pow_pos hq _).ne' (pow_pos hq _).ne' (pow_pos hq _).ne' (hpos t).ne' hR

end GlobalTheory.SingleBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeNatCastIff
section
namespace GlobalTheory.AxSen

variable {K : Type} [Field K]

def Ge (A : ValuationSubring K) (ϖ w : K) (q : ℚ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℚ) ≤ q * b → A.valuation w ^ b ≤ A.valuation ϖ ^ a

variable {A : ValuationSubring K} {ϖ : K}

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_zero (q : ℚ) : _root_.GlobalTheory.AxSen.Ge A ϖ 0 q := by
  intro a b hb _
  rw [map_zero, zero_pow hb.ne']
  exact zero_le'

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mono {w : K} {q q' : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hq : q' ≤ q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w q' :=
  fun a b hb hab => h a b hb (hab.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg b)))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.of_le {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hw : A.valuation w' ≤ A.valuation w) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w' q :=
  fun a b hb hab => (pow_le_pow_left' hw b).trans (h a b hb hab)

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.add {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w + w') q := by
  rcases le_total (A.valuation w) (A.valuation w') with hle | hle
  · exact h'.of_le ((Valuation.map_add _ _ _).trans (max_le hle le_rfl))
  · exact h.of_le ((Valuation.map_add _ _ _).trans (max_le le_rfl hle))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.symm {x y : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) : _root_.GlobalTheory.AxSen.Ge A ϖ (y - x) q :=
  h.of_le (by rw [Valuation.map_sub_swap])

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.trans {x y z : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ (y - z) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (x - z) q := by
  have := h.add h'
  rwa [sub_add_sub_cancel] at this

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mul (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {w w' : K} {q q' : ℚ} (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q)
    (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q') :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w * w') (q + q') := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hd : 0 < q.den := q.den_pos
  have hd' : 0 < q'.den := q'.den_pos
  have h₁ := h (q.num * q'.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q]; ring))
  have h₂ := h' (q'.num * q.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q']; ring))
  have hexp : a * ((q.den * q'.den : ℕ) : ℤ) ≤ (q.num * q'.den * b + q'.num * q.den * b) := by
    have hq : ((a * ((q.den * q'.den : ℕ) : ℤ) : ℤ) : ℚ)
        ≤ ((q.num * q'.den * b + q'.num * q.den * b : ℤ) : ℚ) := by
      push_cast
      rw [← Rat.mul_den_eq_num q, ← Rat.mul_den_eq_num q']
      have hdd : (0 : ℚ) ≤ q.den * q'.den := by positivity
      calc (a : ℚ) * (q.den * q'.den) ≤ ((q + q') * b) * (q.den * q'.den) :=
            mul_le_mul_of_nonneg_right hab hdd
        _ = _ := by ring
    exact_mod_cast hq
  have key : (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
      ≤ (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by
    calc (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
        = A.valuation w ^ (q.den * q'.den * b) * A.valuation w' ^ (q.den * q'.den * b) := by
          rw [map_mul, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm b]
      _ ≤ A.valuation ϖ ^ (q.num * q'.den * b) * A.valuation ϖ ^ (q'.num * q.den * b) :=
          mul_le_mul' h₁ h₂
      _ = A.valuation ϖ ^ (q.num * q'.den * b + q'.num * q.den * b) := by
          rw [← zpow_add₀ hv]
      _ ≤ A.valuation ϖ ^ (a * ((q.den * q'.den : ℕ) : ℤ)) :=
          zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hexp
      _ = (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by rw [zpow_mul, zpow_natCast]
  exact (pow_le_pow_iff_left₀ zero_le' zero_le' (by positivity)).1 key

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.root {w : K} {q : ℚ} {N : ℕ} (hN : 0 < N)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (w ^ N) (q * N)) : _root_.GlobalTheory.AxSen.Ge A ϖ w q := by
  intro a b hb hab
  have h₁ := h (a * N) b hb (by
    push_cast
    calc (a : ℚ) * N ≤ q * b * N := mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N)
      _ = q * N * b := by ring)
  refine (pow_le_pow_iff_left₀ zero_le' zero_le' hN.ne').1 ?_
  calc (A.valuation w ^ b) ^ N = A.valuation (w ^ N) ^ b := by
        rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
    _ ≤ A.valuation ϖ ^ (a * (N : ℤ)) := h₁
    _ = (A.valuation ϖ ^ a) ^ N := by rw [zpow_mul, zpow_natCast]

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.div (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {c w : K} {q : ℚ} {e : ℕ} (hc : A.valuation ϖ ^ e ≤ A.valuation c)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (c * w) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w (q - e) := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc0 : A.valuation c ≠ 0 := by
    intro hc0
    rw [hc0] at hc
    exact pow_ne_zero e hv (le_zero_iff.1 hc)
  have h₁ := h (a + e * b) b hb (by push_cast; linarith [hab, sub_mul q (e : ℚ) b])
  rw [map_mul, mul_pow, zpow_add₀ hv] at h₁
  have h₂ : A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) ≤ A.valuation c ^ b := by
    rw [zpow_mul, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left' hc b
  refine (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 (pow_ne_zero b hc0))).1 ?_
  calc A.valuation w ^ b * A.valuation c ^ b = A.valuation c ^ b * A.valuation w ^ b := mul_comm _ _
    _ ≤ A.valuation ϖ ^ a * A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) := h₁
    _ ≤ A.valuation ϖ ^ a * A.valuation c ^ b := mul_le_mul' le_rfl h₂

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_natCast_iff (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {w : K}
    {m : ℕ} : _root_.GlobalTheory.AxSen.Ge A ϖ w m ↔ ∃ z ∈ A, w = ϖ ^ m * z := by
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  constructor
  · intro h
    have h₁ := h m 1 one_pos (by simp)
    rw [pow_one, zpow_natCast, ← map_pow] at h₁
    refine ⟨w / ϖ ^ m, ?_, by field_simp⟩
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero m h0)))).2 h₁
  · rintro ⟨z, hz, rfl⟩ a b hb hab
    have hz' : A.valuation z ≤ 1 := (ValuationSubring.valuation_le_one_iff A z).2 hz
    have hab' : a ≤ ((m * b : ℕ) : ℤ) := by
      have : (a : ℚ) ≤ ((m * b : ℕ) : ℚ) := by push_cast; exact hab
      exact_mod_cast this
    rw [map_mul, mul_pow, map_pow]
    calc (A.valuation ϖ ^ m) ^ b * A.valuation z ^ b ≤ (A.valuation ϖ ^ m) ^ b * 1 :=
          mul_le_mul' le_rfl (pow_le_one' hz' b)
      _ = A.valuation ϖ ^ ((m * b : ℕ) : ℤ) := by rw [mul_one, ← pow_mul, zpow_natCast]
      _ ≤ A.valuation ϖ ^ a := zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hab'


variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.map (h0 : ϖ ≠ 0) (f : K →+* K)
    (hf : ∀ x ∈ A, f x ∈ A) (hϖ : f ϖ = ϖ) {w : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) : _root_.GlobalTheory.AxSen.Ge A ϖ (f w) q := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h₁ := h a b hb hab
  have hpos : 0 < A.valuation ϖ ^ a := zero_lt_iff.2 (zpow_ne_zero a hv)
  rw [← div_le_one₀ hpos, ← map_pow, ← map_zpow₀, ← map_div₀,
    ValuationSubring.valuation_le_one_iff] at h₁ ⊢
  have := hf _ h₁
  rwa [map_div₀, map_pow, map_zpow₀, hϖ] at this

end GlobalTheory.AxSen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtDetOfOne
section
namespace GlobalTheory.DetDerivativeAtOne

open Equiv Finset

theorem hasDerivAt_det_of_one {n : Type} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A (0 : ℝ) = (1 : Matrix n n ℂ))
    (hd : ∀ (i j : n), HasDerivAt (fun (t : ℝ) ↦ A t i j) (A' i j) (0 : ℝ)) :
    HasDerivAt (fun (t : ℝ) ↦ Matrix.det (A t)) (Matrix.trace A') (0 : ℝ) := by
  have hfun : (fun t : ℝ ↦ Matrix.det (A t)) =
      fun t ↦ ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i :=
    funext fun t ↦ Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ : Perm n, HasDerivAt (fun t : ℝ ↦ ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 :=
    fun σ ↦ HasDerivAt.fun_finsetProd (fun i _ ↦ hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm n)))
    (fun σ _ ↦ (hσ σ).const_mul ((Perm.sign σ : ℤ) : ℂ))
  refine hsum.congr_deriv (Eq.symm ?_)
  rw [h0]
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [Matrix.trace, Perm.one_apply, Matrix.one_apply]
  · intro σ _ hσ1
    have hz : ∀ i, (∏ j ∈ univ.erase i, (1 : Matrix n n ℂ) (σ j) j) = 0 := by
      intro i
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hc
        push Not at hc
        exact hσ1 (Equiv.ext hc)
      by_cases hki : k = i
      · subst hki
        apply Finset.prod_eq_zero (i := σ k)
        · simp [hk]
        · have : σ (σ k) ≠ σ k := fun h ↦ hk (σ.injective h)
          simp [Matrix.one_apply_ne this]
      · apply Finset.prod_eq_zero (i := k)
        · simp [hki]
        · simp [Matrix.one_apply_ne hk]
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.DetDerivativeAtOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Imports
section
namespace GlobalTheory.IdealPowerMembership

open MvPolynomial

theorem main : ∀ (K L : Type) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L], ∃ (f : MvPolynomial (Fin (Module.finrank K L)) K), MvPolynomial.IsHomogeneous f (Module.finrank K L) ∧ ∀ (x : L), (Algebra.norm K : L → K) x = (MvPolynomial.eval fun (i : Fin (Module.finrank K L)) ↦ ((Module.Basis.repr (Module.finBasis K L) : L → Fin (Module.finrank K L) →₀ K) x : Fin (Module.finrank K L) → K) i : MvPolynomial (Fin (Module.finrank K L)) K → K) f := by
  intro K L _ _ _ _
  classical
  let b := Module.finBasis K L
  let P : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) (MvPolynomial (Fin (Module.finrank K L)) K) :=
    fun j k => ∑ i, X i * C (Algebra.leftMulMatrix b (b i) j k)
  have hP : ∀ j k, (P j k).IsHomogeneous 1 := by
    intro j k
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_X K i).mul (isHomogeneous_C (Fin (Module.finrank K L)) (Algebra.leftMulMatrix b (b i) j k))
  refine ⟨P.det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    apply IsHomogeneous.sum
    intro σ _
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (Module.finrank K L))) (fun i => P (σ i) i) (fun _ => 1) (fun i _ => hP (σ i) i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact h
    · rw [hs, Units.neg_smul, one_smul]; exact h.neg
  · intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j k
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    have e1 : Algebra.leftMulMatrix b x = ∑ i, b.repr x i • Algebra.leftMulMatrix b (b i) := by
      conv_lhs => rw [hx]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
    rw [e1, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, eval_mul, eval_X, eval_C, Matrix.smul_apply, smul_eq_mul]
    rfl
end GlobalTheory.IdealPowerMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsFurther
section
namespace GlobalTheory.DeterminantSimpLemma

open NumberField

theorem main {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
    {M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)} {x : Fin n → K} :
    x ∈ Submodule.span K (↑M : Set (Fin n → K)) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ M := by
  intro hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 := by
      simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • (c • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [← hab, map_mul]
      field_simp
    rw [key]
    exact M.smul_mem _ h

end GlobalTheory.DeterminantSimpLemma
end

