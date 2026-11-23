module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0475

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.RecursionIdentity
section
noncomputable section

open GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertLevi

def aTerm (q N : ℕ) (X α : ℂ) (a : ℤ) : ℂ :=
  (q : ℂ) ^ ((2 * N + 2) * a.toNat) * X ^ a.natAbs * (α ^ a * (q : ℂ) ^ (-a * ((N : ℤ) + 1)))

theorem aTerm_nat {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (k : ℕ) :
    aTerm q N X α (k : ℤ) = ((q : ℂ) ^ (N + 1) * X * α) ^ k := by
  have h : (q : ℂ) ^ (-(k : ℤ) * ((N : ℤ) + 1)) = ((q : ℂ) ^ ((N + 1) * k))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast
    ring
  have h2 : (q : ℂ) ^ ((2 * N + 2) * k) = (q : ℂ) ^ ((N + 1) * k) * (q : ℂ) ^ ((N + 1) * k) := by
    rw [← pow_add]
    congr 1
    ring
  have h3 : (q : ℂ) ^ ((N + 1) * k) ≠ 0 := pow_ne_zero _ hq
  rw [aTerm, h, Int.toNat_natCast, Int.natAbs_natCast, zpow_natCast, h2, mul_pow, mul_pow, ← pow_mul]
  field_simp

theorem aTerm_neg {q N : ℕ} {X α : ℂ} (k : ℕ) :
    aTerm q N X α (-((k : ℤ) + 1)) = ((q : ℂ) ^ (N + 1) * X / α) * ((q : ℂ) ^ (N + 1) * X / α) ^ k := by
  have h : (q : ℂ) ^ (-(-((k : ℤ) + 1)) * ((N : ℤ) + 1)) = (q : ℂ) ^ ((N + 1) * (k + 1)) := by
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  have h1 : (-((k : ℤ) + 1)).toNat = 0 := by omega
  have h2 : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
  have h3 : α ^ (-((k : ℤ) + 1)) = (α ^ (k + 1))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [aTerm, h, h1, h2, h3, ← pow_succ', div_pow, mul_pow, ← pow_mul]
  simp only [mul_zero, pow_zero, one_mul, div_eq_mul_inv]
  ring

theorem hasSum_aTerm {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (h1 : ‖(q : ℂ) ^ (N + 1) * X * α‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X / α‖ < 1) :
    HasSum (aTerm q N X α) ((1 - (q : ℂ) ^ (N + 1) * X * α)⁻¹ +
      ((q : ℂ) ^ (N + 1) * X / α) * (1 - (q : ℂ) ^ (N + 1) * X / α)⁻¹) := by
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · simp only [aTerm_nat hq]
    exact hasSum_geometric_of_norm_lt_one h1
  · simp only [aTerm_neg]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left _

theorem step : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hya hyb H hZ
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy' : ‖(q : ℂ) ^ (N + 1) * X‖ < 1 := hy ▸ hy1
  have h1 : ‖y * α‖ < 1 := by rwa [norm_mul]
  have h2 : ‖y / α‖ < 1 := by rwa [norm_div, div_eq_mul_inv]
  have hA := hasSum_aTerm (N := N) (X := X) (α := α) hq0 (hy ▸ h1) (hy ▸ h2)
  rw [← hy] at hA
  set A := aTerm q N X α with hAdef
  set B : Y → ℂ := fun b => ((q : ℂ) ^ 2 * X) ^ l b * φ₀ b with hBdef
  set w : ℤ × Y → ℂ := fun p => α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * φ₀ p.2 with hw
  set f : (ℤ × Y) × C → ℂ := fun p => X ^ ℓ p.1.1 p.1.2 p.2 *
    (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2) with hf
  have hAn : Summable fun a => ‖A a‖ := hA.summable.norm
  have hBn : Summable fun b => ‖B b‖ := hZ.summable.norm
  have hABn : Summable fun p : ℤ × Y => ‖A p.1‖ * ‖B p.2‖ :=
    hAn.mul_of_nonneg hBn (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hAB : Summable fun p : ℤ × Y => A p.1 * B p.2 :=
    Summable.of_norm (by simpa only [norm_mul] using hABn)
  have key : ∀ (X' : ℂ) (p : ℤ × Y), (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X' ^ (p.1.natAbs + l p.2) *
      (α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * φ₀ p.2) =
      aTerm q N X' α p.1 * (((q : ℂ) ^ 2 * X') ^ l p.2 * φ₀ p.2) := by
    intro X' p
    rw [aTerm]
    generalize α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) = t
    ring

  have hin : ∀ p : ℤ × Y, HasSum (fun c => f (p, c)) (jFac q N X * (A p.1 * B p.2)) := by
    intro p
    have := (H X hy' p.1 p.2).mul_right (w p)
    have e : (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2) * w p = A p.1 * B p.2 := key X p
    have e' : jFac q N X * (A p.1 * B p.2) = (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) *
        X ^ (p.1.natAbs + l p.2) * jFac q N X * w p := by
      rw [← e]
      ring
    rw [e']
    exact this

  have hX' : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, norm_norm] using hy'
  have hR : ∀ p : ℤ × Y, ∃ v : ℝ, HasSum (fun c => ‖f (p, c)‖) v ∧
      v ≤ ‖jFac q N (‖X‖ : ℝ)‖ * (‖A p.1‖ * ‖B p.2‖) := by
    intro p
    have h3 := Complex.hasSum_re (H _ hX' p.1 p.2)
    have h4 := h3.mul_right ‖w p‖
    refine ⟨((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (p.1.natAbs + l p.2) *
      jFac q N (‖X‖ : ℝ)).re * ‖w p‖, ?_, ?_⟩
    · have e : (fun c => ‖f (p, c)‖) = fun c => (((‖X‖ : ℝ) : ℂ) ^ ℓ p.1 p.2 c).re * ‖w p‖ := funext fun c => by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
        change ‖X ^ ℓ p.1 p.2 c * w p‖ = _
        rw [norm_mul, norm_pow]
      rw [e]
      exact h4
    · have e : ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2)‖ * ‖w p‖ =
          ‖A p.1‖ * ‖B p.2‖ := by
        rw [← norm_mul, ← norm_mul]
        exact congrArg norm (key X p)
      have e2 : ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (p.1.natAbs + l p.2) *
          jFac q N (‖X‖ : ℝ)‖ = ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2)‖ *
          ‖jFac q N (‖X‖ : ℝ)‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_real, norm_norm]
      refine (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)).trans (le_of_eq ?_)
      rw [e2, ← e]
      ring
  choose v hv1 hv2 using hR
  have hfs : Summable f := by
    refine Summable.of_norm ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun p => (hv1 p).summable, ?_⟩)
    have e : (fun p => ∑' c, ‖f (p, c)‖) = v := funext fun p => (hv1 p).tsum_eq
    rw [e]
    exact Summable.of_nonneg_of_le (fun p => (hv1 p).nonneg fun _ => norm_nonneg _) hv2 (hABn.mul_left _)
  have h5 := hfs.hasSum.prod_fiberwise hin
  have h6 := (hA.mul hZ hAB).mul_left (jFac q N X)
  have h7 := h5.unique h6
  have hy2 : 1 - y ^ 2 ≠ 0 := fun h => by
    have e : y ^ 2 = 1 := by linear_combination -h
    have e2 : ‖y‖ ^ 2 = 1 := by rw [← norm_pow, e, norm_one]
    have : ‖y‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hy1 two_ne_zero
    linarith
  have hd1 : 1 - y * α ≠ 0 := fun h => by
    have e : y * α = 1 := by linear_combination -h
    rw [e, norm_one] at h1
    exact lt_irrefl _ h1
  have hd2 : 1 - y / α ≠ 0 := fun h => by
    have e : y / α = 1 := by linear_combination -h
    rw [e, norm_one] at h2
    exact lt_irrefl _ h2
  have hval : (1 - X) * (1 + q * X) * ((1 - y * α)⁻¹ * (1 - y / α)⁻¹) * Z =
      jFac q N X * (((1 - y * α)⁻¹ + y / α * (1 - y / α)⁻¹) * Z) := by
    obtain ⟨t, ht⟩ : ∃ t, t = y / α := ⟨_, rfl⟩
    have htα : t * α = y := by rw [ht]; field_simp
    rw [← ht] at hd2 ⊢
    have e : (1 - y * α)⁻¹ + t * (1 - t)⁻¹ = (1 - y ^ 2) * ((1 - y * α)⁻¹ * (1 - t)⁻¹) := by
      field_simp
      linear_combination (-y) * htα
    rw [e, jFac, ← hy]
    field_simp
  rw [hval, ← h7]
  exact hfs.hasSum

end GlobalTheory.CompanionTheory.InertLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SphericalTransitiveOfLevi
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertTrans

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem conj_mem_radU {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n} (hm : m ∈ leviU σ β) (hu : u ∈ radU σ β) :
    m * u * m⁻¹ ∈ radU σ β := by
  have hA : ∀ i j, β i ≠ β j → mat m i j = 0 := hm
  have hC : ∀ i j, β i ≠ β j → mat m⁻¹ i j = 0 := inv_mem hm
  have hB : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  show ∀ i j, β j ≤ β i → mat (m * u * m⁻¹) i j = (1 : Matrix (Fin n) (Fin n) L) i j
  intro i j h
  have e : (mat m * mat u * mat m⁻¹) i j = (mat m * mat m⁻¹) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : β p = β j
    · congr 1
      rw [Matrix.mul_apply]
      calc _ = ∑ l, mat m i l * (1 : Matrix (Fin n) (Fin n) L) l p := Finset.sum_congr rfl fun l _ => by
              by_cases hl : β i = β l
              · rw [hB l p (by omega)]
              · rw [hA i l hl, zero_mul, zero_mul]
        _ = _ := by rw [← Matrix.mul_apply, Matrix.mul_one]
    · rw [hC p j hp, mul_zero, mul_zero]
  rw [mat_mul, mat_mul, e, mat_mul_inv]

theorem blk_mono {i j : Fin (N + 2)} (h : j < i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · simp at h
  · simp at h
  · simp at h
  · simp
  · simp
  · exact absurd h (not_lt.2 (Fin.le_last _))
  · simp
  · simp
  · simp

theorem isUnipU_of_radQ {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : IsUnipU u := by
  have hB : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · exact (hB i j (blk_mono h)).trans (Matrix.one_apply_ne (ne_of_gt h))
  · exact (hB i i le_rfl).trans (Matrix.one_apply_eq i)

theorem levi_off {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) :
    (∀ l, mat m 0 (mid l) = 0) ∧ (∀ l, mat m (mid l) 0 = 0) ∧ mat m 0 (Fin.last (N + 1)) = 0 ∧
      mat m (Fin.last (N + 1)) 0 = 0 ∧ (∀ l, mat m (mid l) (Fin.last (N + 1)) = 0) ∧
      ∀ l, mat m (Fin.last (N + 1)) (mid l) = 0 := by
  have hA : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  exact ⟨fun l => hA _ _ (by simp), fun l => hA _ _ (by simp), hA _ _ (by simp), hA _ _ (by simp),
    fun l => hA _ _ (by simp), fun l => hA _ _ (by simp)⟩

theorem levi_borel {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) (hg : IsBorelU g) :
    IsBorelU m := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · simp at hij
  · simp at hij
  · simp at hij
  · exact o2 _
  · exact (h.2.2.2 i j).trans (hg i j (by
      have h' : j.val + 1 < i.val + 1 := hij
      exact Fin.lt_def.2 (by omega)))
  · exact absurd hij (not_lt.2 (Fin.le_last _))
  · exact o4
  · exact o6 _
  · exact absurd hij (lt_irrefl _)

theorem levi_mem_K {ϖ : L} {g : GU σ N} {m : GU σ (N + 2)} (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h : IsLeviElt ϖ 0 g m) (hg : g ∈ KU σ N) : m ∈ KU σ (N + 2) := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  rw [mem_KU_iff hσ]
  intro i j
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · rw [h.2.1, zpow_zero]; exact one_mem _
  · rw [o1]; exact zero_mem _
  · rw [o3]; exact zero_mem _
  · rw [o2]; exact zero_mem _
  · rw [h.2.2.2]; exact P.fSatake_K_int hg i j
  · rw [o5]; exact zero_mem _
  · rw [o4]; exact zero_mem _
  · rw [o6]; exact zero_mem _
  · rw [h.2.2.1, neg_zero, zpow_zero]; exact one_mem _

theorem levi_eq_mul {ϖ : L} {a : ℤ} {b k : GU σ N} {mb mk m : GU σ (N + 2)} (hb : IsLeviElt ϖ a b mb)
    (hk : IsLeviElt ϖ 0 k mk) (hm : IsLeviElt ϖ a (b * k) m) : m = mb * mk := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := levi_off hb
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := levi_off hk
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := levi_off hm
  apply mat_injective
  ext i j
  rw [mat_mul, Matrix.mul_apply, sum_idx]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp only [b1, b2, b3, b4, b5, b6, k1, k2, k3, k4, k5, k6, m1, m2, m3, m4, m5, m6, hb.2.1, hb.2.2.1, hb.2.2.2,
      hk.2.1, hk.2.2.1, hk.2.2.2, hm.2.1, hm.2.2.1, hm.2.2.2, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
      zero_add, zpow_zero, neg_zero, mul_one, mat_mul, Matrix.mul_apply]

theorem sphTrans_of_leviExists : LeviExists → SphTrans := by
  intro hL L _ _ ϖ σ q N r hU hr α φ φ₀ hα hφ h1 hφ₀ h01 a g₀ m hm u hu
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have e := levi_eq_mul hmb hmk hm
  have hkK : mk ∈ KU σ (N + 2) := levi_mem_K hU.2.1 hmk hk₀
  have hmbB : IsBorelU mb := levi_borel hmb hb₀
  have hu' : mk * u * mk⁻¹ ∈ radQ σ N := conj_mem_radU hmk.1 hu
  have hu'B := isUnipU_of_radQ hu'
  have e2 : m * u = (mb * (mk * u * mk⁻¹)) * 1 * mk := by rw [e]; group
  have d : ∀ (i : Fin (N + 2)) (x : L), mat mb i i = x →
      (((mb * (mk * u * mk⁻¹) : GU σ (N + 2)) : GL (Fin (N + 2)) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i i = x := by
    intro i x hx
    have := P.fSatake_borel_diag_mul hmbB hu'B.1 i
    rw [hu'B.2, mul_one] at this
    exact this.trans hx
  have e3 : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hφ₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h01, mul_one] at this
  rw [e2, hφ _ _ _ (P.fSatake_borel_mul hmbB hu'B.1) hkK, h1, mul_one, e3]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · have h0 : ((0 : Fin (r + 1)) : ℕ) < N + 2 := by simp
    rw [dite_eq_left h0]
    have e0 : (⟨((0 : Fin (r + 1)) : ℕ), h0⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0, d _ _ hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    push_cast
    simp only [Fin.val_zero]
    congr 3
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.val < N := by have := i.2; omega
    have hi' : (i.succ : Fin (r + 1)).val < N + 2 := by simp; omega
    rw [dite_eq_left hi, dite_eq_left hi']
    have ei : (⟨(i.succ : Fin (r + 1)).val, hi'⟩ : Fin (N + 2)) = mid ⟨i.val, hi⟩ := by
      ext; simp
    rw [ei, d _ _ (hmb.2.2.2 ⟨i.val, hi⟩ ⟨i.val, hi⟩)]
    have ex : ((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ : Fin (r + 1)).val : ℤ) = (N : ℤ) - 1 - 2 * (i.val : ℤ) := by
      simp; ring
    rw [ex]
    rfl

end GlobalTheory.CompanionTheory.InertTrans

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.TraceIndexFormula
section
open GlobalTheory.InertZeta Formalism.UG

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem traceZero_eq_map {σ : L →+* L} {c : L} (hc : c ≠ 0) (hσ : σ c = c) :
    traceZero σ c =
      ((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker).map (AddMonoidHom.mulLeft c⁻¹) := by
  ext x
  rw [mem_traceZero, AddSubgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c * x, AddSubgroup.mem_inf.2 ⟨h1, ?_⟩, by simp [hc]⟩
    rw [AddMonoidHom.mem_ker]
    show σ (c * x) + c * x = 0
    rw [map_mul, hσ, ← mul_add, h2, mul_zero]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hy
    rw [AddMonoidHom.mem_ker] at h2
    have h2' : σ y + y = 0 := h2
    have hi : σ c⁻¹ = c⁻¹ := by rw [map_inv₀, hσ]
    refine ⟨?_, ?_⟩
    · show c * (c⁻¹ * y) ∈ intL L
      rw [mul_inv_cancel_left₀ hc]
      exact h1
    · show σ (c⁻¹ * y) + c⁻¹ * y = 0
      rw [map_mul, hi, ← mul_add, h2', mul_zero]

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hbase := GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex GlobalTheory.SatakeWeyl.intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, hv, -, -, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  have hϖ1 : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv', ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have hS : ∀ f : ℕ, traceZero σ (ϖ ^ f) = T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) := fun f =>
    traceZero_eq_map (pow_ne_zero f h0) (by rw [map_pow, hϖ])
  have hmono : ∀ f : ℕ, traceZero σ (ϖ ^ f) ≤ traceZero σ (ϖ ^ (f + 1)) := by
    intro f x hx
    obtain ⟨h1, h2⟩ := mem_traceZero.1 hx
    refine mem_traceZero.2 ⟨?_, h2⟩
    rw [pow_succ', mul_assoc]
    exact mul_mem hϖ1 h1
  have hstep : ∀ f : ℕ, (traceZero σ (ϖ ^ f)).relIndex (traceZero σ (ϖ ^ (f + 1))) = q := by
    intro f
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) :=
      mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ h0))
    have e : T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨ϖ * y, ⟨y, hy, rfl⟩, ?_⟩
        field_simp
        ring
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        field_simp
        ring
    rw [hS f, hS (f + 1), e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hbase
  induction f with
  | zero =>
    rw [pow_zero, pow_zero, AddSubgroup.relIndex_self]
  | succ f ih =>
    have hle : traceZero σ 1 ≤ traceZero σ (ϖ ^ f) := by
      clear ih
      induction f with
      | zero => rw [pow_zero]
      | succ f ih => exact ih.trans (hmono f)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle (hmono f), ih, hstep, pow_succ]

end GlobalTheory.CompanionTheory.InertZeta
end

