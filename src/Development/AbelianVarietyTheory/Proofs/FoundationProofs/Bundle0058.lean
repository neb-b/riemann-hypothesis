module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVector
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Per

def qp (q u : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * u)

theorem multipliable_qp {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun m : ℕ => 1 - q ^ (m + 1) * u := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * u)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem qp_shift {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : qp q u = (1 - q * u) * qp q (q * u) := by
  have e : (fun m : ℕ => 1 - q ^ (m + 1 + 1) * u) = fun m : ℕ => 1 - q ^ (m + 1) * (q * u) := by
    funext m; ring
  have h : Multipliable fun m : ℕ => (fun m : ℕ => 1 - q ^ (m + 1) * u) (m + 1) := by
    show Multipliable fun m : ℕ => 1 - q ^ (m + 1 + 1) * u
    rw [e]; exact multipliable_qp hq _
  have := tprod_eq_zero_mul' (f := fun m : ℕ => 1 - q ^ (m + 1) * u) h
  simp only [e, zero_add, pow_one] at this
  exact this

def tp (q u : ℂ) : ℂ := (1 - u) * qp q u * qp q u⁻¹

theorem tp_shift {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) : tp q (q * u) = -u⁻¹ * tp q u := by
  have e : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  unfold tp
  rw [← qp_shift hq u, qp_shift hq (q * u)⁻¹, e]
  have : 1 - u⁻¹ = -u⁻¹ * (1 - u) := by field_simp; ring
  rw [this]; ring

theorem tp_shift_pow {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) (k : ℕ) :
    tp q (q ^ k * u) = (-u⁻¹) ^ k * (q ^ (k.choose 2))⁻¹ * tp q u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : q ^ (k + 1) * u = q * (q ^ k * u) := by ring
    have e2 : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [e, tp_shift hq hq0 (mul_ne_zero (pow_ne_zero _ hq0) hu), ih, e2, pow_add q, pow_succ (-u⁻¹)]
    generalize (-u⁻¹) ^ k = A
    field_simp

theorem cth_eq {q t : ℂ} (hq : ‖q‖ < 1) (c : ℕ) (h1 : ∀ m : ℕ, 1 - q ^ (m + 1) * t ^ c ≠ 0)
    (h2 : ∀ m : ℕ, 1 - q ^ (m + 1) * (t ^ c)⁻¹ ≠ 0) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have pA := (multipliable_qp hq t).hasProd
  have pB := (multipliable_qp hq t⁻¹).hasProd
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ h1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ h2
  have hP : HasProd (fun m : ℕ => cthFac c q t (m + 1)) (qp q t ^ (c ^ 2) * qp q t⁻¹ ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, div_eq_mul_inv, qp] using this
  have eC : qp q (t ^ c) = C := pC.tprod_eq
  have eD : qp q (t ^ c)⁻¹ = D := pD.tprod_eq
  unfold cth tp
  rw [hP.tprod_eq, eC, eD]
  simp only [div_eq_mul_inv, mul_inv, mul_pow]
  ring

theorem expo (c : ℕ) : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c.choose 2 : ℕ) : ℤ) := by
  have h : (c : ℤ) - (c : ℤ) ^ 2 = 2 * -((c.choose 2 : ℕ) : ℤ) := by
    induction c with
    | zero => simp
    | succ k ih =>
      have e2 : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
      rw [e2]; push_cast; linarith
  rw [h]; exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem mono_shift {q t : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ht : t ≠ 0) (c : ℕ) :
    (-(q * t)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q (q * t) ^ (c ^ 2) / tp q ((q * t) ^ c)) =
      (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have hs : (-t⁻¹) ^ (c ^ 2) = (-(t ^ c)⁻¹) ^ c := by
    have hpar : (-1 : ℂ) ^ (c ^ 2) = (-1) ^ c := by
      rcases Nat.even_or_odd c with h | h
      · rw [h.neg_one_pow, (h.pow_of_ne_zero two_ne_zero).neg_one_pow]
      · rw [h.neg_one_pow, h.pow.neg_one_pow]
    rw [neg_pow, neg_pow (t ^ c)⁻¹, hpar, ← inv_pow, ← pow_mul, sq]
  have hn : (-(t ^ c)⁻¹) ^ c ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  have hqk : q ^ (c.choose 2) ≠ 0 := pow_ne_zero _ hq0
  have e : -(q * t) = q * -t := by ring
  rw [tp_shift hq hq0 ht, mul_pow q t c, tp_shift_pow hq hq0 (pow_ne_zero c ht), mul_pow, hs, e, mul_zpow, expo,
    zpow_neg q, zpow_natCast]
  generalize (-(t ^ c)⁻¹) ^ c = A at hn
  generalize q ^ (c.choose 2) = B at hqk
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

theorem sg_eq {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    sg c x τ = ee τ ^ ((c ^ 2 - 1) / 12) * ((-ee (pt x τ)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (tp (ee τ) (ee (pt x τ)) ^ (c ^ 2) / tp (ee τ) (ee (pt x τ) ^ c))) := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  unfold sg
  rw [cth_eq (norm_ee_lt_one τ) c (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).1)
    (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).2), mul_assoc]

theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (n : Fin 2 → ℤ) : admitted c fun i => x i + n i := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact h.2.2 ⟨⟨a - c * n 0, by push_cast; rw [ha]; ring⟩, ⟨b - c * n 1, by push_cast; rw [hb]; ring⟩⟩

theorem sg_step {c : ℕ} {x y : Fin 2 → ℚ} (hx : admitted c x) (hy : admitted c y) (τ : ℍ) (h0 : y 0 = x 0 + 1) (h1 : y 1 = x 1) :
    sg c y τ = sg c x τ := by
  have e : ee (pt y τ) = ee τ * ee (pt x τ) := by
    rw [← ee_add]; congr 1; simp only [pt, h0, h1]; push_cast; ring
  rw [sg_eq hx, sg_eq hy, e, mono_shift (norm_ee_lt_one τ) (ee_ne_zero _) (ee_ne_zero _)]

theorem sg_fst {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (τ : ℍ) (k : ℤ) :
    sg c (fun i => x i + (![k, 0] : Fin 2 → ℤ) i) τ = sg c x τ := by
  induction k using Int.induction_on with
  | zero =>
    congr 1; funext i; fin_cases i <;> simp
  | succ k ih =>
    rw [← ih]
    exact sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)
  | pred k ih =>
    rw [← ih]
    exact (sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)).symm

theorem sg_add_int : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x →
    sg c (fun i => x i + n i) τ = sg c x τ := by
  intro c x n τ hx
  rw [← sg_fst hx τ (n 0)]
  have e1 : ee (n 1 : ℂ) = 1 := by
    unfold ee
    rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
  unfold sg
  congr 1
  rw [← mul_one (ee (pt (fun i => x i + (![n 0, 0] : Fin 2 → ℤ) i) τ)), ← e1, ← ee_add]
  congr 1
  simp [pt]; ring

end GlobalTheory.Sieg.Per
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotient
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg.ThQuot

theorem ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

theorem ee_nat_mul (n : ℕ) (z : ℂ) : ee ((n : ℂ) * z) = ee z ^ n := by
  unfold ee
  rw [← Complex.exp_nat_mul]; congr 1; ring

theorem ee_neg (z : ℂ) : ee (-z) = (ee z)⁻¹ := by
  unfold ee
  rw [← Complex.exp_neg]; congr 1; ring

theorem norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

theorem multipliable_one_sub {q : ℂ} (hq : ‖q‖ < 1) (t : ℂ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1) * t) := by
  have h : Summable (fun n : ℕ => -(q ^ (n + 1) * t)) := by
    have h0 := (summable_geometric_of_norm_lt_one hq).mul_right (q * t)
    refine h0.neg.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable h

theorem hasProd_pow_div {f g : ℕ → ℂ} {a b : ℂ} (hf : HasProd f a) (hg : HasProd g b) (hb : b ≠ 0) (k : ℕ) :
    HasProd (fun n => f n ^ k / g n) (a ^ k / b) := by
  unfold HasProd at *
  simp only [Finset.prod_div_distrib, Finset.prod_pow]
  exact (hf.pow k).div hg hb

theorem twelve_dvd {c : ℕ} (h1 : 1 < c) (h : Nat.Coprime c 6) : ∃ k, c ^ 2 = 12 * k + 1 := by
  have h2 : ¬ 2 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  have h3 : ¬ 3 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  obtain ⟨m, hm⟩ : ∃ m, c = 6 * m + 1 ∨ c = 6 * m + 5 := ⟨c / 6, by omega⟩
  rcases hm with rfl | rfl
  · exact ⟨3 * m ^ 2 + m, by ring⟩
  · exact ⟨3 * m ^ 2 + 5 * m + 2, by ring⟩

theorem cth_eq_th_quot : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → th ((c : ℂ) * z) τ ≠ 0 →
    cth c (ee (τ : ℂ)) (ee z) = (-1) ^ (c * (c - 1) / 2) * th z τ ^ (c ^ 2) / th ((c : ℂ) * z) τ := by
  intro c τ z h1 hc hne
  obtain ⟨k, hk⟩ := twelve_dvd h1 hc
  have hodd : Odd c := by
    have : Odd (c ^ 2) := ⟨6 * k, by omega⟩
    exact (Nat.odd_pow_iff (by norm_num)).mp this
  obtain ⟨j, hj⟩ := hodd
  have hq := norm_ee_lt_one τ
  set s := ee (z / 2) with hs
  set u := ee ((τ : ℂ) / 12) with hu
  have hs0 : s ≠ 0 := ee_ne_zero _
  have hu0 : u ≠ 0 := ee_ne_zero _
  have ht : ee z = s ^ 2 := by
    rw [hs, ← ee_nat_mul]; congr 1; push_cast; ring
  have hqu : ee (τ : ℂ) = u ^ 12 := by
    rw [hu, ← ee_nat_mul]; congr 1; push_cast; ring
  have e1 : ee (-z / 2) = s⁻¹ := by rw [neg_div, ee_neg]
  have e2 : ee ((c : ℂ) * z / 2) = s ^ c := by rw [mul_div_assoc, ee_nat_mul]
  have e3 : ee (-((c : ℂ) * z) / 2) = (s ^ c)⁻¹ := by rw [neg_div, ee_neg, e2]
  have e4 : ee ((c : ℂ) * z) = ee z ^ c := ee_nat_mul c z
  unfold th at hne ⊢
  unfold cth
  rw [e2, e3, e4] at hne ⊢
  rw [e1, ← hs, ← hu] at *
  have mf := ((multipliable_one_sub hq (ee z)).mul (multipliable_one_sub hq (ee z)⁻¹)).hasProd
  have mg := ((multipliable_one_sub hq (ee z ^ c)).mul (multipliable_one_sub hq (ee z ^ c)⁻¹)).hasProd
  set A := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) with hA
  set B := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z ^ c) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z ^ c)⁻¹) with hB
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hne
  have hd : s ^ c - (s ^ c)⁻¹ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hP : ∏' m : ℕ, cthFac c (ee (τ : ℂ)) (ee z) (m + 1) = A ^ (c ^ 2) / B := by
    have := hasProd_pow_div mf mg hB0 (c ^ 2)
    refine (HasProd.tprod_eq ?_)
    simpa only [cthFac, mul_pow] using this
  rw [hP]
  have x1 : (c ^ 2 - 1) / 12 = k := by omega
  have x2 : c * (c - 1) / 2 = c * j := by
    have : c * (c - 1) = 2 * (c * j) := by
      have : c - 1 = 2 * j := by omega
      rw [this]; ring
    omega
  have x3 : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c * j : ℕ) : ℤ) := by
    have : (c : ℤ) - (c : ℤ) ^ 2 = 2 * (-((c * j : ℕ) : ℤ)) := by
      subst hj; push_cast; ring
    rw [this]; omega
  rw [x1, x2, x3, zpow_neg, zpow_natCast, ht, hqu]
  have hsc : s ^ c ≠ 0 := pow_ne_zero _ hs0
  have y1 : s ^ c - (s ^ c)⁻¹ = -(1 - (s ^ 2) ^ c) / s ^ c := by
    field_simp; ring
  have y2 : s - s⁻¹ = -(1 - s ^ 2) / s := by field_simp; ring
  have hd' : 1 - (s ^ 2) ^ c ≠ 0 := by
    intro h; apply hd; rw [y1, h]; simp
  have hc2 : Odd (c ^ 2) := ⟨6 * k, by omega⟩
  have y3 : s ^ (c ^ 2) = s ^ c * (s ^ 2) ^ (c * j) := by
    rw [← pow_mul, ← pow_add]; congr 1; subst hj; ring
  have y4 : u ^ (c ^ 2) = u * (u ^ 12) ^ k := by rw [hk, ← pow_mul]; ring
  have y5 : ((-1 : ℂ)) ^ (c * j) * (-1) ^ (c * j) = 1 := by rw [← mul_pow]; simp
  rw [y1, y2, mul_pow, mul_pow, div_pow, hc2.neg_pow, y3, y4, neg_pow (s ^ 2)]
  have hS : (s ^ 2) ^ (c * j) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hs0)
  generalize (s ^ 2) ^ (c * j) = S at *
  generalize (1 - (s ^ 2) ^ c) = D at *
  generalize (1 - s ^ 2) ^ (c ^ 2) = E at *
  generalize s ^ c = T at *
  generalize A ^ (c ^ 2) = A' at *
  generalize (u ^ 12) ^ k = U at *
  generalize ((-1 : ℂ)) ^ (c * j) = ε at *
  have hε : ε ≠ 0 := left_ne_zero_of_mul (y5 ▸ one_ne_zero)
  have hi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right y5
  rw [mul_inv, hi]
  field_simp

end GlobalTheory.Sieg.ThQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem span_translates_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, (∀ v, Fixes W A v → ∃ c : ℂ, v = c • e) → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W h A hA e he hsm
  rw [eq_top_iff]
  intro v _
  obtain ⟨T, hT, hv⟩ := hsm v
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, mul_one]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]; exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hSm : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSv : Fixes W S v := fun a ha => hv a ha.1 ha.2
  have hSt : ∀ t ∈ T, Fixes W S (W (-t) v) := by
    intro t ht a ha
    rw [h.comm, ha.2 _ (T.neg_mem ht), one_smul, hSv a ha]
  obtain ⟨h1, -, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup
    (fun a ha => ⟨fun hs => hs.2, fun hs => ⟨ha, hs⟩⟩)
    (fun t _ => ⟨fun ht a ha => h.iso hA ha ht,
      fun ht => (hA t).2 fun a ha => h.swap_eq_one (ht a ha)⟩) hT
  have hn : idx S A ≠ 0 := by
    unfold idx
    rw [h1]
    exact hT
  obtain ⟨-, -, h2⟩ := perfect_pairing_quotients h A.toAddSubgroup T.toAddSubgroup
    S.toAddSubgroup A.toAddSubgroup
    (fun t _ => hA t)
    (fun a ha => ⟨fun hs t ht => h.swap_eq_one (hs.2 t ht),
      fun hs => ⟨ha, fun t ht => h.swap_eq_one (hs t ht)⟩⟩) hn
  obtain ⟨t1, t2, -⟩ := sumOp_transversal h S A hA
  obtain ⟨⟨m, f, hf, hu⟩, hfix, -⟩ := t2 hn
  have hg : ∀ t ∈ T, ∑ i, γ t (f i) • W (f i) v ∈ Submodule.span ℂ (Set.range fun x => W x e) := by
    intro t ht
    obtain ⟨c, hc⟩ := he _ (hfix _ (hSt t ht))
    rw [(t1 _ (hSt t ht) _ f hf hu).1] at hc
    have h3 := congrArg (W t) hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul] at h3
    have h4 : ∀ i, W t (W (f i) (W (-t) v)) = γ (w • t) (-t) • (γ t (f i) • W (f i) v) := by
      intro i
      rw [h.comm, h.comp t (-t), add_neg_cancel, h.zero, map_smul, smul_comm]
    rw [Finset.sum_congr rfl fun i _ => h4 i, ← Finset.smul_sum] at h3
    rw [← Submodule.smul_mem_iff _ (h.ne_zero (w • t) (-t)), h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  haveI : Finite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hT
  letI := Fintype.ofFinite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)
  have h5 := Submodule.sum_mem (Submodule.span ℂ (Set.range fun x => W x e))
    (t := (Finset.univ : Finset
      (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)))
    (fun q _ => hg _ (Quotient.out q : T.toAddSubgroup).2)
  rw [Finset.sum_comm] at h5
  obtain ⟨i₀, hi₀, hi⟩ := hu 0 A.zero_mem
  simp only [zero_sub, neg_mem_iff] at hi₀ hi
  have h6 : ∀ i, ∑ q : T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup,
      γ ((Quotient.out q : T.toAddSubgroup) : X) (f i) • W (f i) v
      = if i = i₀ then (idx A T : ℂ) • v else 0 := by
    intro i
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, h2 _ (hf i)]
    by_cases hii : i = i₀
    · subst hii
      rw [if_pos rfl, if_pos (show f i ∈ S.toAddSubgroup from hi₀), hSv _ hi₀]
      rfl
    · rw [if_neg hii, if_neg (fun hh : f i ∈ S.toAddSubgroup => hii (hi i hh)), zero_smul]
  rw [Finset.sum_congr rfl fun i _ => h6 i, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h5
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hT)).1 h5

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumGl2FirstColumnUnitSetSuccFibre
section
noncomputable section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem glFibre_val_map {p n : ℕ} [NeZero p] (x : ZMod (p ^ (n + 1))) :
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val = x.val % p ^ n := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

theorem glFibre_isUnit_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ n)) :
    IsUnit x ↔ ¬ p ∣ x.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    hp.coprime_iff_not_dvd]

theorem glFibre_dvd_map_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [glFibre_val_map, Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_unitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  intro p _ n K _ G Φ hn
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hent : ∀ (γ : GL (Fin 2) (ZMod (p ^ (n + 1)))) (a b : Fin 2),
      (Matrix.GeneralLinearGroup.map ρ γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) a b =
        ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) a b) := fun _ _ _ => rfl
  have hmaps : ∀ γ ∈ unitSet p (n + 1), Matrix.GeneralLinearGroup.map ρ γ ∈ unitSet p n := by
    intro γ hγ
    simp only [unitSet, mem_filter, mem_univ, true_and] at hγ ⊢
    rw [hent, hent, hρ, glFibre_dvd_map_iff hn, glFibre_dvd_map_iff hn]
    exact hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [(mem_filter.mp hγ).2]), ← Finset.mul_sum]
  congr 1
  simp only [← Finset.sum_product']
  refine Finset.sum_bij (fun γ _ => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1))) ?_ ?_ ?_ ?_
  · intro γ hγ
    obtain ⟨_, hγg⟩ := mem_filter.mp hγ
    simp only [mem_product, mem_filter, mem_univ, true_and, ← hγg, hent, and_self]
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    ext a b
    fin_cases a <;> fin_cases b
    exacts [h1, h2, h3, h4]
  · rintro ⟨a, b, c, d⟩ hb
    simp only [mem_product, mem_filter, mem_univ, true_and] at hb
    obtain ⟨ha, hb', hc, hd⟩ := hb
    let B : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))) := !![a, b; c, d]
    have hBm : ρ.mapMatrix B = (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) := by
      ext i j
      fin_cases i <;> fin_cases j
      exacts [ha, hb', hc, hd]
    have hdet : IsUnit B.det := by
      have h1 : IsUnit (ρ B.det) := by
        rw [RingHom.map_det, hBm]; exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rw [glFibre_isUnit_iff hn, hρ, glFibre_dvd_map_iff hn] at h1
      exact (glFibre_isUnit_iff (by omega) _).mpr h1
    obtain ⟨γ, hγ⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hdet
    have hmap : Matrix.GeneralLinearGroup.map ρ γ = g := by
      apply Units.ext
      rw [← hBm, ← hγ]; rfl
    refine ⟨γ, ?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, hmap⟩
      simp only [unitSet, mem_filter, mem_univ, true_and] at hg ⊢
      rw [← glFibre_dvd_map_iff hn, ← glFibre_dvd_map_iff hn, ← hρ, ← hent, ← hent, hmap]
      exact hg
    · simp only [hγ, B]
      rfl
  · intro γ _
    rfl

end GlobalTheory.KummerEisensteinGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrixStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix : ∀ (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ) (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ), L.det ≠ 0 → Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L) → Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0) → Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | exact GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | (intros; apply GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThreeStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F ρ).det ≠ 0 → 3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  first | exact @GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | exact GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | (intros; apply GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLeStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ y β : L, v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.valuation_add_pow_sub_le | exact GlobalTheory.AlmostEt.valuation_add_pow_sub_le | (intros; apply GlobalTheory.AlmostEt.valuation_add_pow_sub_le <;> assumption)
end

