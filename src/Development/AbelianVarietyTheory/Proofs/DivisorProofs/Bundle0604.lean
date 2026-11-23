module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvariance
section
open GlobalTheory.LeviCut

noncomputable section

namespace GlobalTheory.LeviCut.RankTwoProof

variable {W : Type} [AddCommGroup W] [Module ℚ W]

theorem coef_succ_mul (i k : ℕ) :
    coef i (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + i + 2)) = - coef i k := by
  unfold coef
  rw [show k + 1 + i + 1 = (k + i + 1) + 1 by ring, Nat.factorial_succ (k + i + 1), Nat.factorial_succ k]
  have a1 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have a2 : (((k + i + 1).factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

theorem pow_succ_apply' (Y : Module.End ℚ W) (k : ℕ) (v : W) : (Y ^ (k + 1)) v = Y ((Y ^ k) v) := by
  rw [pow_succ', Module.End.mul_apply]

theorem comm_sub' (A B X x y : Module.End ℚ W) (h1 : A * X - X * A = x) (h2 : B * X - X * B = y) :
    (A - B) * X - X * (A - B) = x - y := by
  rw [← h1, ← h2]; noncomm_ring

theorem eig_pow (H X : Module.End ℚ W) (d c : ℚ) (hHX : H * X - X * H = d • X) (v : W)
    (hv : H v = c • v) (k : ℕ) : H ((X ^ k) v) = (c + k * d) • (X ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have e := LinearMap.congr_fun hHX ((X ^ k) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at e
    rw [pow_succ_apply', eq_add_of_sub_eq e, ih, map_smul, ← add_smul]
    congr 1; push_cast; ring

theorem comm_pow_apply (Z Y P : Module.End ℚ W) (h : Z * Y - Y * Z = P) (hP : P * Y = Y * P) (v : W)
    (k : ℕ) : Z ((Y ^ (k + 1)) v) = (Y ^ (k + 1)) (Z v) + ((k : ℚ) + 1) • P ((Y ^ k) v) := by
  induction k with
  | zero =>
    have e := LinearMap.congr_fun h v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, one_smul]
    rw [eq_add_of_sub_eq e]; abel
  | succ k ih =>
    have e := LinearMap.congr_fun h ((Y ^ (k + 1)) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hp : P ((Y ^ (k + 1)) v) = Y (P ((Y ^ k) v)) := by
      rw [pow_succ_apply', ← Module.End.mul_apply P Y, hP, Module.End.mul_apply]
    rw [pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (Z v), eq_add_of_sub_eq e, ih, hp, map_add (f := _), map_smul]
    push_cast
    module

theorem sl2_X_Ypow (X Y H : Module.End ℚ W) (hXY : X * Y - Y * X = H) (hHY : H * Y - Y * H = (-2 : ℚ) • Y)
    (v : W) (c : ℚ) (hv : H v = c • v) (k : ℕ) :
    X ((Y ^ (k + 1)) v) = (Y ^ (k + 1)) (X v) + (((k : ℚ) + 1) * (c - k)) • (Y ^ k) v := by
  induction k with
  | zero =>
    have e := LinearMap.congr_fun hXY v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]
    rw [eq_add_of_sub_eq e, hv]; abel
  | succ k ih =>
    have e := LinearMap.congr_fun hXY ((Y ^ (k + 1)) v)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hH := eig_pow H Y (-2) c hHY v hv (k + 1)
    rw [pow_succ_apply' Y (k + 1) v, pow_succ_apply' Y (k + 1) (X v), eq_add_of_sub_eq e, ih, hH, map_add (f := _),
      map_smul, ← pow_succ_apply' Y k v]
    push_cast
    module

theorem sl2_Xpow_Y (X Y H : Module.End ℚ W) (hXY : X * Y - Y * X = H) (hHX : H * X - X * H = (2 : ℚ) • X)
    (u : W) (c : ℚ) (hu : H u = c • u) (l : ℕ) :
    (X ^ (l + 1)) (Y u) = Y ((X ^ (l + 1)) u) + (((l : ℚ) + 1) * (c + l)) • (X ^ l) u := by
  induction l with
  | zero =>
    have e := LinearMap.congr_fun hXY u
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]
    rw [eq_add_of_sub_eq e, hu]; abel
  | succ l ih =>
    have e := LinearMap.congr_fun hXY ((X ^ (l + 1)) u)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    have hH := eig_pow H X 2 c hHX u hu (l + 1)
    rw [pow_succ_apply' X (l + 1) (Y u), ih, map_add (f := _), map_smul, eq_add_of_sub_eq e, hH,
      ← pow_succ_apply' X (l + 1) u, ← pow_succ_apply' X l u]
    push_cast
    module

theorem pow_succ_apply2 (Y : Module.End ℚ W) (k : ℕ) (v : W) : (Y ^ (k + 1)) v = (Y ^ k) (Y v) := by
  rw [pow_succ, Module.End.mul_apply]

theorem rankTwo : RankTwo := by
  intro W _ _ N K D hG hB o p q ho hp hq hop hoq hpq j T hoo hpp hqq hpqT
  have hpo := Ne.symm hop
  have hqo := Ne.symm hoq
  have hqp := Ne.symm hpq
  have rZXp : D p q * D o p - D o p * D p q = -D o q := by
    simpa [hqo] using hG p q o p hp hq ho hp
  have rZXq : D p q * D o q = D o q * D p q := by
    have := hG p q o q hp hq ho hq; simpa [hqo, hqp, sub_eq_zero] using this
  have rZYp : D p q * D p o = D p o * D p q := by
    have := hG p q p o hp hq hp ho; simpa [hqp, hop, sub_eq_zero] using this
  have rZYq : D p q * D q o - D q o * D p q = D p o := by
    simpa [hop] using hG p q q o hp hq hq ho
  have rXqXp : D o q * D o p = D o p * D o q := by
    have := hG o p o q ho hp ho hq
    exact (by simpa [hpo, hqo, sub_eq_zero] using this : D o p * D o q = D o q * D o p).symm
  have rYpYq : D p o * D q o = D q o * D p o := by
    have := hG p o q o hp ho hq ho; simpa [hoq, hop, sub_eq_zero] using this
  have sXYp : D o p * D p o - D p o * D o p = D o o - D p p := by simpa using hG o p p o ho hp hp ho
  have sXYq : D o q * D q o - D q o * D o q = D o o - D q q := by simpa using hG o q q o ho hq hq ho
  have hHpXp : (D o o - D p p) * D o p - D o p * (D o o - D p p) = (2 : ℚ) • D o p := by
    rw [comm_sub' _ _ _ (D o p) (-D o p) (by simpa [hpo] using hG o o o p ho ho ho hp)
      (by simpa [hpo] using hG p p o p hp hp ho hp), sub_neg_eq_add, two_smul]
  have hHqXq : (D o o - D q q) * D o q - D o q * (D o o - D q q) = (2 : ℚ) • D o q := by
    rw [comm_sub' _ _ _ (D o q) (-D o q) (by simpa [hqo] using hG o o o q ho ho ho hq)
      (by simpa [hqo] using hG q q o q hq hq ho hq), sub_neg_eq_add, two_smul]
  have hHqYq : (D o o - D q q) * D q o - D q o * (D o o - D q q) = (-2 : ℚ) • D q o := by
    rw [comm_sub' _ _ _ (-D q o) (D q o) (by simpa [hoq] using hG o o q o ho ho hq ho)
      (by simpa [hoq] using hG q q q o hq hq hq ho), neg_smul, two_smul]; abel
  have hHpXq : (D o o - D p p) * D o q - D o q * (D o o - D p p) = (1 : ℚ) • D o q := by
    rw [comm_sub' _ _ _ (D o q) 0 (by simpa [hqo] using hG o o o q ho ho ho hq)
      (by simpa [hpo, hqp] using hG p p o q hp hp ho hq), sub_zero, one_smul]
  have hHpYq : (D o o - D p p) * D q o - D q o * (D o o - D p p) = (-1 : ℚ) • D q o := by
    rw [comm_sub' _ _ _ (-D q o) 0 (by simpa [hoq] using hG o o q o ho ho hq ho)
      (by simpa [hpq, hop] using hG p p q o hp hp hq ho), sub_zero, neg_one_smul]
  have hHpT : (D o o - D p p) T = (0 : ℚ) • T := by simp [hoo, hpp]
  have hHqT : (D o o - D q q) T = (0 : ℚ) • T := by simp [hoo, hqq]
  have hZv : ∀ k : ℕ, D p q ((D o q ^ k) T) = 0 := fun k => by
    have c := LinearMap.congr_fun (Commute.pow_right rZXq k).eq T
    simp only [Module.End.mul_apply] at c
    rw [c, hpqT, map_zero]
  have hHqv : ∀ k : ℕ, (D o o - D q q) ((D o q ^ k) T) = ((2 : ℚ) * k) • (D o q ^ k) T := fun k => by
    rw [eig_pow _ _ 2 0 hHqXq T hHqT k]; congr 1; ring
  have hXqK : (D o q ^ (K + 1)) T = 0 := by
    apply hB o ho q hq (2 * K + 2 : ℤ)
    · rw [← LinearMap.sub_apply, hHqv]; congr 1; push_cast; ring
    · push_cast; omega
  have hproj : ∀ (i : ℕ) (X Y : Module.End ℚ W) (x : W),
      (proj K i X Y) x = ∑ k ∈ Finset.range (K + 1), coef i k • (Y ^ k) ((X ^ k) x) := by
    intro i X Y x; unfold proj; rw [LinearMap.sum_apply]; simp only [LinearMap.smul_apply, Module.End.mul_apply]
  obtain ⟨T', hT'⟩ : ∃ x : W, x = (proj K (j + 1) (D o q) (D q o)) T := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ u : W, u = ∑ k ∈ Finset.range K,
      (((k : ℚ) + 1) * coef (j + 1) (k + 1)) • (D q o ^ k) ((D o q ^ (k + 1)) T) := ⟨_, rfl⟩

  have hZT' : D p q T' = D p o U := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT', hproj, map_sum, Finset.sum_range_succ', hU, map_sum]
    simp only [map_smul, pow_zero, Module.End.one_apply, hpqT, smul_zero, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [comm_pow_apply _ _ _ rZYq rYpYq, hZv, map_zero, zero_add, smul_smul, mul_comm]

  have key : ∀ k : ℕ, coef (j + 1) k + coef (j + 1) (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + 2)) =
      -((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1)) := by
    intro k; have := coef_succ_mul (j + 1) k; push_cast at this; linear_combination this
  have hXq_step : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) ((D o q ^ (k + 1)) T)) =
      (D q o ^ (k + 1)) ((D o q ^ (k + 1 + 1)) T) +
        (((k : ℚ) + 1) * ((k : ℚ) + 2)) • (D q o ^ k) ((D o q ^ (k + 1)) T) := fun k => by
    rw [sl2_X_Ypow _ _ _ sXYq hHqYq _ _ (hHqv (k + 1)) k, ← pow_succ_apply' (D o q) (k + 1) T]
    congr 2; push_cast; ring
  have hS : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), coef (j + 1) k • D o q ((D q o ^ k) ((D o q ^ k) T)) =
      coef (j + 1) n • (D q o ^ n) ((D o q ^ (n + 1)) T) + ∑ k ∈ Finset.range n,
        (-((j : ℚ) + 1) * (((k : ℚ) + 1) * coef (j + 1) (k + 1))) • (D q o ^ k) ((D o q ^ (k + 1)) T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hXq_step n, Finset.sum_range_succ, ← key n]
      module
  have hXqT' : D o q T' = (-((j : ℚ) + 1)) • U := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT', hproj, map_sum]
    simp only [map_smul]
    rw [hS K, hXqK, map_zero, smul_zero, zero_add, hU, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]

  have hHpU : (D o o - D p p) U = (1 : ℚ) • U := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hU, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, eig_pow _ _ (-1) _ hHpYq _ (eig_pow _ _ 1 0 hHpXq T hHpT (k + 1)) k, smul_smul, smul_smul]
    congr 1; push_cast; ring
  have hXpU : (D o p ^ K) U = 0 := by
    apply hB o ho p hp (2 * K + 1 : ℤ)
    · rw [← LinearMap.sub_apply, eig_pow _ _ 2 1 hHpXp U hHpU K]; congr 1; push_cast; ring
    · push_cast; omega
  have hP : (-D o q) * D o p = D o p * (-D o q) := by rw [neg_mul, mul_neg, rXqXp]
  have hf : ∀ l : ℕ, D p q ((D p o ^ (l + 1)) ((D o p ^ (l + 1)) T')) =
      (D p o ^ (l + 1 + 1)) ((D o p ^ (l + 1)) U) +
        (((l : ℚ) + 1) * ((l : ℚ) + j + 2)) • (D p o ^ (l + 1)) ((D o p ^ l) U) := by
    intro l
    have e1 := LinearMap.congr_fun (Commute.pow_right rZYp (l + 1)).eq ((D o p ^ (l + 1)) T')
    simp only [Module.End.mul_apply] at e1
    have c := LinearMap.congr_fun (Commute.pow_right rXqXp l).eq T'
    simp only [Module.End.mul_apply] at c
    rw [e1, comm_pow_apply _ _ _ rZXp hP, hZT', LinearMap.neg_apply, c, hXqT', map_smul, neg_smul, neg_neg,
      sl2_Xpow_Y _ _ _ sXYp hHpXp U 1 hHpU l]
    simp only [map_add (f := _), map_smul]
    rw [← pow_succ_apply2 (D p o) (l + 1)]
    push_cast
    module
  have hT5 : ∀ n : ℕ, D p q (∑ l ∈ Finset.range (n + 1), coef j l • (D p o ^ l) ((D o p ^ l) T')) =
      coef j n • (D p o ^ (n + 1)) ((D o p ^ n) U) := by
    intro n
    induction n with
    | zero => simp [hZT']
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add (f := _), ih, map_smul, hf n, smul_add, smul_smul, coef_succ_mul, neg_smul]
      abel
  rw [← hT', hproj, hT5 K, hXpU, map_zero, smul_zero]

end GlobalTheory.LeviCut.RankTwoProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundaries
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz.RedCob

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ τ : Type} {d : ℕ}

variable [PerfectRing k p]

end GlobalTheory.Katz.RedCob

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_lift_self [CharP k p] {σ : Type} (f : MvPowerSeries σ k) :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p f) f := by
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  exact ⟨WittVector.teichmuller p (coeff α f), _root_.GlobalTheory.Katz.coeff_lift p f α,
    by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
omit [CharP k p] [PerfectRing k p] in
private theorem constantCoeff_at2_eq_zero {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) R} {a b : Fin d → MvPowerSeries τ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hf : constantCoeff f = 0) : constantCoeff (_root_.GlobalTheory.Katz.at2 f a b) = 0 := by
  have h : ∀ s, constantCoeff (Sum.elim a b s) = 0 := by
    rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hf

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
private theorem red_at2_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {f' : MvPowerSeries (Fin d ⊕ Fin d) k}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i))
    (hf : _root_.GlobalTheory.Katz.Red p f f') :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.at2 f a b)
      (_root_.GlobalTheory.Katz.at2 f' a' b') := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).1 f f' hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_X' {σ : Type} (s : σ) :
    _root_.GlobalTheory.Katz.Red p (X s : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k))
      (X s) := by
  classical
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  refine ⟨if α = Finsupp.single s 1 then 1 else 0, ?_, ?_⟩
  · rw [coeff_X]; split_ifs <;> simp
  · rw [coeff_X]; split_ifs <;> simp

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_sub_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f - g) (f' - g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v - w, by rw [map_sub, map_sub, hv, hw], by rw [map_sub, map_sub, hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_add_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f + g) (f' + g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v + w, by rw [map_add (f := _), map_add (f := _), hv, hw], by rw [map_add (f := _), map_add (f := _), hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
private theorem at2_mem_intBy_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) (c : WittVector p k)
    (hf : f ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c) :
    _root_.GlobalTheory.Katz.at2 f a b ∈ _root_.GlobalTheory.Katz.intBy p k τ c := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).2 c f hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i


open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.Katz.red_coboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, _root_.GlobalTheory.Katz.Red p g c → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g) (_root_.GlobalTheory.Katz.cob2 μ c) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.swap g) (_root_.GlobalTheory.Katz.swap c)) ∧ (∀ b b', _root_.GlobalTheory.Katz.Red p b b' → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) b) (_root_.GlobalTheory.Katz.cob1 μ b') ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin b) (_root_.GlobalTheory.Katz.lin b')) ∧ (∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i) (_root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c → _root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g ∈ _root_.GlobalTheory.Katz.intBy p k _ c ∧ _root_.GlobalTheory.Katz.swap g ∈ _root_.GlobalTheory.Katz.intBy p k _ c := by
  intro p _ k _ _ _ d μ hμ
  have hL₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.lift p (μ i)) = 0 := fun i =>
    _root_.GlobalTheory.Katz.constantCoeff_lift p (hμ i)
  have hL : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p (μ i)) (μ i) :=
    fun i => red_lift_self (μ i)
  have hop : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k))
      (a' b' : Fin d → MvPowerSeries τ k),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i)) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) →
      (∀ i, constantCoeff (_root_.GlobalTheory.Katz.op
        (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i) = 0) ∧
      ∀ i, _root_.GlobalTheory.Katz.Red p
        (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i)
        (_root_.GlobalTheory.Katz.op μ a' b' i) := by
    intro τ a b a' b' ha₀ hb₀ ha hb
    exact ⟨fun i => constantCoeff_at2_eq_zero ha₀ hb₀ (hL₀ i),
      fun i => red_at2_of_red ha₀ hb₀ ha hb (hL i)⟩
  have hx₁₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x1 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₂₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x2 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₃₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x3 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₁ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x1 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x1 (R := k) i) := fun i => red_X' _
  have hx₂ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x2 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x2 (R := k) i) := fun i => red_X' _
  have hx₃ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x3 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x3 (R := k) i) := fun i => red_X' _
  obtain ⟨h₁₂₀, h₁₂⟩ := hop _ _ _ _ hx₁₀ hx₂₀ hx₁ hx₂
  obtain ⟨h₂₃₀, h₂₃⟩ := hop _ _ _ _ hx₂₀ hx₃₀ hx₂ hx₃
  have hl₀ : ∀ i, constantCoeff (X (Sum.inl i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hr₀ : ∀ i, constantCoeff (X (Sum.inr i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hl : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inl i)) := fun i => red_X' _
  have hr : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inr i)) := fun i => red_X' _
  refine ⟨fun g c hg => ⟨?_, ?_⟩, fun b b' hb => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩,
    fun c g hg => ⟨?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.Katz.cob2
    exact red_sub_divisor (red_add_divisor (red_sub_divisor
      (red_at2_of_red hx₂₀ hx₃₀ hx₂ hx₃ hg)
      (red_at2_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ hg))
      (red_at2_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ hg))
      (red_at2_of_red hx₁₀ hx₂₀ hx₁ hx₂ hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact red_at2_of_red hr₀ hl₀ hr hl hg
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    exact red_sub_divisor (red_sub_divisor
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hL₀ hL).1 b b' hb)
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hl₀ hl).1 b b' hb))
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hr₀ hr).1 b b' hb)
  · unfold _root_.GlobalTheory.Katz.lin _root_.GlobalTheory.Katz.RedV
    unfold _root_.GlobalTheory.Katz.Red at hb
    intro i
    exact hb _
  · exact (hop _ _ _ _ hx₁₀ h₂₃₀ hx₁ h₂₃).2 i
  · exact (hop _ _ _ _ h₁₂₀ hx₃₀ h₁₂ hx₃).2 i
  · unfold _root_.GlobalTheory.Katz.cob2
    exact sub_mem (add_mem (sub_mem
      (at2_mem_intBy_of_red hx₂₀ hx₃₀ hx₂ hx₃ c hg)
      (at2_mem_intBy_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ hx₂₀ hx₁ hx₂ c hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_mem_intBy_of_red hr₀ hl₀ hr hl c hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstOneAddXPowLogEqNsmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul

theorem subst_pow_log (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (m : ℕ) :
    subst (up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B)))
      (PowerSeries.log Q : MvPowerSeries Unit Q)
      = (m : Q) • (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  have h1 : up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B))
      = fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit Q) := by
    funext j
    simp [up]
  have h2 : formalLog (1 + X () : MvPowerSeries Unit Q)
      = (PowerSeries.log Q : MvPowerSeries Unit Q) := by
    rw [formalLog, add_sub_cancel_left, PowerSeries.subst]
    exact congrFun MvPowerSeries.subst_self _
  have h3 := formalLog_pow m (g := (1 + X () : MvPowerSeries Unit Q)) (by simp)
  rw [h2] at h3
  rw [h1, Nat.cast_smul_eq_nsmul, ← h3]
  rfl

end GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧ (∀ (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (i j : ℤ), cup q (rootClass i ζ) (rootClass j ζ) = (rootClass (i + j) ζ).cast (by ring) rfl ∧ rootClass 0 ζ = one q (sch.obj X)) := by
  first
  | exact @GlobalTheory.EtC.CupGen.main
  | exact GlobalTheory.EtC.CupGen.main
  | (intros; apply GlobalTheory.EtC.CupGen.main <;> assumption)
end

