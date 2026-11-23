module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTowerStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧ ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  first | exact @GlobalTheory.ConvSer.exists_torsion_tower | exact GlobalTheory.ConvSer.exists_torsion_tower | (intros; apply GlobalTheory.ConvSer.exists_torsion_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolynomialTorsionCharacterLevel
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem ev_pow_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ : Type) [Fintype σ] (x : σ → K) (hx : ∀ i, ‖x i‖ < 1) (S : MvPowerSeries σ K)
    (hS : Intg S) (k : ℕ) : ev (S ^ k) x = ev S x ^ k := by
  obtain ⟨-, halg, hC, -⟩ := _root_.GlobalTheory.ConvSer.ev_algebra K σ x hx
  obtain ⟨-, -, hpow, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ
  have hB : Bdd S := (hpow S 0).2.2 hS
  induction k with
  | zero => simpa using hC 1
  | succ k ih => rw [pow_succ, (halg _ _ ((hpow S k).2.1 hB) hB).2.2, ih, pow_succ]

theorem exists_intg_polynomial_level (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K) (hF : Intg F.toPowerSeries)
    (t : ℕ → K) (ht : ∀ n, ‖t n‖ < 1) (h0 : t 0 = 0) (h1 : t 1 ≠ 0)
    (hp : ∀ n, ev1 (nMul F p) (t (n + 1)) = t n) (n : ℕ) (ζ : K) (hζ : ζ ^ (p ^ n) = 1) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧
      ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hord := (_root_.GlobalTheory.ConvSer.tower_exact_order K p F hF t ht h0 h1 hp).2.2 n
  obtain ⟨-, -, hnorm, hadd, -⟩ := (_root_.GlobalTheory.ConvSer.nMul_point K F hF).2 (t n) (ht n)
  set x : ZMod (p ^ n) → K := fun i => ev1 (nMul F i.val) (t n) with hx
  have hxlt : ∀ i, ‖x i‖ < 1 := fun i => (hnorm i.val).1.trans_lt (ht n)
  have hinj : Function.Injective x := by
    intro i j hij
    have := (hord _ _).1 hij
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 this
    simpa using h2
  have hxadd : ∀ i j, x (i + j) = ev F.toPowerSeries ![x i, x j] := by
    intro i j
    simp only [hx]
    rw [hadd, hord, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hχ : ∀ i j : ZMod (p ^ n), ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
    intro i j
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]
  have hcard : (Finset.univ.image x).card = Fintype.card (ZMod (p ^ n)) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_integral_poly_of_character' K (ZMod (p ^ n)) x (fun i => ζ ^ i.val) hinj hχ (by
    intro k
    have hc := _root_.GlobalTheory.ConvSer.exists_integral_interpolation_two K (Finset.univ.image x) (F.toPowerSeries ^ (k : ℕ))
      (by
        intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact hxlt i)
      (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 _ _).1 hF)
    rw [hcard] at hc
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨c, hc1, fun i j => ?_⟩
    rw [← hc2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hxadd,
      ev_pow_of_intg K (Fin 2) _ _ _ hF]
    intro l
    fin_cases l
    · exact hxlt i
    · exact hxlt j)
  refine ⟨g, hg, fun j => ?_⟩
  have := hgx (j : ZMod (p ^ n))
  simp only [hx, ZMod.val_natCast] at this
  rw [← pow_eq_pow_mod _ hζ] at this
  rw [← this, (hord j (j % p ^ n)).2 (Nat.mod_modEq _ _).symm]

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormFormalGroupHeightOneTorsionTower
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.TowerNorm

theorem norm_natCast_eq_one {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (h : ‖(p : K)‖ < 1) {j : ℕ} (hj : ¬ p ∣ j) : ‖(j : K)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K j) ?_
  by_contra hlt
  push_neg at hlt
  have hc : IsCoprime (p : ℤ) (j : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hj)
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (u : K) * (p : K) + (v : K) * (j : K) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huv
  have h2 := IsUltrametricDist.norm_add_le_max ((u : K) * (p : K)) ((v : K) * (j : K))
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have hu := IsUltrametricDist.norm_intCast_le_one K u
  have hv := IsUltrametricDist.norm_intCast_le_one K v
  have a1 : ‖(u : K)‖ * ‖(p : K)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hu (norm_nonneg _) h
  have a2 : ‖(v : K)‖ * ‖(j : K)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hv (norm_nonneg _) hlt
  exact absurd h2 (not_le.2 (max_lt a1 a2))

theorem prod_range_mul (g : ℕ → ℝ) (N b : ℕ) :
    ∏ j ∈ Finset.range (N * b), g j =
      ∏ a ∈ Finset.range N, ∏ c ∈ Finset.range b, g (a + N * c) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_range_succ, add_comm (N * b) a]

theorem prod_range_ite (f : ℕ → ℝ) (c : ℝ) {M : ℕ} (hM : 0 < M) :
    ∏ j ∈ Finset.range M, (if j = 0 then c else f j) = c * ∏ j ∈ Finset.Ico 1 M, f j := by
  rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hM]
  simp only [if_true, zero_add]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have := (Finset.mem_Ico.1 hj).1
  rw [if_neg (by omega)]

section

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem prod_fibre (f : PowerSeries K) (p : ℕ) (hp : 0 < p) (hf : Intg f)
    (h0 : PowerSeries.constantCoeff f = 0)
    (h1 : ‖PowerSeries.coeff p f‖ = 1) (hl : ∀ k < p, ‖PowerSeries.coeff k f‖ < 1)
    (c : K) (hc : ‖c‖ < 1) (x : ℕ → K) (T : Finset ℕ) (hT : T.card = p)
    (hinj : Set.InjOn x T) (hx : ∀ b ∈ T, ‖x b‖ < 1 ∧ ev1 f (x b) = c) :
    ∏ b ∈ T, ‖x b‖ = ‖c‖ := by
  classical
  obtain ⟨A1, A2, A3, A4, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  have hC : Intg (PowerSeries.C c : PowerSeries K) := (A4 c).2.1 hc.le
  have hI : Intg (f - PowerSeries.C c) := (A1 _ _ hf hC).2.1
  have hcard : (T.image x).card = p := by rw [Finset.card_image_of_injOn hinj, hT]
  have key := (_root_.GlobalTheory.ConvSer.norm_coeff_le_prod_zeros K (f - PowerSeries.C c) (T.image x) hI (by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    refine ⟨(hx b hb).1, ?_⟩
    obtain ⟨-, B2, B3, -⟩ := _root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K (x b) (hx b hb).1
    rw [(B2 _ _ ((A3 f 0).2.2 hf) ((A3 _ 0).2.2 hC)).2.1, B3, (hx b hb).2, sub_self])).2
  rw [hcard, Finset.prod_image hinj] at key
  have hz : PowerSeries.coeff 0 (f - PowerSeries.C c) = -c := by
    simp [h0]
  have hn : ∀ k, k ≠ 0 → PowerSeries.coeff k (f - PowerSeries.C c) = PowerSeries.coeff k f := by
    intro k hk
    simp [PowerSeries.coeff_C, hk]
  rw [key, hz, norm_neg]
  · rw [hn p hp.ne', h1]
  · intro k hk
    by_cases hk0 : k = 0
    · rw [hk0, hz, norm_neg]; exact hc
    · rw [hn k hk0]; exact hl k hk

theorem prod_zero_fibre (f : PowerSeries K) (p : ℕ) (hp : 0 < p) (hf : Intg f)
    (h0 : PowerSeries.constantCoeff f = 0)
    (h1 : ‖PowerSeries.coeff p f‖ = 1) (hl : ∀ k < p, ‖PowerSeries.coeff k f‖ < 1)
    (x : ℕ → K) (T : Finset ℕ) (hT : T.card = p - 1)
    (hinj : Set.InjOn x T) (hx : ∀ b ∈ T, ‖x b‖ < 1 ∧ ev1 f (x b) = 0 ∧ x b ≠ 0) :
    ∏ b ∈ T, ‖x b‖ = ‖PowerSeries.coeff 1 f‖ := by
  classical
  obtain ⟨A1, A2, A3, A4, A5, -, -, -, -, A10⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  set h : PowerSeries K := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f with hh
  have hco : ∀ k, PowerSeries.coeff k h = PowerSeries.coeff (k + 1) f := by
    intro k; simp [hh]
  have hI : Intg h := ((A10 h).1).2 fun n => by rw [hco]; exact ((A10 f).1).1 hf _
  have hX : Intg (PowerSeries.X : PowerSeries K) := (A5 ()).1
  have hfe : f = PowerSeries.X * h := by
    have := PowerSeries.eq_X_mul_shift_add_const f
    rw [h0, map_zero, add_zero] at this
    exact this
  have hcard : (T.image x).card = p - 1 := by rw [Finset.card_image_of_injOn hinj, hT]
  have key := (_root_.GlobalTheory.ConvSer.norm_coeff_le_prod_zeros K h (T.image x) hI (by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    refine ⟨(hx b hb).1, ?_⟩
    obtain ⟨-, B2, -, B4, -⟩ := _root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K (x b) (hx b hb).1
    have e := (B2 _ _ ((A3 _ 0).2.2 hX) ((A3 _ 0).2.2 hI)).2.2
    rw [← hfe, B4, (hx b hb).2.1] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (hx b hb).2.2)).2
  rw [hcard, Finset.prod_image hinj] at key
  rw [key, hco]
  · rw [hco, Nat.sub_add_cancel hp, h1]
  · intro k hk
    rw [hco]; exact hl _ (by omega)

end

theorem tower_norm : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ‖t 1‖ ^ (p - 1) = ‖(p : K)‖ ∧ ‖(p : K)‖ < 1 ∧ (∀ n j, ¬ p ^ n ∣ j → ‖t 1‖ ≤ ‖ev1 (nMul F j) (t n)‖) ∧ ∀ n, ∏ j ∈ Finset.Ico 1 (p ^ n), ‖ev1 (nMul F j) (t n)‖ = ‖(p : K)‖ ^ n := by
  intro K _ _ _ _ _ p hpf F hF h1 hl t ht ht0 ht1 htt
  have hp : p.Prime := hpf.out
  obtain ⟨M1, -⟩ := _root_.GlobalTheory.ConvSer.nMul_props K F
  obtain ⟨P0, P⟩ := _root_.GlobalTheory.ConvSer.nMul_point K F hF
  obtain ⟨O1, O2, O3⟩ := _root_.GlobalTheory.ConvSer.tower_exact_order K p F hF t ht ht0 ht1 htt
  have hpn : ‖(p : K)‖ < 1 := by
    have := hl 1 hp.one_lt
    rwa [(M1 p).2] at this
  have hlt : ∀ n j, ‖ev1 (nMul F j) (t n)‖ < 1 := fun n j =>
    lt_of_le_of_lt ((P _ (ht n)).2.2.1 j).1 (ht n)
  have hunit : ∀ n j, ¬ p ∣ j → ‖ev1 (nMul F j) (t n)‖ = ‖t n‖ := fun n j hj =>
    ((P _ (ht n)).2.2.1 j).2 (norm_natCast_eq_one hp hpn hj)
  have hdown : ∀ n j, ev1 (nMul F p) (ev1 (nMul F j) (t (n + 1))) = ev1 (nMul F j) (t n) :=
    fun n j => by rw [(P _ (ht (n + 1))).2.2.2.2.1, O1]
  have hbot : ∀ n j, ev1 (nMul F (p ^ n * j)) (t (n + 1)) = ev1 (nMul F j) (t 1) :=
    fun n j => by rw [add_comm n 1, O2]
  have hnd : ∀ b ∈ Finset.Ico 1 p, ¬ p ∣ b := fun b hb =>
    Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.1 hb).1 (Finset.mem_Ico.1 hb).2
  have hB : ∏ b ∈ Finset.Ico 1 p, ‖ev1 (nMul F b) (t 1)‖ = ‖(p : K)‖ := by
    rw [← (M1 p).2]
    refine prod_zero_fibre (nMul F p) p hp.pos (P0 p) (M1 p).1 h1 hl
      (fun b => ev1 (nMul F b) (t 1)) _ (by simp) ?_ ?_
    · intro b hb b' hb' e
      have := (O3 1 b b').1 e
      rw [pow_one] at this
      exact Nat.ModEq.eq_of_lt_of_lt this (Finset.mem_Ico.1 hb).2 (Finset.mem_Ico.1 hb').2
    · intro b hb
      refine ⟨hlt _ _, ?_, ?_⟩
      · have := hdown 0 b
        rw [zero_add] at this
        rw [this, ht0]
        have e := ((P 0 (by simp)).2.2.1 b).1
        rw [norm_zero] at e
        exact norm_le_zero_iff.1 e
      · rw [← norm_ne_zero_iff, hunit 1 b (hnd b hb), norm_ne_zero_iff]
        exact ht1
  have hA : ∀ n a, ∏ b ∈ Finset.range p, ‖ev1 (nMul F (a + p ^ n * b)) (t (n + 1))‖ =
      ‖ev1 (nMul F a) (t n)‖ := by
    intro n a
    refine prod_fibre (nMul F p) p hp.pos (P0 p) (M1 p).1 h1 hl _ (hlt n a)
      (fun b => ev1 (nMul F (a + p ^ n * b)) (t (n + 1))) _ (by simp) ?_ ?_
    · intro b hb b' hb' e
      have := (O3 (n + 1) _ _).1 e
      have h2 := Nat.ModEq.add_left_cancel' a this
      rw [pow_succ] at h2
      have h3 := Nat.ModEq.mul_left_cancel' (pow_pos hp.pos n).ne' h2
      exact Nat.ModEq.eq_of_lt_of_lt h3 (Finset.mem_range.1 hb) (Finset.mem_range.1 hb')
    · intro b hb
      refine ⟨hlt _ _, ?_⟩
      rw [hdown, O3]
      simp [Nat.ModEq]
  refine ⟨?_, hpn, ?_, ?_⟩
  · rw [← hB, Finset.prod_congr rfl fun b hb => hunit 1 b (hnd b hb)]
    simp
  · intro n
    induction n with
    | zero => intro j hj; simp at hj
    | succ n ih =>
      intro j hj
      by_cases hd : p ^ n ∣ j
      · obtain ⟨j', rfl⟩ := hd
        rw [hbot, hunit 1 j']
        intro h
        exact hj (by rw [pow_succ]; exact Nat.mul_dvd_mul_left _ h)
      · refine (ih j hd).trans ?_
        rw [← hdown]
        exact ((P _ (hlt _ _)).2.2.1 p).1
  · intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hN : 0 < p ^ n := pow_pos hp.pos n
      have e1 := prod_range_ite (fun j => ‖ev1 (nMul F j) (t (n + 1))‖) 1 (pow_pos hp.pos (n + 1))
      rw [one_mul] at e1
      rw [← e1, pow_succ p n, prod_range_mul, pow_succ', ← ih, ← prod_range_ite _ _ hN]
      refine Finset.prod_congr rfl fun a _ => ?_
      by_cases ha : a = 0
      · subst ha
        rw [if_pos rfl, ← hB, ← one_mul (∏ b ∈ Finset.Ico 1 p, _), ← prod_range_ite _ _ hp.pos]
        refine Finset.prod_congr rfl fun b _ => ?_
        by_cases hb : b = 0
        · simp [hb]
        · rw [if_neg hb, zero_add, if_neg (Nat.mul_ne_zero hN.ne' hb), hbot]
      · rw [if_neg ha, ← hA n a]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [if_neg (by omega)]

end GlobalTheory.ConvSer.TowerNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDetVectorMultiplierShiftPlus
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem prod_add_ite_shift {n : ℕ} (ν : Fin n → ℂ) (s : Fin n) (u : ℂ) :
    (∏ t, (u + ν t + if t = s then 1 else 0)) =
      (∏ t, (u + ν t)) + ∏ t ∈ Finset.univ.erase s, (u + ν t) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun t => u + ν t) (Finset.mem_univ s)]
  have : ∏ t ∈ Finset.univ.erase s, (u + ν t + if t = s then 1 else 0) =
      ∏ t ∈ Finset.univ.erase s, (u + ν t) :=
    Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  rw [this]; simp only [if_true]; ring

theorem qdet_vector_multiplier_shift_plus : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), GlRel E → GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t + if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  cases n with
  | zero => exact j.elim0
  | succ m =>
  let M : (Fin (m + 1) → Fin (m + 1) → Module.End ℂ W) → Module.End ℂ (Fin (m + 1) → W) :=
    fun B => LinearMap.pi fun a => ∑ k, (B a k).comp (LinearMap.proj k)
  have hM : ∀ B y a, M B y a = ∑ k, B a k (y k) := by
    intro B y a
    simp [M, LinearMap.sum_apply]
  let Ω := M (fun l a => E' a l)
  let X : ℂ → Module.End ℂ (Fin (m + 1) → W) := fun u => M (fun a k =>
    ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1))
  choose c hc using fun a k : Fin (m + 1) =>
    _root_.GlobalTheory.qminor_polyMap (Module.End ℂ W) (m + 1) m E' (Fin.succAbove a) (Fin.succAbove k) 1
  have hXc : ∀ u, X u = ∑ i ∈ Finset.range (m + 1), u ^ i •
      M (fun a k => ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • c a k i) := by
    intro u
    refine LinearMap.ext fun y => funext fun a => ?_
    simp only [X, hM, hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      Pi.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  have hΩ : ∀ (u : ℂ) (y : Fin (m + 1) → W),
      u • X u y + Ω (X u y) = (∏ s, (u + ν s)) • y := by
    intro u y
    funext l
    have h1 : (u • X u y + Ω (X u y)) l = ∑ a, Tm E' u a l (X u y a) := by
      simp only [Pi.add_apply, Pi.smul_apply, Ω, hM, Tm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp [Finset.smul_sum]
      · intro b _ hb; simp [hb]
      · simp
    have h2 : ∀ k : Fin (m + 1), ∑ a : Fin (m + 1), Tm E' u a l ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k)) = if l = k then qdet E' u (y k) else 0 := by
      intro k
      have := LinearMap.congr_fun (_root_.GlobalTheory.capelli_left_comatrix (Module.End ℂ W) m E' hE' u k l) (y k)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
      simp only [LinearMap.smul_apply, map_smul]
      rw [this]
      split_ifs <;> simp
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [X, hM, map_sum]
    rw [Finset.sum_comm]
    simp only [h2]
    simp [hq]
  obtain ⟨v, hv, hXv⟩ := _root_.GlobalTheory.exists_sum_eigen_split_of_resolvent (Fin (m + 1) → W) (m + 1) Ω X (m + 1) _ ν hν hXc hΩ
    (Pi.single j w)
  have hqι : ∀ u y, qdet E u (ι y) = (∏ s, (u + ν s)) • ι y := by
    intro u y
    rw [← map_smul, ← hq]
    exact (_root_.GlobalTheory.qminor_intertwine V W (m + 1) (m + 1) E E' ι hι id id u y).symm
  have hmu : ∀ (u : ℂ) (y : Fin (m + 1) → W), qdet E u (∑ a, x a (ι (y a))) =
      (∏ s, (u + ν s)) • (∑ a, x a (ι (y a))) + ∑ a, x a (ι (X u y a)) := by
    intro u y
    have h3 : ∀ k : Fin (m + 1), qdet E u (x k (ι (y k))) = (∏ s, (u + ν s)) • x k (ι (y k)) +
        ∑ a : Fin (m + 1), x a (ι ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k))) := by
      intro k
      have := LinearMap.congr_fun (GlobalTheory.T.capelliDet_mul_vectorType (Module.End ℂ V) m E x hE hx u k) (ι (y k))
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
        LinearMap.add_apply, hqι, map_smul] at this
      rw [this]
      simp only [LinearMap.smul_apply, map_smul, _root_.GlobalTheory.qminor_intertwine V W (m + 1) m E E' ι hι]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, h3, Finset.sum_add_distrib, Finset.smul_sum, X, hM]
    rw [Finset.sum_comm]
  refine ⟨v, ?_, fun s u => ?_⟩
  · rw [Finset.sum_comm]
    have : ∀ a, ∑ s, x a (ι (v s a)) = x a (ι ((Pi.single j w : Fin (m + 1) → W) a)) := by
      intro a
      rw [hv]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    simp only [this]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  · rw [hmu, hXv, prod_add_ite_shift, add_smul]
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum]

end GlobalTheory
end

