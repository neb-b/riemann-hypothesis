module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorTypeStatement
section
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_mul_vectorType : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A), GlRel E → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (u : ℂ) (j : Fin (m + 1)), qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  first | exact @GlobalTheory.qdet_mul_vector | exact GlobalTheory.qdet_mul_vector | (intros; apply GlobalTheory.qdet_mul_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTower
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  obtain ⟨-, -, -, -, hX, -, hsub, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  induction n with
  | zero =>
    rw [nMul_zero]
    intro ν
    simp
  | succ n ih =>
    rw [nMul_succ]
    have hc : PowerSeries.constantCoeff (nMul F n) = 0 := ((_root_.GlobalTheory.ConvSer.nMul_props K F).1 n).1
    refine (hsub (Fin 2) ![nMul F n, PowerSeries.X] F.toPowerSeries ?_ ?_).1 hF
    · intro j
      fin_cases j
      · exact ih
      · exact (hX ()).1
    · intro j
      fin_cases j
      · exact hc
      · exact PowerSeries.constantCoeff_X

theorem exists_torsion_tower (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (hp : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (hlt : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧
      ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  classical
  have hpr : p.Prime := Fact.out
  have hI := intg_nMul_of_intg K F hF p
  set h := nMul F p with hh
  obtain ⟨-, -, hpow, -, -, -, -, -, -, hiff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  have hev := fun (x : K) (hx : ‖x‖ < 1) => _root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K x hx
  have hbdd : ∀ f : PowerSeries K, Intg f → Bdd f := fun f hf => (hpow f 0).2.2 hf
  have hcoef : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1 := (hiff h).1.1 hI
  have h0 : PowerSeries.coeff 0 h = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ((_root_.GlobalTheory.ConvSer.nMul_props K F).1 p).1
  have h0c : PowerSeries.constantCoeff h = 0 := ((_root_.GlobalTheory.ConvSer.nMul_props K F).1 p).1
  have h1 : PowerSeries.coeff 1 h = (p : K) := ((_root_.GlobalTheory.ConvSer.nMul_props K F).1 p).2
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have hz : ‖(0 : K)‖ < 1 := by simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hzero⟩ := hev 0 hz

  have hstep : ∀ c : {c : K // ‖c‖ < 1}, ∃ y : {y : K // ‖y‖ < 1}, ev1 h y = c := by
    rintro ⟨c, hc⟩
    have hIc : Intg (h - PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rcases n with _ | n
      · simp [h0c, hc.le]
      · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), sub_zero]
        exact hcoef _
    obtain ⟨y, hy, hy0⟩ := _root_.GlobalTheory.ConvSer.exists_root_of_weierstrassDegree K (h - PowerSeries.C c) p hpr.pos hIc (by
        rw [map_sub, PowerSeries.coeff_C, if_neg hpr.ne_zero, sub_zero]
        exact hp) (by
        intro k hk
        rcases k with _ | k
        · simpa [h0, h0c] using hc
        · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k), sub_zero]
          exact hlt _ hk)
    refine ⟨⟨y, hy⟩, ?_⟩
    obtain ⟨-, hops, hCe, -⟩ := hev y hy
    have hCI : Intg (PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rw [PowerSeries.coeff_C]
      split_ifs
      · exact hc.le
      · simp
    have e := (hops h (PowerSeries.C c) (hbdd h hI) (hbdd _ hCI)).2.1
    rw [hy0, hCe] at e
    simp only
    linear_combination -e

  set g : PowerSeries K := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) h with hg
  have hgI : Intg g := by
    rw [(hiff _).1]
    intro n
    rw [hg, PowerSeries.coeff_mk]
    exact hcoef _
  have hp1 : 0 < p - 1 := by have := hpr.two_le; omega
  obtain ⟨x, hx, hx0⟩ := _root_.GlobalTheory.ConvSer.exists_root_of_weierstrassDegree K g (p - 1) hp1 hgI (by
      rw [hg, PowerSeries.coeff_mk, Nat.sub_add_cancel hpr.one_lt.le]
      exact hp) (by
      intro k hk
      rw [hg, PowerSeries.coeff_mk]
      exact hlt _ (by omega))
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [hzero, hg, PowerSeries.coeff_mk, h1] at hx0
    exact hp0 hx0
  have hXI : Intg (PowerSeries.X : PowerSeries K) := by
    rw [(hiff _).1]
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs <;> simp
  have hXg : h = PowerSeries.X * g := by
    ext n
    rcases n with _ | n
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hg, PowerSeries.coeff_mk]
  have hxroot : ev1 h x = 0 := by
    obtain ⟨-, hops, -, hXe, -⟩ := hev x hx
    rw [hXg, ((hops _ _ (hbdd _ hXI) (hbdd _ hgI)).2.2), hXe, hx0, mul_zero]
  choose f hf using hstep
  let x0 : {y : K // ‖y‖ < 1} := ⟨x, hx⟩
  refine ⟨fun n => if n = 0 then 0 else ((f^[n - 1] x0 : {y : K // ‖y‖ < 1}) : K), ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs
    · exact hz
    · exact (f^[n - 1] x0).2
  · simp
  · simpa [x0] using hxne
  · intro n
    rcases n with _ | m
    · simpa [x0] using hxroot
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), Function.iterate_succ_apply']
      exact hf _

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrder
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem seq_eq_iff_modEq_of_op {K : Type*} (G : K → K → K) (τ : ℕ → K)
    (hG : ∀ i j, G (τ i) (τ j) = τ (i + j)) (q : ℕ) (hq : 0 < q) (h0 : τ q = τ 0)
    (hord : ∀ {M : Type} [AddMonoid M] (x : M), (∀ d : ℕ, d • x = 0 ↔ τ d = τ 0) →
      addOrderOf x = q) (i j : ℕ) :
    τ i = τ j ↔ i ≡ j [MOD q] := by
  have shift : ∀ a m, τ m = τ 0 → τ (a + m) = τ a := by
    intro a m hm
    rw [← hG a m, hm, hG a 0, Nat.add_zero]
  have mulS : ∀ s, τ s = τ 0 → ∀ n, τ (s * n) = τ 0 := by
    intro s hs n
    induction n with
    | zero => rw [Nat.mul_zero]
    | succ n ih => rw [Nat.mul_succ, shift _ _ hs, ih]
  have cancel : ∀ a k, τ (a + k) = τ a → τ k = τ 0 := by
    intro a k hak
    have e : (q - 1) * a + a = q * a := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt hq)]
    calc τ k = τ (k + q * a) := (shift k _ (mulS q h0 a)).symm
      _ = G (τ (a + k)) (τ ((q - 1) * a)) := by rw [hG, ← e]; congr 1; ac_rfl
      _ = G (τ a) (τ ((q - 1) * a)) := by rw [hak]
      _ = τ (q * a) := by rw [hG, Nat.add_comm, e]
      _ = τ 0 := mulS q h0 a
  classical
  have hex : ∃ r, 0 < r ∧ τ r = τ 0 := ⟨q, hq, h0⟩
  obtain ⟨r, hr, hmin⟩ : ∃ r, (0 < r ∧ τ r = τ 0) ∧ ∀ m < r, ¬ (0 < m ∧ τ m = τ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hdvd : ∀ d, τ d = τ 0 ↔ r ∣ d := by
    intro d
    constructor
    · intro hd
      have hmod : τ (d % r) = τ 0 := by
        have h := shift (d % r) (r * (d / r)) (mulS r hr.2 _)
        rw [Nat.mod_add_div] at h
        rw [← h, hd]
      by_contra hnd
      have hpos : 0 < d % r := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
      exact hmin _ (Nat.mod_lt d hr.1) ⟨hpos, hmod⟩
    · rintro ⟨c, rfl⟩
      exact mulS r hr.2 c
  have hrq : r = q := by
    have h := hord (M := ZMod r) (1 : ZMod r) (fun d => by
      rw [nsmul_eq_mul, mul_one, CharP.cast_eq_zero_iff (ZMod r) r, hdvd])
    rwa [ZMod.addOrderOf_one] at h
  have key : ∀ d, τ d = τ 0 ↔ q ∣ d := by
    intro d; rw [hdvd, hrq]
  wlog hij : i ≤ j generalizing i j with H
  · rw [eq_comm, Nat.ModEq.comm]; exact H j i (by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.modEq_iff_dvd' hij, Nat.add_sub_cancel_left, ← key, eq_comm]
  exact ⟨cancel i k, fun h => shift i k h⟩

theorem tower_exact_order : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → (∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n)) ∧ (∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n)) ∧ ∀ n i j, ev1 (nMul F i) (t n) = ev1 (nMul F j) (t n) ↔ i ≡ j [MOD p ^ n] := by
  intro K _ _ _ p _ F hF t ht ht0 ht1 htp
  have base := (_root_.GlobalTheory.ConvSer.nMul_point K F hF).2
  have hA : ∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n) := by
    intro n j
    rw [← htp n, (base (t (n + 1)) (ht _)).2.2.2.2.1 j p, Nat.mul_comm p j]
  have hB : ∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n) := by
    intro n m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      rw [← Nat.add_assoc, pow_succ', Nat.mul_assoc, hA, ih]
  refine ⟨hA, hB, fun n i j => ?_⟩
  have hτ0 : ev1 (nMul F 0) (t n) = 0 := (base (t n) (ht n)).1
  have hpn : ev1 (nMul F (p ^ n)) (t n) = 0 := by
    have h := hB 0 n 1
    rw [Nat.mul_one, Nat.zero_add, (base (t 0) (ht 0)).2.1, ht0] at h
    exact h
  refine seq_eq_iff_modEq_of_op (fun a b => ev F.toPowerSeries ![a, b])
    (fun d => ev1 (nMul F d) (t n)) (base (t n) (ht n)).2.2.2.1 (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (by simp only [hpn, hτ0]) ?_ i j
  intro M _ x hx
  have hx' : ∀ d : ℕ, d • x = 0 ↔ ev1 (nMul F d) (t n) = 0 := by
    intro d; rw [hx d]; simp only [hτ0]
  rcases n with _ | k
  · have h := (hx' 1).2 (by rw [(base (t 0) (ht 0)).2.1, ht0])
    rw [one_nsmul] at h
    subst h
    simp
  · have h1k : ev1 (nMul F (p ^ k)) (t (k + 1)) = t 1 := by
      have h := hB 1 k 1
      rw [Nat.mul_one, Nat.add_comm 1 k, (base (t 1) (ht 1)).2.1] at h
      exact h
    exact addOrderOf_eq_prime_pow (fun h => ht1 (by rw [← h1k]; exact (hx' _).1 h)) ((hx' _).2 hpn)

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet
section
open Formalism.REAL Finset

namespace GlobalTheory.CapelliNegT


open Finset in
theorem _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), _root_.Formalism.REAL.GlRel E →
      _root_.Formalism.REAL.GlRel (fun a b => -E b a) ∧
        ∀ u : ℂ, _root_.Formalism.REAL.qdet (fun a b => -E b a) u = ((-1 : ℂ) ^ n) • _root_.Formalism.REAL.qdet E ((n : ℂ) - 1 - u) := by
  intro A _ _ n E hE
  refine ⟨?_, fun u => ?_⟩
  · unfold _root_.Formalism.REAL.GlRel at hE ⊢
    intro a b c d
    have h := hE b a d c
    rw [neg_mul_neg, neg_mul_neg, h]
    simp only [@eq_comm _ a d, @eq_comm _ c b]
    split_ifs <;> abel
  · have hrow : ∀ v : ℂ, _root_.Formalism.REAL.qdet E v = _root_.PI.qminorRow E id id v := by
      intro v
      have key : _root_.PI.RowForm := _root_.quantum_minor_row_form
      unfold _root_.PI.RowForm at key
      exact key A n n E hE id id v
    have hM : ∀ (x : ℂ) (a b : Fin n),
        _root_.Formalism.REAL.Tm (fun a b => -E b a) x a b = -_root_.Formalism.REAL.Tm E (-x) b a := by
      intro x a b
      unfold _root_.Formalism.REAL.Tm
      by_cases h : a = b
      · subst h
        simp only [if_true, map_neg]
        abel
      · simp only [h, Ne.symm h, if_false]
        abel
    have hneg : ∀ g : Fin n → A, (List.ofFn fun k => -g k).prod = (-1) ^ n * (List.ofFn g).prod := by
      intro g
      have hl : (List.ofFn fun k => -g k) = (List.ofFn g).map Neg.neg := by
        rw [List.map_ofFn]
        rfl
      rw [hl, List.prod_map_neg, List.length_ofFn]
    have harg : ∀ k : Fin n, -(u - ((k : ℕ) : ℂ)) = (n : ℂ) - 1 - u - n + 1 + ((k : ℕ) : ℂ) := by
      intro k
      ring
    rw [hrow]
    unfold _root_.Formalism.REAL.qdet _root_.Formalism.REAL.qminor _root_.PI.qminorRow
    rw [Algebra.smul_def, map_pow, map_neg, map_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hM, hneg, harg, id]
    rw [← mul_assoc, ← mul_assoc, ((Commute.neg_one_right _).pow_right n).eq]

end GlobalTheory.CapelliNegT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevEAddTwo
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

open Finset in
open scoped InnerProductSpace in
private lemma adMat_conjTranspose_eq_adMat_swap {n : ℕ} (a b : Fin n) :
    (_root_.GlobalTheory.CasKAdjoint.adMat a b).conjTranspose = _root_.GlobalTheory.CasKAdjoint.adMat b a := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.CasKAdjoint.adMat, Prod.mk.injEq, star_sub, apply_ite star,
    star_one, star_zero]
  congr 1
  · exact if_congr ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃.symm⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂.symm, h₁⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂.symm, h₁⟩⟩ rfl rfl

open Finset in
open scoped InnerProductSpace in
private lemma sum_adMat_apply_first_index_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (a b : Fin n) (x : Fin n × Fin n → M) (i : Fin n × Fin n) :
    ∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j =
      (if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0) := by
  obtain ⟨i₁, i₂⟩ := i
  simp only [_root_.GlobalTheory.CasKAdjoint.adMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and]

open Finset in
open scoped InnerProductSpace in
private lemma norm_ite_zero_sq {M : Type} [NormedAddCommGroup M] (p : Prop) [Decidable p] (y : M) :
    ‖if p then y else 0‖ ^ 2 = if p then ‖y‖ ^ 2 else 0 := by
  split_ifs <;> simp

open Finset in
open scoped InnerProductSpace in
private lemma sum_norm_sq_adMat_mulVec_le {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} (a b : Fin n) (x : Fin n × Fin n → M) :
    ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 ≤
      2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2 := by
  simp_rw [sum_adMat_apply_first_index_smul]
  calc ∑ i : Fin n × Fin n, ‖(if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0)‖ ^ 2
      ≤ ∑ i : Fin n × Fin n, (2 * ‖if i.1 = a then x (b, i.2) else 0‖ ^ 2
          + 2 * ‖if i.2 = b then x (i.1, a) else 0‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_sub_le (if i.1 = a then x (b, i.2) else 0) (if i.2 = b then x (i.1, a) else 0)
        nlinarith [norm_nonneg ((if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0)),
          sq_nonneg (‖if i.1 = a then x (b, i.2) else 0‖ - ‖if i.2 = b then x (i.1, a) else 0‖)]
    _ = 2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2 := by
        simp only [norm_ite_zero_sq, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_prod_type]
        rw [Finset.sum_comm (f := fun x_1 y => if y = b then ‖x (x_1, a)‖ ^ 2 else 0)]
        simp

open Finset in
open scoped InnerProductSpace in
private lemma sum_eq_sign_norm_sq_adMat_mulVec_le {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} (ε : Fin n → Bool) (x : Fin n × Fin n → M) :
    (∑ a, ∑ b, if ε a = ε b then ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 else 0) ≤
      (8 * (n : ℝ)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have hS : ∑ j, ‖x j‖ ^ 2 = ∑ b, ∑ k, ‖x (b, k)‖ ^ 2 := Fintype.sum_prod_type _
  have hS' : ∑ j, ‖x j‖ ^ 2 = ∑ a, ∑ k, ‖x (k, a)‖ ^ 2 := by
    rw [hS, Finset.sum_comm]
  have h0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ a, ∑ b, if ε a = ε b then ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 else 0)
      ≤ ∑ a : Fin n, ∑ b : Fin n, (2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · exact sum_norm_sq_adMat_mulVec_le a b x
        · positivity
    _ = 4 * n * ∑ j, ‖x j‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [← hS, ← hS']
        ring
    _ ≤ (8 * (n : ℝ)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * n) h0)
            (by linarith : (0:ℝ) ≤ 16 * n - 1)]

open Finset in
open scoped InnerProductSpace in
private lemma sum_adMat_apply_second_index_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (a b : Fin n) (y : Fin n × Fin n → M) (j : Fin n × Fin n) :
    ∑ i, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • y i =
      (if j.1 = b then y (a, j.2) else 0) - (if j.2 = a then y (j.1, b) else 0) := by
  obtain ⟨j₁, j₂⟩ := j
  simp only [_root_.GlobalTheory.CasKAdjoint.adMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, eq_comm]

open Finset in
open scoped InnerProductSpace in
private lemma sum_abs_shifted_weight_sub_le_add_two {n : ℕ} (ω μ : Fin n → ℝ) (a b : Fin n) :
    ∑ c, |ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c| ≤ ∑ c, |ω c - μ c| + 2 := by
  calc ∑ c, |ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c|
      ≤ ∑ c, (|ω c - μ c| + ((if c = a then 1 else 0) + (if c = b then 1 else 0))) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 : (0:ℝ) ≤ if c = a then 1 else 0 := by split_ifs <;> norm_num
        have h2 : (0:ℝ) ≤ if c = b then 1 else 0 := by split_ifs <;> norm_num
        rw [show ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c
          = (ω c - μ c) + ((if c = a then 1 else 0) - (if c = b then 1 else 0)) by ring]
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_le]; constructor <;> linarith
    _ = ∑ c, |ω c - μ c| + 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp; norm_num

open Finset in
open scoped InnerProductSpace in
private lemma isWeight_shift_of_glRel {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ M} (hG : _root_.Formalism.REAL.GlRel E) {ω : Fin n → ℝ} {x : M} (hx : _root_.Formalism.REAL.IsWeight E ω x)
    (a b : Fin n) :
    _root_.Formalism.REAL.IsWeight E (fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) (E a b x) := by
  intro c
  have h := LinearMap.congr_fun (hG c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul, ite_apply, LinearMap.zero_apply,
    @eq_comm _ b c] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases ha : c = a <;> by_cases hb : c = b
  · subst ha; subst hb; simp
  · subst ha; simp [hb, add_smul]; abel
  · subst hb; simp [ha, sub_smul]; abel
  · simp [ha, hb]


open Finset in
open scoped InnerProductSpace in
theorem _root_.GlobalTheory.lev_E_add_two : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (j : ℕ) (w : M), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.IsUnitary ε E → _root_.BranchingSupport.Lev ε E μ j w → ∀ a b, _root_.BranchingSupport.Lev ε E μ (j + 2) (E a b w) := by
  intro M _ _ n ε E μ j w hG hU hw a b
  unfold _root_.BranchingSupport.Lev _root_.BranchingSupport.WtNear at hw ⊢
  obtain ⟨hC, hS⟩ := hw
  refine ⟨?_, ?_⟩
  · have hK := _root_.Formalism.REAL.isUnitary_kUnit ε E hU
    have h := _root_.GlobalTheory.TensOp.casKLe_tensor_operator M n ε E M (Fin n × Fin n) E (fun i => E i.1 i.2)
      _root_.GlobalTheory.CasKAdjoint.adMat _ (8 * n) hK hK (by positivity) (by positivity)
      (fun a b _ => adMat_conjTranspose_eq_adMat_swap a b)
      (sum_eq_sign_norm_sq_adMat_mulVec_le ε)
      (fun a b _ k v => by
        have hs := sum_adMat_apply_second_index_smul a b (fun i => E i.1 i.2 v) k
        simp only at hs ⊢
        rw [hs]
        have h := LinearMap.congr_fun (hG a b k.1 k.2) v
        simp only [LinearMap.sub_apply, Module.End.mul_apply, ite_apply, LinearMap.zero_apply,
          @eq_comm _ b k.1] at h
        rw [sub_eq_iff_eq_add'] at h
        rw [h]
        split_ifs <;> simp)
      w hC (a, b)
    convert h using 1
    push_cast
    ring
  · rw [← Submodule.mem_comap]
    refine Submodule.span_le.2 ?_ hS
    rintro x ⟨ω, hd, hx⟩
    exact Submodule.subset_span ⟨_, (sum_abs_shifted_weight_sub_le_add_two ω _ a b).trans (by push_cast; linarith),
      isWeight_shift_of_glRel hG hx a b⟩

end GlobalTheory
end

