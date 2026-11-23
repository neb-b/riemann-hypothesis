module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorType
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem qdet_mul_vector (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ)
    (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A) (hE : GlRel E)
    (hx : ∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0)
    (u : ℂ) (j : Fin (m + 1)) :
    qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  have h1 := _root_.GlobalTheory.capelli_left_comatrix A m E hE u j j
  rw [if_pos rfl] at h1
  have h2 : ∀ a : Fin (m + 1), qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) * x j
      = x j * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) := by
    intro a
    refine GlobalTheory.T.qminor_commute_of_commute_columns A (m + 1) m E (x j) _ _ _ ?_
    intro c i
    rw [hx, if_neg (Fin.succAbove_ne j i), add_zero]
  have h3 : ∀ a : Fin (m + 1), Tm E u a j * x j = x j * Tm E u a j + x a := by
    intro a
    have h := hx a j j
    rw [if_pos rfl] at h
    unfold Tm
    by_cases haj : a = j
    · simp only [if_pos haj, add_mul, mul_add, h, Algebra.commutes]
      abel
    · simp only [if_neg haj, zero_add, h]
  rw [← h1, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, mul_assoc, h2, ← mul_assoc, h3, add_mul,
    mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundElementaryApply
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.CasKAdjoint

def adMat {n : ℕ} (a b : Fin n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun i j =>
  (if i.1 = a ∧ j = (b, i.2) then 1 else 0) - (if i.2 = b ∧ j = (i.1, a) then 1 else 0)

end GlobalTheory.CasKAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundEmbeddedComponent
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem casKLe_io_component : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  intro M _ _ n ε E N _ _ F io pr c s y hE hF hT hc hy d
  have key := _root_.GlobalTheory.TensOp.casKLe_tensor_operator (N s) n ε (F s) M (Fin n) E
    (fun j => (LinearMap.proj j : (Fin n → M) →ₗ[ℂ] M) ∘ₗ io s)
    (fun a b => Matrix.single a b (1 : ℂ)) c (Real.sqrt n)
    (isUnitary_kUnit ε _ (hF s)) (isUnitary_kUnit ε _ hE) hc (Real.sqrt_nonneg _)
    (by
      intro a b _
      simp [Matrix.conjTranspose_single])
    (by
      intro x
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      have h1 : ∀ a b : Fin n,
          ∑ i, ‖∑ j, (Matrix.single a b (1 : ℂ)) i j • x j‖ ^ 2 = ‖x b‖ ^ 2 := by
        intro a b
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · simp
          · intro j _ hj
            simp [Matrix.single, hj.symm]
          · simp
        · intro i _ hi
          simp [Matrix.single, hi.symm]
        · simp
      calc _ ≤ ∑ _a : Fin n, ∑ b : Fin n, ‖x b‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
            split_ifs
            · exact (h1 a b).le
            · positivity
        _ = _ := by simp)
    (by
      intro a b _ j w
      have h := congrFun (hT.io_comm s a b w) j
      simp only [dualTens] at h
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [h, Finset.sum_eq_single a]
      · by_cases hj : j = b
        · subst hj
          simp
        · simp [hj, Matrix.single, Ne.symm hj]
      · intro i _ hi
        simp [Matrix.single, hi.symm]
      · simp)
    y hy d
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensor
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem kUnit_of_isUnitary_proj {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (h : IsUnitary ε E) : KUnit ε E := by
  intro a b hab u v
  have := h a b u v
  simpa [Formalism.REAL.sgn, hab] using this

theorem casKLe_proj_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε E c w → ∀ s d, CasKLe ε (F s) (c + Real.sqrt n) (pr s (Pi.single d w)) := by
  intro M _ _ n ε E N _ _ F io pr c w hE hF hT hc hw s d
  have key := _root_.GlobalTheory.TensOp.casKLe_tensor_operator M n ε E (N s) (Fin n) (F s)
    (fun j => (pr s) ∘ₗ (LinearMap.single ℂ (fun _ : Fin n => M) j))
    (fun a b => Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) c (Real.sqrt n)
    (kUnit_of_isUnitary_proj hE) (kUnit_of_isUnitary_proj (hF s)) hc (Real.sqrt_nonneg _) ?_ ?_ ?_ w hw d
  · simpa using key
  · intro a b _
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : i = a ∧ j = b
    · simp [h.1, h.2]
    · have h' : ¬ (j = b ∧ i = a) := fun h2 => h ⟨h2.2, h2.1⟩
      simp [h, h']
  · intro x
    rw [Real.sq_sqrt (Nat.cast_nonneg n), Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ∀ b : Fin n, ∑ i, ‖∑ j, (Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) i j • x j‖ ^ 2
        = ‖x a‖ ^ 2 := by
      intro b
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      · intro i _ hi; simp [hi]
      · simp
    calc _ ≤ ∑ _b : Fin n, ‖x a‖ ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          split_ifs
          · exact (h1 b).le
          · positivity
      _ = _ := by simp
  · intro a b _ j v
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.of_apply]
    rw [← hT.pr_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, ← map_add (f := _)]
    congr 1
    funext i
    rw [Finset.sum_eq_single b]
    · simp only [dualTens, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      by_cases h1 : i = j <;> by_cases h2 : i = b <;> by_cases h3 : j = a <;>
        simp_all [sub_eq_add_neg, eq_comm]
    · intro k _ hk; simp [hk]
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegree
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.DiscRoot

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_span_pow (p x : ball K) (n : ℕ) :
    x ∈ Ideal.span {p} ^ n ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : ‖(a : K)‖ ≤ 1 := a.2
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ha
  · intro h
    by_cases hp : (p : K) ^ n = 0
    · rw [← norm_pow, hp, norm_zero, norm_le_zero_iff] at h
      exact ⟨0, Subtype.ext (by simp [h])⟩
    · refine ⟨⟨x / p ^ n, ?_⟩, Subtype.ext ?_⟩
      · change ‖(x : K) / p ^ n‖ ≤ 1
        rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ h (by positivity)
      · simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
        exact div_mul_cancel₀ _ hp

theorem smod_iff (p x y : ball K) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule (ball K) (ball K))] ↔
      ‖(x : K) - y‖ ≤ ‖(p : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow]
  rfl

theorem adicComplete [CompleteSpace K] (p : ball K) (hp : ‖(p : K)‖ < 1) :
    IsAdicComplete (Ideal.span {p}) (ball K) := by
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : K)‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp
  have hH : IsHausdorff (Ideal.span {p}) (ball K) := ⟨fun x hx => by
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      simpa using (smod_iff p x 0 n).1 (hx n)
    exact Subtype.ext (by simpa using this)⟩
  have hP : IsPrecomplete (Ideal.span {p}) (ball K) := ⟨fun f hf => by
    have hc : CauchySeq fun n => (f n : K) := by
      refine cauchySeq_of_le_tendsto_0' (fun n => ‖(p : K)‖ ^ n) (fun n m hnm => ?_) ht
      rw [dist_eq_norm]
      exact (smod_iff p _ _ n).1 (hf hnm)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => (f n).2
    refine ⟨⟨L, hL1⟩, fun n => (smod_iff p _ _ n).2 ?_⟩
    refine le_of_tendsto ((tendsto_const_nhds (x := (f n : K))).sub hL).norm ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact (smod_iff p _ _ n).1 (hf hm)⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem division [CompleteSpace K] (h : PowerSeries K) (d : ℕ) (hd : 0 < d)
    (hi : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff d h‖ = 1)
    (hl : ∀ k < d, ‖PowerSeries.coeff k h‖ < 1) :
    ∃ (q : PowerSeries K) (r : Polynomial K), (∀ n, ‖PowerSeries.coeff n q‖ ≤ 1) ∧
      ‖PowerSeries.coeff 0 q‖ = 1 ∧ r.degree < d ∧ (∀ n, ‖r.coeff n‖ < 1) ∧
      PowerSeries.X ^ d = h * q + (r : PowerSeries K) := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range d)
    (fun k => ‖PowerSeries.coeff k h‖) ⟨0, Finset.mem_range.2 hd⟩
  let g : PowerSeries (ball K) := PowerSeries.mk fun n => ⟨PowerSeries.coeff n h, hi n⟩
  have hg : ∀ n, ((PowerSeries.coeff n g : ball K) : K) = PowerSeries.coeff n h := fun n => by
    simp [g]
  let p : ball K := PowerSeries.coeff k g
  have hp : ‖(p : K)‖ < 1 := by rw [hg]; exact hl k (Finset.mem_range.1 hk)
  set I : Ideal (ball K) := Ideal.span {p} with hI
  have hmem : ∀ x : ball K, x ∈ I ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ := fun x => by
    simpa using mem_span_pow p x 1
  have hlow : ∀ j < d, PowerSeries.coeff j g ∈ I := fun j hj => by
    rw [hmem, hg, hg]; exact hmax j (Finset.mem_range.2 hj)
  have hord : (g.map (Ideal.Quotient.mk I)).order = d := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem, hmem, hg, h1]
      exact not_le.2 hp
    · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
      exact hlow i hi
  have hord' : (g.map (Ideal.Quotient.mk I)).order.toNat = d := by rw [hord]; rfl
  have H : g.IsWeierstrassDivisorAt I := by
    rw [PowerSeries.IsWeierstrassDivisorAt, hord']
    have h0 : PowerSeries.coeff d h ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff d h)⁻¹, ?_⟩ (Subtype.ext ?_)
    · change ‖(PowerSeries.coeff d h)⁻¹‖ ≤ 1
      rw [norm_inv, h1, inv_one]
    · rw [Subring.coe_mul, hg]
      exact mul_inv_cancel₀ h0
  haveI := adicComplete p hp
  have HD := H.isWeierstrassDivisionAt_div_mod (PowerSeries.X ^ d)
  set q := H.div (PowerSeries.X ^ d)
  set r := H.mod (PowerSeries.X ^ d)
  have hdeg : r.degree < d := hord' ▸ HD.degree_lt
  have hgh : g.map (ball K).subtype = h := by
    ext n; simp [hg]
  refine ⟨q.map (ball K).subtype, r.map (ball K).subtype, fun n => ?_, ?_,
    lt_of_le_of_lt (Polynomial.degree_map_le) hdeg, fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff n q).2
  · have e := congrArg (PowerSeries.coeff d) HD.eq_mul_add
    rw [g.eq_X_pow_mul_shift_add_trunc d, add_mul, mul_assoc, map_add (f := _), map_add (f := _),
      PowerSeries.coeff_X_pow_self, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_degree_lt hdeg, add_zero, PowerSeries.coeff_X_pow_mul',
      if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_mul] at e
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at e
    have e2 : PowerSeries.coeff d (((g.trunc d : Polynomial (ball K)) : PowerSeries (ball K)) * q) ∈ I := by
      refine PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) d
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hh
      · exact hlow i hh
      · exact zero_mem _
    have e3 := ((hmem _).1 e2).trans_lt hp
    have e4 := congrArg (fun z : ball K => (z : K)) e
    simp only [PowerSeries.coeff_mk, zero_add, Subring.coe_add, Subring.coe_mul, hg, OneMemClass.coe_one] at e4
    rw [PowerSeries.coeff_map]
    refine le_antisymm (PowerSeries.coeff 0 q).2 (not_lt.1 fun hlt => ?_)
    have e5 := congrArg norm e4
    rw [norm_one] at e5
    refine absurd (e5.le.trans (IsUltrametricDist.norm_add_le_max _ _)) (not_le.2 (max_lt ?_ e3))
    rw [norm_mul, h1, one_mul]
    exact hlt
  · rw [Polynomial.coeff_map]
    by_cases hn : n < d
    · have := HD.coeff_f_sub_r_mem (i := n) (hord'.symm ▸ hn)
      rw [map_sub, PowerSeries.coeff_X_pow, if_neg hn.ne, zero_sub, neg_mem_iff,
        Polynomial.coeff_coe] at this
      exact ((hmem _).1 this).trans_lt hp
    · rw [Polynomial.coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast not_lt.1 hn))]
      simp
  · have := congrArg (PowerSeries.map (ball K).subtype) HD.eq_mul_add
    rw [map_pow, PowerSeries.map_X, map_add (f := _), map_mul, hgh] at this
    rw [this, Polynomial.polynomial_map_coe]

theorem root_small [IsAlgClosed K] (r : Polynomial K) (d : ℕ) (hd : 0 < d) (hr : r.degree < d)
    (hc : ∀ n, ‖r.coeff n‖ < 1) : ∃ x : K, ‖x‖ < 1 ∧ (Polynomial.X ^ d - r).eval x = 0 := by
  have hdeg : (Polynomial.X ^ d - r).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.X ^ d - r)
    (by rw [hdeg]; exact_mod_cast hd.ne')
  refine ⟨x, not_le.1 fun h1 => ?_, hx⟩
  have e : x ^ d = ∑ i ∈ Finset.range d, r.coeff i * x ^ i := by
    have := hx.eq_zero
    rw [Polynomial.eval_sub, sub_eq_zero, Polynomial.eval_pow, Polynomial.eval_X] at this
    rw [this]
    by_cases h0 : r = 0
    · simp [h0]
    exact Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt h0).2 hr) x
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := Finset.range d) ⟨0, Finset.mem_range.2 hd⟩ (fun i => r.coeff i * x ^ i)
  rw [← e, norm_mul, norm_pow, norm_pow] at hle
  have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ d := pow_le_pow_right₀ h1 (Finset.mem_range.1 hi).le
  have h3 : 0 < ‖x‖ ^ i := by positivity
  have h4 := hc i
  nlinarith

end GlobalTheory.ConvSer.DiscRoot

theorem GlobalTheory.ConvSer.exists_root_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  intro K _ _ _ _ h d hd hi h1 hl
  obtain ⟨-, -, hA, -, -, -, -, -, -, hB⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨q, r, hq, hq0, hr, hrc, e⟩ := DiscRoot.division h d hd ((hB h).1.1 hi) h1 hl
  obtain ⟨x, hx, hx0⟩ := DiscRoot.root_small r d hd hr hrc
  refine ⟨x, hx, ?_⟩
  obtain ⟨-, hmul, -, -, hP, -, hI, -⟩ := _root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K x hx
  have hq' : Intg q := (hB q).1.2 hq
  have e2 : ((Polynomial.X ^ d - r : Polynomial K) : PowerSeries K) = h * q := by
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, e]; ring
  have e3 := (hP (Polynomial.X ^ d - r)).2
  rw [hx0, e2, (hmul h q ((hA h 0).2.2 hi) ((hA q 0).2.2 hq')).2.2] at e3
  refine (mul_eq_zero.1 e3).resolve_right fun h0 => ?_
  have := (hI q hq').2.1
  rw [h0, zero_sub, norm_neg, hq0] at this
  exact absurd hx (not_lt.2 this)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscProperties
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_for_point {K : Type} [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  induction n with
  | zero =>
    rw [nMul_zero]
    exact GlobalTheory.BddAlg.intg_zero
  | succ n ih =>
    rw [nMul_succ]
    have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1
    refine GlobalTheory.BddAlg.Le.subst (c := 1) (fun j => ?_) (fun j => ?_) hF
    · fin_cases j
      · exact ih
      · exact hX
    · fin_cases j
      · exact nMul_constantCoeff F n
      · exact PowerSeries.constantCoeff_X

private lemma ev1_zero {K : Type} [NormedField K] (y : K) : ev1 (0 : PowerSeries K) y = 0 := by
  simp [ev1]

theorem nMul_point : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  intro K _ _ _ F hF
  have hI : ∀ n, Intg (nMul F n) := intg_nMul_for_point F hF
  have hB : Bdd F.toPowerSeries := GlobalTheory.BddAlg.bdd_of_intg hF
  have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1

  have hleft : MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_succ F 0
    rw [nMul_zero, nMul_one] at h
    exact h.symm
  have hright : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_add F 1 0
    rw [nMul_zero, nMul_one] at h
    simpa using h
  refine ⟨hI, fun x hx => ?_⟩
  obtain ⟨-, -, -, hevX, -, -, hnorm, hsub, hpair, -, -⟩ := _root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K x hx
  refine ⟨by rw [nMul_zero]; exact ev1_zero x, by rw [nMul_one]; exact hevX, fun j => ?_,
    fun i j => ?_, fun i j => ?_, fun y hy => ?_⟩
  · obtain ⟨-, h1, h2⟩ := hnorm (nMul F j) (hI j)
    have h0 : PowerSeries.coeff 0 (nMul F j) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact nMul_constantCoeff F j
    rw [h0, sub_zero] at h1 h2
    rw [nMul_coeff_one] at h2
    refine ⟨h1, fun hj => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using h1
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hsq : ‖x‖ ^ 2 < ‖x‖ := by nlinarith
      have hjx : ‖(j : K) * x‖ = ‖x‖ := by rw [norm_mul, hj, one_mul]
      set v := ev1 (nMul F j) x
      have hlt : ‖v - (j : K) * x‖ < ‖(j : K) * x‖ := by rw [hjx]; exact lt_of_le_of_lt h2 hsq
      have hdecomp : v = (j : K) * x + (v - (j : K) * x) := by ring
      rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
        max_eq_left hlt.le, hjx]
  · rw [← hpair F.toPowerSeries (nMul F i) (nMul F j) hB (hI i) (hI j)
      (nMul_constantCoeff F i) (nMul_constantCoeff F j), nMul_add]
  · rw [← hsub (nMul F i) (nMul F j) (hI j) (nMul_constantCoeff F j)
      (GlobalTheory.BddAlg.bdd_of_intg (hI i)), nMul_subst_nMul]
  · obtain ⟨-, -, -, hevXy, -, -, -, -, hpairy, -, -⟩ := _root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K y hy
    have hz : Intg (0 : PowerSeries K) := GlobalTheory.BddAlg.intg_zero
    have hc0 : PowerSeries.constantCoeff (0 : PowerSeries K) = 0 := by simp
    have hcX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
    constructor
    · have h := hpairy F.toPowerSeries 0 PowerSeries.X hB hz hX hc0 hcX
      rw [hleft, hevXy, ev1_zero] at h
      exact h.symm
    · have h := hpairy F.toPowerSeries PowerSeries.X 0 hB hX hz hcX hc0
      rw [hright, hevXy, ev1_zero] at h
      exact h.symm

end GlobalTheory.ConvSer
end

