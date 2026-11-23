module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0003
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsWtOnIffOfTorus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AddCharMemValuationSubring
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FourierChainCompare

section Duality

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]

variable [Fintype A] [Fintype B]


end Duality

section Fourier

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]

end Fourier

section Chain

variable {R : Type} [CommRing R] {d : ℕ}

theorem act_zero {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : A.act 0 = 0 := by
  have hc := A.const 0
  have h1 : A.act 0 = G.add (A.act 0) (A.act 0) := by rw [← A.add_act, add_zero]
  have h2 : A.act 0 = comp1 (A.act 0) (A.act 0) := by rw [← A.mul_act, mul_zero]
  have h3 : dLin (A.act 0) = 0 := by
    have := GlobalTheory.FormalMulN.dLin_add G hc hc
    rw [← h1] at this
    exact left_eq_add.mp this
  have h4 : ∀ i, 2 ≤ (A.act 0 i).order := fun i =>
    GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
      obtain ⟨j0, j⟩ := j
      obtain rfl : j0 = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun h3 i) j⟩
  have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (A.act 0 i).order := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
        (a := fun p : Fin 1 × Fin d => (![A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
        (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
        (fun p => by simpa using ih p.2) (h4 i)
      rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
      rw [congrFun h2 i]
      exact this
  funext i
  exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i

end Chain

end GlobalTheory.FourierChainCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AevalNegEqZeroOfResolventIdentity
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem shift_coeff_of_eval_identity {N : Type} [AddCommGroup N] [Module ℂ N]
    (Ω : Module.End ℂ N) (M : ℕ) (a : ℕ → N) (ha : ∀ i, M ≤ i → a i = 0) (p : Polynomial ℂ)
    (w : N) (h : ∀ u : ℂ, u • (∑ i ∈ Finset.range M, u ^ i • a i)
      + Ω (∑ i ∈ Finset.range M, u ^ i • a i) = p.eval u • w) :
    Ω (a 0) = p.coeff 0 • w ∧ ∀ k, a k + Ω (a (k + 1)) = p.coeff (k + 1) • w := by
  have hc : ∀ (f : N →ₗ[ℂ] ℂ) (k : ℕ),
      (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i))).coeff k = f (a k) := by
    intro f k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · rw [ha k (by simpa using hk), map_zero]
  have key : ∀ f : N →ₗ[ℂ] ℂ,
      Polynomial.X * (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i)))
        + (∑ i ∈ Finset.range M, Polynomial.monomial i ((f ∘ₗ Ω) (a i)))
        = p * Polynomial.C (f w) := by
    intro f
    apply Polynomial.funext
    intro u
    have h1 := congrArg f (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_sum, smul_eq_mul] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_C,
      LinearMap.comp_apply]
    rw [← h1]
    simp only [mul_comm]
  refine ⟨?_, fun k => ?_⟩
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P 0) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, hc, Polynomial.coeff_mul_C,
      zero_add] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_smul, smul_eq_mul, h1, sub_self]
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P (k + 1)) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, hc, Polynomial.coeff_mul_C] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_add (f := _), map_smul, smul_eq_mul, h1, sub_self]

theorem aeval_neg_eq_zero_and_eigen_of_resolvent_identity :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  intro N _ _ Ω X d c p hX h
  let a : N → ℕ → N := fun w i => if i < d then c i w else 0
  have ha : ∀ w i, d ≤ i → a w i = 0 := fun w i hi => if_neg (by omega)
  have hXa : ∀ (M : ℕ), d ≤ M → ∀ (u : ℂ) (w : N),
      X u w = ∑ i ∈ Finset.range M, u ^ i • a w i := by
    intro M hM u w
    rw [hX u, LinearMap.sum_apply]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hM)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [a, if_pos (Finset.mem_range.1 hi), LinearMap.smul_apply]
    · intro i _ hi
      rw [ha w i (by simpa using hi), smul_zero]
  have hco : ∀ w, Ω (a w 0) = p.coeff 0 • w ∧
      ∀ k, a w k + Ω (a w (k + 1)) = p.coeff (k + 1) • w := by
    intro w
    refine shift_coeff_of_eval_identity Ω d (a w) (ha w) p w fun u => ?_
    rw [← hXa d le_rfl u w]
    exact h u w
  refine ⟨?_, ?_⟩
  · ext w
    have tel : ∀ n, ∑ i ∈ Finset.range (n + 1), p.coeff i • ((-Ω) ^ i) w
        = ((-Ω) ^ n) (Ω (a w n)) := by
      intro n
      induction n with
      | zero => simp [(hco w).1]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, ← map_smul, ← (hco w).2 n, map_add (f := _), ← add_assoc]
        have : ((-Ω) ^ (n + 1)) (a w n) = - ((-Ω) ^ n) (Ω (a w n)) := by
          rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, map_neg]
        rw [this, add_neg_cancel, zero_add]
    rw [Polynomial.aeval_eq_sum_range' (n := d + p.natDegree + 1) (by omega), LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [tel, ha w _ (by omega), map_zero, map_zero, LinearMap.zero_apply]
  · intro α w hw q hq u
    have step : ∀ k, a w (k + 1) = q.coeff (k + 1) • w → a w k = q.coeff k • w := by
      intro k hk
      have h1 := (hco w).2 k
      rw [hk, map_smul, hw, hq, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, add_smul, smul_smul, mul_comm] at h1
      exact add_right_cancel h1
    have all : ∀ k, a w k = q.coeff k • w := by
      intro k
      have hk : k ≤ k + d + q.natDegree + 1 := by omega
      refine Nat.decreasingInduction (motive := fun k _ => a w k = q.coeff k • w)
        (fun j _ hj => step j hj) ?_ hk
      rw [ha w _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
    rw [hXa (d + q.natDegree + 1) (by omega), Polynomial.eval_eq_sum_range' (n := d + q.natDegree + 1) (by omega), Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [all, smul_smul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNear
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem l1_shift_single_le {n : ℕ} (ω Λ : Fin n → ℝ) (t e : ℝ) (he : |e| ≤ 1) (c : Fin n)
    (h : ∑ a, |ω a - Λ a| ≤ t) :
    ∑ a, |(ω a + if a = c then e else 0) - Λ a| ≤ t + 1 := by
  have h1 : ∀ a, |(ω a + if a = c then e else 0) - Λ a| ≤ |ω a - Λ a| + if a = c then 1 else 0 := by
    intro a
    split_ifs
    · have : ω a + e - Λ a = (ω a - Λ a) + e := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by linarith)
    · simp
  calc _ ≤ ∑ a, (|ω a - Λ a| + if a = c then 1 else 0) := Finset.sum_le_sum fun a _ => h1 a
    _ = ∑ a, |ω a - Λ a| + 1 := by rw [Finset.sum_add_distrib]; simp
    _ ≤ t + 1 := by linarith

theorem algTens_wtNear : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  intro M _ _ n ε E N _ _ F io pr Λ t hT
  refine ⟨fun w hw s c => ?_, fun s y hy d => ?_⟩
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = c then -1 else 0,
        l1_shift_single_le ω Λ t (-1) (by simp) c hω, fun a => ?_⟩
      rw [← hT.pr_comm, ← map_smul]
      congr 1
      ext i
      by_cases hi : i = c
      · subst hi
        by_cases ha : a = i
        · subst ha
          simp [dualTens, hx a, add_smul, sub_eq_add_neg]
        · have : ¬ i = a := fun h => ha h.symm
          simp [dualTens, hx a, ha, this]
      · by_cases ha : i = a
        · subst ha
          simp [dualTens, hi]
        · simp [dualTens, hi, ha]
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add (f := _)]; exact add_mem hx hy
    | smul r x _ hx => rw [Pi.single_smul, map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = d then 1 else 0,
        l1_shift_single_le ω Λ t 1 (by simp) d hω, fun a => ?_⟩
      have h := congrFun (hT.io_comm s a a x) d
      rw [hx a, map_smul] at h
      simp only [dualTens, Pi.smul_apply] at h
      rw [eq_sub_iff_add_eq] at h
      rw [← h]
      by_cases ha : a = d
      · subst ha
        simp [add_smul]
      · have : ¬ d = a := fun h => ha h.symm
        simp [ha, this]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), Pi.add_apply]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, Pi.smul_apply]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem card_filter_fin_bounds {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (0 : ℝ) ≤ ((univ.filter p).card : ℝ) ∧ ((univ.filter p).card : ℝ) ≤ n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h : (univ.filter p).card ≤ n :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  exact_mod_cast h

theorem abs_lowK_sub_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a : Fin n) :
    -(n : ℝ) ≤ lowK ε μ a - μ a ∧ lowK ε μ a - μ a ≤ n := by
  have e : lowK ε μ a - μ a = rhoN ε a - rhoC ε a := by
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [e]
  simp only [rhoN, rhoC]
  obtain ⟨h1, h2⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b ≠ ε a)
  obtain ⟨h3, h4⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b ≠ ε a)
  obtain ⟨h5, h6⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b = ε a)
  obtain ⟨h7, h8⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b = ε a)
  constructor <;> linarith

private lemma four_sq_add_le_of_large_bv {n : ℕ} {bv : ℝ} (hn : 2 ≤ n) (hb : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv) :
    4 * (n : ℝ) ^ 2 + 2 + n ≤ bv / 32 - bv / 100 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsq : 4 * (n : ℝ) ^ 2 + 2 + n ≤ 6 * (n : ℝ) ^ 2 := by nlinarith
  linarith

theorem shape_position : ∀ (n kk j : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ), Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → 0 < bv ∧ (∀ ω : Fin n → ℝ, ∑ a, |ω a - lowK ε μ a| ≤ j → ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -ω a ∧ -ω a ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -ω a ∧ -ω a ≤ 2 * bv + bv / 32)) ∧ ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ 2 * bv + bv / 32) := by
  intro n kk j ε μ bv hS hj
  obtain ⟨hk1, hkn, -, hcl, hnd, hb⟩ := hS
  have hn : 2 ≤ n := by omega
  have hm := four_sq_add_le_of_large_bv hn hb
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbpos : 0 < bv := by
    have : (0 : ℝ) < (n : ℝ) ^ 7 := by positivity
    linarith
  have hjr : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2 := by exact_mod_cast hj
  refine ⟨hbpos, ?_, ?_⟩
  · intro ω hω a
    have hle : |ω a - lowK ε μ a| ≤ j :=
      le_trans (Finset.single_le_sum (f := fun b => |ω b - lowK ε μ b|)
        (fun b _ => abs_nonneg _) (Finset.mem_univ a)) hω
    obtain ⟨hl1, hl2⟩ := abs_lowK_sub_le ε μ a
    obtain ⟨ha1, ha2⟩ := abs_le.mp hle
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith
  · intro a
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasKIsSymmetricAndForm
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_casK_eq_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (h : KUnit ε E) (x y : M) :
    ⟪x, CasK ε E y⟫_ℂ = ∑ a, ∑ b, if ε a = ε b then ⟪E a b x, E a b y⟫_ℂ else 0 := by
  unfold CasK
  rw [Finset.sum_comm]
  simp only [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [if_pos hab.symm, if_pos hab, Module.End.mul_apply, h a b hab]
  · rw [if_neg (fun e => hab e.symm), if_neg hab]
    simp

theorem casK_isSymmetric_and_form :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E →
      LinearMap.IsSymmetric (CasK ε E) ∧
        ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  intro M _ _ n ε E h
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [← inner_conj_symm, inner_casK_eq_sum h, inner_casK_eq_sum h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [inner_conj_symm]
    · simp
  · rw [inner_casK_eq_sum h]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapSubsetOfSetBoundIntegral
section
open Finset
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompareIterDegree

open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms

theorem fdeg_ratio_abs {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (hinj : Function.Injective μ) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, |(μ s + t - μ c) / (μ s - μ c)| := by
  set μ' : Fin n → ℝ := μ + Pi.single s t with hμ'
  have hμ'a : ∀ a, μ' a = μ a + if a = s then t else 0 := by
    intro a; simp [hμ', Pi.single_apply]
  set r : Fin n → ℝ := fun c => |(μ s + t - μ c) / (μ s - μ c)| with hr
  have hfac : ∀ a b : Fin n, a < b →
      |μ' a - μ' b| / |μ a - μ b| = (if a = s then r b else 1) * (if b = s then r a else 1) := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    by_cases has : a = s
    · subst has
      have hbs : b ≠ a := fun h => hne h.symm
      rw [hμ'a, hμ'a, if_pos rfl, if_neg hbs, if_pos rfl, if_neg hbs]
      simp [hr, abs_div]
    · by_cases hbs : b = s
      · subst hbs
        rw [hμ'a, hμ'a, if_neg has, if_pos rfl, if_neg has, if_pos rfl]
        simp only [hr, one_mul, add_zero, abs_div]
        rw [abs_sub_comm (μ a) (μ b + t), abs_sub_comm (μ a) (μ b)]
      · rw [hμ'a, hμ'a, if_neg has, if_neg hbs, if_neg has, if_neg hbs]
        have h0 : μ a - μ b ≠ 0 := sub_ne_zero.2 (fun h => hne (hinj h))
        simp only [add_zero, mul_one]
        exact div_self (abs_ne_zero.2 h0)
  have hden : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun a _ => prod_ne_zero_iff.2 fun b hb => ?_
    have hab : a < b := (mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  unfold fdegHC
  rw [div_div_div_cancel_right₀ hden, ← prod_div_distrib]
  simp_rw [← prod_div_distrib]
  rw [prod_congr rfl (fun a _ => prod_congr rfl (fun b hb => hfac a b (mem_filter.1 hb).2))]
  simp_rw [prod_mul_distrib]
  have h1 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if a = s then r b else 1)) = ∏ b ∈ univ.filter (fun b : Fin n => s < b), r b := by
    rw [prod_eq_single s]
    · simp
    · intro a _ has; simp [has]
    · intro h; exact absurd (mem_univ s) h
  have h2 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if b = s then r a else 1)) = ∏ a ∈ univ.filter (fun a : Fin n => a < s), r a := by
    rw [prod_filter]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_ite_eq']
    simp
  rw [h1, h2, ← prod_filter_mul_prod_filter_not (univ.erase s) (fun c => s < c)]
  congr 1
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega

end GlobalTheory.CompareIterDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsBesselMapSmBesselCharIff
section
open Matrix

noncomputable section

namespace GlobalTheory.BesselMapCompare

open PI.UpqRep GlobalTheory.IndefiniteRowSideFullHecke

section Maps

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem isHCParam_of_isHCTypeW {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V)}
    (h : IsHCTypeW k r z u π) : PI.UpqRep.IsHCParam u := by
  obtain ⟨g, -, hg⟩ := h
  exact (KTypeCompare.isHCParam_iff u).2 ((KTypeCompare.isHCTypeU_iff u _).1 hg).param

end Maps

end GlobalTheory.BesselMapCompare

end
end

