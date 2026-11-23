module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdNabValLeadingMinors
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.CrudeValue

variable {k : Type} [CommRing k] {d : ℕ}

theorem constantCoeff_expS [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) :
    constantCoeff (FB.expS k g) = 1 := by
  unfold FB.expS
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [map_pow, hg, zero_pow hj, smul_zero]

theorem constantCoeff_ev_eq_zero {m n : ℕ} (a : Fin m → Pt k n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have ha' : ∀ q : Fin m × Fin d, constantCoeff ((fun q : Fin m × Fin d => a q.1 q.2) q) = 0 :=
    fun q => ha q.1 q.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
    (hasSubst_of_constantCoeff_zero ha') ha' hf

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]


omit [Algebra ℚ k] in
theorem constantCoeff_hL (B : FB R d O) (h : PS k 2 d) (hh : constantCoeff h = 0) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have hp : ∀ i, constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => constantCoeff_X _
  refine constantCoeff_ev_eq_zero _ (fun j i => ?_) h hh
  fin_cases j
  · exact hp i
  · refine constantCoeff_ev_eq_zero ![pt k d 0] (fun j i' => ?_) (B.actK k w0 i) ?_
    · fin_cases j
      exact hp i'
    · unfold FB.actK
      rw [constantCoeff_map, B.A.const, map_zero]

theorem nabVal_monomial (B : FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (e : ι →₀ ℕ) :
    B.nabVal k h w0 q f u (MvPolynomial.monomial e 1) =
      constantCoeff (DmonOf (B.G.mapF (algebraMap R k)) u e
        (f * FB.expS k ((q : k) • B.hL k h w0))) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  · simp only [FB.nabVal, FB.FK, DpolyOf, MvPolynomial.support_monomial,
      if_neg (one_ne_zero : (1 : k) ≠ 0), Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_true, map_one, one_mul]

end GlobalTheory.CrudeValue

namespace GlobalTheory


end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDualStandardRel
section
open Formalism.REAL

namespace GlobalTheory

theorem _root_.GlobalTheory.tensor_dual_standard_rel : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), _root_.Formalism.REAL.GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → _root_.Formalism.REAL.GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hsym hEt hOm
  have hE' : ∀ a b c d (v : V), E a b (E c d v) - E c d (E a b v) = (if b = c then E a d v else 0) - if d = a then E c b v else 0 := by
    intro a b c d v
    have := congrArg (fun T : Module.End ℂ V => T v) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [this]; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    ext y e
    have key : E a b (E c d (y.ofLp e)) = E c d (E a b (y.ofLp e)) + ((if b = c then E a d (y.ofLp e) else 0) - if d = a then E c b (y.ofLp e) else 0) := by
      have h := hE' a b c d (y.ofLp e); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have hR : (((if b = c then Et a d else 0) - if d = a then Et c b else 0) y).ofLp e = (if b = c then (Et a d y).ofLp e else 0) - (if d = a then (Et c b y).ofLp e else 0) := by
      split_ifs <;> simp
    rw [hR]
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    rw [WithLp.ofLp_sub, Pi.sub_apply, hEt, hEt, hEt, hEt, hEt, hEt, map_sub, map_sub, key]
    split_ifs <;> simp only [hEt, map_zero, sub_zero, zero_sub] <;> subst_vars <;>
      first | abel1 | (exfalso; tauto) | (simp_all; done) | (split_ifs <;> subst_vars <;> first | abel1 | (exfalso; tauto) | (simp_all; done) | (simp_all; abel1))
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, hsym]
    have h1 : ∀ i, inner ℂ (if i = b then x.ofLp a else 0) (y.ofLp i) = if i = b then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    have h2 : ∀ i, inner ℂ (x.ofLp i) (if i = a then y.ofLp b else 0) = if i = a then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hsym]
    exact Finset.sum_comm
  · intro a b
    ext y e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.End.mul_apply, hOm, hEt, map_sub, map_sum]
    have key : ∀ i, E e i (E a b (y.ofLp i)) = E a b (E e i (y.ofLp i)) + (if i = a then E e b (y.ofLp i) else 0) - (if b = e then E a i (y.ofLp i) else 0) := by
      intro i; have h := hE' e i a b (y.ofLp i); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have h3 : ∀ i, E e i (if i = b then y.ofLp a else 0) = if i = b then E e b (y.ofLp a) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [key, h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : e = b
    · subst h; simp only [if_true]; abel
    · simp only [h, Ne.symm h, if_false, Finset.sum_const_zero]; abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
section
open Formalism.REAL

namespace GlobalTheory

theorem tensorStd_rel_adjoint_splitCasimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hadj hEt hOm
  have hv : ∀ a b c d v, E a b (E c d v) = E c d (E a b v) +
      ((if b = c then E a d v else 0) - if d = a then E c b v else 0) := by
    intro a b c d v
    have h := LinearMap.congr_fun (hE a b c d) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_iff_eq_add', h]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_
    have h1 : ((if b = c then Et a d else 0) - if d = a then Et c b else 0 :
        Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) y k =
        (if b = c then Et a d y k else 0) - if d = a then Et c b y k else 0 := by
      split_ifs <;> simp
    rw [h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, hEt, map_add (f := _)]
    rw [hv a b c d]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_add_left, inner_add_right, Finset.sum_add_distrib, hadj]
    congr 1
    have h1 : ∀ c, inner ℂ (if c = a then x b else 0) (y c) =
        if c = a then inner ℂ (x b) (y c) else 0 := by
      intro c; split_ifs <;> simp
    have h2 : ∀ c, inner ℂ (x c) (if c = b then y a else 0) =
        if c = b then inner ℂ (x c) (y a) else 0 := by
      intro c; split_ifs <;> simp
    simp [h1, h2]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hadj]
    exact Finset.sum_comm
  · intro a b
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.End.mul_apply, hEt, hOm, map_add (f := _), map_sum, Finset.sum_add_distrib]
    have h1 : ∀ c, E c k (E a b (y c)) = _ := fun c => hv c k a b (y c)
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, apply_ite (E _ k), map_zero]
    by_cases h : k = a
    · simp [h, add_assoc]
    · simp [h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearOrthDecomp
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.WtOrth

theorem inner_eq_zero_of_ne {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsUnitary ε E) {ω ω' : Fin n → ℝ} {x y : M}
    (hx : IsWeight E ω x) (hy : IsWeight E ω' y) (hne : ω ≠ ω') : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h := hU a a x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right] at h
  simp only [Formalism.REAL.sgn, if_true, Complex.ofReal_one, one_mul, Complex.conj_ofReal] at h
  have h2 : ((ω a : ℂ) - (ω' a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h3)) ha
  · exact h3

theorem exists_decomp {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M) (hw : w ∈ WtNear E Λ t) :
    ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t) ∧
      (∀ ω, IsWeight E ω (x ω)) ∧ (∀ ω, ω ∉ T → x ω = 0) ∧ w = ∑ ω ∈ T, x ω := by
  classical
  unfold WtNear at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ω, h1, h2⟩ := hy
    refine ⟨{ω}, fun ω' => if ω' = ω then y else 0, ?_, ?_, ?_, ?_⟩
    · intro ω' h
      rw [Finset.mem_singleton.mp h]; exact h1
    · intro ω'
      by_cases h : ω' = ω
      · simp only [h, if_true]; exact h2
      · intro a; simp [h]
    · intro ω' h
      have : ω' ≠ ω := fun e => h (Finset.mem_singleton.mpr e)
      simp [this]
    · simp
  | zero => exact ⟨∅, fun _ => 0, by simp, fun ω a => by simp, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    obtain ⟨T', x', h1', h2', h3', h4'⟩ := hz
    refine ⟨T ∪ T', fun ω => x ω + x' ω, ?_, ?_, ?_, ?_⟩
    · intro ω h
      rcases Finset.mem_union.mp h with h | h
      · exact h1 ω h
      · exact h1' ω h
    · intro ω a
      simp only [map_add (f := _), h2 ω a, h2' ω a, smul_add]
    · intro ω h
      rw [Finset.mem_union, not_or] at h
      simp [h3 ω h.1, h3' ω h.2]
    · rw [Finset.sum_add_distrib, h4, h4']
      congr 1
      · exact Finset.sum_subset Finset.subset_union_left fun ω _ h => h3 ω h
      · exact Finset.sum_subset Finset.subset_union_right fun ω _ h => h3' ω h
  | smul c y _ hy =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    refine ⟨T, fun ω => c • x ω, h1, ?_, ?_, ?_⟩
    · intro ω a
      simp only [map_smul, h2 ω a]
      exact smul_comm _ _ _
    · intro ω h
      simp [h3 ω h]
    · rw [h4, Finset.smul_sum]

theorem wtNear_orth_decomp : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, h1, h2, _, h4⟩ := exists_decomp E Λ t w hw
  exact ⟨T, x, fun ω h => ⟨h1 ω h, h2 ω⟩, h4,
    fun ω _ ω' _ hne => inner_eq_zero_of_ne hU (h2 ω) (h2 ω') hne⟩

end GlobalTheory.WtOrth
end

