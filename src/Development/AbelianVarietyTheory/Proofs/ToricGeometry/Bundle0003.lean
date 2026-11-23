module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.Imports
section
universe u_1 u_2

namespace GlobalTheory.CommonDenominatorForFinset

theorem exists_common_denominator {R : Type u_1} {A : Type u_2} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := A)
  choose f hf0 r hr using h
  refine ⟨∏ b ∈ S, f b, Finset.prod_ne_zero_iff.mpr fun b _ => hf0 b, ?_⟩

  let N : Submodule R A :=
    { carrier := {b | ∃ p : Polynomial R, algebraMap R A (∏ b ∈ S, f b) * b = Polynomial.aeval a p}
      add_mem' := by
        rintro x y ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p + q, by rw [mul_add, hp, hq, map_add (f := _)]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨p, hp⟩
        refine ⟨Polynomial.C c * p, ?_⟩
        rw [map_mul, Polynomial.aeval_C, ← hp, Algebra.smul_def]
        ring }

  have hgen : (S : Set A) ⊆ N := by
    intro b hb
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem f hb
    refine ⟨Polynomial.C t * r b, ?_⟩
    rw [map_mul, Polynomial.aeval_C, ← hr b, ht, map_mul]
    ring
  have htop : (⊤ : Submodule R A) ≤ N := by
    rw [← hS, Submodule.span_le]
    exact hgen
  intro b
  exact htop Submodule.mem_top

end GlobalTheory.CommonDenominatorForFinset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.NodupRootsOfDerivativeNeZero
section
open Filter Topology Polynomial

namespace GlobalTheory.SimpleRoots

variable {d : ℕ}

theorem eval_map_eq_sum (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ) (y : ℂ) :
    (p.map (MvPolynomial.eval x)).eval y
      = ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval x (p.coeff i) * y ^ i := by
  rw [eval_map, eval₂_eq_sum_range]

theorem analyticAt_mvPolynomial_eval (a : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    AnalyticAt ℂ (fun x : Fin d → ℂ => MvPolynomial.eval x a) x :=
  AnalyticOnNhd.eval_mvPolynomial a x (Set.mem_univ x)

theorem analyticAt_eval_map (p : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval w.1)).eval w.2) z := by
  simp only [eval_map_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((analyticAt_mvPolynomial_eval _ _).comp analyticAt_fst).mul (analyticAt_snd.pow i)

theorem exists_analytic_root (p : Polynomial (MvPolynomial (Fin d) ℂ)) {x₀ : Fin d → ℂ} {y₀ : ℂ}
    (h0 : (p.map (MvPolynomial.eval x₀)).eval y₀ = 0)
    (h1 : (p.map (MvPolynomial.eval x₀)).derivative.eval y₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0) ∧
      ∀ᶠ w in 𝓝 (x₀, y₀), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 ↔ ψ w.1 = w.2 := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun w => (p.map (MvPolynomial.eval w.1)).eval w.2 with hf
  have ha : AnalyticAt ℂ f (x₀, y₀) := analyticAt_eval_map p _
  have hc : ContDiffAt ℂ ⊤ f (x₀, y₀) := ha.contDiffAt
  have hd : HasFDerivAt (fun y : ℂ => f (x₀, y))
      (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ) y₀ :=
    ha.differentiableAt.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)
  have hd' := ((p.map (MvPolynomial.eval x₀)).hasDerivAt y₀).hasFDerivAt
  have he := hd.unique hd'
  have hi : (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [he]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨hc.implicitFunction (by simp) hi, ?_, hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · exact (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  · filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with x hx
    exact hx.trans h0
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hi] with w hw
    rw [← hw]
    exact Iff.of_eq (congrArg _ h0.symm)

theorem nodup_roots_of_derivative_ne_zero {P : ℂ[X]} (hP : P ≠ 0)
    (h : ∀ y, P.eval y = 0 → P.derivative.eval y ≠ 0) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rw [count_roots]
  by_contra hy
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hP).mp (not_le.mp hy)
  exact h y h1 h2

theorem exists_analytic_roots {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0) :
    ∃ ψ : ℂ → (Fin d → ℂ) → ℂ,
      (∀ y ∈ (p.map (MvPolynomial.eval x₀)).roots, AnalyticAt ℂ (ψ y) x₀ ∧ ψ y x₀ = y) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).roots
        = (p.map (MvPolynomial.eval x₀)).roots.map fun y => ψ y x := by
  classical
  have hne : ∀ x, p.map (MvPolynomial.eval x) ≠ 0 := fun x => (hp.map _).ne_zero
  have hex : ∀ y, ∃ ψ : (Fin d → ℂ) → ℂ, y ∈ (p.map (MvPolynomial.eval x₀)).roots →
      AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y ∧
        ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0 := by
    intro y
    by_cases hy : y ∈ (p.map (MvPolynomial.eval x₀)).roots
    · have hy' := (mem_roots (hne x₀)).mp hy
      obtain ⟨ψ, h1, h2, h3, -⟩ := exists_analytic_root p hy' (h y hy')
      exact ⟨ψ, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun hy' => absurd hy' hy⟩
  choose ψ hψ using hex
  refine ⟨ψ, fun y hy => ⟨(hψ y hy).1, (hψ y hy).2.1⟩, ?_⟩
  set S := (p.map (MvPolynomial.eval x₀)).roots with hS
  have hnd : S.Nodup := nodup_roots_of_derivative_ne_zero (hne x₀) h
  have hcard : ∀ x, (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := fun x => by
    rw [← hp.natDegree_map (MvPolynomial.eval x)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have e1 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 :=
    (Finset.eventually_all _).mpr fun y hy => (hψ y (Multiset.mem_toFinset.mp hy)).2.2
  have e2 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, ∀ y' ∈ S.toFinset, y ≠ y' → ψ y x ≠ ψ y' x := by
    refine (Finset.eventually_all _).mpr fun y hy => (Finset.eventually_all _).mpr fun y' hy' => ?_
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun _ hn => absurd hyy hn
    · obtain ⟨a1, a2, -⟩ := hψ y (Multiset.mem_toFinset.mp hy)
      obtain ⟨b1, b2, -⟩ := hψ y' (Multiset.mem_toFinset.mp hy')
      have := (a1.continuousAt.ne_iff_eventually_ne b1.continuousAt).mp (by rwa [a2, b2])
      exact this.mono fun x hx _ => hx
  filter_upwards [e1, e2] with x h1 h2
  symm
  refine Multiset.eq_of_le_of_card_le ?_ ?_
  · refine (Multiset.le_iff_subset (hnd.map_on fun y hy y' hy' hyy => ?_)).mpr fun t ht => ?_
    · by_contra hn
      exact h2 y (Multiset.mem_toFinset.mpr hy) y' (Multiset.mem_toFinset.mpr hy') hn hyy
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ht
      exact (mem_roots (hne x)).mpr (h1 y (Multiset.mem_toFinset.mpr hy))
  · rw [Multiset.card_map, hcard, hS, hcard]

theorem differentiableAt_coeff_prod {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Multiset ι) (ψ : ι → E → ℂ) {x₀ : E} (h : ∀ y ∈ T, DifferentiableAt ℂ (ψ y) x₀) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (T.map fun y => X - C (ψ y x)).prod.coeff k) x₀ := by
  induction T using Multiset.induction_on generalizing k with
  | empty => simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine DifferentiableAt.sub ?_ (ha.mul (ih' k))
    cases k with
    | zero => simp
    | succ k => simpa only [coeff_X_mul] using ih' k

theorem norm_coeff_prod_le (T : Multiset ℂ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ y ∈ T, ‖y‖ ≤ R) (k : ℕ) :
    ‖(T.map fun y => X - C y).prod.coeff k‖ ≤ (1 + R) ^ T.card := by
  induction T using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one, Multiset.card_zero, pow_zero]
    split_ifs <;> simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul,
      Multiset.card_cons]
    have h1 : ‖(X * (T.map fun y => X - C y).prod).coeff k‖ ≤ (1 + R) ^ T.card := by
      cases k with
      | zero => simp; positivity
      | succ k => simpa only [coeff_X_mul] using ih' k
    have h2 : ‖a * (T.map fun y => X - C y).prod.coeff k‖ ≤ R * (1 + R) ^ T.card := by
      rw [norm_mul]
      exact mul_le_mul ha (ih' k) (norm_nonneg _) hR
    refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    ring

theorem exists_norm_eval_le (a : MvPolynomial (Fin d) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin d → ℂ, ‖MvPolynomial.eval x a‖ ≤ C * (1 + ‖x‖) ^ m := by
  induction a using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩
  | add a b ha hb =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    obtain ⟨C₂, m₂, h₂, hb⟩ := hb
    refine ⟨C₁ + C₂, m₁ + m₂, by positivity, fun x => ?_⟩
    have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    rw [map_add (f := _), add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((ha x).trans ?_) ((hb x).trans ?_))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₁
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₂
  | mul_X a i ha =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    refine ⟨C₁, m₁ + 1, h₁, fun x => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    refine mul_le_mul (ha x) ?_ (norm_nonneg _) (by positivity)
    linarith [norm_le_pi_norm x i]

theorem norm_root_le {P : ℂ[X]} (hP : P.Monic) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ M) {y : ℂ} (hy : P.eval y = 0) : ‖y‖ ≤ M + 1 := by
  have h1 := IsRoot.norm_lt_cauchyBound hP.ne_zero hy
  lift M to NNReal using hM0
  have h2 : P.cauchyBound ≤ M + 1 := by
    unfold cauchyBound
    rw [hP.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi => by exact_mod_cast hM i (Finset.mem_range.mp hi)
  exact_mod_cast (h1.trans_le h2).le

theorem exists_norm_root_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  choose C m hC h using fun i => exists_norm_eval_le (p.coeff i)
  set s := Finset.range p.natDegree
  have hs : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨∑ i ∈ s, C i + 1, ∑ i ∈ s, m i, by positivity, fun x y hy => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h2 := norm_root_le (hp.map _) (M := (∑ i ∈ s, C i) * (1 + ‖x‖) ^ (∑ i ∈ s, m i))
    (by positivity) (fun i hi => ?_) hy
  · rw [add_mul, one_mul]
    linarith [one_le_pow₀ h1 (n := ∑ i ∈ s, m i)]
  · rw [hp.natDegree_map] at hi
    have hi' : i ∈ s := Finset.mem_range.mpr hi
    rw [coeff_map]
    refine (h i x).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi')
      (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi'))
      (by positivity) hs)

end GlobalTheory.SimpleRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaPositivity

variable {g : ℕ}


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.form_conj {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    w ⬝ᵥ Hm.mulVec (star z) = star (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [← star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, ← Matrix.dotProduct_mulVec]

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.form_add_self {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    ((z + w) ⬝ᵥ Hm.mulVec (star (z + w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (z ⬝ᵥ Hm.mulVec (star w)).re
        + (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    _root_.GlobalTheory.ThetaPositivity.form_conj hH z w]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
private lemma continuous_re_dotProduct_mulVec_star (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous (fun z : Fin g → ℂ => (z ⬝ᵥ Hm.mulVec (star z)).re) :=
  Complex.continuous_re.comp (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.exists_norm_le (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Continuous θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) :
    ∃ C : ℝ, ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
  classical
  set F : (Fin g → ℂ) → ℝ := fun z =>
    ‖θ z‖ * Real.exp (-(Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)) with hFdef
  have hF : Continuous F :=
    hθ.norm.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_re_dotProduct_mulVec_star Hm)).neg))
  have hper : ∀ (l : Λ) z, F (z + l) = F z := by
    intro l z
    have hre : ∀ a b : ℂ, ((Real.pi : ℂ) * a + Real.pi / 2 * b).re
        = Real.pi * a.re + Real.pi / 2 * b.re := fun a b => by
      simp [Complex.add_re, Complex.re_ofReal_mul]
    simp only [hFdef, htr, norm_mul, hχ, one_mul, Complex.norm_exp, hre,
      _root_.GlobalTheory.ThetaPositivity.form_add_self hH]
    rw [mul_comm (Real.exp _) ‖θ z‖, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  have hK : IsCompact (closure (ZSpan.fundamentalDomain bR)) :=
    (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun z => ?_⟩
  have hmem : ((ZSpan.floor bR z : Submodule.span ℤ (Set.range bR)) : Fin g → ℂ) ∈ Λ := by
    exact (Module.Basis.ofZLatticeBasis_span ℝ Λ b).le (ZSpan.floor bR z).2
  have hz : F z = F (ZSpan.fract bR z) := by
    have := hper ⟨_, hmem⟩ (ZSpan.fract bR z)
    rw [← this, ZSpan.fract_apply]
    simp
  have hbd : F z ≤ C := by
    rw [hz]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain bR z)))
  have hexp := Real.exp_pos (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)
  calc ‖θ z‖ = F z * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
        rw [hFdef, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) :=
        mul_le_mul_of_nonneg_right hbd hexp.le

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
private lemma re_form_add_smul_of_isHermitian {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) (t : ℂ) :
    ((z + t • w) ⬝ᵥ Hm.mulVec (star (z + t • w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (star t * (z ⬝ᵥ Hm.mulVec (star w))).re
        + Complex.normSq t * (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [_root_.GlobalTheory.ThetaPositivity.form_add_self hH]
  have h1 : z ⬝ᵥ Hm.mulVec (star (t • w)) = star t * (z ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (t • w) ⬝ᵥ Hm.mulVec (star (t • w)) =
      (Complex.normSq t : ℂ) * (w ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm (star t), Complex.star_def, Complex.mul_conj]
  rw [h1, h2, Complex.re_ofReal_mul]


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) {C : ℝ}
    (hC : ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re))
    {w : Fin g → ℂ} (hw : (w ⬝ᵥ Hm.mulVec (star w)).re < 0) : θ = 0 := by
  funext z
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have hp := Real.exp_pos (Real.pi / 2 * ((0 : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star 0)).re)
    nlinarith [norm_nonneg (θ 0)]
  set a := -(w ⬝ᵥ Hm.mulVec (star w)).re with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set A := (z ⬝ᵥ Hm.mulVec (star z)).re with hA
  set B := ‖z ⬝ᵥ Hm.mulVec (star w)‖ with hB
  set f : ℂ → ℂ := fun t => θ (z + t • w) with hfdef
  have hf : Differentiable ℂ f :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const w))
  have hbound : ∀ t, ‖f t‖ ≤ C * Real.exp (Real.pi / 2 * (A + 2 * B * ‖t‖ - a * ‖t‖ ^ 2)) := by
    intro t
    refine (hC _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [re_form_add_smul_of_isHermitian hH, Complex.normSq_eq_norm_sq]
    have h : (star t * (z ⬝ᵥ Hm.mulVec (star w))).re ≤ ‖t‖ * B := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_star]
    nlinarith
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (Real.pi / 2 * (A + 2 * B * r - a * r ^ 2)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => (A + 2 * B ^ 2 / a) + (-(a / 2)) * r ^ 2) atTop atBot :=
      tendsto_atBot_add_const_left _ _
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith))
    have h1 : Tendsto (fun r : ℝ => A + 2 * B * r - a * r ^ 2) atTop atBot := by
      refine tendsto_atBot_mono (fun r => ?_) h2
      have key : 2 * B ^ 2 / a + a / 2 * r ^ 2 - 2 * B * r = (a * r - 2 * B) ^ 2 / (2 * a) := by
        field_simp
        ring
      have : 0 ≤ (a * r - 2 * B) ^ 2 / (2 * a) := by positivity
      nlinarith
    have h3 := Real.tendsto_exp_atBot.comp (h1.const_mul_atBot (by positivity : 0 < Real.pi / 2))
    simpa using h3.const_mul C
  have hf0 : Tendsto f (cocompact ℂ) (𝓝 0) :=
    squeeze_zero_norm hbound (hlim.comp tendsto_norm_cocompact_atTop)
  have := hf.apply_eq_of_tendsto_cocompact 0 hf0
  simpa [hfdef] using this


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
theorem _root_.GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
        (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
        (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) →
        Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 →
        (∀ (l : Λ) z, θ (z + l) =
          (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
            Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) →
        ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro g Λ hdisc hspan Hm χ Ef θ hH hχ hE hinj hθ hθ0 htr z hz
  classical
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hpsd : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := by
    intro w
    by_contra hw
    push_neg at hw
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
    exact hθ0 (_root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg hH hθ hC hw)
  refine lt_of_le_of_ne (hpsd z) (fun hz0 => hz ?_)
  have him : ∀ v : Fin g → ℂ, (z ⬝ᵥ Hm.mulVec (star v)).im = 0 := by
    intro v
    have key : ∀ s : ℝ, 0 ≤ 2 * s * (z ⬝ᵥ Hm.mulVec (star v)).im
        + s ^ 2 * (v ⬝ᵥ Hm.mulVec (star v)).re := by
      intro s
      have h := hpsd (z + ((s : ℂ) * Complex.I) • v)
      rw [re_form_add_smul_of_isHermitian hH, ← hz0] at h
      have e1 : (star ((s : ℂ) * Complex.I) * (z ⬝ᵥ Hm.mulVec (star v))).re =
          s * (z ⬝ᵥ Hm.mulVec (star v)).im := by
        simp [Complex.mul_re]
      have e2 : Complex.normSq ((s : ℂ) * Complex.I) = s ^ 2 := by simp [sq]
      rw [e1, e2] at h
      linarith
    set c := (z ⬝ᵥ Hm.mulVec (star v)).im
    set d := (v ⬝ᵥ Hm.mulVec (star v)).re
    have hd1 : 0 < d + 1 := by linarith [hpsd v]
    have h' : 0 ≤ -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
      have e : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
        field_simp
        ring
      linarith [key (-c / (d + 1))]
    rw [neg_div, neg_nonneg, div_le_iff₀ (by positivity), zero_mul] at h'
    have hc2 : c ^ 2 = 0 := by nlinarith [sq_nonneg c, hpsd v]
    exact (pow_eq_zero_iff two_ne_zero).mp hc2
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  let M : Matrix _ _ ℤ := Matrix.of fun i j => Ef (b i) (b j)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have hl : Ef (b.equivFun.symm c) = 0 := by
      refine b.ext fun j => ?_
      have := congrFun hc j
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Module.Basis.equivFun_symm_apply, map_sum, Matrix.vecMul, dotProduct, M] using this
    have := hinj (hl.trans (map_zero Ef).symm)
    have h2 := congrArg b.equivFun this
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  have hr : (fun i => bR.repr z i) ᵥ* M.map (Int.cast : ℤ → ℝ) = 0 := by
    funext j
    have h := him (b j : Fin g → ℂ)
    rw [← bR.sum_repr z] at h
    simp only [sum_dotProduct, smul_dotProduct, Complex.im_sum, Complex.smul_im,
      Module.Basis.ofZLatticeBasis_apply, bR, ← hE] at h
    simpa [Matrix.vecMul, dotProduct, M] using h
  have hdetR : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    have e : (M.map (Int.castRingHom ℝ)).det = Int.castRingHom ℝ M.det := (RingHom.map_det _ _).symm
    simpa using e ▸ (Int.cast_ne_zero.mpr hdet)
  have hr0 : (fun i => bR.repr z i) = 0 := by
    by_contra hne
    exact hdetR (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hr⟩)
  have hz' : bR.repr z = 0 := by
    ext i
    exact congrFun hr0 i
  simpa using hz'

end GlobalTheory.ThetaPositivity
end

