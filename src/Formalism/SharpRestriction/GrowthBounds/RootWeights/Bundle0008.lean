module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0040
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantOrthogonalityHolds
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def loweringMonoid (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {g | ∃ c d : Fin n, d < c ∧ g = E c d}

def hwvLoweringSpan (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ loweringMonoid E, ∃ w, IsHWV E mu w ∧ x = u w}

theorem isotypic_stable_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V} (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator .. | (apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K V | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n K | exact @UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator n

theorem hwv_lowering_span_lower (E : GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n} (hab : b < a) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E a b x ∈ hwvLoweringSpan E mu := by
  first | exact UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower .. | (apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x hx | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab x | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b hab | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V ‹_› | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K V | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n K | exact @UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower n

theorem lowering_word_hwv_operator_mem {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) {w : V} (hw : IsHWV E mu w)
    {u : Module.End K V} (hu : u ∈ loweringMonoid E) : ∀ c d : Fin n, E c d (u w) ∈ hwvLoweringSpan E mu := by
  unfold loweringMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one =>
    intro c d
    rw [Module.End.one_apply]
    rcases lt_trichotomy c d with h | h | h
    · rw [hw.2.2 c d h]; exact Submodule.zero_mem _
    · subst h
      rw [(mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, w, hw, rfl⟩)
    · exact Submodule.subset_span ⟨E c d, Submonoid.subset_closure ⟨c, d, h, rfl⟩, w, hw, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨b, a, hab, rfl⟩ := hg
    intro c d
    rw [Module.End.mul_apply, gl_commutation_apply hE c d b a (y w)]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (hwv_lowering_span_lower E mu hab (ih c d)) ?_) ?_
    · split_ifs
      · exact ih c a
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih b d
      · exact Submodule.zero_mem _

theorem hwv_lowering_span_stable {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) (c d : Fin n) {x : V}
    (hx : x ∈ hwvLoweringSpan E mu) : E c d x ∈ hwvLoweringSpan E mu := by
  have hx' := hx
  unfold hwvLoweringSpan at hx'
  induction hx' using Submodule.span_induction with
  | mem x hx1 =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx1
    exact lowering_word_hwv_operator_mem hE mu hv hu c d
  | zero => simp
  | add x y hx1 hy1 hx2 hy2 =>
    rw [map_add (f := _)]; exact Submodule.add_mem _ (hx2 hx1) (hy2 hy1)
  | smul c x hx1 hx2 => rw [map_smul]; exact Submodule.smul_mem _ _ (hx2 hx1)

theorem isotypic_le_lowering_span {E : GLOps n K V} (hE : IsGLRep E) (mu : Fin n → ℤ) : isoSub E mu ≤ hwvLoweringSpan E mu := by
  unfold isoSub
  rw [Submodule.span_le]
  rintro x ⟨u, hu, v, hv, rfl⟩
  unfold Umon at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact Submodule.subset_span ⟨1, (loweringMonoid E).one_mem, v, hv, rfl⟩
  | mul_left g hg y _ ih =>
    obtain ⟨ab, rfl⟩ := hg
    exact hwv_lowering_span_stable hE mu ab.1 ab.2 ih

theorem hwv_orthogonal_lowering_span [CharZero K] {E : GLOps n K V} (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ a b x y, B (E a b x) y = B x (E b a y)) {lam mu : Fin n → ℤ} (hne : lam ≠ mu) {v : V}
    (hv : IsHWV E lam v) {z : V} (hz : z ∈ hwvLoweringSpan E mu) : B v z = 0 := by
  unfold hwvLoweringSpan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    unfold loweringMonoid at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      rw [Module.End.one_apply]
      obtain ⟨a, ha⟩ : ∃ a, lam a ≠ mu a := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      have h1 := hB a a v w
      rw [(mem_weightSpace_iff_diagonal_rep E lam v).1 hv.2.1 a, (mem_weightSpace_iff_diagonal_rep E mu w).1 hw.2.1 a, map_smul, map_smul,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
      have h2 : ((lam a : K) - (mu a : K)) * B v w = 0 := by rw [sub_mul, h1, sub_self]
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exfalso; apply ha
        have : (lam a : K) = (mu a : K) := sub_eq_zero.1 h3
        exact_mod_cast this
      · exact h3
    | mul_left g hg y _ _ =>
      obtain ⟨c, d, hcd, rfl⟩ := hg
      rw [Module.End.mul_apply, ← hB d c v (y w), hv.2.2 d c hcd]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem contravariant_orthogonality_holds : ContravariantIsotypicOrthogonal := by
  intro K V _ _ _ _ n E hE B hB lam mu hne x hx
  unfold isoSub at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    unfold Umon at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro y hy
      exact hwv_orthogonal_lowering_span B hB hne hv (isotypic_le_lowering_span hE mu hy)
    | mul_left g hg u' _ ih =>
      obtain ⟨ab, rfl⟩ := hg
      intro y hy
      rw [Module.End.mul_apply]
      show B (E ab.1 ab.2 (u' v)) y = 0
      rw [hB]
      exact ih _ (isotypic_stable_operator E mu _ _ hy)
  | zero => intro y _; simp
  | add x y _ _ hx hy => intro z hz; rw [map_add (f := _), LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  | smul c x _ hx => intro z hz; rw [map_smul, LinearMap.smul_apply, hx z hz, smul_zero]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DescendingProdEqFactorialChoose
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpCon

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ}

def polarizationSource (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, b) else (l, a)

def polarizationTarget (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, a) else (l, b)

def polarizationLetterSign (R : Type*) [CommRing R] (LL : Letters ι) (l : ι) : R := if LL.vec l then 1 else -1

theorem polarizationSource_injective (LL : Letters ι) (a b : Fin n) : Function.Injective (polarizationSource LL a b) := by
  intro l l' h
  have h1 : ∀ l₀, (polarizationSource LL a b l₀).1 = l₀ := fun l₀ => by
    unfold polarizationSource; split_ifs <;> rfl
  rw [← h1 l, h, h1 l']

theorem polarizationTarget_ne_source (LL : Letters ι) (a b : Fin n) (hab : a ≠ b) (l l' : ι) :
    polarizationTarget LL a b l' ≠ polarizationSource LL a b l := by
  intro h
  have e1 : (polarizationTarget LL a b l').1 = l' := by unfold polarizationTarget; split_ifs <;> rfl
  have e2 : (polarizationSource LL a b l).1 = l := by unfold polarizationSource; split_ifs <;> rfl
  have hl : l' = l := by rw [← e1, h, e2]
  subst hl
  unfold polarizationTarget polarizationSource at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h
  · exact hab h.2
  · exact hab h.2.symm

open Classical in
theorem glAct_eq_sum_polarizations (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    glAct R LL S a b = ∑ l ∈ Finset.univ.filter (· ∈ S),
      polarizationDerivation (polarizationLetterSign R LL) (polarizationSource LL a b) (polarizationTarget LL a b) l := by
  rw [glAct, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp_all [polarizationDerivation, polarizationLetterSign, polarizationSource, polarizationTarget]

open Classical in
theorem divPowMono_eq_monomialSum (LL : Letters ι) (S : Set ι) (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) :
    divPowMono R LL S a b k m =
      dividedPowerMonomialSum (polarizationLetterSign R LL) (polarizationSource LL a b) (polarizationTarget LL a b) (Finset.univ.filter (· ∈ S)) k m := by
  unfold divPowMono dividedPowerMonomialSum
  refine Finset.sum_congr rfl fun f hf => ?_
  have hsub : f.support ⊆ Finset.univ.filter (· ∈ S) := (Finset.mem_finsuppAntidiag.1 hf).2
  unfold dividedPowerMonomialTerm dividedPowerExponent dividedPowerCoefficient
  congr 1
  rw [← Finset.prod_subset hsub (f := fun l => polarizationLetterSign R LL l ^ f l *
    ((m (polarizationSource LL a b l)).choose (f l) : R)) ?_]
  · refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hv : LL.vec l <;> simp [polarizationLetterSign, polarizationSource, hv]
  · intro l _ hl
    rw [Finsupp.notMem_support_iff.1 hl]
    simp

theorem glAct_comp_divPow (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    glAct R LL S a b ∘ₗ divPow R LL S a b k = (k + 1) • divPow R LL S a b (k + 1) := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply]
  simp only [divPow, Module.Basis.constr_basis]
  rw [divPowMono_eq_monomialSum, divPowMono_eq_monomialSum, glAct_eq_sum_polarizations]
  exact polarization_dividedPowerSum_succ _ _ _ (polarizationSource_injective LL a b) (polarizationTarget_ne_source LL a b hab) _ m k

theorem divPow_zero' (LL : Letters ι) (S : Set ι) (a b : Fin n) : divPow R LL S a b 0 = LinearMap.id := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [LinearMap.id_apply]
  simp only [divPow, Module.Basis.constr_basis]
  rw [divPowMono_eq_monomialSum, dividedPowerMonomialSum_zero, MvPolynomial.coe_basisMonomials]

theorem glAct_pow_eq_factorial_divPow (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    (glAct R LL S a b : Module.End R (MvPolynomial (ι × Fin n) R)) ^ k = k.factorial • divPow R LL S a b k := by
  induction k with
  | zero => rw [pow_zero, divPow_zero', Nat.factorial_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', ih, Module.End.mul_eq_comp, LinearMap.comp_smul, glAct_comp_divPow LL S a b hab k,
      smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    ring

theorem X_mul_pderiv_monomial' {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    X v * pderiv v (monomial m c) = ((m v : ℕ) : R) • monomial m c := by
  classical
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]

theorem glAct_diagonal_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = ((wtS LL S m a : ℤ) : R) • monomial m c := by
  classical
  rw [glAct, LinearMap.sum_apply, wtS, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp_all [-MvPolynomial.pderiv_monomial, X_mul_pderiv_monomial']

theorem list_prod_shifted_eigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (w : K) (x : V)
    (h : T x = w • x) (L : List ℕ) :
    ((L.map fun j : ℕ => T - (j : K) • (1 : Module.End K V)).prod) x = ((L.map fun j : ℕ => w - (j : K)).prod) • x := by
  induction L with
  | nil => simp
  | cons j L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h]
    rw [← sub_smul, smul_smul, mul_comm]

theorem list_range_prod_eq_finset_prod {K : Type*} [CommRing K] (w : K) (k : ℕ) :
    ((List.range k).map fun j : ℕ => w - (j : K)).prod = ∏ j ∈ Finset.range k, (w - (j : K)) := by
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.prod_coe]

theorem descending_prod_eq_factorial_choose (z : ℤ) (k : ℕ) : ∏ j ∈ Finset.range k, (z - (j : ℤ)) = (k.factorial : ℤ) * Ring.choose z k := by
  rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

end v2dpCon

theorem dividedPower_formula_char_zero : DividedPowerFormulaCharZero := by
  intro R _ _ ι _ LL n S a b k hab
  show ((k.factorial : R)⁻¹) • (glAct R LL S a b) ^ k = divPow R LL S a b k
  rw [glAct_pow_eq_factorial_divPow LL S a b hab k, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

theorem binomial_formula_char_zero : BinomialFormulaCharZero := by
  intro R _ _ ι _ LL n S a k
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials]
  show ((k.factorial : R)⁻¹ • ((List.range k).map fun j : ℕ =>
    glAct R LL S a a - (j : R) • (1 : Module.End R (MvPolynomial (ι × Fin n) R))).prod) (monomial m 1) = _
  rw [LinearMap.smul_apply, list_prod_shifted_eigen (glAct R LL S a a) ((wtS LL S m a : ℤ) : R) (monomial m 1)
    (glAct_diagonal_monomial LL S a m 1), list_range_prod_eq_finset_prod, smul_smul]
  have hc : ∏ j ∈ Finset.range k, (((wtS LL S m a : ℤ) : R) - (j : R)) =
      (((k.factorial : ℤ) * Ring.choose (wtS LL S m a) k : ℤ) : R) := by
    rw [← descending_prod_eq_factorial_choose]
    push_cast
    rfl
  rw [hc]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowersPreserveZero
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section good

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def DividedPowersPreserve (Q : V → Prop) (D : Module.End K V) : Prop :=
  ∀ (k : ℕ) (x : V), Q x → Q (((k.factorial : K)⁻¹) • (D ^ k) x)

theorem predicate_finset_sum_mem (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y)) {α : Type*}
    (s : Finset α) (f : α → V) (h : ∀ i ∈ s, Q (f i)) : Q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem divided_powers_preserve_add (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y))
    (D D' : Module.End K V) (hc : Commute D D') (hD : DividedPowersPreserve Q D) (hD' : DividedPowersPreserve Q D') :
    DividedPowersPreserve Q (D + D') := by
  intro k x hx
  rw [hc.add_pow, LinearMap.sum_apply, Finset.smul_sum]
  refine predicate_finset_sum_mem Q h0 hadd _ _ fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have h1 := hD m _ (hD' (k - m) x hx)
  have h2 : ((k.factorial : K)⁻¹) • (D ^ m * D' ^ (k - m) * ((k.choose m : ℕ) : Module.End K V)) x =
      ((m.factorial : K)⁻¹) • (D ^ m) ((((k - m).factorial : K)⁻¹) • (D' ^ (k - m)) x) := by
    have h3 : ((k.choose m : ℕ) : Module.End K V) x = ((k.choose m : ℕ) : K) • x := by
      rw [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    simp only [Module.End.mul_apply, h3, map_smul, smul_smul]
    congr 1
    have h4 : ((k.choose m : ℕ) : K) = (k.factorial : K) / ((m.factorial : K) * ((k - m).factorial : K)) :=
      Nat.cast_choose K hmk
    have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hm' : (m.factorial : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hkm : ((k - m).factorial : K) ≠ 0 := by exact_mod_cast (k - m).factorial_ne_zero
    rw [h4]
    field_simp
  rw [h2]
  exact h1

end good

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExtremalProjectorLatticeScaledMem
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Wt

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem operator_pow_shifts_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (ν : Fin n → ℤ) (k : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : ((E a b) ^ k) x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  unfold OperatorsShiftWeightsByRoots at hs
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := hs a b _ _ ih
    convert h1 using 2
    rw [Nat.cast_succ, add_smul, one_smul, add_assoc]

end Wt

section Lattice

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem binomial_subring_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    (u : Module.End (KK O) V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ M, u x ∈ M := by
  unfold binomialDiagonalSubring at hu
  unfold UZStable at hM
  induction hu using Subring.closure_induction with
  | mem u hu => obtain ⟨a, k, rfl⟩ := hu; exact hM _ (Or.inr ⟨a, k, rfl⟩)
  | zero => intro x _; simp
  | one => intro x hx; simpa using hx
  | add u v _ _ hu hv => intro x hx; rw [LinearMap.add_apply]; exact M.add_mem (hu x hx) (hv x hx)
  | neg u _ hu => intro x hx; rw [LinearMap.neg_apply]; exact M.neg_mem (hu x hx)
  | mul u v _ _ hu hv => intro x hx; rw [Module.End.mul_apply]; exact hu _ (hv x hx)

end Lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightDominantHolds
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

theorem highest_weight_dominant_pair {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) {a b : Fin n} (hab : a < b) : lam b ≤ lam a := by
  have hne : a ≠ b := ne_of_lt hab
  have hw := (mem_weightSpace_iff_diagonal_rep E lam v).1 hv.2.1
  have hhv : (E a a - E b b) v = ((lam a - lam b : ℤ) : K) • v := by
    rw [LinearMap.sub_apply, hw a, hw b, ← sub_smul]; push_cast; rfl
  by_cases h0 : E a a - E b b = 0
  · rw [h0, LinearMap.zero_apply] at hhv
    have := (smul_eq_zero.1 hhv.symm).resolve_right hv.1
    have h1 : lam a - lam b = 0 := by exact_mod_cast this
    omega
  have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) := by
    refine ⟨h0, ?_, ?_, ?_⟩
    · rw [Ring.lie_def, hE.1 a b b a]; simp
    · rw [sub_lie, Ring.lie_def, Ring.lie_def, hE.1 a a a b, hE.1 b b a b]
      simp [hne, hne.symm, two_smul]
    · rw [sub_lie, Ring.lie_def, Ring.lie_def, hE.1 a a b a, hE.1 b b b a]
      simp [hne, hne.symm, two_smul]
      abel
  have P : t.HasPrimitiveVectorWith v (((lam a - lam b : ℤ) : K)) :=
    ⟨hv.1, hhv, hv.2.2 a b hab⟩
  obtain ⟨m, hm⟩ := P.exists_nat
  have : lam a - lam b = (m : ℤ) := by exact_mod_cast hm
  omega

theorem highest_weight_dominant_holds : HighestWeightDominant := by
  intro K V _ _ _ _ _ n E hE lam v hv a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact highest_weight_dominant_pair hE hv h

end Formalism.MainNotions.G.GLWeightTheory
end
end

