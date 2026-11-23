module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isotypic_stable_under_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) :
    ∀ x ∈ isoSub E mu, E a b x ∈ isoSub E mu := by
  unfold isoSub
  intro x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, v, hv, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem isotypic_sum_stable_gl_operator (E : GLOps n K V) (a b : Fin n) :
    ∀ x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu), E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
  intro x hx
  have hle : (⨆ mu : Fin n → ℤ, isoSub E mu) ≤ (⨆ mu : Fin n → ℤ, isoSub E mu).comap (E a b) :=
    iSup_le fun mu y hy =>
      Submodule.mem_comap.mpr (Submodule.mem_iSup_of_mem mu (isotypic_stable_under_gl_operator E mu a b y hy))
  exact hle hx

theorem list_prod_preserves_submodule (W : Submodule K V) (l : List (Module.End K V))
    (h : ∀ u ∈ l, ∀ x ∈ W, u x ∈ W) : ∀ x ∈ W, l.prod x ∈ W := by
  induction l with
  | nil =>
    intro x hx
    simpa using hx
  | cons u l ih =>
    intro x hx
    rw [List.prod_cons]
    show u (l.prod x) ∈ W
    exact h u (by simp) _ (ih (fun v hv => h v (by simp [hv])) x hx)

theorem binomial_preserves_diagonal_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (a : Fin n) (k : ℕ) : ∀ x ∈ W, binomE E a k x ∈ W := by
  unfold binomE
  intro x hx
  rw [LinearMap.smul_apply]
  apply W.smul_mem
  refine list_prod_preserves_submodule W _ ?_ x hx
  intro u hu
  simp only [List.mem_map, List.mem_range] at hu
  obtain ⟨j, -, rfl⟩ := hu
  intro y hy
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  exact W.sub_mem (hW a y hy) (W.smul_mem _ (by simpa using hy))

theorem binomial_subring_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (u : Module.End K V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ W, u x ∈ W := by
  unfold binomialDiagonalSubring at hu
  let S : Subring (Module.End K V) :=
    { carrier := {u | ∀ x ∈ W, u x ∈ W}
      mul_mem' := fun {u v} hu hv x hx => hu _ (hv x hx)
      one_mem' := fun x hx => hx
      add_mem' := fun {u v} hu hv x hx => W.add_mem (hu x hx) (hv x hx)
      zero_mem' := fun x _ => W.zero_mem
      neg_mem' := fun {u} hu x hx => W.neg_mem (hu x hx) }
  have hle : Subring.closure {u | ∃ a k, u = binomE E a k} ≤ S := by
    rw [Subring.closure_le]
    rintro v ⟨a, k, rfl⟩
    exact binomial_preserves_diagonal_stable E W hW a k
  intro x hx
  exact (hle hu : u ∈ S) x hx

theorem weight_projection_mem_weightSpace (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (μ : Fin n → ℤ) (x : V) :
    Θ μ x ∈ weightSp E μ := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ (weightSp E μ).comap (Θ μ) := by
    refine iSup_le fun ν y hy => ?_
    rw [Submodule.mem_comap, hΘ μ ν y hy]
    split_ifs with h
    · subst h
      exact hy
    · exact Submodule.zero_mem _
  exact hle hx

theorem sum_weight_projections_eq_self (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (box : Finset (Fin n → ℤ))
    (hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box) (x : V) : ∑ μ ∈ box, Θ μ x = x := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ LinearMap.ker ((∑ μ ∈ box, Θ μ) - 1) := by
    refine iSup_le fun ν y hy => ?_
    have hy' : ∀ μ, Θ μ y = if ν = μ then y else 0 := fun μ => hΘ μ ν y hy
    rw [LinearMap.mem_ker]
    by_cases hν : weightSp E ν = ⊥
    · have h0 : y = 0 := by
        rw [hν] at hy
        exact (Submodule.mem_bot K).mp hy
      subst h0
      simp
    · simp [hy', hbox ν hν]
  have h := hle hx
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

def negHeightFunctional (ν : Fin n → ℤ) : ℤ := - ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c

theorem negHeight_add_root (ν : Fin n → ℤ) (a b : Fin n) :
    negHeightFunctional (ν + rootW a b) = negHeightFunctional ν + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) := by
  unfold negHeightFunctional rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end

theorem sum_isotypic_top_of_weight_data (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (hs : OperatorsShiftWeightsByRoots E)
    (hb : WeightsBounded E) (hθ : WeightProjectionsIntegralBinomial E) : IsotypicComponentsSpanModule E := by
  classical
  unfold IsotypicComponentsSpanModule
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE (⨆ mu : Fin n → ℤ, isoSub E mu) (fun a b => isotypic_sum_stable_gl_operator E a b)
  by_contra hne
  have hW'ne : W' ≠ ⊥ := by
    intro h0
    rw [h0] at hc
    exact hne (by simpa using hc.sup_eq_top)
  obtain ⟨x, hxW', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'ne
  obtain ⟨m, hm⟩ := hb
  obtain ⟨Θ, hΘm, hΘ⟩ := hθ
  set box : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(m : ℤ)) m) with hboxdef
  have hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hboxdef, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hbox x
  have hex : ∃ ν ∈ box, Θ ν x ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [hsum]; exact hx0
  set S : Finset (Fin n → ℤ) := box.filter (fun ν => W' ⊓ weightSp E ν ≠ ⊥) with hS
  have hSne : S.Nonempty := by
    obtain ⟨ν, hν, hν0⟩ := hex
    refine ⟨ν, ?_⟩
    rw [hS, Finset.mem_filter]
    refine ⟨hν, fun hbot => hν0 ?_⟩
    have : Θ ν x ∈ W' ⊓ weightSp E ν :=
      ⟨binomial_subring_preserves_stable E W' (fun a => hW' a a) (Θ ν) (hΘm ν) x hxW', weight_projection_mem_weightSpace E hE Θ hΘ ν x⟩
    rw [hbot] at this
    simpa using this
  obtain ⟨ν, hνS, hmax⟩ := Finset.exists_max_image S negHeightFunctional hSne
  rw [hS, Finset.mem_filter] at hνS
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hνS.2
  have hraise : ∀ a b : Fin n, a < b → E a b y = 0 := by
    intro a b hab
    by_contra hne0
    have hmem : E a b y ∈ W' ⊓ weightSp E (ν + rootW a b) := ⟨hW' a b y hy.1, hs a b ν y hy.2⟩
    have h1 : W' ⊓ weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmem
      exact hne0 (by simpa using hmem)
    have h2' : weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at h1
      exact h1 (by simp)
    have h3 : ν + rootW a b ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨hbox _ h2', h1⟩
    have h4 := hmax _ h3
    rw [negHeight_add_root] at h4
    have h5 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    linarith
  have hhw : IsHWV E ν y := ⟨hy0, hy.2, hraise⟩
  have hyiso : y ∈ isoSub E ν := Submodule.subset_span ⟨1, (Umon E).one_mem, y, hhw, rfl⟩
  have hyW : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := (le_iSup (fun mu : Fin n → ℤ => isoSub E mu) ν) hyiso
  have : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ W' := ⟨hyW, hy.1⟩
  rw [hc.inf_eq_bot] at this
  exact hy0 (by simpa using this)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivationFinsetSumApply
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem derivation_finset_sum_apply {σ α : Type} (s : Finset α)
    (D : α → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (F : MvPolynomial σ K) :
    (∑ l ∈ s, D l) F = ∑ l ∈ s, D l F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]


open Classical in
def glDerivation (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) :=
  ∑ l : ι, if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin n) K) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin n) K) • pderiv (l, a)))
    else 0

theorem gl_action_eq_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glAct K LL S a b F = glDerivation K LL S a b F := by
  unfold glAct glDerivation
  rw [LinearMap.sum_apply, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

open Classical in
theorem gl_derivation_variable (LL : Letters ι) (S : Set ι) (a b : Fin n) (l : ι) (c : Fin n) :
    glDerivation K LL S a b (X (l, c)) =
      if l ∈ S then (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  unfold glDerivation
  rw [derivation_finset_sum_apply, Finset.sum_eq_single l]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro l' _ hl'
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']
  · simp

theorem gl_derivation_lie_bracket (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    ⁅glDerivation K LL S a b, glDerivation K LL S c d⁆ =
      (if b = c then glDerivation K LL S a d else 0) - (if d = a then glDerivation K LL S c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply]
  by_cases hl : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = d <;> by_cases h4 : e = b <;>
        subst_vars <;> simp_all [gl_derivation_variable] <;> grind
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, map_neg, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = c <;> by_cases h4 : e = a <;>
        subst_vars <;> simp_all [gl_derivation_variable]
  · by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [gl_derivation_variable, hl, h1, h2]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.EnvelopingMonoidPreservesStable
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_action (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, sub_eq_zero]

theorem gl_operator_commutator {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have hx : E a b (E c d x) - E c d (E a b x) = (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
    have h1 := LinearMap.congr_fun (hrel a b c d) x
    split_ifs at h1 ⊢ <;> simpa using h1
  rw [← hx]
  abel

theorem operator_shifts_weight_by_root {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b : Fin n) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diag_action] at hx ⊢
  intro c
  rw [gl_operator_commutator hrel c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb; simp [rootW]
  · subst hca; simp [rootW, Pi.single_apply, hcb, Ne.symm hcb, add_smul]
  · subst hcb; simp [rootW, Pi.single_apply, hca, sub_smul, add_smul]
  · simp [rootW, Pi.single_apply, hca, hcb, Ne.symm hcb]

inductive LoweringWordAlt (E : GLOps n K V) (h : V) : ℕ → V → Prop
  | zero : LoweringWordAlt E h 0 h
  | succ {k : ℕ} {x : V} {a b : Fin n} : b < a → LoweringWordAlt E h k x → LoweringWordAlt E h (k + 1) (E a b x)

def loweringSpan (E : GLOps n K V) (h : V) : Submodule K V := Submodule.span K {x | ∃ k, LoweringWordAlt E h k x}

private theorem c14D_Low_mem_lemma {E : GLOps n K V} {h : V} {k : ℕ} {x : V}
    (hx : LoweringWordAlt E h k x) : x ∈ loweringSpan E h := by
  unfold loweringSpan
  exact Submodule.subset_span ⟨k, hx⟩

theorem lowering_span_stable_lowering (E : GLOps n K V) (h : V) {a b : Fin n} (hab : b < a) (z : V) (hz : z ∈ loweringSpan E h) :
    E a b z ∈ loweringSpan E h := by
  have key : loweringSpan E h ≤ (loweringSpan E h).comap (E a b) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨k, hk⟩
    exact Submodule.mem_comap.mpr (c14D_Low_mem_lemma (LoweringWordAlt.succ hab hk))
  exact key hz

theorem mem_highestWeight_iff (E : GLOps n K V) (lam : Fin n → ℤ) (h : V) :
    h ∈ highestWeightVectors E lam ↔ h ∈ weightSp E lam ∧ ∀ a b, a < b → E a b h = 0 := by
  simp only [highestWeightVectors, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem lowering_word_operator_mem_span {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) (k : ℕ) (x : V) (hx : LoweringWordAlt E h k x) :
    ∀ c d, E c d x ∈ loweringSpan E h := by
  induction hx with
  | zero =>
    intro c d
    have hh' := (mem_highestWeight_iff E lam h).1 hh
    rcases lt_trichotomy c d with hcd | hcd | hcd
    · rw [hh'.2 c d hcd]
      exact Submodule.zero_mem _
    · subst hcd
      rw [(mem_weightSpace_iff_diag_action E lam h).1 hh'.1 c]
      exact Submodule.smul_mem _ _ (c14D_Low_mem_lemma LoweringWordAlt.zero)
    · exact c14D_Low_mem_lemma (LoweringWordAlt.succ hcd LoweringWordAlt.zero)
  | @succ k y a b hab hk ih =>
    intro c d
    rw [gl_operator_commutator hrel c d a b y]
    refine Submodule.add_mem _ (lowering_span_stable_lowering E h hab _ (ih c d)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih c b
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih a d
      · exact Submodule.zero_mem _

theorem lowering_span_stable_all {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) (c d : Fin n) (z : V) (hz : z ∈ loweringSpan E h) :
    E c d z ∈ loweringSpan E h := by
  have key : loweringSpan E h ≤ (loweringSpan E h).comap (E c d) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨k, hk⟩
    exact Submodule.mem_comap.mpr (lowering_word_operator_mem_span hrel lam h hh k y hk c d)
  exact key hz

theorem enveloping_monoid_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ z ∈ W, u z ∈ W := by
  let S : Submonoid (Module.End K V) :=
    { carrier := {f | ∀ z ∈ W, f z ∈ W}
      mul_mem' := by
        intro f g hf hg
        show ∀ z ∈ W, (f * g) z ∈ W
        intro z hz
        exact hf _ (hg z hz)
      one_mem' := by
        show ∀ z ∈ W, (1 : Module.End K V) z ∈ W
        intro z hz
        exact hz }
  have hle : Umon E ≤ S := by
    unfold Umon
    rw [Submonoid.closure_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show ∀ z ∈ W, E a b z ∈ W
    exact hW a b
  exact hle hu

theorem generated_le_lowering_span {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ highestWeightVectors E lam) : generatedSubrep E h ≤ loweringSpan E h := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨u, hu, rfl⟩
  exact enveloping_monoid_preserves_stable E (loweringSpan E h) (fun a b z hz => lowering_span_stable_all hrel lam h hh a b z hz) u hu h
    (c14D_Low_mem_lemma LoweringWordAlt.zero)

def weightHeightSum (mu : Fin n → ℤ) : ℤ := ∑ a : Fin n, (a.val : ℤ) * mu a

theorem heightSum_add_root (mu : Fin n → ℤ) (a b : Fin n) :
    weightHeightSum (mu + rootW a b) = weightHeightSum mu + ((a.val : ℤ) - (b.val : ℤ)) := by
  simp only [weightHeightSum, Pi.add_apply, rootW, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem lowering_word_weight_and_monoid {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (lam : Fin n → ℤ) (h : V) (hh : h ∈ weightSp E lam) (k : ℕ) (x : V) (hx : LoweringWordAlt E h k x) :
    (∃ mu, x ∈ weightSp E mu ∧ weightHeightSum lam + k ≤ weightHeightSum mu) ∧ (∃ u ∈ Umon E, x = u h) ∧ (k = 0 → x = h) := by
  induction hx with
  | zero =>
    refine ⟨⟨lam, hh, by simp⟩, ⟨1, one_mem _, rfl⟩, fun _ => rfl⟩
  | @succ k y a b hab hk ih =>
    obtain ⟨⟨mu, hmu, hht⟩, ⟨u, hu, hyu⟩, -⟩ := ih
    have hE : E a b ∈ Umon E := by
      unfold Umon
      exact Submonoid.subset_closure ⟨(a, b), rfl⟩
    refine ⟨⟨mu + rootW a b, operator_shifts_weight_by_root hrel a b mu y hmu, ?_⟩, ⟨E a b * u, mul_mem hE hu, ?_⟩,
      fun h0 => absurd h0 (Nat.succ_ne_zero k)⟩
    · rw [heightSum_add_root]
      have hab' : b.val < a.val := hab
      push_cast
      omega
    · subst hyu
      rfl

end

theorem hwv_generated_multiple_of_hwv : GeneratedMultipleOfHWV := by
  intro K V _ _ _ n E hE lam h hh
  have hrel := hE.1
  refine le_trans (generated_le_lowering_span hrel lam h hh) ?_
  refine Submodule.span_le.mpr ?_
  rintro x ⟨k, hk⟩
  rw [SetLike.mem_coe]
  obtain ⟨⟨mu, hmu, hht⟩, ⟨u, hu, hxu⟩, h0⟩ :=
    lowering_word_weight_and_monoid hrel lam h ((mem_highestWeight_iff E lam h).1 hh).1 k x hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [h0 hk0]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self h)
  · apply Submodule.mem_sup_right
    have hne : mu ≠ lam := by
      rintro rfl
      omega
    have hg : x ∈ generatedSubrep E h := by
      unfold generatedSubrep
      exact Submodule.subset_span ⟨u, hu, hxu⟩
    have hx : x ∈ weightSp E mu ⊓ generatedSubrep E h := Submodule.mem_inf.mpr ⟨hmu, hg⟩
    exact Submodule.mem_iSup_of_mem mu
      (Submodule.mem_iSup_of_mem (show mu ∈ {mu : Fin n → ℤ | mu ≠ lam} from hne) hx)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightLatticeOfFirstPart
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def LatticeNablaDeltaBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      (∀ x ∈ Nabla (O := O) E lam v, ((p : O) ^ (N0 n * deF p n (ellWt lam))) • x ∈ Delta (O := O) E v)

theorem highest_weight_lattice_of_first_part (D : Formalism.BasicNotions.D7) (h : LatticeNablaDeltaBound) : NablaDeltaComparisonField D := by
  intro p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI
  refine ⟨h p n' O S hR n lam V E v hI, ?_⟩
  intro M hM _ hl
  have := dvr_fraction_field_char_zero_prime S hR.prime
  exact highest_weight_lattice_bounds E hI.1.2.2 lam v M hM.1 hl

end Formalism.MainNotions.G.GLWeightTheory
end
end

