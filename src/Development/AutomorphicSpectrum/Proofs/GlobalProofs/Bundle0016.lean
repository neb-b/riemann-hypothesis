module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentatives

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelSummationByPartsWeights
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity

variable {r : ℕ}

theorem update_add_single (i : Fin r) (m : Fin r → ℕ) (n k : ℕ) :
    Function.update (m + (Pi.single i n : Fin r → ℕ)) i k = Function.update m i k := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

theorem update_self_add (i : Fin r) (m : Fin r → ℕ) (e : ℕ) :
    Function.update m i (m i + e) = m + (Pi.single i e : Fin r → ℕ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

theorem partialSum_succ (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    partialSum i v (m + Pi.single i 1) = partialSum i v m + v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_succ, Function.update_eq_self]

theorem partialSum_of_zero (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (h : m i = 0) :
    partialSum i v m = 0 := by
  simp [partialSum, h]

theorem partialSumMean_add_single_one (l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    meanP l i v (m + Pi.single i 1) = meanP l i v m := by
  simp only [meanP, update_add_single]

theorem partialSum_period {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : GoodAt l i v)
    (m : Fin r → ℕ) : partialSum i v (m + Pi.single i l) = partialSum i v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_add]
  have h2 : ∑ e ∈ Finset.range l, v (Function.update m i (m i + e)) = 0 := by
    simp only [update_self_add]
    exact h.2 m
  rw [h2, add_zero]

theorem partialSum_bound {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (h : GoodAt l i v) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m, |(v m : ℝ)| ≤ C) :
    ∀ m, |(partialSum i v m : ℝ)| ≤ l * C := by
  have key : ∀ n, ∀ m : Fin r → ℕ, m i = n → |(partialSum i v m : ℝ)| ≤ l * C := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hm
      by_cases hn : n < l
      · simp only [partialSum, hm]
        push_cast
        calc |∑ k ∈ Finset.range n, (v (Function.update m i k) : ℝ)|
            ≤ ∑ k ∈ Finset.range n, |(v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _
          _ = n * C := by simp
          _ ≤ l * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hn.le) hC0
      · rw [not_lt] at hn
        have hmm : m = Function.update m i (n - l) + Pi.single i l := by
          funext j
          by_cases hj : j = i
          · subst hj
            simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]
            omega
          · simp [Function.update_apply, hj, Pi.single_apply]
        rw [hmm, partialSum_period h]
        exact ih (n - l) (by omega) _ (by simp)
  exact fun m => key (m i) m rfl

theorem abs_partialSumMean_le {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    {K : ℝ} (hK : ∀ m, |(partialSum i v m : ℝ)| ≤ K) (m : Fin r → ℕ) :
    |(meanP l i v m : ℝ)| ≤ K := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  simp only [meanP]
  push_cast
  rw [abs_div, abs_of_pos hl', div_le_iff₀ hl']
  calc |∑ k ∈ Finset.range l, (partialSum i v (Function.update m i k) : ℝ)|
      ≤ ∑ k ∈ Finset.range l, |(partialSum i v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range l, K := Finset.sum_le_sum fun k _ => hK _
    _ = K * l := by simp [mul_comm]

theorem summable_cast_mul {α : Type*} (w : α → ℚ) (K : ℝ) (hw : ∀ m, |(w m : ℝ)| ≤ K)
    {g : α → ℂ} (hg : Summable g) : Summable (fun m => (w m : ℂ) * g m) := by
  have hn : Summable (fun m => ‖g m‖) := by
    first
      | exact hg.norm
      | exact summable_norm_iff.mpr hg
  refine Summable.of_norm_bounded (hn.mul_left K) (fun m => ?_)
  rw [norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hw m) (norm_nonneg _)

theorem stepIdentity (r l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (g : (Fin r → ℕ) → ℂ)
    (hl : 0 < l) (hgood : GoodAt l i v) (hv : BddW v) (hg : Summable g) :
    ∑' m, (v m : ℂ) * g m = ∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m := by
  obtain ⟨C, hC⟩ := hv
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hlC : 0 ≤ (l : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC0
  have hPS := partialSum_bound hl hgood hC0 hC
  have hMP : ∀ m, |(meanP l i v m : ℝ)| ≤ l * C := abs_partialSumMean_le hl hPS
  set δ : Fin r → ℕ := Pi.single i 1 with hδ
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  have hBb : ∀ m, |(Bop l i v m : ℝ)| ≤ l * C := by
    intro m
    unfold Bop
    split_ifs
    · exact hMP m
    · rw [Rat.cast_zero, abs_zero]
      exact hlC
  have hAb : ∀ m, |(Aop l i v m : ℝ)| ≤ 2 * (l * C) := by
    intro m
    simp only [Aop, Rat.cast_sub]
    calc _ ≤ |(partialSum i v (m + Pi.single i 1) : ℝ)| + |(meanP l i v m : ℝ)| := hsub _ _
      _ ≤ l * C + l * C := add_le_add (hPS _) (hMP m)
      _ = _ := by ring
  let T : (Fin r → ℕ) → ℂ := fun m =>
    ((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℂ) * g m
  have hTb : ∀ m, |((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℝ)| ≤ 3 * (l * C) := by
    intro m
    push_cast
    calc _ ≤ |(partialSum i v m : ℝ) - meanP l i v m| + |(Bop l i v m : ℝ)| := abs_add_le _ _
      _ ≤ (|(partialSum i v m : ℝ)| + |(meanP l i v m : ℝ)|) + |(Bop l i v m : ℝ)| :=
          add_le_add (hsub _ _) le_rfl
      _ ≤ (l * C + l * C) + l * C := add_le_add (add_le_add (hPS m) (hMP m)) (hBb m)
      _ = _ := by ring
  have hinj : Function.Injective (fun m : Fin r → ℕ => m + δ) := add_left_injective δ
  have hgs : Summable (fun m => g (m + δ)) := hg.comp_injective hinj
  have hfd : Summable (fd i g) := by
    have : fd i g = fun m => g (m + δ) - g m := rfl
    rw [this]
    exact hgs.sub hg
  have hsB : Summable (fun m => (Bop l i v m : ℂ) * g m) := summable_cast_mul _ _ hBb hg
  have hsA : Summable (fun m => (Aop l i v m : ℂ) * fd i g m) := summable_cast_mul _ _ hAb hfd
  have hsT : Summable T := summable_cast_mul _ _ hTb hg
  have hsT' : Summable (fun m => T (m + δ)) := hsT.comp_injective hinj
  have hT0 : ∀ m, m i = 0 → T m = 0 := by
    intro m hm
    simp [T, Bop, hm, partialSum_of_zero i v m hm]
  have hBs : ∀ m, Bop l i v (m + δ) = 0 := by
    intro m
    simp [Bop, δ]
  have hpt : ∀ m, (v m : ℂ) * g m =
      ((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m) := by
    intro m
    have h1 := partialSum_succ i v m
    have h2 := partialSumMean_add_single_one l i v m
    have h3 : Bop l i v (m + Pi.single i 1) = 0 := hBs m
    simp only [T, Aop, fd, hδ, h1, h2, h3]
    push_cast
    ring
  have hshift : ∑' m, T (m + δ) = ∑' m, T m := by
    refine hinj.tsum_eq (f := T) ?_
    intro m hm
    have hmi : m i ≠ 0 := fun h0 => hm (hT0 m h0)
    refine ⟨m - δ, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.sub_apply, δ, Pi.single_eq_same]
      omega
    · simp [δ, Pi.single_apply, hj]
  calc ∑' m, (v m : ℂ) * g m
      = ∑' m, (((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m)) :=
        tsum_congr hpt
    _ = (∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m) +
          (∑' m, T (m + δ) - ∑' m, T m) := by
        rw [(hsB.sub hsA).tsum_add (hsT'.sub hsT), hsB.tsum_sub hsA, hsT'.tsum_sub hsT]
    _ = _ := by rw [hshift, sub_self, add_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrank
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard

theorem finite_and_card_realEmbeddings (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  have e : (F →+* ℝ) ≃ (F →+* ℂ) :=
    { toFun := fun σ => Complex.ofRealHom.comp σ
      invFun := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
      left_inv := fun σ => by
        ext x
        apply Complex.ofReal_injective
        simp [ComplexEmbedding.IsReal.coe_embedding_apply]
      right_inv := fun φ => by
        ext x
        simp [ComplexEmbedding.IsReal.coe_embedding_apply] }
  have hc : Nat.card (F →+* ℂ) = Module.finrank ℚ F := by
    rw [Nat.card_eq_fintype_card]
    exact Embeddings.card F ℂ
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComboNotMemSpan
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.StellarLI

theorem combo_notMem_span {V : Type} [AddCommGroup V] [Module ℚ V] {s : Set V} {p q : V} {a b : ℚ}
    (ha : a ≠ 0) (hp : p ∉ Submodule.span ℚ s) (hq : q ∈ Submodule.span ℚ s) :
    a • p + b • q ∉ Submodule.span ℚ s := by
  intro h
  apply hp
  have h1 : a • p ∈ Submodule.span ℚ s := by
    have := Submodule.sub_mem _ h (Submodule.smul_mem _ b hq)
    simpa using this
  have h2 := Submodule.smul_mem _ a⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2

theorem main : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq V] (p q : V) (r : Finset V) (a b : ℚ), 0 < a → 0 < b → p ≠ q → p ∉ r → q ∉ r →
  LinearIndepOn ℚ id ((insert p (insert q r) : Finset V) : Set V) →
  (a • p + b • q) ∉ r ∧ (a • p + b • q) ≠ p ∧ (a • p + b • q) ≠ q ∧
  LinearIndepOn ℚ id ((insert (a • p + b • q) (insert q r) : Finset V) : Set V) ∧
  LinearIndepOn ℚ id ((insert p (insert (a • p + b • q) r) : Finset V) : Set V) ∧
  LinearIndepOn ℚ id ((insert (a • p + b • q) r : Finset V) : Set V) := by
  intro V _ _ _ p q r a b ha hb hpq hpr hqr hli
  simp only [Finset.coe_insert] at hli ⊢
  have hp' : p ∉ insert q (r : Set V) := by simp [hpq, hpr]
  have hq' : q ∉ (r : Set V) := by simpa using hqr
  have hq'' : q ∉ insert p (r : Set V) := by simp [hpq.symm, hqr]
  obtain ⟨hli1, hpn⟩ := (linearIndepOn_id_insert hp').mp hli
  obtain ⟨hliR, -⟩ := (linearIndepOn_id_insert hq').mp hli1
  have hli' : LinearIndepOn ℚ id (insert q (insert p (r : Set V))) := by rwa [Set.insert_comm]
  obtain ⟨hli2, hqn2⟩ := (linearIndepOn_id_insert hq'').mp hli'
  have hw1 : a • p + b • q ∉ Submodule.span ℚ (insert q (r : Set V)) :=
    combo_notMem_span ha.ne' hpn (Submodule.subset_span (Set.mem_insert q _))
  have hw2 : a • p + b • q ∉ Submodule.span ℚ (insert p (r : Set V)) := by
    rw [add_comm]
    exact combo_notMem_span hb.ne' hqn2 (Submodule.subset_span (Set.mem_insert p _))
  have hw3 : a • p + b • q ∉ Submodule.span ℚ (r : Set V) := fun h =>
    hw1 (Submodule.span_mono (Set.subset_insert q _) h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hw3 (Submodule.subset_span (Finset.mem_coe.mpr h))
  · intro h
    exact hw2 (by rw [h]; exact Submodule.subset_span (Set.mem_insert p _))
  · intro h
    exact hw1 (by rw [h]; exact Submodule.subset_span (Set.mem_insert q _))
  · exact (linearIndepOn_id_insert fun h => hw1 (Submodule.subset_span h)).mpr ⟨hli1, hw1⟩
  · rw [Set.insert_comm]
    exact (linearIndepOn_id_insert fun h => hw2 (Submodule.subset_span h)).mpr ⟨hli2, hw2⟩
  · exact (linearIndepOn_id_insert fun h => hw3 (Submodule.subset_span h)).mpr ⟨hliR, hw3⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.StellarLI
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBound
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem one_le_sizeE_of_nonneg {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i) : 1 ≤ sizeE x := by
  unfold sizeE
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx i)
  linarith

theorem linF_comparable_sizeE {ι : Type} {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      c * sizeE x ≤ linF a b j x ∧ linF a b j x ≤ C * sizeE x := by
  let f : Option (Fin r) → ℝ := fun o => o.elim (b j) (a j)
  obtain ⟨p, hp⟩ := Finite.exists_min f
  obtain ⟨q, hq⟩ := Finite.exists_max f
  have hpos : ∀ o, 0 < f o := by
    intro o
    cases o with
    | none => exact hb
    | some i => exact ha i
  refine ⟨f p, f q, hpos p, hpos q, fun x hx => ?_⟩
  unfold linF sizeE
  constructor
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hp none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp (some i)) (hx i))
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hq none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hq (some i)) (hx i))

theorem rpow_le_of_comparable (c C T : ℝ) (hc : 0 < c) (hC : 0 < C) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L E t D : ℝ, 1 ≤ E → c * E ≤ L → L ≤ C * E → |t| ≤ T → t ≤ D →
      L ^ t ≤ K * E ^ D := by
  refine ⟨Real.exp ((|Real.log c| + |Real.log C|) * T), (Real.exp_pos _).le, ?_⟩
  intro L E t D hE h1 h2 ht htD
  have hE0 : 0 < E := by linarith
  have hL : 0 < L := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hu : 0 < L / E := div_pos hL hE0
  have hu1 : c ≤ L / E := (le_div_iff₀ hE0).2 h1
  have hu2 : L / E ≤ C := (div_le_iff₀ hE0).2 h2
  have hlog1 : Real.log c ≤ Real.log (L / E) := Real.log_le_log hc hu1
  have hlog2 : Real.log (L / E) ≤ Real.log C := Real.log_le_log hu hu2
  have habs : |Real.log (L / E)| ≤ |Real.log c| + |Real.log C| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log c)
      have := abs_nonneg (Real.log C)
      linarith
    · have := le_abs_self (Real.log C)
      have := abs_nonneg (Real.log c)
      linarith
  have hLE : L = (L / E) * E := by field_simp
  have hfirst : (L / E) ^ t ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) := by
    rw [Real.rpow_def_of_pos hu]
    apply Real.exp_le_exp.2
    calc Real.log (L / E) * t ≤ |Real.log (L / E) * t| := le_abs_self _
      _ = |Real.log (L / E)| * |t| := abs_mul _ _
      _ ≤ (|Real.log c| + |Real.log C|) * T :=
        mul_le_mul habs ht (abs_nonneg _) (by positivity)
  have hsecond : E ^ t ≤ E ^ D := Real.rpow_le_rpow_of_exponent_le hE htD
  calc L ^ t = (L / E) ^ t * E ^ t := by
        rw [← Real.mul_rpow hu.le hE0.le, ← hLE]
    _ ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) * E ^ D :=
        mul_le_mul hfirst hsecond (Real.rpow_nonneg hE0.le _) (Real.exp_pos _).le

theorem prod_zpow_eq_zpow_sum {ι : Type} (E : ℝ) (hE : E ≠ 0) (S : Finset ι) (f : ι → ℤ) :
    ∏ j ∈ S, E ^ f j = E ^ ∑ j ∈ S, f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hE]

theorem norm_factor_le {ι : Type} (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) (B R β : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β : ℂ))‖ ≤ K * sizeE x ^ ((B : ℤ) - (β : ℤ)) := by
  obtain ⟨c, C, hc, hC, hcmp⟩ := linF_comparable_sizeE a b j ha hb
  obtain ⟨K, hK0, hK⟩ := rpow_le_of_comparable c C ((R : ℝ) + β) hc hC (by positivity)
  refine ⟨K, hK0, fun s hs hs' x hx => ?_⟩
  have hE := one_le_sizeE_of_nonneg x hx
  have hE0 : 0 < sizeE x := by linarith
  obtain ⟨h1, h2⟩ := hcmp x hx
  have hL : 0 < linF a b j x := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hre : (-s - (β : ℂ)).re = -s.re - β := by simp
  have hsr : |s.re| ≤ R := (Complex.abs_re_le_norm s).trans hs
  have hβ : (0 : ℝ) ≤ β := by positivity
  have ht : |-s.re - (β : ℝ)| ≤ (R : ℝ) + β := by
    rw [abs_le] at hsr ⊢
    constructor <;> linarith [hsr.1, hsr.2]
  have htD : -s.re - (β : ℝ) ≤ (((B : ℤ) - (β : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hL, hre, ← Real.rpow_intCast]
  exact hK _ _ _ _ hE h1 h2 ht htD

theorem baseBound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  intro ι _ r a b ha hb B R β
  have hj := fun j => norm_factor_le r a b j (ha j) (hb j) B R (β j)
  choose K hK0 hK using hj
  refine ⟨∏ j, K j, Finset.prod_nonneg fun j _ => hK0 j, fun s hs hs' x hx => ?_⟩
  have hE0 : sizeE x ≠ 0 := by
    have := one_le_sizeE_of_nonneg x hx
    intro h
    linarith
  unfold Fr
  rw [norm_prod]
  calc ∏ j, ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β j : ℂ))‖
      ≤ ∏ j, (K j * sizeE x ^ ((B : ℤ) - (β j : ℤ))) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hK j s hs hs' x hx)
    _ = (∏ j, K j) * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
        rw [Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum _ hE0, Finset.sum_sub_distrib]
        simp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeTilingBySignRegions
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_coneTerm_neg_nat_rational :
    ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  intro ι _ r a b p h cs
  induction cs with
  | nil =>
    choose q hq using h
    refine ⟨q, fun m => ?_⟩
    show GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm a b (-(p : ℂ)) m = _
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm, neg_neg, Complex.cpow_natCast]
    rw [← Complex.ofReal_ratCast, ← hq m]
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  | cons c cs ih =>
    obtain ⟨ρ, hρ⟩ := ih
    refine ⟨fun m => ρ (m + Pi.single c 1) - ρ m, fun m => ?_⟩
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at hρ ⊢
    rw [hρ, hρ, Rat.cast_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitPowerInCongruence
section
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem exists_pow_mem_congUnits : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  intro F _ _ 𝔣 h𝔣
  haveI : Finite (𝓞 F ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  have hpos : 0 < Nat.card (𝓞 F ⧸ 𝔣)ˣ := Nat.card_pos
  refine ⟨2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ, by omega, fun u => ⟨?_, fun σ => ?_⟩⟩
  · have h1 : (Units.map (Ideal.Quotient.mk 𝔣 : 𝓞 F →* 𝓞 F ⧸ 𝔣) u) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) = 1 := by
      rw [mul_comm, pow_mul, pow_card_eq_one', one_pow]
    have h2 : Ideal.Quotient.mk 𝔣 ((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) = Ideal.Quotient.mk 𝔣 1 := by
      have h3 := congrArg (fun z : (𝓞 F ⧸ 𝔣)ˣ => (z : 𝓞 F ⧸ 𝔣)) h1
      simpa using h3
    exact Ideal.Quotient.eq.mp h2
  · have hne : σ (((u : 𝓞 F)) : F) ≠ 0 := by
      rw [Ne, map_eq_zero]
      simp
    have h : (((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) : F) = (((u : 𝓞 F)) : F) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) := by
      simp
    rw [h, map_pow, pow_mul]
    exact pow_pos (by positivity) _

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentativesStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_group_finite_representatives : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
    ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay <;> assumption)
end

