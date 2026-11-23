module

public import ReciprocityTheory.SemistableReduction.Bundle0004
public import Mathlib
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
public import ReciprocityTheory.SemistableReduction.Bundle0012
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import ReciprocityTheory.SemistableReduction.Bundle0005
public import ReciprocityTheory.SemistableReduction.Bundle0007
public import ReciprocityTheory.SemistableReduction.Bundle0011
public import ReciprocityTheory.SemistableReduction.Bundle0013
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.SemistableReduction.Bundle0010
public import ReciprocityTheory.SemistableReduction.Bundle0016

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.AlgAll
section
namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem fieldOfS : FieldOfSStatement := genericImageFinite

theorem dedekindRank : DedekindRankStatement := integralClosureRank_and_residueTrdegLe.1

theorem residueTrdeg : ResidueTrdegStatement := residueTrdeg_holds residueTrdegLe

theorem normLength : NormLengthStatement := gaugeSplitting_holds

theorem normOrd : NormOrdStatement := normValuation_eq_factorization normLength

end ReciprocityTheory.MultiplicativeHeights.Closed
end

-- bundled from ReciprocityTheory.SemistableReduction.ApproxBasis
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

private theorem normSq_smul_eq_norm_sq_mul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    normSq (c • u) = ‖c‖ ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

private theorem le_approxR {r : ℕ} (hr : 0 < r) {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : μ ≤ approxR r μ ρ := by
  unfold approxR
  have h1 : (1 : ℝ) ≤ Real.sqrt r := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hr)
  rw [le_div_iff₀ hρ]
  nlinarith [mul_le_mul_of_nonneg_left hρ1 hμ.le, mul_le_mul_of_nonneg_left h1 hμ.le]

private theorem normSq_le_of_normSq_sub_approxR_single_le {r : ℕ} {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (j : Fin r) (x : Fin r → ℂ)
    (hx : normSq (x - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) :
    normSq x ≤ (2 * approxR r μ ρ) ^ 2 := by
  have hR := le_approxR j.pos hμ hρ hρ1
  have h := approxB_normSq_add_le (x - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
    ((approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
  rw [sub_add_cancel, approxB_normSq_single] at h
  nlinarith [mul_le_mul hR hR hμ.le (le_trans hμ.le hR)]

private theorem mulVec_embVec_sum_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (Q : Matrix (Fin r) (Fin r) ℂ) {α : Type*} (s : Finset α) (g : α → K) (f : α → Fin r → K) :
    Q *ᵥ embVec σ (∑ j ∈ s, g j • f j) = ∑ j ∈ s, σ (g j) • (Q *ᵥ embVec σ (f j)) := by
  rw [approxB_embVec_sum, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [approxB_embVec_smul, Matrix.mulVec_smul]

theorem approxBasis_holds (hG : ApproxGraphStatement) : ApproxStatement := by
  unfold ApproxGraphStatement at hG
  unfold ApproxStatement
  intro K _ _ ι _ _ r p S σ Q L v μ ρ hp hμ hρ hρ1 hQ hS hInt hcov hvL hvi hvμ
  choose l0 hl0L hl0 using fun j : Fin r =>
    hcov (fun _ => (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
  obtain ⟨X, hX⟩ : ∃ X : ι → Fin r → Fin r → ℂ,
      ∀ i j, X i j = Q i *ᵥ embVec (σ i) (l0 j) := ⟨_, fun _ _ => rfl⟩
  have happ : ∀ i j, normSq (X i j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
      ≤ μ ^ 2 := by
    intro i j
    rw [hX]
    refine le_trans ?_ (hl0 j)
    exact Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') (l0 j) -
      (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))) (fun i' _ => approxB_normSq_nonneg _)
      (Finset.mem_univ i)
  have hGi := fun i => hG r p μ ρ (X i) hp hμ hρ hρ1 (fun j _ => happ i j)
  have hdiag : ∀ i j, normSq (X i j) ≤ (2 * approxR r μ ρ) ^ 2 :=
    fun i j => normSq_le_of_normSq_sub_approxR_single_le hμ hρ hρ1 j _ (happ i j)
  have hinj : ∀ g : ApproxPosIdx r p → K,
      (∀ k : ApproxPosIdx r p, S.h (l0 k.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0) → g = 0 := by
    intro g hg
    by_contra hne
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hzz : S.h (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0 := by
      rw [approxB_h_sum_left]
      exact Finset.sum_eq_zero fun j _ => by rw [approxB_h_smul_left, hg j, mul_zero]
    have h1 := hS i (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1)
    rw [hzz, map_zero, mulVec_embVec_sum_smul] at h1
    have hx : (fun k : ApproxPosIdx r p => σ i (g k)) ≠ 0 := by
      intro hx
      apply hne
      funext k
      exact (map_eq_zero (σ i)).mp (congrFun hx k)
    have h2 := (approxB_graph_pos hρ1 hρ (X i) (hGi i).1 (fun k => σ i (g k))).2 hx
    simp only [hX] at h2
    rw [← h1] at h2
    simp at h2
  obtain ⟨Δ, coef, a, hΔ0, hΔ, horth, hmem, hli⟩ :=
    approxB_split hp S L hInt l0 v hl0L hvi hinj
  obtain ⟨la, hla⟩ : ∃ la : Fin r → Fin r → K, la = fun j : Fin r => if h : (j : ℕ) < p then l0 j
      else Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1 := ⟨_, rfl⟩
  have hla_pos : ∀ (j : Fin r) (h : (j : ℕ) < p), la j = l0 j := fun j h => by
    rw [hla]; simp only [dif_pos h]
  have hla_neg : ∀ (j : Fin r) (h : ¬ (j : ℕ) < p), la j =
      Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1 := fun j h => by
    rw [hla]; simp only [dif_neg h]
  have hli' : LinearIndependent K la := by rw [hla]; exact hli
  have horth' : ∀ (k : Fin r), (k : ℕ) < p → ∀ j : Fin r, ¬ (j : ℕ) < p →
      S.h (l0 k) (la j) = 0 := fun k hk j hj => by
    rw [hla_neg j hj]; exact horth _ ⟨k, hk⟩
  have hdet : ∀ i, ((Matrix.of la).map (σ i)).det ≠ 0 := by
    intro i
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hu : IsUnit (Matrix.of la) :=
      (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of la)).mp hli'
    exact (map_ne_zero (σ i)).mpr ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have hcomb : ∀ i (w : Fin r → ℂ),
      Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • (Q i *ᵥ embVec (σ i) (la j)) := by
    intro i w
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
  have hne : ∀ i (w : Fin r → ℂ), w ≠ 0 → Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) ≠ 0 := by
    intro i w hw h0
    apply hw
    have h1 := Matrix.eq_zero_of_mulVec_eq_zero (hQ i) h0
    refine Matrix.eq_zero_of_vecMul_eq_zero (hdet i) ?_
    rw [← h1]
    funext b
    simp [Matrix.vecMul, dotProduct, embVec, Finset.sum_apply]
  refine ⟨la, fun j => ?_, hli', ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : (j : ℕ) < p
    · rw [hla_pos j h]; exact hl0L j
    · rw [hla_neg j h]; exact hmem _ (hvL _)
  · intro j k hj hk
    rw [hla_pos j hj]
    exact horth' j hj k (not_lt.mpr hk)
  · intro i w hw
    have hsum : Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • X i j := by
      rw [hcomb]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (j : ℕ) < p
      · rw [hla_pos j h, hX]
      · rw [hw j (not_lt.mp h), zero_smul, zero_smul]
    rw [hsum]
    obtain ⟨h1, h2⟩ := (hGi i).1 w hw
    refine ⟨h1, fun hw0 => ?_⟩
    have h3 := h2 hw0
    rw [approxB_jForm_self_re]
    have hq : (ρ / 3) ^ 2 < 1 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hq h3]
  · intro i w hw hw0
    refine (hGi i).2.1 _ (fun j hj => ?_) (hne i w hw0)
    rw [hcomb, approxB_jForm_sum_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [approxB_jForm_smul_right]
    by_cases hk : (k : ℕ) < p
    · rw [hw k hk, zero_mul]
    · rw [hX, ← hS, horth' j hj k hk, map_zero, mul_zero]
  · intro i j hj
    rw [hS i, hla_pos j hj, ← hX]
    exact le_trans (approxB_norm_jForm_self_le p _) (hdiag i j)
  · intro i j hj
    have hj' : ¬ (j : ℕ) < p := not_lt.mpr hj
    obtain ⟨x, hx⟩ : ∃ x, x = v (a ⟨j, hj'⟩) := ⟨_, rfl⟩
    rw [hS i, hla_neg j hj', ← hx]
    have hort : ∀ k : Fin r, (k : ℕ) < p → jForm p (X i k) (Q i *ᵥ embVec (σ i)
        (Δ • x - ∑ k', coef x k' • l0 k'.1)) = 0 := by
      intro k hk
      have h0 : S.h (l0 k) (Δ • x - ∑ k', coef x k' • l0 k'.1) = 0 := horth x ⟨k, hk⟩
      rw [hX, ← hS, h0, map_zero]
    have hspan : Q i *ᵥ embVec (σ i) (Δ • x) -
        Q i *ᵥ embVec (σ i) (Δ • x - ∑ k', coef x k' • l0 k'.1)
        ∈ Submodule.span ℂ (X i '' {j | (j : ℕ) < p}) := by
      rw [← Matrix.mulVec_sub, ← approxB_embVec_sub, sub_sub_cancel, mulVec_embVec_sum_smul]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.1, k.2, hX i k.1⟩)
    have hb := (hGi i).2.2 _ _ hort hspan
    rw [approxB_embVec_smul, Matrix.mulVec_smul, normSq_smul_eq_norm_sq_mul] at hb
    have hxμ : normSq (Q i *ᵥ embVec (σ i) x) ≤ μ ^ 2 := by
      refine le_trans (Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') x))
        (fun _ _ => approxB_normSq_nonneg _) (Finset.mem_univ i)) ?_
      rw [hx]
      exact hvμ _
    have hgram : (σ i).mapMatrix (Matrix.of fun k j : ApproxPosIdx r p => S.h (l0 k.1) (l0 j.1)) =
        Matrix.of fun k j : ApproxPosIdx r p => jForm p (X i k.1) (X i j.1) := by
      ext k j
      simp [RingHom.mapMatrix_apply, hS, hX]
    have hΔbd : ‖σ i Δ‖ ≤ ((2 * approxR r μ ρ) ^ 2) ^ p := by
      rw [hΔ, RingHom.map_det, hgram]
      have h := approxB_det_le_of_posSemidef _ (approxB_gram_posSemidef hρ1 hρ (X i) (hGi i).1)
        ((2 * approxR r μ ρ) ^ 2) fun k => by
          simp only [Matrix.of_apply]
          exact le_trans (Complex.re_le_norm _)
            (le_trans (approxB_norm_jForm_self_le p _) (hdiag i k.1))
      rwa [approxB_card_pos hp] at h
    have hsq : ‖σ i Δ‖ ^ 2 ≤ (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hΔbd 2
    have hpow : (2 * approxR r μ ρ) ^ (4 * p) =
        (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2 := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [hpow]
    refine le_trans hb ?_
    have hs0 := approxB_normSq_nonneg (Q i *ᵥ embVec (σ i) x)
    nlinarith [mul_le_mul hsq hxμ hs0 (by positivity)]

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.ApproxGraphC
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

lemma jForm_zero_left (p : ℕ) {r : ℕ} (y : Fin r → ℂ) : jForm p 0 y = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.jForm]

lemma jForm_add_left (p : ℕ) {r : ℕ} (x x' y : Fin r → ℂ) :
    jForm p (x + x') y = jForm p x y + jForm p x' y := by
  simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]

lemma jForm_smul_left (p : ℕ) {r : ℕ} (c : ℂ) (x y : Fin r → ℂ) :
    jForm p (c • x) y = conj c * jForm p x y := by
  simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma jForm_sum_left (p : ℕ) {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ)
    (y : Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jForm_add_left, ih]

lemma jForm_span_zero (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (y : Fin r → ℂ)
    (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (w : Fin r → ℂ)
    (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) : jForm p (∑ j, w j • X j) y = 0 := by
  rw [jForm_sum_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [jForm_smul_left]
  by_cases hj : (j : ℕ) < p
  · rw [hy j hj, mul_zero]
  · rw [hw j (not_lt.mp hj), map_zero, zero_mul]

lemma pos_small_of_orth {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) :
    ‖euc (posPart p y)‖ ≤ ρ / 3 * ‖euc (negPart p y)‖ := by
  obtain ⟨w, hw, hwb⟩ := exists_graph_pos X hμ hρ hρ1 hX y
  have h0 : ReciprocityTheory.MultiplicativeHeights.jForm p (∑ j, w j • X j) y = 0 := jForm_span_zero p X y hy w hw
  have hb := (graph_bound X hμ hρ hρ1 hX w hw).1
  rw [hwb] at hb
  rw [jForm_eq, hwb, sub_eq_zero] at h0
  have h1 := congrArg (fun z : ℂ => (RCLike.re z : ℝ)) h0
  rw [inner_self_eq_norm_sq] at h1
  have h2 : ‖euc (posPart p y)‖ ^ 2 ≤
      ‖euc (negPart p (∑ j, w j • X j))‖ * ‖euc (negPart p y)‖ :=
    h1 ▸ (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hA := norm_nonneg (euc (posPart p y))
  have hB := norm_nonneg (euc (negPart p y))
  have h3 : ‖euc (posPart p y)‖ ^ 2 ≤
      ρ / 3 * ‖euc (posPart p y)‖ * ‖euc (negPart p y)‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hb hB)
  rcases hA.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (div_nonneg hρ.le (by norm_num)) hB
  · nlinarith

lemma approxGraph_two {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (hy0 : y ≠ 0) :
    (jForm p y y).re < 0 := by
  have hs := pos_small_of_orth X hμ hρ hρ1 hX y hy
  rw [jForm_self, Complex.ofReal_re, posSq_eq, negSq_eq]
  have hA := norm_nonneg (euc (posPart p y))
  have hB := norm_nonneg (euc (negPart p y))
  have hB0 : 0 < ‖euc (negPart p y)‖ := by
    refine lt_of_le_of_ne hB fun h => hy0 ?_
    have hA0 : ‖euc (posPart p y)‖ = 0 :=
      le_antisymm (by rw [← h, mul_zero] at hs; exact hs) hA
    rw [← posPart_add_negPart p y, euc_eq_zero (norm_eq_zero.mp hA0),
      euc_eq_zero (norm_eq_zero.mp h.symm), add_zero]
  have hk : ρ / 3 ≤ 1 / 3 := by linarith
  have hs' : ‖euc (posPart p y)‖ ≤ ‖euc (negPart p y)‖ / 3 :=
    hs.trans (by nlinarith)
  nlinarith [mul_le_mul hs' hs' hA (by linarith : (0 : ℝ) ≤ ‖euc (negPart p y)‖ / 3)]

private theorem exists_coeffs_of_mem_span_lemma {r p : ℕ} (X : Fin r → Fin r → ℂ) {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧ u = ∑ j, w j • X j := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨(Pi.single j 1 : Fin r → ℂ), fun k hk => ?_, ?_⟩
    · have hkj : k ≠ j := fun h => by subst h; exact (not_lt.mpr hk) hj
      simp [hkj]
    · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨c • a, fun j hj => by simp [ha j hj], ?_⟩
    simp [Finset.smul_sum, smul_smul]

lemma approxGraph_three {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (v y : Fin r → ℂ) (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0)
    (hvy : v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p})) :
    ‖jForm p y y‖ ≤ 2 * normSq v := by
  obtain ⟨w, hw, hu⟩ := exists_coeffs_of_mem_span_lemma X hvy
  have hv : v = y + ∑ j, w j • X j := by rw [← hu]; abel
  have h0 : ReciprocityTheory.MultiplicativeHeights.jForm p (∑ j, w j • X j) y = 0 := jForm_span_zero p X y hy w hw
  have hb := (graph_bound X hμ hρ hρ1 hX w hw).1
  have hs := pos_small_of_orth X hμ hρ hρ1 hX y hy
  rw [jForm_eq, sub_eq_zero] at h0
  have hre : RCLike.re (inner ℂ (euc (posPart p y))
        (euc (posPart p (∑ j, w j • X j)))) =
      RCLike.re (inner ℂ (euc (negPart p y)) (euc (negPart p (∑ j, w j • X j)))) := by
    rw [inner_re_symm, h0, inner_re_symm]
  have hI := (RCLike.abs_re_le_norm (inner ℂ (euc (negPart p y))
    (euc (negPart p (∑ j, w j • X j))))).trans (norm_inner_le_norm _ _)
  rw [jForm_self, Complex.norm_real, Real.norm_eq_abs, normSq_split p v, posSq_eq,
    posSq_eq, negSq_eq, negSq_eq, hv, posPart_add, negPart_add, euc_add,
    euc_add, norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hre]
  have hPy := norm_nonneg (euc (posPart p y))
  have hNy := norm_nonneg (euc (negPart p y))
  have hPu := norm_nonneg (euc (posPart p (∑ j, w j • X j)))
  have hNu := norm_nonneg (euc (negPart p (∑ j, w j • X j)))
  have hk : ρ / 3 ≤ 1 / 3 := by linarith
  have hs' : ‖euc (posPart p y)‖ ≤ ‖euc (negPart p y)‖ / 3 :=
    hs.trans (by nlinarith)
  have hb' : ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (posPart p (∑ j, w j • X j))‖ / 3 :=
    hb.trans (by nlinarith)
  have hI' := (abs_le.mp hI).1
  have ha : ‖euc (posPart p y)‖ ^ 2 ≤ ‖euc (negPart p y)‖ ^ 2 := by nlinarith
  have hc : ‖euc (negPart p y)‖ * ‖euc (negPart p (∑ j, w j • X j))‖ ≤
      ‖euc (negPart p y)‖ * (‖euc (posPart p (∑ j, w j • X j))‖ / 3) :=
    mul_le_mul_of_nonneg_left hb' hNy
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg (‖euc (posPart p (∑ j, w j • X j))‖ -
      2 / 3 * ‖euc (negPart p y)‖), sq_nonneg ‖euc (posPart p y)‖,
      sq_nonneg ‖euc (negPart p (∑ j, w j • X j))‖, sq_nonneg ‖euc (negPart p y)‖]

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

-- bundled from ReciprocityTheory.SemistableReduction.DegAddHolds
section
namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

theorem degAdd_holds : DegAddStatement := by
  intro K _ _ r k m H L b c hH hL hb hc hlin hspan
  obtain ⟨hbi, -, hdis⟩ := DegAdd.indep_parts hlin
  have hidx := DegAdd.index_split L b c hb hc hdis
  have hne := DegAdd.relIndex_ne_zero_of_fg L hL (Fin.append b c) hspan
  rw [hidx] at hne
  have h1 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  have hs : ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ (Fin.append b c)).det.re =
      ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re +
        ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => DegAdd.log_det_gram_append (H σ) σ b c (hH σ) hbi hlin
  unfold latDeg quotDeg
  rw [hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr h1) (Nat.cast_ne_zero.mpr h2), hs]
  ring

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.IntCores
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial

def blockSlice {B n : ℕ} (b : Fin B) (p : Fin B → Fin n → ℂ) :
    Fin B × Fin n → MvPolynomial (Fin n) ℂ :=
  fun q => if q.1 = b then X q.2 else C (p q.1 q.2)

theorem blockSlice_isHomogeneous {B n : ℕ} {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) ℂ}
    (hf : IsMultiHomogeneous a f) (b : Fin B) (p : Fin B → Fin n → ℂ) :
    (bind₁ (blockSlice b p) f).IsHomogeneous (a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro s hs
  rw [bind₁_monomial]
  have hdeg : ∀ q, (blockSlice b p q).IsHomogeneous (if q.1 = b then 1 else 0) := by
    intro q; unfold blockSlice; split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_C _ _
  have hprod := IsHomogeneous.prod s.support (fun q => blockSlice b p q ^ s q)
    (fun q => (if q.1 = b then 1 else 0) * s q) (fun q _ => (hdeg q).pow (s q))
  have hsum : ∑ q ∈ s.support, (if q.1 = b then 1 else 0) * s q = a b := by
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun q _ hq => by simp [Finsupp.notMem_support_iff.1 hq])]
    rw [← hf s hs b, Fintype.sum_prod_type]
    simp [ite_mul]
  rw [← zero_add (a b), ← hsum]
  exact (isHomogeneous_C _ _).mul hprod

theorem eval_blockSlice {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) ℂ) (b : Fin B)
    (p : Fin B → Fin n → ℂ) (w : Fin n → ℂ) :
    eval w (bind₁ (blockSlice b p) f) = eval (fun q => Function.update p b w q.1 q.2) f := by
  have hφ : (fun q => eval₂Hom (RingHom.id ℂ) w (blockSlice b p q)) =
      fun q => Function.update p b w q.1 q.2 := by
    funext q
    by_cases hq : q.1 = b
    · simp [blockSlice, hq]
    · simp [blockSlice, hq]
  show eval₂Hom (RingHom.id ℂ) w (bind₁ _ f) = _
  rw [eval₂Hom_bind₁, hφ]
  rfl

theorem sphereLogIntegrable_holds (hSJ : SJStatement) : SphereLogIntegrableStatement := by
  intro B n a f _ hf
  set F : (Fin B → Fin n → ℂ) → ℂ := fun p => eval (fun q => p q.1 q.2) f with hFdef
  have hF : BlockPoly B n a F := by
    refine ⟨(continuous_eval f).comp (continuous_pi fun q =>
      (continuous_apply q.2).comp (continuous_apply q.1)), fun b p => ?_⟩
    exact ⟨_, blockSlice_isHomogeneous hf b p, fun w => (eval_blockSlice f b p w).symm⟩
  by_cases hz : ∃ z0, onSpheres F z0 ≠ 0
  · obtain ⟨z0, hz0⟩ := hz
    exact (blockPoly_claim hSJ n B a F hF z0 hz0).1
  · simp only [not_exists, not_not] at hz
    have : (fun z : BlockSphere B n => Real.log ‖eval (blockPoint z) f‖) = fun _ => 0 := by
      funext z
      have h0 : eval (blockPoint z) f = 0 := hz z
      rw [h0, norm_zero, Real.log_zero]
    rw [this]
    exact integrable_zero _ _ _

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.TorusLex
section
namespace ReciprocityTheory.MultiplicativeHeights

theorem torusLex_holds (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement ∧ TorusL2Cauchy :=
  ⟨TorusLexOrder.torusLex_of hBasic hCoeff, TorusLexOrder.torus_l2_cauchy_of_basic hBasic⟩

end ReciprocityTheory.MultiplicativeHeights
end

