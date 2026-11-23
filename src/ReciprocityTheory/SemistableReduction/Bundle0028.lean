module

public import ReciprocityTheory.SemistableReduction.Bundle0027

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegH
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem isIntegralElt_add {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isIntegralElt_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) {x : K}
    (hx : IsIntegralElt x) : IsIntegralElt (S.c x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨RingOfIntegers.mapRingHom S.c z, rfl⟩

theorem norm_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (z : K) :
    Algebra.norm ℚ (S.c z) = Algebra.norm ℚ z := by
  have hs : Function.Surjective S.c := fun x => ⟨S.c x, S.c_invol x⟩
  let e : K ≃+* K := RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩
  let e' : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])
  exact Algebra.norm_eq_of_algEquiv e' z

def projLt (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if (i : ℕ) < e then x i else 0
  map_add' x y := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]

theorem spanIdx_pair {K : Type} [Field K] [NumberField K] {r : ℕ} (j p : Fin r)
    (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K)) (hj : ∀ x ∈ Gj, IsAt j x)
    (hp : ∀ x ∈ Gp, IsAt p x) (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hy : y ∈ Gp) :
    spanIdx (Gj ⊔ Gp) ![x0, y] = spanIdx Gj ![x0] * spanIdx Gp ![y] := by
  unfold spanIdx
  have hspan : Submodule.span (𝓞 K) (Set.range ![x0, y]) =
      Submodule.span (𝓞 K) {x0} ⊔ Submodule.span (𝓞 K) {y} := by
    rw [Matrix.range_cons_cons_empty, Submodule.span_insert]
  have h1 : Set.range ![x0] = {x0} := Matrix.range_cons_empty _ _
  have h2 : Set.range ![y] = {y} := Matrix.range_cons_empty _ _
  rw [hspan, h1, h2, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  set X0 := (Submodule.span (𝓞 K) {x0}).toAddSubgroup
  set Y := (Submodule.span (𝓞 K) {y}).toAddSubgroup
  have hX0 : X0 ≤ Gj.toAddSubgroup := by
    show Submodule.span (𝓞 K) {x0} ≤ Gj
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx0
  have hY : Y ≤ Gp.toAddSubgroup := by
    show Submodule.span (𝓞 K) {y} ≤ Gp
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hy
  have key := AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_left hY X0)
    (sup_le_sup_right hX0 Gp.toAddSubgroup)
  rw [← key, mul_comm (X0.relIndex _)]
  congr 1
  · refine relIndex_sup_proj (projGe K r p).toAddMonoidHom X0 Y Gp.toAddSubgroup hY ?_ ?_
    · intro a ha
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 ha
      show projGe K r p (t • x0) = 0
      rw [map_smul]
      have : projGe K r p x0 = 0 := by
        funext i
        show (if (p : ℕ) ≤ i then x0 i else 0) = 0
        split_ifs with h
        · exact hj x0 hx0 i (fun hi => by rw [hi] at h; omega)
        · rfl
      rw [this, smul_zero]
    · intro x hx
      show projGe K r p x = x
      funext i
      show (if (p : ℕ) ≤ i then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hp x hx i (fun hi => by rw [hi] at h; omega)).symm
  · rw [sup_comm X0, sup_comm Gj.toAddSubgroup]
    refine relIndex_sup_proj (projLt K r p).toAddMonoidHom Gp.toAddSubgroup X0 Gj.toAddSubgroup
      hX0 ?_ ?_
    · intro x hx
      show projLt K r p x = 0
      funext i
      show (if (i : ℕ) < p then x i else 0) = 0
      split_ifs with h
      · exact hp x hx i (fun hi => by rw [hi] at h; omega)
      · rfl
    · intro x hx
      show projLt K r p x = x
      funext i
      show (if (i : ℕ) < p then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hj x hx i (fun hi => by rw [hi] at h; omega)).symm

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ShareBallC
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix Module
open scoped ComplexOrder

theorem sb_re_dot_comm {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re = (star w ⬝ᵥ v).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem sb_normSq_split (p : ℕ) {r : ℕ} (v : Fin r → ℂ) : normSq v = posSq p v + negSq p v := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_normSq_nonneg {r : ℕ} (v : Fin r → ℂ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem sb_setup {r p : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} {s : ℝ} (hH : H.PosDef)
    (hJ : H * signMat p r * H = signMat p r)
    (hP : ∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) :
    ∀ w : Fin r → ℂ, ∃ x, signMat p r *ᵥ (H *ᵥ x) = x ∧ sbDp p r *ᵥ x = sbDp p r *ᵥ w := by
  intro w
  have hJJ : signMat p r * signMat p r = 1 := sb_J_mul_J p r
  have hA2 : signMat p r * H * (signMat p r * H) = 1 := by
    calc signMat p r * H * (signMat p r * H) = signMat p r * (H * signMat p r * H) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have hHx : ∀ x : Fin r → ℂ, H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
    intro x; rw [mulVec_mulVec, hJJ, one_mulVec]
  have hre : ∀ x : Fin r → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
    intro x hx
    have := hH.re_dotProduct_pos hx
    simpa using this
  have hplus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = x → sbDp p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, sb_re_dot_J, sb_posSq_eq, hDx, sb_negSq_eq] at h1
    have h2 := sb_normSq_nonneg (sbDn p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  have hminus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = -x → sbDn p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, mulVec_neg, dotProduct_neg, Complex.neg_re, sb_re_dot_J, sb_posSq_eq,
      sb_negSq_eq, hDx] at h1
    have h2 := sb_normSq_nonneg (sbDp p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r) (Fin r) ℂ, P = (1 / 2 : ℂ) • (1 + signMat p r * H) :=
    ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin r) (Fin r) ℂ, N = (1 / 2 : ℂ) • (1 - signMat p r * H) :=
    ⟨_, rfl⟩
  have hAP : signMat p r * H * P = P := by
    rw [hP, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hA2, add_comm]
  have hAN : signMat p r * H * N = -N := by
    rw [hN, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hA2, ← smul_neg, neg_sub]
  have hPN : P + N = 1 := by
    rw [hP, hN]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hPv : ∀ x, signMat p r *ᵥ (H *ᵥ (P *ᵥ x)) = P *ᵥ x := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAP]
  have hNv : ∀ x, signMat p r *ᵥ (H *ᵥ (N *ᵥ x)) = -(N *ᵥ x) := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAN, neg_mulVec]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin r) (Fin r) ℂ, F = sbDp p r * P + sbDn p r * N := ⟨_, rfl⟩
  have hFp : ∀ x, sbDp p r *ᵥ (F *ᵥ x) = sbDp p r *ᵥ (P *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dp_mul_Dp,
      sb_Dp_mul_Dn, zero_mul, zero_mulVec, add_zero]
  have hFn : ∀ x, sbDn p r *ᵥ (F *ᵥ x) = sbDn p r *ᵥ (N *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dn_mul_Dn,
      sb_Dn_mul_Dp, zero_mul, zero_mulVec, zero_add]
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    have h0 : F *ᵥ (x - y) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hxy
    have hp : P *ᵥ (x - y) = 0 := hplus _ (hPv _) (by rw [← hFp, h0, mulVec_zero])
    have hn : N *ᵥ (x - y) = 0 := hminus _ (hNv _) (by rw [← hFn, h0, mulVec_zero])
    have : x - y = 0 := by
      rw [← one_mulVec (x - y), ← hPN, add_mulVec, hp, hn, add_zero]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective F.mulVec :=
    mulVec_surjective_iff_isUnit.mpr (mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨x, hx⟩ := hsurj (sbDp p r *ᵥ w)
  refine ⟨P *ᵥ x, hPv x, ?_⟩
  rw [← hFp, hx, mulVec_mulVec, sb_Dp_mul_Dp]

end ReciprocityTheory.MultiplicativeHeights
end
end

