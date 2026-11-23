module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0002
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolve

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFinAlt
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField

theorem resFin_holds : ResFin := by
  intro E _ _ V _ _ _ _ Λ hΛ c hc
  have hZ : (Λ.restrictScalars ℤ).FG := by
    first
      | exact Submodule.FG.restrictScalars hΛ
      | (obtain ⟨t, ht⟩ := hΛ
         obtain ⟨s0, hs0⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
         rw [← ht, ← Submodule.span_smul_of_span_eq_top hs0]
         exact Submodule.fg_def.2 ⟨_, s0.finite_toSet.smul t.finite_toSet, rfl⟩)
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hmem : ∀ x ∈ Λ, ∃ a : Fin n → ℤ, ∑ i, a i • g i = x := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx'
    exact hx'
  haveI : NeZero c := ⟨by omega⟩
  refine ⟨Fin n → ZMod c, inferInstance,
    fun x => if hx : x ∈ Λ then fun i => (((hmem x hx).choose i : ℤ) : ZMod c) else 0, ?_⟩
  intro x hx y hy hxy
  beta_reduce at hxy
  rw [dite_eq_left hx, dite_eq_left hy] at hxy
  have hax := (hmem x hx).choose_spec
  have hby := (hmem y hy).choose_spec
  have hdiv : ∀ i, (c : ℤ) ∣ (hmem y hy).choose i - (hmem x hx).choose i := fun i => by
    have hi := congrFun hxy i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    exact hi
  choose k hk using hdiv
  refine ⟨∑ i, k i • g i, ?_, ?_⟩
  · have hs : ∑ i, k i • g i ∈ Submodule.span ℤ (Set.range g) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [hg] at hs
    exact hs
  · rw [← hax, ← hby, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, hk i, mul_smul, Nat.cast_smul_eq_nsmul E, natCast_zsmul]

end PI.TermsAtPtFiniteW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.RightInvHolds
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S Matrix

theorem rowsDep_holds : RowsDep := by
  intro E _ r Z u hu hdep
  have hcast : ∀ (h : r ≤ r + 1) (c : Fin r), Fin.castLE h c = Fin.castSucc c := fun h c => Fin.ext rfl
  have hcast1 : ∀ (h : r + 1 ≤ r + 1) (c : Fin (r + 1)), Fin.castLE h c = c := fun h c => Fin.ext rfl
  constructor
  · unfold leadMinorE
    rw [dite_eq_left le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Fin.snoc (α := fun _ => E) u 0, ?_, ?_⟩
    · intro h0
      apply hu
      funext c
      have h1 := congrFun h0 (Fin.castSucc c)
      simpa using h1
    · funext b
      simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast1, Pi.zero_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
      exact hdep b
  · unfold leadMinorE
    rw [dite_eq_left (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨u, hu, ?_⟩
    funext b
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast, Pi.zero_apply]
    exact hdep (Fin.castSucc b)

theorem rightInv_holds : RightInv := by
  intro E _ r β hind
  have hinjT : Function.Injective (Matrix.mulVecLin βᵀ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hind u
    intro b
    have h1 := congrFun hu b
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h1
    exact h1
  have hrank : β.rank = r := by
    rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj hinjT]
    simp
  have hsurj : Function.Surjective (Matrix.mulVecLin β) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    show β.rank = _
    rw [hrank]
    simp
  have hker : Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin β)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
    simp at h1
    omega
  obtain ⟨v0, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)))
  have hspan := (finrank_eq_one_iff_of_nonzero' v0 hv0).1 hker
  set vv : Fin (r + 1) → E := (v0 : Fin (r + 1) → E) with hvv
  have hvv0 : vv ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hfv : β *ᵥ vv = 0 := v0.2
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hvv0
  have hj' : vv j ≠ 0 := hj
  choose x hx using fun c : Fin r => hsurj (Pi.single c 1)
  set x' : Fin r → Fin (r + 1) → E := fun c => x c - ((vv j)⁻¹ * x c j) • vv with hx'
  have hx'f : ∀ c, β *ᵥ x' c = Pi.single c 1 := by
    intro c
    have h1 : β *ᵥ x c = Pi.single c 1 := hx c
    simp only [hx', Matrix.mulVec_sub, Matrix.mulVec_smul, hfv, smul_zero, sub_zero, h1]
  have hx'j : ∀ c, x' c j = 0 := by
    intro c
    simp only [hx', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : (vv j)⁻¹ * x c j * vv j = x c j := by
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hj', one_mul]
    rw [h2, sub_self]
  refine ⟨Matrix.of (fun b c => x' c b), vv, fun k => if k = j then (vv j)⁻¹ else 0, ?_, ?_, ?_⟩
  · ext a c
    have h1 := congrFun (hx'f c) a
    have h2 : ∑ b, β a b * x' c b = (Pi.single c (1 : E) : Fin r → E) a := by
      rw [← h1]
      rfl
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [h2, Pi.single_apply]
  · intro c
    have h1 := congrFun hfv c
    simpa [Matrix.mulVec, dotProduct] using h1
  · intro i k
    set y : Fin (r + 1) → E := ∑ c, β c k • x' c with hy
    have hQ : (Matrix.of (fun b c => x' c b) * β) i k = y i := by
      simp [Matrix.mul_apply, hy, Finset.sum_apply, mul_comm]
    have hyf : β *ᵥ y = β *ᵥ Pi.single k 1 := by
      funext a
      simp only [hy, Matrix.mulVec_sum, Matrix.mulVec_smul, hx'f]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have hyj : y j = 0 := by
      simp [hy, Finset.sum_apply, hx'j]
    have hmem : Pi.single k 1 - y ∈ LinearMap.ker (Matrix.mulVecLin β) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hyf, sub_self]
    obtain ⟨t, ht⟩ := hspan ⟨_, hmem⟩
    have ht' : t • vv = Pi.single k 1 - y := congrArg Subtype.val ht
    have htj := congrFun ht' j
    have hti := congrFun ht' i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hyj, sub_zero, Pi.single_apply] at htj hti
    show (Matrix.of (fun b c => x' c b) * β) i k = _
    rw [hQ]
    by_cases hkj : k = j
    · subst hkj
      simp only [if_true] at htj
      have htv : t = (vv k)⁻¹ := by
        field_simp
        linear_combination htj
      simp only [if_true]
      rw [htv] at hti
      linear_combination hti
    · have hjk : j ≠ k := fun h => hkj h.symm
      simp only [if_neg hjk] at htj
      have ht0 : t = 0 := by
        rcases mul_eq_zero.1 htj with h | h
        · exact h
        · exact absurd h hj
      simp only [if_neg hkj, mul_zero, sub_zero]
      rw [ht0, zero_mul] at hti
      linear_combination hti

end PI.TermsAtPtFiniteW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolveAlt
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S Matrix

theorem skewSolve_holds : SkewSolve := by
  intro E _ _ r β x Q v l hind hβQ hβv hQβ hskew
  have hS : βᴴ * x + xᴴ * β = 0 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib]
    exact hskew a b
  have h1 : x * Q + (x * Q)ᴴ = 0 := by
    have h0 := congrArg (fun M => Qᴴ * M * Q) hS
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at h0
    have e1 : Qᴴ * (βᴴ * x) * Q = x * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hβQ, Matrix.conjTranspose_one, Matrix.one_mul]
    have e2 : Qᴴ * (xᴴ * β) * Q = (x * Q)ᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, hβQ, Matrix.mul_one]
    rw [e1, e2] at h0
    exact h0
  have hβv' : β *ᵥ v = 0 := by
    funext c
    exact hβv c
  have hw : βᴴ *ᵥ (x *ᵥ v) = 0 := by
    have h0 := congrArg (fun M => M *ᵥ v) hS
    simp only [Matrix.add_mulVec, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hβv', Matrix.mulVec_zero,
      add_zero] at h0
    exact h0
  have hxv : x *ᵥ v = 0 := by
    have hu := hind (fun c => star ((x *ᵥ v) c)) (fun b => by
      have hb := congrFun hw b
      have h2 : ∑ c, star ((x *ᵥ v) c) * β c b = star ((βᴴ *ᵥ (x *ᵥ v)) b) := by
        show _ = star (∑ c, βᴴ b c * (x *ᵥ v) c)
        simp only [Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [h2, hb]
      simp)
    funext c
    have hc := congrFun hu c
    simpa using hc
  refine ⟨fun c d => ?_, ?_⟩
  · have hcd := congrFun (congrFun h1 c) d
    simpa only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] using hcd
  · rw [Matrix.mul_assoc]
    ext i j
    rw [Matrix.mul_apply]
    simp only [hQβ, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hi := congrFun hxv i
    have h' : ∑ k, x i k * (v k * l j) = (x *ᵥ v) i * l j := by
      show _ = (∑ k, x i k * v k) * l j
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h', hi]
    simp

end PI.TermsAtPtFiniteW
end
end

