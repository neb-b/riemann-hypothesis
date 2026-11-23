module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0003
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.AbsDAtTop
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private lemma abs_d_atTop (d : ℕ → ℕ)
    (hfac : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [hfac 1, eventually_ge_atTop M.factorial] with j hj hM
  by_contra hlt
  have h1 : (d j).factorial ≤ M.factorial := Nat.factorial_le (not_le.1 hlt).le
  have h2 : ((d j).factorial : ℝ) ≤ j := by exact_mod_cast h1.trans hM
  have h3 := Real.add_one_le_exp (j : ℝ)
  rw [one_mul] at hj
  linarith

private lemma abs_sum_eq {T : Type} [DecidableEq ℝ] (s : Finset T) (a : T → ℝ) (A : Finset ℝ)
    (Z : Finset ℂ) (hA : ∀ i ∈ s, a i ∈ A) (v : T → ℂ) (C : T → ℂ → ℂ) (t : T → ℂ)
    (f g : ℝ → ℂ) (n : ℕ) (ht : ∀ i ∈ s, t i = ∑ ζ ∈ Z, C i ζ * ζ ^ n) :
    ∑ q ∈ A ×ˢ Z, (∑ i ∈ s with a i = q.1, v i * C i q.2) * f q.1 * g q.1 * q.2 ^ n =
      ∑ i ∈ s, v i * f (a i) * g (a i) * t i := by
  rw [Finset.sum_product, ← Finset.sum_fiberwise_of_maps_to hA]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  rw [ht i hi1, hi2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  ring

theorem UpperTheory.ConvolutionTheory.Ci.abs :
    ∀ (T : Type) (a : T → ℝ) (τ : T → ℕ → ℂ) (act good : T → Prop) (x : ℝ), 0 < x → x ≤ 1 → ∀ (p : ℕ), 0 < p → ∀ (c₁ : ℝ) (d : ℕ → ℕ),
      Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      (∀ i, act i → 0 < a i → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ i j = ∑ ζ ∈ s, c ζ * ζ ^ j) →
      (∀ η : ℝ, 0 < η → η < x → ∃ (s : Finset T) (u : T → ℕ → ℂ) (u' : T → ℂ) (k : ℂ), k ≠ 0 ∧ (∀ i, i ∈ s ↔ η < a i ∧ act i) ∧
        (∀ i ∈ s, Tendsto (u i) atTop (𝓝 (u' i))) ∧ (∀ i ∈ s, good i → a i = x → u' i = k) ∧ (∀ i ∈ s, ¬ good i → u' i = 0) ∧
        ∀ (N : ℝ) (s₀ : ℕ), ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
          ‖∑ i ∈ s, u i (d j) * (a i : ℂ) ^ d j * (cheb η (j / p + m) (a i) : ℂ) * τ i (j + m')‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      {i | act i ∧ good i ∧ a i = x}.Finite ∧ ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0 := by
  intro T a τ act good x hx hx1 p hp c₁ d hd hfac hτ H
  classical
  have hdt := abs_d_atTop d hfac
  have hτ' : ∀ i, ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ (act i → 0 < a i →
      ∀ᶠ j : ℕ in atTop, ∀ Z : Finset ℂ, s ⊆ Z → τ i j = ∑ ζ ∈ Z, c ζ * ζ ^ j) := by
    intro i
    by_cases h : act i ∧ 0 < a i
    · obtain ⟨s, c, h0, hc⟩ := hτ i h.1 h.2
      refine ⟨s, fun ζ => if ζ ∈ s then c ζ else 0, h0, fun _ _ => ?_⟩
      filter_upwards [hc] with j hj Z hZ
      rw [hj, ← Finset.sum_subset hZ]
      · exact Finset.sum_congr rfl fun ζ hζ => by simp [hζ]
      · intro ζ _ hζ; simp [hζ]
    · exact ⟨∅, 0, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose S C hS0 hSC using hτ'
  have hF : {i | act i ∧ good i ∧ a i = x}.Finite := by
    obtain ⟨s, -, -, -, -, hs, -⟩ := H (x / 2) (by linarith) (by linarith)
    refine s.finite_toSet.subset fun i hi => ?_
    exact (hs i).2 ⟨by rw [hi.2.2]; linarith, hi.1⟩
  refine ⟨hF, ?_⟩
  have key : ∀ ζ₀ : ℂ, ζ₀ ≠ 0 → ∑ i ∈ hF.toFinset, C i ζ₀ = 0 := by
    intro ζ₀ hζ₀
    obtain ⟨η, hη, hηx, hE⟩ :=
      UpperTheory.ConvolutionTheory.FX.exponents2 d hd hfac p hp c₁ (-Real.log ‖ζ₀‖) x hx hx1
    obtain ⟨N, hE⟩ := hE η hη le_rfl
    obtain ⟨s, u, u', k, hk, hs, hu, hg, hng, hb⟩ := H η hη hηx
    set A : Finset ℝ := insert x (s.image a) with hA
    set Z : Finset ℂ := insert ζ₀ (s.biUnion S) with hZ
    have hAη : ∀ α ∈ A, η < α := by
      intro α hα
      rcases Finset.mem_insert.1 hα with rfl | hα
      · exact hηx
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hα
        exact ((hs i).1 hi).1
    have hZ0 : ∀ ζ ∈ Z, ζ ≠ 0 := by
      intro ζ hζ
      rcases Finset.mem_insert.1 hζ with rfl | hζ
      · exact hζ₀
      · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hζ
        rintro rfl
        exact hS0 i hi
    have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ Z, C i ζ * ζ ^ j := by
      refine (Filter.eventually_all_finset s).2 fun i hi => ?_
      filter_upwards [hSC i ((hs i).1 hi).2 (hη.trans ((hs i).1 hi).1)] with j hj
      exact hj Z ((Finset.subset_biUnion_of_mem S hi).trans (Finset.subset_insert _ _))
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    have hmem : (x, ζ₀) ∈ A ×ˢ Z :=
      Finset.mem_product.2 ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    have main := hE (A ×ˢ Z : Finset (ℝ × ℂ)) (fun q => q.1.1) (fun q => q.1.2)
      (fun q => hAη _ (Finset.mem_product.1 q.2).1) (fun q => hZ0 _ (Finset.mem_product.1 q.2).2)
      (fun q q' h => Subtype.ext h)
      (fun j q => ∑ i ∈ s with a i = q.1.1, u i (d j) * C i q.1.2)
      (fun q => ∑ i ∈ s with a i = q.1.1, u' i * C i q.1.2)
      (fun q => tendsto_finsetSum _ fun i hi =>
        ((hu i (Finset.mem_filter.1 hi).1).comp hdt).mul_const _)
      (fun s₀ => by
        obtain ⟨K, hK⟩ := hb N s₀
        refine ⟨K, ?_⟩
        filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'
        have e := abs_sum_eq s a A Z
          (fun i hi => Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hi))
          (fun i => u i (d j)) C (fun i => τ i (j + m')) (fun α => (α : ℂ) ^ d j)
          (fun α => (cheb η (j / p + m) α : ℂ)) (j + m') (hJ (j + m') (by omega))
        rw [← Finset.sum_coe_sort] at e
        exact (congrArg norm e).trans_le (hj m hm m' hm'))
      ⟨(x, ζ₀), hmem⟩ le_rfl
      (by simp only [neg_neg]; rw [Real.exp_log (norm_pos_iff.2 hζ₀)])
    have e : ∑ i ∈ s with a i = x, u' i * C i ζ₀ = k * ∑ i ∈ hF.toFinset, C i ζ₀ := by
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
      · intro i hi
        have hi := hF.mem_toFinset.1 hi
        exact Finset.mem_filter.2 ⟨(hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩, hi.2.2⟩
      · intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.1 hi
        obtain ⟨hi3, hi4⟩ := Finset.mem_filter.1 hi1
        rw [hng i hi3 fun h => hi2 (hF.mem_toFinset.2 ⟨((hs i).1 hi3).2, h, hi4⟩), zero_mul]
      · intro i hi
        have hi := hF.mem_toFinset.1 hi
        rw [hg i ((hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩) hi.2.1 hi.2.2]
    exact (mul_eq_zero.1 (e.symm.trans main)).resolve_left hk
  have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ hF.toFinset,
      τ i j = ∑ ζ ∈ hF.toFinset.biUnion S, C i ζ * ζ ^ j := by
    refine (Filter.eventually_all_finset _).2 fun i hi => ?_
    have hi' := hF.mem_toFinset.1 hi
    filter_upwards [hSC i hi'.1 (by rw [hi'.2.2]; exact hx)] with j hj
    exact hj _ (Finset.subset_biUnion_of_mem S hi)
  filter_upwards [hev] with j hj
  refine (finsum_mem_eq_finite_toFinset_sum (fun i => τ i j) hF).trans ?_
  rw [Finset.sum_congr rfl hj, Finset.sum_comm]
  refine Finset.sum_eq_zero fun ζ hζ => ?_
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hζ
  rw [← Finset.sum_mul, key ζ (by rintro rfl; exact hS0 i hi), zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.CprsMulRight
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold prj
  congr 1

private theorem prj_mem_iff {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v = v ↔ v ∈ V := by
  unfold prj
  rw [Submodule.starProjection_eq_self_iff, hV.submodule_topologicalClosure_eq]

private noncomputable def cprs (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) : Module.End ℂ E :=
  (E.orthogonalProjectionOnto : H →ₗ[ℂ] E) ∘ₗ (T : H →ₗ[ℂ] H) ∘ₗ E.subtype

private theorem cprs_coe (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) (v : E) :
    (cprs E T v : H) = E.starProjection (T v) := rfl

private theorem trOn_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    trOn E T = LinearMap.trace ℂ E (cprs E T) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b, trOn, prj_eq, GroundTheory.Automorphic.trace]
  set S : H →L[ℂ] H := T ∘L E.starProjection with hS
  refine HasSum.tsum_eq ?_
  have h := hasSum_sum (s := Finset.univ) fun k _ =>
    (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)
  convert (preTransparency := .reducible) h using 1
  · rfl
  · funext i
    rw [ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]
    simp only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (b k).2]

private theorem comm_proj (E : Submodule ℂ H) [FiniteDimensional ℂ E] (U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E)
    (h' : ∀ v ∈ E, ContinuousLinearMap.adjoint U v ∈ E) (v : H) :
    E.starProjection (U v) = U (E.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (E.starProjection_apply_mem v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact E.starProjection_inner_eq_zero v _ (h' w hw)

private theorem cprs_mul_right (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E) :
    cprs E T * cprs E U = cprs E (T * U) := by
  ext v
  rw [mul_apply_eq_comp, cprs_coe, cprs_coe, cprs_coe, Submodule.starProjection_eq_self_iff.2 (h _ v.2)]
  rfl

private theorem cprs_mul_left (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H)
    (h : ∀ v, E.starProjection (U v) = U (E.starProjection v)) :
    cprs E U * cprs E T = cprs E (U * T) := by
  ext v
  rw [mul_apply_eq_comp, cprs_coe, cprs_coe, cprs_coe, mul_apply_eq_comp, h, h,
    Submodule.starProjection_eq_self_iff.2 (E.starProjection_apply_mem _)]

private theorem mem_eig {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (A U : H →L[ℂ] H) (x : ℝ)
    (h1 : Commute U (prj V)) (h2 : Commute U A) : ∀ v ∈ eigIn V A x, U v ∈ eigIn V A x := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [← prj_mem_iff hV] at hv1 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h1.eq
    simp only [mul_apply_eq_comp, hv1] at this
    exact this.symm
  · rw [Module.End.mem_eigenspace_iff] at hv2 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h2.eq
    simp only [mul_apply_eq_comp] at this
    simp only [ContinuousLinearMap.coe_coe] at hv2 ⊢
    rw [← this, hv2, map_smul]

private theorem abs_form (hE : ExpForm) (l : ℕ) (hl : 0 < l) (V : Submodule ℂ H) (hV : IsClosed (V : Set H))
    (A T : H →L[ℂ] H) (hA : 0 ≤ A) (x : ℝ) [FiniteDimensional ℂ (eigIn V A x)] (U : ZMod l → H →L[ℂ] H)
    (h1 : ∀ i, Commute (U i) (prj V)) (h2 : ∀ i, Commute (U i) A) (h3 : ∀ i k, Commute (U i) (U k))
    (h4 : ∀ i, T * U i = U (i + 1) * T) :
    ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop,
      trOn (eigIn V A x) ((U 0 ^ j) ∘L T) = ∑ ζ ∈ s, c ζ * ζ ^ j := by
  have hAs : IsSelfAdjoint A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA
  have hPs : IsSelfAdjoint (prj V) := isSelfAdjoint_starProjection _
  have hm : ∀ i, ∀ v ∈ eigIn V A x, U i v ∈ eigIn V A x := fun i => mem_eig hV A _ x (h1 i) (h2 i)
  have hm' : ∀ i, ∀ v ∈ eigIn V A x, ContinuousLinearMap.adjoint (U i) v ∈ eigIn V A x := fun i => by
    refine mem_eig hV A _ x ?_ ?_
    · have := (h1 i).star_star
      rwa [hPs.star_eq] at this
    · have := (h2 i).star_star
      rwa [hAs.star_eq] at this
  have hc := fun i => comm_proj _ (U i) (hm i) (hm' i)
  obtain ⟨s, c, hs, h⟩ := hE (eigIn V A x) l hl (fun i => cprs _ (U i)) (cprs _ T)
    (fun i k => by
      show _ * _ = _ * _
      rw [cprs_mul_right _ _ _ (hm k), cprs_mul_right _ _ _ (hm i), (h3 i k).eq])
    (fun i => by rw [cprs_mul_right _ _ _ (hm i), cprs_mul_left _ _ _ (hc (i + 1)), h4])
  refine ⟨s, c, hs, (eventually_ge_atTop (Module.finrank ℂ (eigIn V A x))).mono fun j hj => ?_⟩
  rw [← h j hj, trOn_eq]
  congr 1
  clear hj
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ j ih => rw [pow_succ', pow_succ', mul_assoc, ← ih, cprs_mul_left _ _ _ (hc 0)]; rfl

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Ci.trExp :
    ExpForm → TrExp := by
  intro hE K _ _ n l hl μ _ θ 𝔰 V x hA hV hfin
  exact abs_form hE l hl V hV.closed _ _ hA x 𝔰.Uq (fun i => 𝔰.Uq_inner i V hV.closed hV.inv) 𝔰.Uq_amp 𝔰.Uq_comm
    𝔰.Uq_perm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.EvalPowE
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

theorem UpperTheory.ConvolutionTheory.Ci.valBc :
    ValBc := by
  classical
  intro F E _ _ _ _ _ n x Λ t P hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := P) (p₂ := P) ?_ ?_ rfl
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [val, bcPR]
      · rintro (_ | y)
        · simp [val, bcPR]
        · simp [val, bcPR, bcInf]
    · intro y hy _
      have h := eval_powE (resDeg F y.1) y.2 _ (hP y hy)
      simp only [val, bcPR, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h]
      have hc : ((eval fun o : Option (Ix F n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1)).comp C)
          = RingHom.id ℂ := by
        ext c
        simp
      rw [hc]
      rfl
  · intro y hy
    have h : bcPR F P = bind₁ (fun x : Pl E × Fin n =>
        (map C (rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)) : PR F n))
        (map (rename (Option.map fun x : Ix E n => (x.1.comp (algebraMap F E), x.2))).toRingHom P) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [h] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    refine ⟨y', vars_map _ _ hy', ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    rfl
  · intro η m
    simp only [chebP, bcPR, eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Polynomial.aeval_algHom_apply]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.ExpForm
section
open UpperTheory.ConvolutionTheory.Ci

namespace UpperTheory.ConvolutionTheory.Ci.ExponentialForm

open Polynomial

private theorem semiconj_aeval {A : Type} [Ring A] [Algebra ℂ A] {a x y : A} (h : SemiconjBy a x y) (p : ℂ[X]) :
    SemiconjBy a (aeval x p) (aeval y p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add (f := _)] using hp.add_right hq
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def]
    have := (h.pow_right n).eq
    unfold SemiconjBy
    rw [mul_smul_comm, smul_mul_assoc, this]

private theorem nil_mul {A : Type} [Ring A] (l : ℕ) (hl : 0 < l) (M : ZMod l → A) (B : A)
    (hc : ∀ i k, Commute (M i) (M k)) (hB : ∀ i, B * M i = M (i + 1) * B) (h0 : IsNilpotent (M 0)) :
    IsNilpotent (M 0 * B) := by
  have h1 : ∀ (m : ℕ) (i : ZMod l), B ^ m * M i = M (i + m) * B ^ m := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hB, mul_assoc, Nat.cast_succ, add_assoc]
  have h2 : ∀ m : ℕ, ∃ P : A, Commute (M 0) P ∧ (M 0 * B) ^ (m + 1) = M 0 * (P * B ^ (m + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨1, Commute.one_right _, by simp⟩
    | succ m ih =>
      obtain ⟨P, hP, h⟩ := ih
      refine ⟨P * M (0 + ((m + 1 : ℕ) : ZMod l)), hP.mul_right (hc _ _), ?_⟩
      rw [pow_succ, h, pow_succ B (m + 1)]
      simp only [mul_assoc]
      rw [← mul_assoc (B ^ (m + 1)) (M 0), h1, mul_assoc]
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  obtain ⟨P, hP, h⟩ := h2 m
  have h3 : Commute (M 0) (B ^ (m + 1)) := by
    have := h1 (m + 1) 0
    rw [ZMod.natCast_self, add_zero] at this
    exact this.symm
  have h4 : IsNilpotent ((M 0 * B) ^ (m + 1)) := by
    rw [h]
    exact (hP.mul_right h3).isNilpotent_mul_right h0
  exact h4.of_pow

private theorem nil_nodal {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (U : Module.End ℂ W) :
    IsNilpotent (aeval U (Lagrange.nodal U.charpoly.roots.toFinset id)) := by
  classical
  set r := Lagrange.nodal U.charpoly.roots.toFinset id with hr
  have h1 : U.charpoly = (U.charpoly.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits U.charpoly).eq_prod_roots_of_monic U.charpoly_monic
  have h2 : (U.charpoly.roots.map fun a => X - C a).prod ∣ (U.charpoly.roots.map fun _ => r).prod :=
    Multiset.prod_dvd_prod_of_dvd _ _ fun a ha =>
      Lagrange.X_sub_C_dvd_nodal id (Multiset.mem_toFinset.2 ha)
  rw [← h1, Multiset.map_const', Multiset.prod_replicate] at h2
  obtain ⟨q, hq⟩ := h2
  refine ⟨U.charpoly.roots.card, ?_⟩
  rw [← map_pow, hq, map_mul, LinearMap.aeval_self_charpoly, zero_mul]

private theorem pow_eq (s : Finset ℂ) (j : ℕ) :
    ∃ q : ℂ[X], X ^ j = Lagrange.nodal s id * q + ∑ z ∈ s, C (z ^ j) * Lagrange.basis s id z := by
  classical
  have h : Lagrange.nodal s id ∣ X ^ j - ∑ z ∈ s, C (z ^ j) * Lagrange.basis s id z := by
    unfold Lagrange.nodal
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
    · intro a ha
      rw [dvd_iff_isRoot, IsRoot.def, eval_sub]
      have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (fun z : ℂ => z ^ j) (Set.injOn_id _) ha
      rw [Lagrange.interpolate_apply] at this
      rw [this]
      simp
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [← hq]; ring⟩

private theorem trace_eq {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (l : ℕ) (hl : 0 < l)
    (U : ZMod l → Module.End ℂ W) (B : Module.End ℂ W) (hc : ∀ i k, Commute (U i) (U k))
    (hB : ∀ i, B * U i = U (i + 1) * B) :
    ∃ (s : Finset ℂ) (p : ℂ → ℂ[X]), ∀ j : ℕ, LinearMap.trace ℂ W (U 0 ^ j * B) =
      ∑ z ∈ s, LinearMap.trace ℂ W (aeval (U 0) (p z) * B) * z ^ j := by
  classical
  refine ⟨(U 0).charpoly.roots.toFinset, Lagrange.basis (U 0).charpoly.roots.toFinset id, fun j => ?_⟩
  obtain ⟨q, hq⟩ := pow_eq (U 0).charpoly.roots.toFinset j
  have hn := nil_nodal (U 0)
  set r := Lagrange.nodal (U 0).charpoly.roots.toFinset id with hr
  have h1 : IsNilpotent (aeval (U 0) (r * q) * B) := by
    refine nil_mul l hl (fun i => aeval (U i) (r * q)) B (fun i k => ?_) (fun i => semiconj_aeval (hB i) _) ?_
    · exact Commute.symm (semiconj_aeval (Commute.symm (semiconj_aeval (hc i k) _)) _)
    · have : Commute (aeval (U 0) r) (aeval (U 0) q) := (Commute.all r q).map _
      simp only [map_mul]
      exact this.isNilpotent_mul_right hn
  have h2 : LinearMap.trace ℂ W (aeval (U 0) (r * q) * B) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero
  have h3 : U 0 ^ j = aeval (U 0) (X ^ j : ℂ[X]) := by simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h3, hq, map_add (f := _), add_mul, map_add (f := _), h2, zero_add, map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul (aeval (U 0)), aeval_C, ← Algebra.smul_def, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]

end UpperTheory.ConvolutionTheory.Ci.ExponentialForm

theorem UpperTheory.ConvolutionTheory.Ci.expForm :
    ExpForm := by
  classical
  intro W _ _ _ l hl U B hc hB
  obtain ⟨s, p, h⟩ := ExponentialForm.trace_eq l hl U B hc hB
  refine ⟨s.erase 0, fun z => LinearMap.trace ℂ W (Polynomial.aeval (U 0) (p z) * B), Finset.notMem_erase _ _,
    fun j hj => ?_⟩
  rw [h j]
  refine (Finset.sum_erase _ ?_).symm
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (Nat.le_zero.1 hj)
    rw [Subsingleton.elim (Polynomial.aeval (U 0) (p 0) * B) 0, map_zero, zero_mul]
  · rw [zero_pow hj0.ne', mul_zero]
end

