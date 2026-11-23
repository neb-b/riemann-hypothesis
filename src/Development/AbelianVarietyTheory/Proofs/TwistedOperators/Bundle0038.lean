module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HilbertTensorTraceClassHasTraceProd
section
open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory

open GlobalTheory.OpTrace

theorem tensorTrace_summable_sq {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
    [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ)
    (hΨ : ∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) (A : ∀ i, Hs i →L[ℂ] Hs i)
    (hA : ∀ i, IsHilbertSchmidt (A i)) :
    Summable fun j : ∀ i, stdIndex (Hs i) => ‖Ψ (fun i => A i (stdBasis (H := Hs i) (j i)))‖ ^ 2 := by
  have hs := (splitHeight_summable_pi_prod (α := fun i => stdIndex (Hs i))
    (f := fun i k => ‖A i (stdBasis (H := Hs i) k)‖ ^ 2) (fun _ _ => sq_nonneg _) hA).mul_left c.re
  refine hs.congr fun j => ?_
  have h1 := hΨ (fun i => A i (stdBasis (H := Hs i) (j i))) (fun i => A i (stdBasis (H := Hs i) (j i)))
  simp only [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((‖Ψ (fun i => A i (stdBasis (H := Hs i) (j i)))‖ ^ 2 : ℝ) : ℂ)
      = c * ((∏ i, ‖A i (stdBasis (H := Hs i) (j i))‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h1
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at h3
  exact h3.symm

theorem tensorTrace_hasTrace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ Φ' : ContinuousMultilinearMap ℂ Hs H) (κ κ' : ℂ), (∀ y y', inner ℂ (Φ y') (Φ y) = ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ y') (Φ' y) = κ * ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ' y') (Φ' y) = κ' * ∏ i, inner ℂ (y' i) (y i)) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ y, X (Φ y) = Φ' fun i => B i (y i)) → (∀ v, (∀ y, inner ℂ (Φ y) v = 0) → X v = 0) → HasTrace X (κ * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ Φ Φ' κ κ' hΦ hΦΦ' hΦ' B b hB X hX hX0
  classical
  let J : ι → Type := fun i => stdIndex (Hs i)
  let e : ∀ i, HilbertBasis (J i) ℂ (Hs i) := fun i => stdBasis (H := Hs i)
  let u : (∀ i, J i) → H := fun j => Φ (fun i => e i (j i))

  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro j' j
    change ⟪Φ _, Φ _⟫_ℂ = _
    rw [hΦ]
    have : ∀ i, ⟪e i (j' i), e i (j i)⟫_ℂ = if j' i = j i then 1 else 0 := fun i =>
      (orthonormal_iff_ite.1 (e i).orthonormal) _ _
    simp only [this]
    by_cases h : ∀ x, j' x = j x
    · rw [if_pos (funext h)]
      exact Finset.prod_eq_one fun i _ => if_pos (h i)
    · rw [if_neg fun h' => h (congrFun h')]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

  have hperp : ∀ x : H, (∀ j, ⟪u j, x⟫_ℂ = 0) → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hx y
    have hL := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e ℂ
      ((innerSL ℂ x).compContinuousMultilinearMap Φ) 0 fun j => by
        simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
          ContinuousMultilinearMap.zero_apply]
        rw [← inner_conj_symm]; simp [u] at hx; simp [hx]
    have := congrArg (fun L : ContinuousMultilinearMap ℂ Hs ℂ => L y) hL
    simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
      ContinuousMultilinearMap.zero_apply] at this
    rw [← inner_conj_symm, this, map_zero]

  have hinj : Function.Injective u := hu.linearIndependent.injective
  obtain ⟨w, bH, hsw, hb⟩ :=
    Orthonormal.exists_hilbertBasis_extension ((orthonormal_subtype_range hinj).2 hu)
  have hoff : ∀ x ∈ w, x ∉ Set.range u → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hxw hxu
    refine hperp x fun j => ?_
    have hne : (⟨u j, hsw ⟨j, rfl⟩⟩ : w) ≠ ⟨x, hxw⟩ := fun h => hxu ⟨j, congrArg Subtype.val h⟩
    have := bH.orthonormal.2 hne
    simpa [hb] using this

  choose n C D hC hD hBeq using fun i => (hB i).1

  have hG : ∀ (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ),
      (∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) → ∀ A : ∀ i, Hs i →L[ℂ] Hs i,
      (∀ i, IsHilbertSchmidt (A i)) → ∃ G : H →L[ℂ] H, (∀ y, G (Φ y) = Ψ (fun i => A i (y i))) ∧
        (∀ v, (∀ y, ⟪Φ y, v⟫_ℂ = 0) → G v = 0) ∧ IsHilbertSchmidt G := by
    intro Ψ c hΨ A hA
    obtain ⟨G, hG1, hG2, hG3⟩ := _root_.GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply H H (∀ i, J i) u
      (fun j => Ψ (fun i => A i (e i (j i)))) hu (tensorTrace_summable_sq Ψ c hΨ A hA)
    refine ⟨G, fun y => ?_, fun v hv => hG2 v fun j => hv _, hG3⟩
    have := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e H (G.compContinuousMultilinearMap Φ)
      (Ψ.compContinuousLinearMap A) fun j => by simpa using hG1 j
    simpa using congrArg (fun L : ContinuousMultilinearMap ℂ Hs H => L y) this
  have hΦ1 : ∀ y y', ⟪Φ y', Φ y⟫_ℂ = 1 * ∏ i, ⟪y' i, y i⟫_ℂ := fun y y' => by rw [one_mul, hΦ]
  choose GD hGD1 hGD2 hGD3 using fun k : ∀ i, Fin (n i) => hG Φ 1 hΦ1 (fun i => D i (k i)) fun i => hD i _
  choose GC hGC1 hGC2 hGC3 using fun k : ∀ i, Fin (n i) => hG Φ' κ' hΦ' (fun i => C i (k i)) fun i => hC i _

  have hXeq : X = ∑ k, GC k ∘L GD k := by
    have hd : Dense (Submodule.span ℂ w : Set H) := by
      have := bH.dense_span
      rw [hb, Subtype.range_coe] at this
      exact Submodule.dense_iff_topologicalClosure_eq_top.2 this
    refine ContinuousLinearMap.ext_on hd fun x hx => ?_
    by_cases hxu : x ∈ Set.range u
    · obtain ⟨j, rfl⟩ := hxu
      change X (Φ _) = _
      rw [hX, ContinuousLinearMap.sum_apply]
      simp only [comp_apply]
      rw [show (fun i => B i (e i (j i))) = fun i => ∑ m, C i m (D i m (e i (j i))) from
        funext fun i => by rw [hBeq i]; simp]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Φ'.map_sum (fun i m => C i m (D i m (e i (j i))))]
      refine Finset.sum_congr rfl fun k _ => ?_
      change _ = GC k (GD k (Φ fun i => e i (j i)))
      rw [hGD1, hGC1]
    · have h0 := hoff x hx hxu
      rw [hX0 x h0, ContinuousLinearMap.sum_apply]
      simp [hGD2 _ x h0]
  have hTC : IsTraceClass X := by
    rw [hXeq]; exact isTraceClass_sum _ fun k _ => (hGC3 k).isTraceClass_comp (hGD3 k)
  refine ⟨hTC, ?_⟩

  have htr := hTC.hasSum_trace bH
  let g : (∀ i, J i) → w := fun j => ⟨u j, hsw ⟨j, rfl⟩⟩
  have hg : Function.Injective g := fun j j' h => hinj (congrArg Subtype.val h)
  have hz : ∀ x ∉ Set.range g, ⟪bH x, X (bH x)⟫_ℂ = 0 := by
    intro x hx
    have hxu : x.1 ∉ Set.range u := fun ⟨j, hj⟩ => hx ⟨j, Subtype.ext hj⟩
    simp [hb, hX0 _ (hoff x.1 x.2 hxu)]
  rw [← hg.hasSum_iff hz] at htr
  have hval : ∀ j, ⟪bH (g j), X (bH (g j))⟫_ℂ = κ * ∏ i, ⟪e i (j i), B i (e i (j i))⟫_ℂ := by
    intro j
    simp only [hb, g]
    change ⟪Φ _, X (Φ _)⟫_ℂ = _
    rw [hX, hΦΦ']
  have hprod := (_root_.GlobalTheory.hasSum_pi_prod_of_summable_norm ι J (fun i k => ⟪e i k, B i (e i k)⟫_ℂ)
    fun i => (hB i).1.summable_norm (e i)).mul_left κ
  have hb' : ∀ i, ∑' k, ⟪e i k, B i (e i k)⟫_ℂ = b i := fun i =>
    ((hB i).1.hasSum_trace (e i)).tsum_eq.trans (hB i).2
  simp only [hb'] at hprod
  refine htr.unique ?_
  simpa only [Function.comp_def, hval] using hprod

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLaw
section
noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil.Intertw

variable {l : Type} [Fintype l]

theorem sympl_smul_left (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl (r • w) w' = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_left]
  ring

theorem sympl_smul_right (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl w (r • w') = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_right]
  ring

theorem sympl_antisymm (w w' : l ⊕ l → ℝ) : sympl w w' = -sympl w' w := by
  simp only [sympl, real_inner_comm (pPart w) (qPart w'), real_inner_comm (qPart w) (pPart w')]
  ring

theorem sympl_sub_left (u u' z : l ⊕ l → ℝ) : sympl (u - u') z = sympl u z - sympl u' z := by
  have h1 : pPart (u - u') = pPart u - pPart u' := rfl
  have h2 : qPart (u - u') = qPart u - qPart u' := rfl
  simp only [sympl, h1, h2, inner_sub_left]
  ring

theorem eq_zero_of_exp_eq_one (D : ℝ) (h : ∀ r : ℝ, exp (((π * (r * D) : ℝ) : ℂ) * I) = 1) : D = 0 := by
  by_contra hD
  have := h D⁻¹
  rw [inv_mul_cancel₀ hD, mul_one, Complex.exp_pi_mul_I] at this
  norm_num at this

theorem rhoFun_gaussian_ne_zero (w : l ⊕ l → ℝ) :
    rhoFun w ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) (-pPart w) ≠ 0 := by
  simp only [rhoFun, neg_add_cancel, GroundTheory.Global.gaussianSchwartz_apply]
  refine mul_ne_zero ?_ ?_
  · intro h
    have := norm_phase w (-pPart w)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · simp

theorem coe_smul_sch (c : ℂ) (f : Sch l) : ⇑(c • f) = c • ⇑f := by
  funext x
  simp

theorem eq_of_smul_eq_smul {c c' : ℂ} {F : EuclideanSpace ℝ l → ℂ} {x : EuclideanSpace ℝ l} (hx : F x ≠ 0)
    (h : c • F = c' • F) : c = c' := by
  have := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx this

theorem eq_of_rhoFun_eq {u u' : l ⊕ l → ℝ} (h : ∀ g : Sch l, rhoFun u ⇑g = rhoFun u' ⇑g) : u = u' := by
  classical
  set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
  have key : ∀ z : l ⊕ l → ℝ, exp (((π * (2 * sympl (u - u') z) : ℝ) : ℂ) * I) = 1 := by
    intro z
    obtain ⟨g1, hg1⟩ := exists_schwartz_rhoFun l z g0
    have h1 := h g1
    rw [hg1, rhoFun_rhoFun, rhoFun_rhoFun] at h1
    have h2 := congrArg (rhoFun z) (h g0)
    rw [rhoFun_rhoFun, rhoFun_rhoFun, add_comm z u, add_comm z u', sympl_antisymm z u, sympl_antisymm z u'] at h2
    set a := sympl u z
    set b := sympl u' z
    set F := rhoFun (u + z) ⇑g0
    set G := rhoFun (u' + z) ⇑g0
    have h3 : (exp (((π * -b : ℝ) : ℂ) * I) * exp (((π * a : ℝ) : ℂ) * I)) • F =
        (exp (((π * b : ℝ) : ℂ) * I) * exp (((π * -a : ℝ) : ℂ) * I)) • F := by
      rw [mul_smul, h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_smul, mul_smul]
    have h4 := eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (u + z)) h3
    rw [← Complex.exp_add, ← Complex.exp_add] at h4
    rw [sympl_sub_left]
    have e : ((π * (2 * (a - b)) : ℝ) : ℂ) * I =
        (((π * -b : ℝ) : ℂ) * I + ((π * a : ℝ) : ℂ) * I) - (((π * b : ℝ) : ℂ) * I + ((π * -a : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [e, Complex.exp_sub, h4, div_self (exp_ne_zero _)]
  have hz : ∀ z, sympl (u - u') z = 0 := by
    intro z
    have := eq_zero_of_exp_eq_one (2 * sympl (u - u') z) fun r => by
      have := key (r • z)
      rwa [sympl_smul_right, show 2 * (r * sympl (u - u') z) = r * (2 * sympl (u - u') z) by ring] at this
    linarith
  have hJ : Matrix.J l ℝ *ᵥ (u - u') = 0 := by
    ext b
    have := hz (Pi.single b 1)
    rw [sympl_antisymm, sympl_single] at this
    simpa using this
  have hd : u - u' = 0 := by
    have : u - u' = -((Matrix.J l ℝ * Matrix.J l ℝ) *ᵥ (u - u')) := by
      rw [Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
    rw [this, ← Matrix.mulVec_mulVec, hJ, Matrix.mulVec_zero, neg_zero]
  exact sub_eq_zero.mp hd

end GlobalTheory.RealWeil.Intertw

namespace GlobalTheory.RealWeil


open Intertw in
theorem intertwining_symplectic_and_group_law : ∀ (l : Type) [Fintype l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l),
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ t w w', sympl (A t w) (A t w') = sympl w w') ∧ (∀ s t w, A (s + t) w = A s (A t w)) ∧ ∀ w, A 0 w = w := by
  intro l _ A T hadd h0 hI _
  have hsurj : ∀ t (h : Sch l), T t (T (-t) h) = h := fun t h => by rw [← hadd, add_neg_cancel, h0]
  refine ⟨fun t w w' => ?_, fun s t w => ?_, fun w => ?_⟩
  · have hE : ∀ v v' : l ⊕ l → ℝ, exp (((π * sympl (A t v) (A t v') : ℝ) : ℂ) * I) =
        exp (((π * sympl v v' : ℝ) : ℂ) * I) := by
      intro v v'
      set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
      obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l v' (T (-t) g0)
      obtain ⟨f₂, hf₂⟩ := exists_schwartz_rhoFun l v f₁
      obtain ⟨f₃, hf₃⟩ := exists_schwartz_rhoFun l (v + v') (T (-t) g0)
      have e2 : f₂ = exp (((π * sympl v v' : ℝ) : ℂ) * I) • f₃ := by
        apply DFunLike.coe_injective
        rw [coe_smul_sch, hf₂, hf₁, hf₃, rhoFun_rhoFun]
      have k1 := hI t v' (T (-t) g0) f₁ hf₁
      have k2 := hI t v f₁ f₂ hf₂
      have k3 := hI t (v + v') (T (-t) g0) f₃ hf₃
      rw [hsurj] at k1 k3
      rw [k1, rhoFun_rhoFun, e2, map_smul, coe_smul_sch, k3, map_add (f := _)] at k2
      exact (eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (A t v + A t v')) k2).symm
    apply sub_eq_zero.mp
    refine eq_zero_of_exp_eq_one _ fun r => ?_
    have := hE (r • w) w'
    rw [map_smul, sympl_smul_left, sympl_smul_left] at this
    rw [show ((π * (r * (sympl (A t w) (A t w') - sympl w w')) : ℝ) : ℂ) * I =
        ((π * (r * sympl (A t w) (A t w')) : ℝ) : ℂ) * I - ((π * (r * sympl w w') : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_sub, this, div_self (exp_ne_zero _)]
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w (T (-(s + t)) g)
    have h1 := hI (s + t) w _ f₁ hf₁
    have h2 := hI t w _ f₁ hf₁
    have h3 := hI s (A t w) _ _ h2
    rw [hsurj] at h1
    rw [← hadd, ← hadd, hsurj, h1] at h3
    exact h3
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w g
    have h := hI 0 w g f₁ hf₁
    rw [h0, h0] at h
    rw [← h, hf₁]

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpOmOm
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.SplitWeil

private lemma rpow_half_mul_rpow_inv_eq_one (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    s ^ (b / 2) * t ^ (-a / 2) * (s ^ (b / 2) * t ^ (-a / 2)) * ((t⁻¹) ^ (-a) * s ^ (-b)) = 1 := by
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_neg]
  have e1 : s ^ (b / 2) * s ^ (b / 2) * s ^ (-b) = 1 := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs, show b / 2 + b / 2 + -b = (0 : ℝ) by ring, Real.rpow_zero]
  have e2 : t ^ (-a / 2) * t ^ (-a / 2) * t ^ a = 1 := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, show -a / 2 + -a / 2 + a = (0 : ℝ) by ring, Real.rpow_zero]
  calc s ^ (b / 2) * t ^ (-a / 2) * (s ^ (b / 2) * t ^ (-a / 2)) * (t ^ a * s ^ (-b))
      = (s ^ (b / 2) * s ^ (b / 2) * s ^ (-b)) * (t ^ (-a / 2) * t ^ (-a / 2) * t ^ a) := by ring
    _ = 1 := by rw [e1, e2, one_mul]

private lemma isUnit_of_valuation_eq_one' (z : ℂ) (hz : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  simp

private lemma unit_mul_real_mul_conj_eq_real_sq_mul (m1 m2 : ℂ) (h1 : ‖m1‖ = 1) (h2 : ‖m2‖ = 1) (r1 r2 : ℝ) (u v : ℂ) :
    m1 * m2 * (r1 : ℂ) * (r2 : ℂ) * u * (starRingEnd ℂ) (m1 * m2 * (r1 : ℂ) * (r2 : ℂ) * v) =
      ((r1 * r2 * (r1 * r2) : ℝ) : ℂ) * (u * (starRingEnd ℂ) v) := by
  have e1 := isUnit_of_valuation_eq_one' m1 h1
  have e2 := isUnit_of_valuation_eq_one' m2 h2
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  linear_combination (m2 * (starRingEnd ℂ) m2 * r1 * r2 * r1 * r2 * u * (starRingEnd ℂ) v) * e1 +
    (r1 * r2 * r1 * r2 * u * (starRingEnd ℂ) v) * e2

private lemma nabs_pos_twisted_operators (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 ((Group.isUnit x).map (distribHaarChar k)).ne_zero)

private lemma nabs_inv_twisted_operators (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by
  show ((distribHaarChar k x⁻¹ : NNReal) : ℝ) = ((distribHaarChar k x : NNReal) : ℝ)⁻¹
  rw [map_inv, NNReal.coe_inv]

theorem ip_om_om : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : ∀ x, ‖(μ x : ℂ)‖ = 1) (g : GL a k) (h : GL b k) (Φ Ψ : Matrix b a k → ℂ), ip ν (om μ g h Φ) (om μ g h Ψ) = ip ν Φ Ψ := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _ μ hμ g h Φ Ψ
  set F : Matrix b a k → ℂ := fun y => Φ y * (starRingEnd ℂ) (Ψ y) with hF
  have hinv : ‖(((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hμ, inv_one]
  set ng := nabs k (Matrix.GeneralLinearGroup.det g) with hng
  set nh := nabs k (Matrix.GeneralLinearGroup.det h) with hnh
  set c : ℝ := ng ^ ((Fintype.card b : ℝ) / 2) * nh ^ (-(Fintype.card a : ℝ) / 2) *
    (ng ^ ((Fintype.card b : ℝ) / 2) * nh ^ (-(Fintype.card a : ℝ) / 2)) with hc
  have hpt : ∀ x, om μ g h Φ x * (starRingEnd ℂ) (om μ g h Ψ x) =
      (c : ℂ) * F ((h⁻¹ : GL b k).val * x * g.val) := fun x =>
    unit_mul_real_mul_conj_eq_real_sq_mul _ _ (hμ _) hinv _ _ _ _
  have hT := (_root_.GlobalTheory.SplitWeil.linear_change_of_variables k a b ν).2 g h⁻¹ F
  have hdet : nabs k (Matrix.GeneralLinearGroup.det h⁻¹) = nh⁻¹ := by
    rw [map_inv, nabs_inv_twisted_operators]
  have hkey : c * (nabs k (Matrix.GeneralLinearGroup.det h⁻¹) ^ (-(Fintype.card a : ℝ)) *
      ng ^ (-(Fintype.card b : ℝ))) = 1 := by
    rw [hdet]
    exact rpow_half_mul_rpow_inv_eq_one ng nh (nabs_pos_twisted_operators k _) (nabs_pos_twisted_operators k _) _ _
  unfold ip
  calc ∫ x, om μ g h Φ x * (starRingEnd ℂ) (om μ g h Ψ x) ∂(volM ν b a)
      = ∫ x, (c : ℂ) * F ((h⁻¹ : GL b k).val * x * g.val) ∂(volM ν b a) := by
        congr 1
        funext x
        exact hpt x
    _ = (c : ℂ) * ∫ x, F ((h⁻¹ : GL b k).val * x * g.val) ∂(volM ν b a) := integral_const_mul _ _
    _ = ∫ x, F x ∂(volM ν b a) := by
        rw [hT, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hkey, Complex.ofReal_one, one_mul]

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair
open SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

theorem ite_mem_SB {X : Type*} [TopologicalSpace X] {p : X → Prop} [DecidablePred p] (h : IsClopen {x | p x})
    (hc : IsCompact {x | p x}) : (fun x => if p x then (1 : ℂ) else 0) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro' hc h.1 fun x hx => if_neg hx⟩
  by_cases hx : p x
  · exact ⟨_, h.2, hx, fun y hy => (if_pos hy).trans (if_pos hx).symm⟩
  · exact ⟨_, h.compl.2, hx, fun y hy => (if_neg hy).trans (if_neg hx).symm⟩

variable [Fintype n] [Fintype n']

theorem isClopen_lattice (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] : IsClopen (L : Set (n → k)) := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      ⋂ i, (fun x => ((g⁻¹ : GL n k).val *ᵥ x) i) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [SetLike.mem_coe, mem_smul_iff, mem_stdLat, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [h]
  refine isClopen_iInter_of_finite fun i => IsClopen.preimage ⟨(isCompact_int k).isClosed, isOpen_int k⟩ ?_
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)


omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maps_stdLat_iff {x : Matrix n n' k} :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by
  classical
  simp only [mem_stdLat]
  refine ⟨fun h i j => ?_, fun h y hy i => sum_mem fun j _ => mul_mem (h i j) (hy j)⟩
  have := h (Pi.single j 1) (fun l => ?_) i
  · simpa using this
  · rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]

theorem isClopen_isCompact_maps (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsFullLattice k]
    [L.IsFullLattice k] : IsClopen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧
      IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  let K : Set (Matrix n n' k) := Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have hKo : IsOpen K :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have e : {x : Matrix n n' k | ∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n} = sideMul g h ⁻¹' K := by
    ext x
    have h1 : sideMul g h x ∈ K ↔ ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k] :=
      ⟨fun H i j => H i trivial j trivial, fun H i _ j _ => H i j⟩
    rw [Set.mem_preimage, h1, ← maps_stdLat_iff, Set.mem_setOf_eq]
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  rw [e]
  exact ⟨IsClopen.preimage ⟨hKc.isClosed, hKo⟩ (sideMul g h).continuous, (sideMul g h).isCompact_preimage.2 hKc⟩

theorem latInd_mem_SB (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsFullLattice k] [L.IsFullLattice k] :
    latInd S L ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_maps S L).1 (isClopen_isCompact_maps S L).2

theorem isClopen_isCompact_mapsPair (P : Pair k n') (Q : Pair k n) :
    IsClopen {x : Matrix n n' k | Maps P Q x} ∧ IsCompact {x : Matrix n n' k | Maps P Q x} := by
  have e : {x : Matrix n n' k | Maps P Q x} = {x : Matrix n n' k | ∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker} ∩
      (fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec) ⁻¹' (Q.ker : Set (n → k)) := by
    ext x
    exact maps_iff_glue P.hasVal_vec Q.hasVal_vec
  have h2 := (isClopen_lattice Q.ker).preimage (f := fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec)
    ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  obtain ⟨h1, hc⟩ := isClopen_isCompact_maps P.ker Q.ker
  rw [e]
  exact ⟨h1.inter h2, hc.inter_right h2.1⟩

theorem phiOne_mem_SB (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_mapsPair P Q).1 (isClopen_isCompact_mapsPair P Q).2

end GlobalTheory.LatPair
end
end

