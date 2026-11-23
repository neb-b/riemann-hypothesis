module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsAnalyticNear {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  ∃ (N : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
    (∀ i, AnalyticOnNhd ℂ (f i) N) ∧ X ∩ N = {z | z ∈ N ∧ ∀ i, f i z = 0}

def GermIrreducibleAt {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  w ∈ X ∧ ∀ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∨ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GenericCountCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsGenericCountCover {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (N : ℕ) : Prop :=
  (∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) ∧
  ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
    (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
    ∀ y ∈ U, g y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N ∧
      ∀ x ∈ Y, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧ Y ∩ V = h '' O

noncomputable def fibreDiscr {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (l : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (y : Fin d → ℂ) : ℂ :=
  if h : {x | x ∈ Y ∧ A x = y}.encard = N then
    ∏ p ∈ (Set.finite_of_encard_eq_coe h).toFinset.offDiag, (l p.1 - l p.2)
  else 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GoodPointChartLemmas
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NormalModelGoodPointChart

open MvPolynomial Topology
open scoped ContDiff

noncomputable section

theorem hasFDerivAt_eval {σ : Type} [Fintype σ] [DecidableEq σ] (q : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun z : σ → ℂ => eval z q)
      (∑ j, eval x (pderiv j q) • ContinuousLinearMap.proj j : (σ → ℂ) →L[ℂ] ℂ) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    have e1 : (fun z : σ → ℂ => eval z (C a)) = fun _ => a := by
      funext z
      simp
    rw [e1]
    convert hasFDerivAt_const (𝕜 := ℂ) a x
    ext v
    simp
  | add p q hp hq =>
    have e1 : (fun z : σ → ℂ => eval z (p + q)) = fun z => eval z p + eval z q := by
      funext z
      simp
    rw [e1]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [Finset.sum_add_distrib, add_mul]
  | mul_X p i hp =>
    have hfun : (fun z : σ → ℂ => eval z (p * X i)) = (fun z => eval z p) * (fun z => z i) := by
      funext z
      simp
    rw [hfun]
    refine (hp.mul (hasFDerivAt_apply i x)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, pderiv_mul,
      pderiv_X, map_add, map_mul, eval_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · by_cases hij : i = i <;> simp [mul_comm]

theorem fderiv_eval_apply {σ : Type} [Fintype σ] [DecidableEq σ] (q : MvPolynomial σ ℂ) (x v : σ → ℂ) :
    fderiv ℂ (fun z : σ → ℂ => eval z q) x v = ∑ s, eval x (pderiv s q) * v s := by
  rw [(hasFDerivAt_eval q x).fderiv]
  simp

theorem exists_clm_ker_inf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (L : E →ₗ[ℂ] F) (hL : Function.Surjective L) (d : ℕ)
    (hd : Module.finrank ℂ E = d + Module.finrank ℂ F) :
    ∃ A : E →L[ℂ] (Fin d → ℂ), ∀ v, A v = 0 → L v = 0 → v = 0 := by
  obtain ⟨q, hq⟩ := (LinearMap.ker L).exists_isCompl
  have hdK : Module.finrank ℂ (LinearMap.ker L) = d := by
    have := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hL, finrank_top] at this
    omega
  let eK : LinearMap.ker L ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ (Fin d → ℂ) (by simp [hdK])
  refine ⟨LinearMap.toContinuousLinearMap (eK.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto q hq),
    fun v hA hLv => ?_⟩
  have h2 : v ∈ LinearMap.ker L := LinearMap.mem_ker.2 hLv
  have h3 : (LinearMap.ker L).projectionOnto q hq v = 0 := eK.injective (by simpa using hA)
  rw [Submodule.projectionOnto_apply_of_mem_left hq h2] at h3
  simpa using congrArg Subtype.val h3

theorem exists_coordChart {σ κ ι : Type} [Fintype σ] [Fintype κ] [Fintype ι]
    (q : κ ⊕ ι → (σ → ℂ) → ℂ) (a : σ → ℂ) (W : Set (σ → ℂ))
    (hq : ∀ k, AnalyticAt ℂ (q k) a)
    (hinj : ∀ v : σ → ℂ, (∀ k, fderiv ℂ (q k) a v = 0) → v = 0)
    (hcard : Fintype.card κ + Fintype.card ι = Fintype.card σ) (hW : W ∈ 𝓝 a) :
    ∃ (V : Set (σ → ℂ)) (O : Set (κ → ℂ)) (φ : (κ → ℂ) → σ → ℂ),
      IsOpen V ∧ a ∈ V ∧ V ⊆ W ∧ IsOpen O ∧ AnalyticOnNhd ℂ φ O ∧
      (∀ y ∈ O, φ y ∈ V) ∧ (∀ y ∈ O, ∀ i, q (Sum.inl i) (φ y) = y i) ∧
      (∀ y ∈ O, ∀ j, q (Sum.inr j) (φ y) = 0) ∧
      (∀ z ∈ V, (∀ j, q (Sum.inr j) z = 0) →
        (fun i => q (Sum.inl i) z) ∈ O ∧ φ (fun i => q (Sum.inl i) z) = z) ∧
      (∀ y ∈ O, ∀ v, (∀ i, fderiv ℂ (q (Sum.inl i)) (φ y) (fderiv ℂ φ y v) = v i) ∧
        ∀ j, fderiv ℂ (q (Sum.inr j)) (φ y) (fderiv ℂ φ y v) = 0) := by
  classical
  set P : (σ → ℂ) →L[ℂ] (κ ⊕ ι → ℂ) := ContinuousLinearMap.pi fun k => fderiv ℂ (q k) a with hP
  have hPinj : Function.Injective P := by
    intro v v' hvv
    rw [← sub_eq_zero]
    refine hinj _ fun k => ?_
    have := congrFun hvv k
    simp only [hP, ContinuousLinearMap.pi_apply] at this
    rw [map_sub, this, sub_self]
  have hPbij : Function.Bijective (P : (σ → ℂ) →ₗ[ℂ] (κ ⊕ ι → ℂ)) :=
    ⟨hPinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, hcard])).1 hPinj⟩
  set Pe : (σ → ℂ) ≃L[ℂ] (κ ⊕ ι → ℂ) :=
    (LinearEquiv.ofBijective _ hPbij).toContinuousLinearEquiv with hPe
  have hPeP : (Pe : (σ → ℂ) →L[ℂ] (κ ⊕ ι → ℂ)) = P := by ext1 x; rfl
  set F : (σ → ℂ) → κ ⊕ ι → ℂ := fun z k => q k z with hF
  have hFan : ∀ z, (∀ k, AnalyticAt ℂ (q k) z) → AnalyticAt ℂ F z := fun z hz => analyticAt_pi_iff.2 hz
  have hFd : HasFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    rw [hPeP]
    exact hasFDerivAt_pi.2 fun k => (hq k).differentiableAt.hasFDerivAt
  have hst : HasStrictFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    have := (hFan a hq).hasStrictFDerivAt; rwa [hFd.fderiv] at this
  set Φ := hst.toOpenPartialHomeomorph F with hΦ
  have hev : ∀ᶠ t in 𝓝 a, (∀ k, AnalyticAt ℂ (q k) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (κ ⊕ ι → ℂ)) → _) := by
    refine (Filter.eventually_all.2 fun k => (hq k).eventually_analyticAt).and
      ((show ∀ᶠ t in 𝓝 a, t ∈ W from hW).and ?_)
    exact (hFan a hq).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨Pe, hFd.fderiv.symm⟩)
  obtain ⟨V₀, hV₀, hV₀o, haV₀⟩ := eventually_nhds_iff.1 hev
  set Ψ := Φ.restrOpen V₀ hV₀o with hΨ
  have hΨs : Ψ.source = Φ.source ∩ V₀ := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hΨF : ∀ z, Ψ z = F z := fun z => rfl
  have haΨ : a ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, haV₀⟩
  have hsrc : ∀ t ∈ Ψ.source, (∀ k, AnalyticAt ℂ (q k) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (κ ⊕ ι → ℂ)) → _) :=
    fun t ht => hV₀ t (hΨs ▸ ht).2
  have hembA : ∀ y, AnalyticAt ℂ (fun y : κ → ℂ => Sum.elim y (0 : ι → ℂ)) y := fun y =>
    analyticAt_pi_iff.2 fun k => by
      rcases k with i | j
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ) i).analyticAt y
      · exact analyticAt_const
  have hemb : Continuous (fun y : κ → ℂ => Sum.elim y (0 : ι → ℂ)) :=
    continuous_iff_continuousAt.2 fun y => (hembA y).continuousAt
  set O : Set (κ → ℂ) := (fun y => Sum.elim y (0 : ι → ℂ)) ⁻¹' Ψ.target with hO
  have hOo : IsOpen O := Ψ.open_target.preimage hemb
  have hφV : ∀ y ∈ O, Ψ.symm (Sum.elim y 0) ∈ Ψ.source := fun y hy => Ψ.map_target hy
  have hFφ : ∀ y ∈ O, F (Ψ.symm (Sum.elim y 0)) = Sum.elim y 0 := fun y hy => Ψ.right_inv hy
  have hφan : AnalyticOnNhd ℂ (fun y => Ψ.symm (Sum.elim y 0)) O := by
    intro y hy
    have hp : Sum.elim y (0 : ι → ℂ) ∈ Ψ.target := hy
    obtain ⟨han, -, e', he'⟩ := hsrc _ (Ψ.map_target hp)
    have hFe : HasFDerivAt Ψ (e' : (σ → ℂ) →L[ℂ] _) (Ψ.symm (Sum.elim y 0)) := by
      rw [he']; exact (hFan _ han).differentiableAt.hasFDerivAt
    have hc : ContDiffAt ℂ ω Ψ.symm (Sum.elim y 0) :=
      Ψ.contDiffAt_symm hp hFe (hFan _ han).contDiffAt
    exact AnalyticAt.comp (g := Ψ.symm) (f := fun y : κ → ℂ => Sum.elim y (0 : ι → ℂ)) (x := y)
      hc.analyticAt (hembA y)
  refine ⟨Ψ.source, O, fun y => Ψ.symm (Sum.elim y 0), Ψ.open_source, haΨ,
    fun t ht => (hsrc t ht).2.1, hOo, hφan, hφV, ?_, ?_, ?_, ?_⟩
  · intro y hy i
    exact congrFun (hFφ y hy) (Sum.inl i)
  · intro y hy j
    exact congrFun (hFφ y hy) (Sum.inr j)
  · intro z hz hz0
    have hFz : F z = Sum.elim (fun i => q (Sum.inl i) z) 0 := by
      funext k
      rcases k with i | j
      · rfl
      · exact hz0 j
    have ht : F z ∈ Ψ.target := by rw [← hΨF]; exact Ψ.map_source hz
    refine ⟨show Sum.elim (fun i => q (Sum.inl i) z) (0 : ι → ℂ) ∈ Ψ.target from hFz ▸ ht, ?_⟩
    show Ψ.symm (Sum.elim (fun i => q (Sum.inl i) z) (0 : ι → ℂ)) = z
    rw [← hFz, ← hΨF]
    exact Ψ.left_inv hz
  · intro y hy v
    have hyn : O ∈ 𝓝 y := hOo.mem_nhds hy
    have hφd : HasFDerivAt (fun y => Ψ.symm (Sum.elim y 0))
        (fderiv ℂ (fun y => Ψ.symm (Sum.elim y 0)) y) y :=
      (hφan y hy).differentiableAt.hasFDerivAt
    have hcomp : ∀ k, fderiv ℂ (fun y' => q k (Ψ.symm (Sum.elim y' 0))) y =
        (fderiv ℂ (q k) (Ψ.symm (Sum.elim y 0))).comp (fderiv ℂ (fun y => Ψ.symm (Sum.elim y 0)) y) :=
      fun k => ((((hsrc _ (hφV y hy)).1 k).differentiableAt.hasFDerivAt).comp y hφd).fderiv
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have he : (fun y' => q (Sum.inl i) (Ψ.symm (Sum.elim y' 0))) =ᶠ[𝓝 y] fun y' => y' i :=
        Filter.eventually_of_mem hyn fun y' hy' => congrFun (hFφ y' hy') (Sum.inl i)
      have := congrArg (fun L : (κ → ℂ) →L[ℂ] ℂ => L v)
        ((hcomp (Sum.inl i)).symm.trans (he.fderiv_eq.trans (hasFDerivAt_apply i y).fderiv))
      simpa using this
    · have he : (fun y' => q (Sum.inr j) (Ψ.symm (Sum.elim y' 0))) =ᶠ[𝓝 y] fun _ => (0 : ℂ) :=
        Filter.eventually_of_mem hyn fun y' hy' => congrFun (hFφ y' hy') (Sum.inr j)
      have := congrArg (fun L : (κ → ℂ) →L[ℂ] ℂ => L v)
        ((hcomp (Sum.inr j)).symm.trans (he.fderiv_eq.trans (hasFDerivAt_const (0 : ℂ) y).fderiv))
      simpa using this

end

end GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GradientAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GradientAtPoint

variable {σ : Type*} (w : σ → ℂ)

def grad : MvPolynomial σ ℂ →ₗ[ℂ] (σ → ℂ) :=
  LinearMap.pi fun i => (aeval w).toLinearMap ∘ₗ (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap

theorem grad_apply (p : MvPolynomial σ ℂ) (i : σ) : grad w p i = eval w (pderiv i p) := by
  simp [grad]

theorem grad_mul (a b : MvPolynomial σ ℂ) :
    grad w (a * b) = eval w a • grad w b + eval w b • grad w a := by
  ext i
  simp only [grad_apply, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, Pi.add_apply, Pi.smul_apply]

theorem grad_X_sub_C [DecidableEq σ] (j : σ) : grad w (X j - C (w j)) = Pi.single j 1 := by
  ext i
  rw [grad_apply, map_sub, pderiv_C, sub_zero, pderiv_X]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem grad_mul_of_eval_eq_zero (r p : MvPolynomial σ ℂ) (hp : eval w p = 0) :
    grad w (r * p) = eval w r • grad w p := by
  rw [grad_mul, hp, zero_smul, add_zero]

def linPart [Fintype σ] (c : σ → ℂ) : MvPolynomial σ ℂ :=
  ∑ i, C (c i) * (X i - C (w i))

theorem sub_C_eval_mem_span (p : MvPolynomial σ ℂ) :
    p - C (eval w p) ∈ Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), show p + q - (C (eval w p) + C (eval w q)) = (p - C (eval w p)) + (q - C (eval w q)) by
      ring]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, eval_X, map_mul,
      show p * X i - C (eval w p) * C (w i) = (p - C (eval w p)) * X i + C (eval w p) * (X i - C (w i)) by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem ker_eval_eq_span :
    RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) =
      Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  apply le_antisymm
  · intro p hp
    have h := sub_C_eval_mem_span w p
    rwa [RingHom.mem_ker.1 hp, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]

theorem grad_eq_zero_of_mem_sq {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2) : grad w p = 0 := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [grad_mul, RingHom.mem_ker.1 ha, RingHom.mem_ker.1 hb, zero_smul, zero_smul, add_zero]
  · rw [map_add (f := _), hx, hy, add_zero]

theorem sub_linPart_mem_sq [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) :
    p - linPart w (grad w p) ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  classical
  rw [ker_eval_eq_span] at hp
  obtain ⟨a, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hp
  have hg : grad w (∑ i, a i * (X i - C (w i))) = fun i => eval w (a i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [grad_mul, grad_X_sub_C, map_sub, eval_X, eval_C, sub_self, zero_smul, add_zero]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hg, linPart, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_mul, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]

theorem mem_sq_of_grad_eq_zero [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) (hg : grad w p = 0) :
    p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  have h := sub_linPart_mem_sq w hp
  rwa [hg, linPart, Finset.sum_eq_zero (fun i _ => by simp), sub_zero] at h

end GradientAtPoint

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HeightCoheightQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ringKrullDim_quotient_eq_coheight {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, hP⟩ : PrimeSpectrum B) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  have h : PrimeSpectrum.zeroLocus (P : Set B) = Set.Ici (⟨P, hP⟩ : PrimeSpectrum B) := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [h]

theorem height_add_ringKrullDim_quotient_le {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by
  have : Nonempty (PrimeSpectrum B) := ⟨⟨P, hP⟩⟩
  rw [ringKrullDim_quotient_eq_coheight, PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) ⟨P, hP⟩

theorem height_map_add_one_le_of_mem_nonZeroDivisors {B : Type*} [CommRing B] [IsNoetherianRing B] {y : B}
    (hy : y ∈ nonZeroDivisors B) (P : Ideal B) [hP : P.IsPrime] (hyP : y ∈ P) :
    (P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 ≤ P.height := by
  set I := Ideal.span {y} with hI
  have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk I)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIP
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (P.map (Ideal.Quotient.mk I)).height = n :=
    ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hP'.ne_top) |>.imp fun _ h => h.symm
  rw [hn]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe (⟨_, hP'⟩ : PrimeSpectrum (B ⧸ I))
    (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hn)
  let f : PrimeSpectrum (B ⧸ I) → PrimeSpectrum B := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · rw [← PrimeSpectrum.asIdeal_le_asIdeal] at hab ⊢
      exact Ideal.comap_mono hab
    · ext1
      have := congrArg PrimeSpectrum.asIdeal hab
      exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective this
  let L := l.map f hf
  have hyhead : y ∈ L.head.asIdeal := by
    change y ∈ (l.head.asIdeal).comap (Ideal.Quotient.mk I)
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self y)]
    exact Ideal.zero_mem _
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (J := L.head.asIdeal) bot_le
  let p0 : PrimeSpectrum B := ⟨p, hp.1.1⟩
  have hlt : p0 < L.head := by
    refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hple) fun h => ?_
    have hyp : y ∈ p := by
      have : p = L.head.asIdeal := congrArg PrimeSpectrum.asIdeal h
      rw [this]
      exact hyhead
    exact Set.disjoint_iff.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) ⟨hyp, hy⟩
  let L' := L.cons p0 hlt
  have hLlast : L'.last = ⟨P, hP⟩ := by
    simp only [L', L, RelSeries.last_cons, LTSeries.last_map, hlast]
    ext1
    exact Ideal.comap_map_mk hIP
  have hlen' : L'.length = n + 1 := by
    simp [L', L, hlen]
  have := Order.length_le_height_last (p := L')
  rw [hLlast, hlen', ← PrimeSpectrum.height_eq_orderHeight] at this
  exact_mod_cast this

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalLimitGlue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology Set Function
open scoped ContDiff Manifold

theorem tendsto_of_forall_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {l : Filter ι} (T : ι → (E → ℝ) → ℝ) (L : (E → ℝ) → ℝ)
    (hT : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → ∀ᶠ ε in l, T ε (f + g) = T ε f + T ε g)
    (hL : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → L (f + g) = L f + L g)
    (hloc : ∀ p : E, ∃ N ∈ 𝓝 p, ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ N → Tendsto (fun ε => T ε f) l (𝓝 (L f)))
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε => T ε f) l (𝓝 (L f)) := by
  choose N hN hNf using hloc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) (isClosed_tsupport f)
    (fun p => interior (N p)) (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hN x)⟩)
  obtain ⟨g, hg⟩ : ∃ g : E → E → ℝ, g = fun i x => ρ i x * f x := ⟨_, rfl⟩
  have hgs : ∀ i, ContDiff ℝ ∞ (g i) := fun i => by
    rw [hg]; exact (ρ i).contMDiff.contDiff.mul hf
  have hgc : ∀ i, HasCompactSupport (g i) := fun i => by
    rw [hg]; exact hfc.mul_left
  have hgN : ∀ i, tsupport (g i) ⊆ N i := fun i => by
    rw [hg]; exact tsupport_mul_subset_left.trans ((hρ i).trans interior_subset)
  have hfin : {i | (support (ρ i) ∩ tsupport f).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hfc
  have hsum : f = ∑ i ∈ hfin.toFinset, g i := by
    funext x
    simp only [Finset.sum_apply, hg]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport f
    · rw [← finsum_eq_sum_of_support_subset (fun i => ρ i x), ρ.sum_eq_one hx, one_mul]
      intro i hi
      simp only [Set.Finite.coe_toFinset, mem_ofPred_eq]
      exact ⟨x, hi, hx⟩
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hT0 : ∀ᶠ ε in l, T ε 0 = 0 := by
    filter_upwards [hT 0 0 contDiff_const HasCompactSupport.zero contDiff_const
      HasCompactSupport.zero] with ε h
    simpa using h
  have hL0 : L 0 = 0 := by
    simpa using hL 0 0 contDiff_const HasCompactSupport.zero contDiff_const HasCompactSupport.zero
  have key : ∀ s : Finset E, ContDiff ℝ ∞ (∑ i ∈ s, g i) ∧ HasCompactSupport (∑ i ∈ s, g i) ∧
      (∀ᶠ ε in l, T ε (∑ i ∈ s, g i) = ∑ i ∈ s, T ε (g i)) ∧
      L (∑ i ∈ s, g i) = ∑ i ∈ s, L (g i) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨contDiff_const, HasCompactSupport.zero, hT0, hL0⟩
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      simp only [Finset.sum_insert ha]
      refine ⟨(hgs a).add h1, (hgc a).add h2, ?_, ?_⟩
      · filter_upwards [hT (g a) _ (hgs a) (hgc a) h1 h2, h3] with ε e1 e2
        rw [e1, e2]
      · rw [hL (g a) _ (hgs a) (hgc a) h1 h2, h4]
  obtain ⟨-, -, hTs, hLs⟩ := key hfin.toFinset
  rw [hsum, hLs]
  exact (tendsto_finsetSum _ fun i _ => hNf i (g i) (hgs i) (hgc i) (hgN i)).congr'
    (hTs.mono fun ε h => h.symm)

end GroundTheory.Heights₂.Heights
end

