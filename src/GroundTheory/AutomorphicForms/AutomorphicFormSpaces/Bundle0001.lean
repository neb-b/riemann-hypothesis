module

public import Mathlib
public import GroundTheory.AutomorphicForms.HarishChandraRegularity
public import GroundTheory.AutomorphicForms.Bundle0006
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ArchSliceUAction

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
section
namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_kernel_eq_conv_of_aeval_laplacian [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic) (hPd : 0 < P.natDegree)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ U ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (h.laplacian bL) P f = 0 →
        ∀ g : G, (f : G → ℂ) g = ∫ y, (f : G → ℂ) (g * y) * κ y ∂μ := by
  let _ := h.chartedSpace
  set b := Module.finBasis ℝ 𝔤
  set d := Module.finrank ℝ 𝔤
  have hfc : ∀ f : h.smoothFuns (F := ℂ), ∀ g : G, Continuous fun y : G => (f : G → ℂ) (g * y) :=
    fun f g => (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous.comp
      (continuous_const.mul continuous_id)
  have hexpc : Continuous fun x : EuclideanSpace ℝ (Fin d) => h.expG (coordEquiv b x) :=
    h.continuous_expG.comp (coordEquiv b).continuous
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_expCoord μ b
  have hV : {x : EuclideanSpace ℝ (Fin d) | h.expG (coordEquiv b x) ∈ U} ∈ 𝓝 0 := by
    refine hexpc.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ρ₀, hρ₀, hρ₀V⟩ := Metric.mem_nhds_iff.1 hV
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    have hsub : ∀ x y : EuclideanSpace ℝ (Fin d), x = y := by
      intro x y; ext i; exact absurd i.2 (by omega)
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens (fun _ => 1) contDiff_const (fun x _ => by
      rw [hsub x 0]; exact Metric.mem_closedBall_self hε.le)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f _ g => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hρ₀V (by rw [hsub x 0]; exact Metric.mem_ball_self hρ₀)
    · have := hκ _ (hfc f g)
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [this, integral_euclideanSpace_of_eq_zero hd]
      simp
  ·
    set Q := P ^ (d + 1)
    have hQ : Q.Monic := hP.pow _
    have hQd : Q.natDegree = (d + 1) * P.natDegree := hP.natDegree_pow _
    obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b Q hQ
    set ρ := min (min δ ε) ρ₀
    have hρ : 0 < ρ := lt_min (lt_min hδ hε) hρ₀
    have hρδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 δ :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
    have hρε : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.closedBall 0 ε :=
      Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))
    have hρV : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 ρ₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hm1 : 1 ≤ 2 * Q.natDegree := by rw [hQd]; nlinarith
    have hnm : d < 2 * (2 * Q.natDegree) := by rw [hQd]; nlinarith
    obtain ⟨E, β, -, -, hEs, -, hβs, -, hβU, hid⟩ := exists_parametrix hd hm1 hnm Metric.isOpen_ball
      hA (fun α hα => (ha α hα).contDiffOn Metric.isOpen_ball.uniqueDiffOn) hell Metric.isOpen_ball
      (Metric.mem_ball_self hρ) hρδ
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens β hβs (hβU.trans hρε)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f hf g => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hρ₀V (hρV (hβU hx))
    · have hQf : Polynomial.aeval (h.laplacian bL) Q f = 0 := by
        rw [show Q = P ^ d * P from pow_succ P d, map_mul, Module.End.mul_apply, hf, map_zero]
      set ψ := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
      have hψ : ContDiff ℝ ∞ ψ := h.contDiff_comp_coordEquiv f.2 g b
      have h1 := hid ψ hψ.contDiffOn
      have h0 : ∫ x, E x * diffOp A a ψ x = 0 := by
        rw [← integral_zero (EuclideanSpace ℝ (Fin d)) ℂ]
        congr 1
        funext x
        by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ
        · rw [hop f g x hx, hQf]; simp
        · rw [image_eq_zero_of_notMem_tsupport fun hE => hx (hρδ (hEs hE)), zero_mul]
      rw [h0, eq_comm, sub_eq_zero] at h1
      have hψ0 : ψ 0 = (f : G → ℂ) g := by simp [ψ]
      rw [← hψ0, h1]
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [hκ _ (hfc f g)]

noncomputable def convDeriv (X : 𝔤) (κ : G → ℂ) (y : G) : ℂ :=
  h.rightDeriv X (fun z => κ z⁻¹) y⁻¹

variable {h}

theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  let _ := h.chartedSpace
  exact ContMDiff.continuous hf

theorem isSmoothFun_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) :
    h.IsSmoothFun (fun z : G => κ z⁻¹) := by
  let _ := h.chartedSpace
  have := h.lieGroup ∞
  exact hκ.comp (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)

theorem continuous_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.rightDeriv X fun z : G => κ z⁻¹) :=
  continuous_of_isSmoothFun (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

theorem continuous_convDeriv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.convDeriv X κ) :=
  (continuous_rightDeriv_comp_inv hκ X).comp continuous_inv

theorem rightDeriv_eq_zero_of_eventually {f : G → ℂ} {g : G} (hf : ∀ᶠ z in 𝓝 g, f z = 0)
    (X : 𝔤) : h.rightDeriv X f g = 0 := by
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := continuous_const.mul h.continuous_expG
  have h0 : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have : Tendsto (fun Y : 𝔤 => g * h.expG Y) (𝓝 0) (𝓝 g) := by
      simpa using hc.tendsto (0 : 𝔤)
    exact this.eventually hf
  simp only [rightDeriv, h0.fderiv_eq, fderiv_const_apply]
  rfl

theorem rightDeriv_comp_inv_eq_zero {κ : G → ℂ} {z : G} (hz : z⁻¹ ∉ tsupport κ) (X : 𝔤) :
    h.rightDeriv X (fun w : G => κ w⁻¹) z = 0 := by
  refine rightDeriv_eq_zero_of_eventually ?_ X
  have hopen : IsOpen (tsupport κ)ᶜ := (isClosed_tsupport κ).isOpen_compl
  have ht : Tendsto (fun w : G => w⁻¹) (𝓝 z) (𝓝 z⁻¹) := continuous_inv.tendsto z
  exact (ht.eventually (hopen.mem_nhds hz)).mono fun w hw =>
    (image_eq_zero_of_notMem_tsupport hw : κ w⁻¹ = 0)

theorem support_convDeriv_subset (X : 𝔤) (κ : G → ℂ) :
    Function.support (h.convDeriv X κ) ⊆ tsupport κ := by
  intro y hy
  by_contra hyκ
  exact hy (rightDeriv_comp_inv_eq_zero (by rwa [inv_inv]) X)

theorem hasCompactSupport_convDeriv {κ : G → ℂ} (hκc : HasCompactSupport κ) (X : 𝔤) :
    HasCompactSupport (h.convDeriv X κ) :=
  hκc.mono' (support_convDeriv_subset X κ)

theorem exists_bound_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    (X : 𝔤) : ∃ M, ∀ z, ‖h.rightDeriv X (fun w : G => κ w⁻¹) z‖ ≤ M := by
  have hDcs : HasCompactSupport (h.rightDeriv X fun w : G => κ w⁻¹) := by
    refine HasCompactSupport.intro (hκc.image continuous_inv) fun z hz => ?_
    refine rightDeriv_comp_inv_eq_zero (fun hk => hz ⟨z⁻¹, hk, inv_inv z⟩) X
  exact hDcs.exists_bound_of_continuous (continuous_rightDeriv_comp_inv hκ X)

theorem rightDeriv_eq_integral_convDeriv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    {f : G → ℂ} (hf : h.IsSmoothFun f) (hconv : ∀ g, f g = ∫ y, f (g * y) * κ y ∂μ)
    (X : 𝔤) (g : G) :
    h.rightDeriv X f g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfc : Continuous f := continuous_of_isSmoothFun hf
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X

  have hshift : ∀ t : ℝ, f (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp [mul_assoc, mul_inv_rev]

  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]

  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0 :=
    h.hasDerivAt_rightDeriv hf X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero
section
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

set_option linter.unusedSectionVars false

def IsLeftInvariant (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  ∀ (γ : GL (Fin n) K) (g : AdelicGLn.AdelicGL K n), φ (AdelicGLn.diagonal K n γ * g) = φ g

def IsSmooth (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  IsArchSmooth φ ∧
    ∀ g, ∀ᶠ y in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), φ (g * finEmb K n y) = φ g

def IsKFinite (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ
    (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
      rightTranslate (k : AdelicGLn.AdelicGL K n) φ))

def IsZFinite (φ : archSmooth K n) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ
    ((fun z => uAction z φ) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n))))

def HasModerateGrowth (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ g, ‖φ g‖ ≤ C * height g ^ N

structure IsAutomorphicForm (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  isLeftInvariant : IsLeftInvariant φ
  isSmooth : IsSmooth φ
  isKFinite : IsKFinite φ
  isZFinite : IsZFinite ⟨φ, isSmooth.1⟩
  hasModerateGrowth : HasModerateGrowth φ

section Closure

variable {φ ψ : AdelicGLn.AdelicGL K n → ℂ}

theorem isLeftInvariant_zero : IsLeftInvariant (0 : AdelicGLn.AdelicGL K n → ℂ) := fun _ _ => rfl

theorem IsLeftInvariant.add (hφ : IsLeftInvariant φ) (hψ : IsLeftInvariant ψ) :
    IsLeftInvariant (φ + ψ) := fun γ g => by simp [hφ γ g, hψ γ g]

theorem IsLeftInvariant.smul (c : ℂ) (hφ : IsLeftInvariant φ) : IsLeftInvariant (c • φ) :=
  fun γ g => by simp [hφ γ g]

theorem isSmooth_zero : IsSmooth (0 : AdelicGLn.AdelicGL K n → ℂ) :=
  ⟨(archSmooth K n).zero_mem, fun _ => Eventually.of_forall fun _ => rfl⟩

theorem IsSmooth.add (hφ : IsSmooth φ) (hψ : IsSmooth ψ) : IsSmooth (φ + ψ) :=
  ⟨(archSmooth K n).add_mem hφ.1 hψ.1, fun g => ((hφ.2 g).and (hψ.2 g)).mono fun y hy => by
    simp [hy.1, hy.2]⟩

theorem IsSmooth.smul (c : ℂ) (hφ : IsSmooth φ) : IsSmooth (c • φ) :=
  ⟨(archSmooth K n).smul_mem c hφ.1, fun g => (hφ.2 g).mono fun y hy => by simp [hy]⟩

theorem isKFinite_zero : IsKFinite (0 : AdelicGLn.AdelicGL K n → ℂ) := by
  unfold IsKFinite
  have : Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
      rightTranslate (k : AdelicGLn.AdelicGL K n) (0 : AdelicGLn.AdelicGL K n → ℂ)) ≤ ⊥ :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; simp; rfl)
  exact Submodule.finiteDimensional_of_le this

theorem IsKFinite.add (hφ : IsKFinite φ) (hψ : IsKFinite ψ) : IsKFinite (φ + ψ) := by
  unfold IsKFinite at *
  have hle : Submodule.span ℂ
      (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) (φ + ψ)) ≤
      Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) φ) ⊔
      Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) ψ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem IsKFinite.smul (c : ℂ) (hφ : IsKFinite φ) : IsKFinite (c • φ) := by
  unfold IsKFinite at *
  have hle : Submodule.span ℂ
      (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) (c • φ)) ≤
      Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) φ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem isZFinite_zero : IsZFinite (0 : archSmooth K n) := by
  unfold IsZFinite
  have : Submodule.span ℂ ((fun z => uAction z (0 : archSmooth K n)) ''
      ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤ ⊥ :=
    Submodule.span_le.2 (by rintro _ ⟨z, -, rfl⟩; simp)
  exact Submodule.finiteDimensional_of_le this

theorem IsZFinite.add {φ ψ : archSmooth K n} (hφ : IsZFinite φ) (hψ : IsZFinite ψ) :
    IsZFinite (φ + ψ) := by
  unfold IsZFinite at *
  have hle : Submodule.span ℂ ((fun z => uAction z (φ + ψ)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤
      Submodule.span ℂ ((fun z => uAction z φ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ⊔
      Submodule.span ℂ ((fun z => uAction z ψ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
      (Submodule.subset_span ⟨z, hz, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem IsZFinite.smul (c : ℂ) {φ : archSmooth K n} (hφ : IsZFinite φ) : IsZFinite (c • φ) := by
  unfold IsZFinite at *
  have hle : Submodule.span ℂ ((fun z => uAction z (c • φ)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤
      Submodule.span ℂ ((fun z => uAction z φ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨z, hz, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem hasModerateGrowth_zero : HasModerateGrowth (0 : AdelicGLn.AdelicGL K n → ℂ) :=
  ⟨0, 0, fun g => by simp⟩

theorem HasModerateGrowth.add (hφ : HasModerateGrowth φ) (hψ : HasModerateGrowth ψ) :
    HasModerateGrowth (φ + ψ) := by
  obtain ⟨C₁, N₁, h₁⟩ := hφ
  obtain ⟨C₂, N₂, h₂⟩ := hψ
  refine ⟨|C₁| + |C₂|, max N₁ N₂, fun g => ?_⟩
  have hg := one_le_height g
  have e₁ : height g ^ N₁ ≤ height g ^ max N₁ N₂ := pow_le_pow_right₀ hg (le_max_left _ _)
  have e₂ : height g ^ N₂ ≤ height g ^ max N₁ N₂ := pow_le_pow_right₀ hg (le_max_right _ _)
  have p₁ : 0 ≤ height g ^ N₁ := pow_nonneg (height_pos g).le _
  have p₂ : 0 ≤ height g ^ N₂ := pow_nonneg (height_pos g).le _
  calc ‖(φ + ψ) g‖ ≤ ‖φ g‖ + ‖ψ g‖ := norm_add_le _ _
    _ ≤ C₁ * height g ^ N₁ + C₂ * height g ^ N₂ := add_le_add (h₁ g) (h₂ g)
    _ ≤ |C₁| * height g ^ max N₁ N₂ + |C₂| * height g ^ max N₁ N₂ :=
        add_le_add
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₁)
            (mul_le_mul_of_nonneg_left e₁ (abs_nonneg _)))
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₂)
            (mul_le_mul_of_nonneg_left e₂ (abs_nonneg _)))
    _ = (|C₁| + |C₂|) * height g ^ max N₁ N₂ := by ring

theorem HasModerateGrowth.smul (c : ℂ) (hφ : HasModerateGrowth φ) : HasModerateGrowth (c • φ) := by
  obtain ⟨C, N, h⟩ := hφ
  refine ⟨‖c‖ * C, N, fun g => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h g) (norm_nonneg c)

theorem archSmooth_mk_add (hφ : IsArchSmooth φ) (hψ : IsArchSmooth ψ) :
    (⟨φ + ψ, (archSmooth K n).add_mem hφ hψ⟩ : archSmooth K n) = ⟨φ, hφ⟩ + ⟨ψ, hψ⟩ :=
  Subtype.ext rfl

theorem archSmooth_mk_smul (c : ℂ) (hφ : IsArchSmooth φ) :
    (⟨c • φ, (archSmooth K n).smul_mem c hφ⟩ : archSmooth K n) = c • ⟨φ, hφ⟩ :=
  Subtype.ext rfl

theorem IsAutomorphicForm.add (hφ : IsAutomorphicForm φ) (hψ : IsAutomorphicForm ψ) :
    IsAutomorphicForm (φ + ψ) := by
  refine ⟨hφ.isLeftInvariant.add hψ.isLeftInvariant, hφ.isSmooth.add hψ.isSmooth,
    hφ.isKFinite.add hψ.isKFinite, ?_, hφ.hasModerateGrowth.add hψ.hasModerateGrowth⟩
  have h := hφ.isZFinite.add hψ.isZFinite
  rwa [← archSmooth_mk_add hφ.isSmooth.1 hψ.isSmooth.1] at h

theorem IsAutomorphicForm.smul (c : ℂ) (hφ : IsAutomorphicForm φ) : IsAutomorphicForm (c • φ) := by
  refine ⟨hφ.isLeftInvariant.smul c, hφ.isSmooth.smul c, hφ.isKFinite.smul c, ?_,
    hφ.hasModerateGrowth.smul c⟩
  have h := hφ.isZFinite.smul c
  rwa [← archSmooth_mk_smul c hφ.isSmooth.1] at h

theorem isAutomorphicForm_zero : IsAutomorphicForm (0 : AdelicGLn.AdelicGL K n → ℂ) :=
  ⟨isLeftInvariant_zero, isSmooth_zero, isKFinite_zero, isZFinite_zero, hasModerateGrowth_zero⟩

end Closure


variable (K n) in
def automorphicForms : Submodule ℂ (AdelicGLn.AdelicGL K n → ℂ) where
  carrier := {φ | IsAutomorphicForm φ}
  zero_mem' := isAutomorphicForm_zero
  add_mem' hφ hψ := hφ.add hψ
  smul_mem' c _ hφ := hφ.smul c

theorem mem_automorphicForms {φ : AdelicGLn.AdelicGL K n → ℂ} :
    φ ∈ automorphicForms K n ↔ IsAutomorphicForm φ :=
  Iff.rfl

end AutomorphicForm

end

end GroundTheory.Automorphic
end

