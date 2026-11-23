module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchChartInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace BranchChartInt

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem differentiable_mulVec {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
  (Matrix.mulVecLin A).toContinuousLinearMap.differentiable


open Classical in
theorem chartDens_indicator_image {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {p : Fin n → ℂ} (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartDens J A (γ.image.indicator g) φ y =
      ∑ᶠ t ∈ {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y},
        (if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
          g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0) := by
  set T : (Fin n → ℂ) → ℝ := fun x => if h : ∃ s, IsSheetAt J A x s then
      γ.image.indicator g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y else 0 with hT
  have h1 : chartDens J A (γ.image.indicator g) φ y = ∑ᶠ x ∈ fibre J A y, T x := rfl
  have h2 : ∑ᶠ x ∈ fibre J A y, T x =
      ∑ᶠ x ∈ γ.toFun '' {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y}, T x := by
    apply finsum_mem_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hx, hTx⟩
      have hxi : x ∈ γ.image := by
        by_contra hni
        apply hTx
        simp only [hT, Set.indicator_of_notMem hni, zero_mul, dite_eq_ite, ite_self]
      obtain ⟨t, ht, rfl⟩ := hxi
      exact ⟨⟨t, ⟨ht, hx.2⟩, rfl⟩, hTx⟩
    · rintro ⟨⟨t, ⟨ht, hty⟩, rfl⟩, hTx⟩
      exact ⟨⟨γ.mapsTo ht, hty⟩, hTx⟩
  have hinj : Set.InjOn γ.toFun {t | t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius ∧ A *ᵥ γ.toFun t = y} :=
    γ.injOn.mono (by intro t ht; exact ht.1)
  rw [h1, h2, finsum_mem_image hinj]
  refine finsum_mem_congr rfl fun t ht => ?_
  have hti : γ.toFun t ∈ γ.image := ⟨t, ht.1, rfl⟩
  simp only [hT, Set.indicator_of_mem hti, ht.2]

theorem maDens_branch_eq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin n → ℂ} (γ : VarBranch J d p) {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) {t : Fin d → ℂ} (ht : t ∈ Metric.ball (0 : Fin d → ℂ) γ.radius)
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A (γ.toFun t) s) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ γ.toFun t) *
        Complex.normSq (jacC (fun t => A *ᵥ γ.toFun t) t).det := by
  obtain ⟨U, hUo, hxU, hsd, hsx, -, V, hV, hVeq⟩ := hs
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  have hτd : DifferentiableOn ℂ τ (Metric.ball 0 γ.radius) :=
    (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hτa : AnalyticAt ℂ τ t := analyticOnNhd_of_differentiableOn Metric.isOpen_ball hτd t ht
  have hΔ : Metric.ball (0 : Fin d → ℂ) γ.radius ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
  have hγc : ContinuousAt γ.toFun t := γ.differentiableOn.continuousOn.continuousAt hΔ
  have hev : ∀ k, φ k ∘ γ.toFun =ᶠ[𝓝 t] (φ k ∘ s) ∘ τ := by
    intro k
    filter_upwards [hΔ, hγc.preimage_mem_nhds hV,
      hτa.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)] with t' ht' hV' hU'
    simp only [Function.comp_apply]
    rw [← hVeq (γ.toFun t') ⟨γ.mapsTo ht', hV'⟩ hU']
  have hmd : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) t := by
    unfold ReciprocityTheory.AnForm.maDens
    congr 3
    funext k
    have h2 : fderiv ℝ (fderiv ℝ (φ k ∘ γ.toFun)) t = fderiv ℝ (fderiv ℝ ((φ k ∘ s) ∘ τ)) t :=
      ((hev k).fderiv (𝕜 := ℝ)).fderiv_eq
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  have hsa : AnalyticAt ℂ s (τ t) := analyticOnNhd_of_differentiableOn hUo hsd (τ t) hxU
  have hc : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (τ t) := by
    intro k
    obtain ⟨O, hOo, hZO, hφO⟩ := hφ k
    have hmem : s (τ t) ∈ O := by
      rw [show s (τ t) = γ.toFun t from hsx]
      exact hZO (γ.mapsTo ht)
    exact ((hφO.contDiffAt (hOo.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)).comp (τ t)
      (hsa.contDiffAt.restrict_scalars ℝ)
  rw [hmd]
  exact maDens_comp (fun k => φ k ∘ s) τ t hτa hc

theorem integrableOn_branch {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : VarBranch J d p) {g : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hg : Continuous g)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    (hK : ∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ Metric.ball 0 γ.radius ∧
      ∀ t ∈ Metric.ball 0 γ.radius, t ∉ K → g (γ.toFun t) = 0) :
    IntegrableOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) := by
  obtain ⟨K, hKc, hKΔ, hK0⟩ := hK
  have hγ : ContDiffOn ℝ 2 γ.toFun (Metric.ball 0 γ.radius) :=
    ((analyticOnNhd_of_differentiableOn Metric.isOpen_ball γ.differentiableOn).contDiffOn_of_completeSpace
      ).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ γ.toFun) (Metric.ball 0 γ.radius) := by
    intro k
    obtain ⟨O, -, hZO, hφO⟩ := hφ k
    exact (hφO.of_le (WithTop.coe_le_coe.2 le_top)).comp hγ fun t ht => hZO (γ.mapsTo ht)
  have hcont : ContinuousOn (fun t => (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t)
      (Metric.ball 0 γ.radius) :=
    (hg.comp_continuousOn γ.differentiableOn.continuousOn).mul
      (ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ Metric.isOpen_ball hc2)
  refine ((hcont.mono hKΔ).integrableOn_compact hKc).of_forall_sdiff_eq_zero measurableSet_ball ?_
  rintro t ⟨htΔ, htK⟩
  simp [hK0 t htΔ htK]

end BranchChartInt


open BranchChartInt in
theorem BranchChartInt.proof (hA : HolomorphicFibreSumInt.Statement) (hS : BranchSheetAE.Statement)
    (hF : ComplexSets.FibreBound.Statement) : BranchChartInt.Statement := by
  classical
  intro n d J A p γ g φ hJ hdim hfin hg hφ hK
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτ
  set H : (Fin d → ℂ) → ℝ := fun t => if h : ∃ s, IsSheetAt J A (γ.toFun t) s then
      g (γ.toFun t) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ γ.toFun t) else 0 with hH
  have hτd : DifferentiableOn ℂ τ Δ := (differentiable_mulVec A).comp_differentiableOn γ.differentiableOn
  have hFin : ∀ y, {t | t ∈ Δ ∧ τ t = y}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hF n d J A hJ hdim hfin y).2.1.subset ?_)
      (γ.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ⟨ht, hty⟩, rfl⟩
    exact ⟨γ.mapsTo ht, hty⟩
  have hae : ∀ᵐ t ∂(volume.restrict Δ), (g ∘ γ.toFun) t * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ γ.toFun) t =
      Complex.normSq (jacC τ t).det * H t := by
    filter_upwards [hS n d J A p γ hJ hdim hfin, ae_restrict_mem measurableSet_ball] with t hts htΔ
    simp only [hH, dif_pos hts, Function.comp_apply]
    rw [maDens_branch_eq γ hφ htΔ hts.choose_spec]
    ring
  have hint : IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Δ :=
    (integrableOn_branch γ hg hφ hK).congr hae
  obtain ⟨hIi, hIeq⟩ := hA d Δ τ H Metric.isOpen_ball hτd hFin hint
  have hcd : chartDens J A (γ.image.indicator g) φ = fun y => ∑ᶠ t ∈ {t | t ∈ Δ ∧ τ t = y}, H t :=
    funext fun y => chartDens_indicator_image J A γ g φ y
  refine ⟨hcd ▸ hIi, ?_⟩
  unfold chartInt ReciprocityTheory.AnForm.maInt
  rw [hcd, hIeq]
  exact (integral_congr_ae hae).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCentredDiscCoverCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Matrix

noncomputable section

theorem centredDiscCover_punctured_branch (hPCC : PuncturedCoverCycles.Statement)
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) :
    ∃ (δ : ℝ) (k : ℕ) (φ : ℂ → σ → ℂ), 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ k ∧
      DifferentiableOn ℂ φ (ball 0 δ \ {0}) ∧ Set.InjOn φ (ball 0 δ \ {0}) ∧
      ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k := by
  obtain ⟨hwY, hN, hmaps, huniq, hcard, -, hsec⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let Φ : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv
  let L : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi fun _ => p.comp (Φ : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))
  let A : Matrix (Fin (0 + 1)) (Fin (Fintype.card σ)) ℂ :=
    LinearMap.toMatrix' (L : (Fin (Fintype.card σ) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
  have hA : ∀ z, A *ᵥ z = fun _ => p (Φ z) := fun z => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have hpT : ∀ z, p (w + Φ z) = p w + p (Φ z) := fun z => map_add p w (Φ z)
  have hT : ∀ x, w + Φ (Φ.symm (x - w)) = x := fun x => by simp
  have hone : ∀ (y : Fin (0 + 1) → ℂ) (t : ℂ), t = y 0 → (fun _ => t) = y := fun y t ht => by
    funext i
    rw [show i = 0 from Subsingleton.elim (α := Fin 1) _ _, ht]
  let X : Set (Fin (Fintype.card σ) → ℂ) := {z | w + Φ z ∈ Y ∧ p (Φ z) ≠ 0}
  obtain ⟨m, ord, ψ, δ, hδ, hδ1, hsum, hord, hdiff, hmap, hinj, -, -⟩ :=
    hPCC (Fintype.card σ) 0 N A 0 ρ X hρ rfl
      (fun x hx => by
        rw [hA, dist_zero_right, pi_norm_const]
        refine ⟨?_, hx.2⟩
        have := hmaps hx.1
        rwa [mem_ball, dist_eq_norm, hpT, add_sub_cancel_left] at this)
      (fun y hy hy0 => by
        have hyρ : p w + y 0 ∈ ball (p w) ρ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
          exact (norm_le_pi_norm y 0).trans_lt (by rwa [dist_zero_right] at hy)
        rw [← hcard _ hyρ (by simpa using hy0), ← ((add_right_injective w).comp Φ.injective).injOn.encard_image]
        congr 1
        ext x
        constructor
        · rintro ⟨z, ⟨⟨hzY, -⟩, hzy⟩, rfl⟩
          refine ⟨hzY, ?_⟩
          rw [Function.comp_apply, hpT, ← congrFun ((hA z).symm.trans hzy) 0]
        · rintro ⟨hxY, hxp⟩
          refine ⟨Φ.symm (x - w), ⟨⟨by rwa [hT], ?_⟩, ?_⟩, hT x⟩
          · simpa [hxp] using hy0
          · rw [hA]
            exact hone y _ (by simp [hxp]))
      (fun x hx => by
        obtain ⟨O₀, V₀, g₀, hO₀, hV₀, hxV₀, hg₀, hpg₀, hYV⟩ :=
          hsec (w + Φ x) hx.1 (by rw [hpT]; simpa using hx.2)
        have hsec' : ∀ z, w + Φ z ∈ Y ∩ V₀ → p w + p (Φ z) ∈ O₀ ∧ g₀ (p w + p (Φ z)) = w + Φ z := by
          intro z hz
          rw [hYV] at hz
          obtain ⟨t, ht, hgt⟩ := hz
          have : t = p w + p (Φ z) := by rw [← hpT, ← hgt, hpg₀ t ht]
          subst this
          exact ⟨ht, hgt⟩
        obtain ⟨hxO, hgx⟩ := hsec' x ⟨hx.1, hxV₀⟩
        refine ⟨{y | p w + y 0 ∈ O₀ ∧ y 0 ≠ 0}, {z | w + Φ z ∈ V₀ ∧ p (Φ z) ≠ 0},
          fun y => Φ.symm (g₀ (p w + y 0) - w),
          (hO₀.preimage (continuous_const.add (continuous_apply 0))).inter
            (isOpen_ne_fun (continuous_apply 0) continuous_const),
          by rw [hA]; exact ⟨hxO, hx.2⟩,
          (hV₀.preimage (continuous_const.add Φ.continuous)).inter
            (isOpen_ne_fun (p.continuous.comp Φ.continuous) continuous_const),
          ⟨hxV₀, hx.2⟩, ?_, by rw [hA]; simp [hgx], fun y hy => ?_, ?_⟩
        · refine Φ.symm.differentiable.comp_differentiableOn
            ((hg₀.comp ((differentiableOn_const _).add (differentiable_apply 0).differentiableOn)
              ?_).sub_const w)
          intro y hy
          exact hy.1
        · rw [hA]
          refine hone y _ ?_
          simp [hpg₀ _ hy.1]
        · ext z
          constructor
          · rintro ⟨⟨hzY, hz0⟩, hzV, -⟩
            obtain ⟨hzO, hgz⟩ := hsec' z ⟨hzY, hzV⟩
            exact ⟨fun _ => p (Φ z), ⟨hzO, hz0⟩, by simp [hgz]⟩
          · rintro ⟨y, ⟨hyO, hy0⟩, rfl⟩
            have hw : w + Φ (Φ.symm (g₀ (p w + y 0) - w)) = g₀ (p w + y 0) := hT _
            have hp : p (Φ (Φ.symm (g₀ (p w + y 0) - w))) = y 0 := by simp [hpg₀ _ hyO]
            have hmem : g₀ (p w + y 0) ∈ Y ∩ V₀ := by rw [hYV]; exact ⟨_, hyO, rfl⟩
            show (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ Y ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0) ∧
              (w + Φ (Φ.symm (g₀ (p w + y 0) - w)) ∈ V₀ ∧ p (Φ (Φ.symm (g₀ (p w + y 0) - w))) ≠ 0)
            rw [hw, hp]
            exact ⟨⟨hmem.1, hy0⟩, hmem.2, hy0⟩)
  obtain ⟨b⟩ : Nonempty (Fin m) := by
    rcases m with _ | m
    · simp at hsum
      omega
    · exact ⟨0⟩
  have hpunct : ∀ s ∈ ball (0 : ℂ) δ \ {0},
      (fun _ => s) ∈ ball (0 : Fin (0 + 1) → ℂ) δ ∩ {t | t 0 ≠ 0} := fun s hs =>
    ⟨by rw [mem_ball, dist_zero_right, pi_norm_const]; exact mem_ball_zero_iff.1 hs.1, hs.2⟩
  refine ⟨δ, ord b, fun s => w + Φ (ψ b fun _ => s), hδ, hδ1, hord b, ?_, ?_, fun s hs => ?_⟩
  · exact (differentiableOn_const w).add (Φ.differentiable.comp_differentiableOn
      ((hdiff b).comp (differentiable_pi.2 fun _ => differentiable_id).differentiableOn hpunct))
  · intro s hs s' hs' hss'
    have := hinj b (hpunct s hs) (hpunct s' hs') (Φ.injective (add_left_cancel hss'))
    exact congrFun this 0
  · obtain ⟨hX, hAψ⟩ := hmap b _ (hpunct s hs)
    refine ⟨hX.1, ?_⟩
    rw [hpT]
    have := congrFun ((hA _).symm.trans hAψ) 0
    simp only [Function.update_self] at this
    rw [this]

theorem centredDiscCover_extend_across_centre
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) {δ : ℝ} {k : ℕ} {φ : ℂ → σ → ℂ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 1 ≤ k) (hφd : DifferentiableOn ℂ φ (ball 0 δ \ {0})) (hφi : Set.InjOn φ (ball 0 δ \ {0}))
    (hφY : ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k) :
    ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
      DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y := by
  obtain ⟨hwY, -, hmaps, huniq, -, hprop, -⟩ := hY
  have hρ : 0 < ρ := dist_nonneg.trans_lt (hmaps hwY)
  set r := min δ (ρ / 2) with hr
  have hr0 : 0 < r := lt_min hδ (half_pos hρ)
  have hrδ : ball (0 : ℂ) r \ {0} ⊆ ball 0 δ \ {0} :=
    Set.sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))
  have hK : IsCompact {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hprop _ (closedBall_subset_ball (half_lt_self hρ)) (isCompact_closedBall _ _)
  have hφK : ∀ s ∈ ball (0 : ℂ) r \ {0}, φ s ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} := by
    intro s hs
    obtain ⟨hY', hp⟩ := hφY s (hrδ hs)
    refine ⟨hY', ?_⟩
    rw [mem_closedBall, hp, dist_eq_norm, add_sub_cancel_left, norm_pow]
    have h1 : ‖s‖ < r := mem_ball_zero_iff.1 hs.1
    calc ‖s‖ ^ k ≤ ‖s‖ :=
          pow_le_of_le_one (norm_nonneg _) (h1.le.trans ((min_le_left _ _).trans hδ1)) (by omega)
      _ ≤ ρ / 2 := h1.le.trans (min_le_right _ _)
  have hbdd : BddAbove (norm ∘ φ '' (ball 0 r \ {0})) := by
    refine (hK.image continuous_norm).bddAbove.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨φ s, hφK s hs, rfl⟩
  have hF := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr0) (hφd.mono hrδ) hbdd
  set ℓ := limUnder (𝓝[≠] (0 : ℂ)) φ with hℓdef
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ ball (0 : ℂ) r \ {0} := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds 0 hr0)] with s h1 h2
    exact ⟨h2, h1⟩
  have hlim : Tendsto φ (𝓝[≠] 0) (𝓝 ℓ) := by
    have hc := (hF.continuousOn.continuousAt (ball_mem_nhds 0 hr0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [Function.update_self] at hc
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Function.update_of_ne hs _ _
  have hℓK : ℓ ∈ {x | x ∈ Y ∧ p x ∈ closedBall (p w) (ρ / 2)} :=
    hK.isClosed.mem_of_tendsto hlim (hev.mono hφK)
  have hpℓ : p ℓ = p w := by
    have h1 : Tendsto (fun s => p (φ s)) (𝓝[≠] 0) (𝓝 (p ℓ)) := (p.continuous.tendsto ℓ).comp hlim
    have h2 : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝[≠] 0) (𝓝 (p w)) := by
      have : Tendsto (fun s : ℂ => p w + s ^ k) (𝓝 0) (𝓝 (p w + 0 ^ k)) :=
        (continuous_const.add (continuous_pow k)).tendsto 0
      rw [zero_pow (by omega), add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [hev] with s hs
    exact (hφY s (hrδ hs)).2
  have hℓ : ℓ = w := huniq ℓ hℓK.1 hpℓ
  refine ⟨r, hr0, Function.update φ 0 w, ?_, ?_, Function.update_self _ _ _, ?_⟩
  · rw [← hℓ]
    exact hF
  · have hoff : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → Function.update φ 0 w s ≠ w := by
      intro s hs h0 heq
      rw [Function.update_of_ne h0] at heq
      have := (hφY s (hrδ ⟨hs, h0⟩)).2
      rw [heq] at this
      exact pow_ne_zero k h0 (by linear_combination -this)
    intro s hs s' hs' hss'
    by_cases h0 : s = 0 <;> by_cases h0' : s' = 0
    · rw [h0, h0']
    · subst h0
      rw [Function.update_self] at hss'
      exact absurd hss'.symm (hoff s' hs' h0')
    · subst h0'
      rw [Function.update_self] at hss'
      exact absurd hss' (hoff s hs h0)
    · rw [Function.update_of_ne h0, Function.update_of_ne h0'] at hss'
      exact hφi (hrδ ⟨hs, h0⟩) (hrδ ⟨hs', h0'⟩) hss'
  · intro s hs
    by_cases h0 : s = 0
    · subst h0
      rw [Function.update_self]
      exact hwY
    · rw [Function.update_of_ne h0]
      exact (hφY s (hrδ ⟨hs, h0⟩)).1

theorem CentredDiscCoverCurve.proof (hPCC : PuncturedCoverCycles.Statement) :
    CentredDiscCoverCurve.Statement := by
  intro σ _ Y w p ρ N hY
  obtain ⟨δ, k, φ, hδ, hδ1, hk, hφd, hφi, hφY⟩ := centredDiscCover_punctured_branch hPCC hY
  exact centredDiscCover_extend_across_centre hY hδ hδ1 hk hφd hφi hφY

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalFlatNotInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

theorem CriticalFlatNotInjective.proof : CriticalFlatNotInjective.Statement := by
  intro k U f a hk hU hf haU hJa hflat hinj
  set J : (Fin k → ℂ) → ℂ := fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hJdef
  have hJan : AnalyticOnNhd ℂ J U := fun z hz =>
    analyticAt_det_fderiv (InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hz)
  set Z : Set (Fin k → ℂ) := {z | J z = 0} with hZdef
  have hZ : IsAnalyticNear Z a := by
    refine ⟨U, 1, fun _ => J, hU, haU, fun _ => hJan, ?_⟩
    ext z
    simp only [hZdef, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
    tauto
  obtain ⟨N, hN, haN, hdense⟩ :=
    RegularLocusDense.proof AnalyticImplicitChart.proof (Fin k) Z a hZ
  have hB : IsOpen (N ∩ U) := hN.inter hU
  have ha : a ∈ closure (regLocus (Z ∩ (N ∩ U))) :=
    hdense (N ∩ U) hB Set.inter_subset_left ⟨hJa, haN, haU⟩
  obtain ⟨c, hc⟩ : (regLocus (Z ∩ (N ∩ U))).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at ha
    exact ha
  obtain ⟨⟨hcZ, hcB⟩, d, A, O, V, g, hO, hV, hcV, hg, hAg, hYV⟩ := hc
  obtain ⟨y0, hy0O, hgy0⟩ : c ∈ g '' O := hYV ▸ ⟨⟨hcZ, hcB⟩, hcV⟩

  have hgO : ∀ y ∈ O, J (g y) = 0 ∧ g y ∈ U := by
    intro y hy
    have h1 : g y ∈ Z ∩ (N ∩ U) ∩ V := hYV ▸ Set.mem_image_of_mem g hy
    exact ⟨h1.1.1, h1.1.2.2⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·
    obtain ⟨z, ⟨hzV, hzB⟩, hzc, hz0⟩ := exists_zero_ne_near hk (hJan c hcB.2) hcZ
      (Filter.inter_mem (hV.mem_nhds hcV) (hB.mem_nhds hcB))
    obtain ⟨y1, -, hgy1⟩ : z ∈ g '' O := hYV ▸ ⟨⟨hz0, hzB⟩, hzV⟩
    exact hzc (by rw [← hgy1, ← hgy0, Subsingleton.elim y1 y0])
  ·
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO y0 hy0O
    have hconst : ∀ y ∈ ball y0 ε, f (g y) = f (g y0) := by
      intro y hy
      have hdiff : ∀ x ∈ ball y0 ε, DifferentiableAt ℂ (f ∘ g) x := fun x hx =>
        (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2)).comp x
          (hg x (hball hx)).differentiableAt
      refine (convex_ball y0 ε).is_const_of_fderivWithin_eq_zero (f := f ∘ g)
        (fun x hx => (hdiff x hx).differentiableWithinAt) (fun x hx => ?_) hy (mem_ball_self hε)
      rw [fderivWithin_of_isOpen isOpen_ball hx,
        fderiv_comp x (hf.differentiableAt (hU.mem_nhds (hgO x (hball hx)).2))
          (hg x (hball hx)).differentiableAt,
        hflat (g x) (hgO x (hball hx)).2 (hgO x (hball hx)).1, ContinuousLinearMap.zero_comp]
    set y1 : Fin d → ℂ := y0 + ((ε / 2 : ℝ) : ℂ) • (fun _ => (1 : ℂ)) with hy1
    have hy1ball : y1 ∈ ball y0 ε := by
      rw [mem_ball, dist_eq_norm, hy1, add_sub_cancel_left, norm_smul, pi_norm_const, norm_one, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hy10 : y1 ≠ y0 := by
      intro h
      have h2 := congrFun (congrArg (· - y0) h) ⟨0, hd⟩
      simp only [hy1, add_sub_cancel_left, sub_self, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        mul_one, Complex.ofReal_eq_zero] at h2
      linarith
    have heq : g y1 = g y0 :=
      hinj (hgO y1 (hball hy1ball)).2 (hgO y0 hy0O).2 (hconst y1 hy1ball)
    exact hy10 (by rw [← hAg y1 (hball hy1ball), ← hAg y0 hy0O, heq])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianPrimeDerivations
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem JacobianPrimeDerivations.proof (hDetect : PolyDerivationsDetectSquare.Statement)
    (hBasis : CotangentBasisInPrime.Statement) (hMinor : DerivationMinorOfDetection.Statement)
    (hClear : LocalGeneratorsClearDenominators.Statement) : JacobianPrimeDerivations.Statement := by
  intro k _ n p hp
  obtain ⟨h, f, hfp, hspan, hind⟩ := hBasis (MvPolynomial (Fin n) k) p
  obtain ⟨D, hD⟩ := hMinor (MvPolynomial (Fin n) k) p h f hfp hind
    (fun g hg hDg => hDetect k n p g hg hDg)
  obtain ⟨s, hs, hsp⟩ := hClear (MvPolynomial (Fin n) k) p h f hfp hspan
  exact ⟨h, f, D, s, hfp, hs, hsp, hD⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

