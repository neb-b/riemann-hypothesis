module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Development
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.HasDerivAtShift
section
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_flow_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  fun_prop

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}

lemma flow_zero (g : Matrix (Fin n) (Fin n) ℂ) :
    g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
  simp

lemma hasDerivAt_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have h0 := Formalism.REAL.hasDerivAt_matrix_exp_smul_at_zero X
  have hc : HasDerivAt (fun u : ℝ => g * NormedSpace.exp ((u : ℂ) • X)) (g * X) 0 := by
    have hL := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)).hasFDerivAt
      (x := NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    exact hL.comp_hasDerivAt (0 : ℝ) h0
  have hFd : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
    hFd.comp_hasDerivAt_of_eq (0 : ℝ) hc (flow_zero g).symm
  have hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [flow_zero]; exact hU.mem_nhds hgU
  have hev : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0]
      (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with u hu
    exact hfF _ hu (hG g hg u)
  exact hcomp.congr_of_eventuallyEq hev

lemma rdV_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    RdV X f g = fderiv ℝ F g (g * X) := (hasDerivAt_local hG hU hgU hF hfF hg).deriv

lemma hasDerivAt_zero (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rdV_local hG hU hgU hF hfF hg]
  exact hasDerivAt_local hG hU hgU hF hfF hg

lemma hasDerivAt_shift (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hh : g * NormedSpace.exp ((t : ℂ) • X) ∈ G := hG g hg t
  have h0 := hasDerivAt_zero hG hf hh
  have h0' : HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]; exact h0
  refine (h0'.comp_sub_const t t).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show f (g * NormedSpace.exp ((s : ℂ) • X)) =
    f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X))
  have hcomm : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  have e : (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X = (s : ℂ) • X := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ hcomm, e]

lemma contOn_of_smooth {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn f G := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG
  exact hfF g hgU hgG

lemma contOn_rdV (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn (RdV X f) G := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hd : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hc : ContinuousAt (fun g => fderiv ℝ F g (g * X)) g₀ :=
    (hd.continuousAt (hU.mem_nhds hg₀U)).clm_apply
      ((continuous_id.matrix_mul continuous_const).continuousAt)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (rdV_local hG hU hg₀U hF hfF hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG
  exact rdV_local hG hU hgU hF hfF hgG

end QnRdSkewW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.SkewReductionGroup
section
open Matrix Filter Topology

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_mul_fix {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
      (NormedSpace.exp ((s : ℂ) • X) * X * E) s := by
    intro s
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) X (s : ℂ)
    have h2 := h.scomp (x := s) Complex.ofRealCLM.hasDerivAt
    have h3 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X))
        (NormedSpace.exp ((s : ℂ) • X) * X) s := by
      have hcomm : X * NormedSpace.exp ((s : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * X :=
        (((Commute.refl X).smul_right (s : ℂ)).exp_right).eq
      exact h2.congr_deriv (by simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; exact hcomm)
    exact h3.mul_const E
  have hc := is_const_of_deriv_eq_zero (f := fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
    (fun s => (hd s).differentiableAt) (fun s => by rw [(hd s).deriv, Matrix.mul_assoc, hXE, Matrix.mul_zero])
  have := hc t 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
  exact this

end Linfty

lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hXv : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  let E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j _ => v j
  have hXE : X * E = 0 := by
    ext j l
    have := congrFun hXv j
    simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h := exp_mul_fix X E hXE t
  funext j
  have := congrFun (congrFun h j) j
  simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma exp_mem_UH {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by
  have hU : IsUnit H := IsUnit.of_mul_eq_one _ hH
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hH
  have h1 : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [hinv]
    calc Yᴴ = Yᴴ * H * H := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = H * (-Y) * H := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hU, hinv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]

lemma glev_mul {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ?_⟩
  · show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    have e1 : gᴴ * Hpk k r * g = Hpk k r := hgU
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hhU
    calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · obtain ⟨g1, g2⟩ := hgF a ha
    obtain ⟨h1, h2⟩ := hhF a ha
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, h1, g1]
    · rw [← Matrix.mulVec_mulVec, h2, g2]

lemma glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩
      ⋂ a : Fin r, ⋂ (_ : a.val < i.val),
        ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)}) := by
    ext g
    simp only [Glev, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

lemma exp_mem_glev {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hL, hF⟩ := hX
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  refine ⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]
  · obtain ⟨h1, h2⟩ := hF a ha
    exact ⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩

theorem skew_reduction_group : StepGroup := by
  intro k r i X hX
  exact ⟨glev_closed k r i, fun g hg t => glev_mul hg (exp_mem_glev hX t), exp_mem_glev hX⟩

end QnRdSkewW
end
end

