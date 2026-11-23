module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

theorem gram_of_lineMap {D : D7} {n m : ℕ} (hm : ∀ i j : Fin m, i = j) (τ : Matrix (Fin n) (Fin m) D.host.E)
    (G : Matrix (Fin n) (Fin n) D.host.E) (G' : Matrix (Fin m) (Fin m) D.host.E) (ζ : Fin n → D.host.E)
    (ζ' : Fin m → D.host.E) (c : D.host.E) (hmap : τ *ᵥ ζ' = -ζ)
    (hnorm : star ζ ⬝ᵥ G *ᵥ ζ = c * (star ζ' ⬝ᵥ G' *ᵥ ζ')) (hne : star ζ' ⬝ᵥ G' *ᵥ ζ' ≠ 0) :
    τᴴ * (G * τ) = c • G' := by
  haveI : Subsingleton (Fin m) := ⟨hm⟩
  have key : ∀ (M : Matrix (Fin m) (Fin m) D.host.E) (i : Fin m), star ζ' ⬝ᵥ M *ᵥ ζ' = star (ζ' i) * (M i i * ζ' i) := by
    intro M i
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_subsingleton _ i, Pi.star_apply]
  have hζ : ζ = -(τ *ᵥ ζ') := by rw [hmap, neg_neg]
  have h1 : star ζ ⬝ᵥ G *ᵥ ζ = star ζ' ⬝ᵥ (τᴴ * (G * τ)) *ᵥ ζ' := by
    rw [hζ, star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, Matrix.star_mulVec,
      Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  refine Matrix.ext fun i j => ?_
  obtain rfl := hm i j
  rw [h1, key _ i, key _ i] at hnorm
  rw [key _ i] at hne
  have hz : star (ζ' i) * ζ' i ≠ 0 := by
    intro h0; apply hne; rw [mul_left_comm, h0, mul_zero]
  have : star (ζ' i) * ζ' i * ((τᴴ * (G * τ)) i i - c * G' i i) = 0 := by
    rw [mul_sub]; rw [show star (ζ' i) * ζ' i * (τᴴ * (G * τ)) i i = star (ζ' i) * ((τᴴ * (G * τ)) i i * ζ' i) by ring, hnorm]; ring
  rw [Matrix.smul_apply, smul_eq_mul]
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hz)
  exact h3

end GlobalTheory.ContrComb
end

noncomputable section
namespace GlobalTheory.ContrComb

theorem link_gram {D : D7} {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) :
    l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • B'.L.gram := by
  rw [Int.cast_one, one_mul]
  refine gram_of_lineMap (fun i j => Fin.ext (by have := i.isLt; have := j.isLt; have := B'.line.1; omega))
    l.τ B.L.gram B'.L.gram B.ζ B'.ζ _ l.map l.norm B'.line.2

theorem integrand_cont_per : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → Continuous (fun p : Mx D B'.L.rank S.rank × (WO B.A S × WO S B'.A) => f₂ ((B'.o.resT S).symm (p.2.2, p.1)) * f₁ ((B.o.resS S).symm (p.2.1, l.κ S p.1))) ∧ ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ (w : Mx D B'.L.rank S.rank) (u : WO B.A S) (v : WO S B'.A), f₂ ((B'.o.resT S).symm (v, γ + w)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + w))) = f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w)) := by
  intro D ρ σ B B' l S ψ f₁ f₂ h₁ h₂
  obtain ⟨hadd, hcont, hrat, -, hsym, -⟩ :=
    GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 (link_gram l) (l.κ S) (fun _ => rfl)
  refine ⟨?_, ?_⟩
  · exact (h₂.cont.comp ((B'.o.continuous_resT_symm S).comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_fst))).mul
      (h₁.cont.comp ((B.o.continuous_resS_symm S).comp
        ((continuous_fst.comp continuous_snd).prodMk (hcont.comp continuous_fst))))
  · intro γ hγ w u v
    obtain ⟨c₀, hc₀⟩ := hrat γ hγ
    obtain ⟨γ₀, hγ₀⟩ := hγ
    have e₂ : (B'.o.resT S).symm (v, γ + w) = (B'.o.resT S).symm (0, γ) + (B'.o.resT S).symm (v, w) := by
      rw [← map_add (f := _)]; simp
    have q₂ : (B'.o.resT S).symm (0, γ) = ratW B'.V₀ S (B'.o.iB * γ₀) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, ← hγ₀]
      show _ = rat _
      rw [rat_mul]; rfl
    have e₁ : (B.o.resS S).symm (u, l.κ S (γ + w)) = (B.o.resS S).symm (0, l.κ S γ) + (B.o.resS S).symm (u, l.κ S w) := by
      rw [hadd, ← map_add (f := _)]; simp
    have q₁ : (B.o.resS S).symm (0, l.κ S γ) = ratW S B.V₀ (c₀ * B.o.qB) := by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, ← hc₀]
      show _ = rat _
      rw [rat_mul]; rfl
    have hph : symplOH B.L S (l.κ S γ) (l.κ S w) = -(symplOH S B'.L γ w) := by
      simp only [symplOH, hsym]
      push_cast
      ring
    rw [e₂, e₁, q₂, q₁, h₂.quasi, h₁.quasi, ← q₂, ← q₁, B'.o.symplOH_resT, B.o.symplOH_resS,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, symplOH_zero_left, zero_add, zero_add, hph, neg_neg]
    have hψ : ψ (-(symplOH S B'.L γ w)) * ψ (symplOH S B'.L γ w) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    linear_combination (f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) * hψ

end GlobalTheory.ContrComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsBiSmooth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
open scoped ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrSmooth

section Gen

variable {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

def LocSm (K : X → E → ℂ) : Prop :=
  ∀ x₀, ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : NormedSpace ℝ G) (ρ : X → G) (c : X → ℂ) (F : G → E → ℂ),
    ContinuousAt ρ x₀ ∧ ContinuousAt c x₀ ∧ ContDiff ℝ ∞ (Function.uncurry F) ∧ ∀ᶠ x in 𝓝 x₀, ∀ t, K x t = c x * F (ρ x) t

theorem LocSm.continuous {K : X → E → ℂ} (h : LocSm K) : Continuous (Function.uncurry K) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h p.1
  have h1 : ContinuousAt (fun q : X × E => c q.1 * Function.uncurry F (ρ q.1, q.2)) p :=
    (hc.comp continuousAt_fst).mul
      (hF.continuous.continuousAt.comp ((hρ.comp continuousAt_fst).prodMk continuousAt_snd))
  refine h1.congr ?_
  filter_upwards [continuousAt_fst.eventually he] with q hq
  exact (hq q.2).symm

theorem LocSm.differentiable {K : X → E → ℂ} (h : LocSm K) (x : X) : Differentiable ℝ (K x) := by
  obtain ⟨G, _, _, ρ, c, F, -, -, hF, he⟩ := h x
  rw [funext he.self_of_nhds]
  exact ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).const_mul _

theorem LocSm.fderiv {K : X → E → ℂ} (h : LocSm K) (y : E) : LocSm fun x t => fderiv ℝ (K x) t y := by
  intro x₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h x₀
  refine ⟨G, inferInstance, inferInstance, ρ, c, fun g t => _root_.fderiv ℝ (F g) t y, hρ, hc, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (Function.uncurry fun (p : G × E) (t : E) => F p.1 t) :=
      hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    exact (ContDiff.fderiv (m := ∞) h1 contDiff_snd (by simp)).clm_apply contDiff_const
  · filter_upwards [he] with x hx t
    have hd : DifferentiableAt ℝ (F (ρ x)) t :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) t
    rw [funext hx, fderiv_const_mul hd]
    rfl

theorem LocSm.mul {K K' : X → E → ℂ} (h : LocSm K) (h' : LocSm K') : LocSm fun x t => K x t * K' x t := by
  intro x₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h x₀
  obtain ⟨G', _, _, ρ', c', F', hρ', hc', hF', he'⟩ := h' x₀
  refine ⟨G × G', inferInstance, inferInstance, fun x => (ρ x, ρ' x), fun x => c x * c' x,
    fun g t => F g.1 t * F' g.2 t, hρ.prodMk hρ', hc.mul hc', ?_, ?_⟩
  · exact (hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).mul
      (hF'.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  · filter_upwards [he, he'] with x hx hx' t
    rw [hx, hx']
    ring

theorem LocSm.comp {Y : Type} [TopologicalSpace Y] {K : X → E → ℂ} (h : LocSm K) {φ : Y → X} (hφ : Continuous φ) :
    LocSm fun y => K (φ y) := by
  intro y₀
  obtain ⟨G, _, _, ρ, c, F, hρ, hc, hF, he⟩ := h (φ y₀)
  exact ⟨G, inferInstance, inferInstance, ρ ∘ φ, c ∘ φ, F, hρ.comp hφ.continuousAt, hc.comp hφ.continuousAt, hF,
    hφ.continuousAt.eventually he⟩

theorem LocSm.continuous_fderiv [FiniteDimensional ℝ E] {K : X → E → ℂ} (h : LocSm K) :
    Continuous fun p : X × E => _root_.fderiv ℝ (K p.1) p.2 :=
  continuous_clm_apply.2 fun y => (h.fderiv y).continuous

end Gen

variable {D : D7}

section Int

variable {m n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasFDerivAt_integral (v : VolM D m n) {K : Mx D m n → E → ℂ} (h : LocSm K)
    (hp : ∀ γ ∈ ratMx D m n, ∀ x t, K (γ + x) t = K x t) (t₀ : E) :
    Integrable (fun x => fderiv ℝ (K x) t₀) (v.μ.restrict v.𝓕) ∧
      HasFDerivAt (fun t => ∫ x in v.𝓕, K x t ∂v.μ) (∫ x in v.𝓕, fderiv ℝ (K x) t₀ ∂v.μ) t₀ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hi := (ParCont.parCont D m n v E K h.continuous hp).1
  have hc : Continuous (Function.uncurry fun x t => ((‖fderiv ℝ (K x) t‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h.continuous_fderiv.norm
  obtain ⟨C, hC⟩ := (ParCont.parCont D m n v E _ hc fun γ hγ x t => by rw [funext (hp γ hγ x)]).2.2.1 t₀
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) := ⟨by
    rw [Measure.restrict_apply_univ, v.covol.2.2]; exact ENNReal.one_lt_top⟩
  have hm : AEStronglyMeasurable (fun x => fderiv ℝ (K x) t₀) (v.μ.restrict v.𝓕) :=
    (h.continuous_fderiv.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hC' : ∀ᶠ t in 𝓝 t₀, ∀ x, ‖fderiv ℝ (K x) t‖ ≤ C := hC.mono fun t ht x => by simpa using ht x
  refine ⟨Integrable.of_bound hm C (Filter.Eventually.of_forall hC'.self_of_nhds), ?_⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun t x => K x t) (F' := fun t x => fderiv ℝ (K x) t)
    (bound := fun _ => C) hC' (Filter.Eventually.of_forall fun t => (hi t).aestronglyMeasurable) (hi t₀) hm
    (Filter.Eventually.of_forall fun x t ht => ht x) (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => (h.differentiable x t).hasFDerivAt)

theorem contDiff_integral (v : VolM D m n) {K : Mx D m n → E → ℂ} (h : LocSm K)
    (hp : ∀ γ ∈ ratMx D m n, ∀ x t, K (γ + x) t = K x t) : ContDiff ℝ ∞ fun t => ∫ x in v.𝓕, K x t ∂v.μ := by
  rw [contDiff_infty]
  intro k
  induction k generalizing K with
  | zero => exact contDiff_zero.2 (ParCont.parCont D m n v E K h.continuous hp).2.1
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun t => (hasFDerivAt_integral v h hp t).2.differentiableAt, by simp, fun y => ?_⟩
    have e : (fun t => fderiv ℝ (fun t => ∫ x in v.𝓕, K x t ∂v.μ) t y) = fun t => ∫ x in v.𝓕, fderiv ℝ (K x) t y ∂v.μ := by
      funext t
      rw [(hasFDerivAt_integral v h hp t).2.fderiv, ContinuousLinearMap.integral_apply (hasFDerivAt_integral v h hp t).1]
    rw [e]
    exact ih (h.fderiv y) fun γ hγ x t => by rw [funext (hp γ hγ x)]

end Int


open GlobalTheory.DualPairCompare in
theorem locSm_theta {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (M : E →+ WO S T) (hM : Continuous M)
    (h0 : ∀ t, (M t).map (finPart D) = 0) : LocSm fun x t => f (x + M t) := by
  intro x₀
  have : IsTopologicalAddGroup (AE D) := inferInstance
  have : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  have : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨co, c1, c2, c3⟩ := exists_coMat D T.rank S.rank
  obtain ⟨U, hU, hl⟩ := hf.level
  have hs : ContDiff ℝ ∞ fun p => f (x₀ + realMat D T.rank S.rank p) := (smoothAlong_iff f).1 hf.smooth x₀
  let N := (co.comp M).toRealLinearMap (c1.comp hM)
  have hN : ∀ t, realMat D T.rank S.rank (N t) = M t := fun t => c3 _ (h0 t)
  have hd : Continuous fun x : WO S T => x - x₀ := continuous_id.sub continuous_const
  let a : WO S T → WO S T := fun x => (x - x₀) - realMat D T.rank S.rank (co (x - x₀))
  have ha : Continuous a := hd.sub ((continuous_realMat D _ _).comp (c1.comp hd))
  have hev : ∀ᶠ x in 𝓝 x₀, a x ∈ U := (hU.preimage ha).mem_nhds (show a x₀ ∈ U by simp [a])
  have key : ∀ x, a x ∈ U → ∀ p, f (x₀ + realMat D T.rank S.rank p + a x) =
      ψ (-symplOH S T x₀ (a x)) * f (x₀ + realMat D T.rank S.rank p) := by
    intro x hx p
    have h1 := congrFun (hl _ hx (c2 _)) (x₀ + realMat D T.rank S.rank p)
    have h2 : symplOH S T (realMat D T.rank S.rank p) (a x) = 0 :=
      GlobalTheory.FinTranslate.symplOH_real_fin (c2 _) (Matrix.ext fun i j => finPart_realPt D (p i j))
    rw [heisO, GlobalTheory.FinTranslate.symplOH_add_left, h2, add_zero] at h1
    rw [← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have dec : ∀ x t, x + M t = x₀ + realMat D T.rank S.rank (co (x - x₀) + N t) + a x := by
    intro x t
    rw [map_add (f := _), hN]
    simp only [a]
    abel
  have hF : ContDiff ℝ ∞ (Function.uncurry fun p t => f (x₀ + realMat D T.rank S.rank (p + N t))) :=
    hs.comp (contDiff_fst.add (N.contDiff.comp contDiff_snd))
  by_cases hz : ∀ p, f (x₀ + realMat D T.rank S.rank p) = 0
  · refine ⟨_, inferInstance, inferInstance, fun x => co (x - x₀), fun _ => 0, _, (c1.comp hd).continuousAt,
      continuousAt_const, hF, ?_⟩
    filter_upwards [hev] with x hx t
    rw [dec, key x hx, hz, mul_zero, mul_zero]
  · obtain ⟨p, hp⟩ := not_forall.1 hz
    refine ⟨_, inferInstance, inferInstance, fun x => co (x - x₀),
      fun x => f (x₀ + realMat D T.rank S.rank p + a x) / f (x₀ + realMat D T.rank S.rank p), _, (c1.comp hd).continuousAt,
      ((hf.cont.comp (continuous_const.add ha)).div_const _).continuousAt, hF, ?_⟩
    filter_upwards [hev] with x hx t
    rw [dec, key x hx, key x hx, mul_div_cancel_right₀ _ hp]

theorem extL_fin {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) (h : u.map (finPart D) = 0) :
    (ContrComb.extL (S := S) o u).map (finPart D) = 0 := by
  rw [ContrComb.extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  rw [Matrix.map_mul, h, Matrix.zero_mul]

theorem extR_fin {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) (h : u.map (finPart D) = 0) :
    (ContrComb.extR (S := S) o u).map (finPart D) = 0 := by
  rw [ContrComb.extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  rw [Matrix.map_mul, h, Matrix.mul_zero]

theorem integrand_periodic {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : WO B.V₀ S → ℂ} {f₂ : WO S B'.V₀ → ℂ} (h₁ : IsThetaFunO ψ B.V₀ S f₁)
    (h₂ : IsThetaFunO ψ S B'.V₀ f₂) (u : WO B.A S) (v : WO S B'.A) (γ : WO S B'.L) (hγ : γ ∈ ratMx D B'.L.rank S.rank)
    (a : WO S B'.L) :
    f₂ ((B'.o.resT S).symm (v, γ + a)) * f₁ ((B.o.resS S).symm (u, l.κ S (γ + a))) =
      f₂ ((B'.o.resT S).symm (v, a)) * f₁ ((B.o.resS S).symm (u, l.κ S a)) := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  obtain ⟨hadd, -, hrat, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)
  have hκ : symplOH B.L S (l.κ S γ) (l.κ S a) = -symplOH S B'.L γ a := by
    rw [symplOH, symplOH, hsym, Int.cast_one, one_mul, mul_neg]
  have r2 : (B'.o.resT S).symm (0, γ) ∈ ratMx D B'.V₀.rank S.rank := by
    refine (B'.o.mem_ratL_resT S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hγ⟩
  have r1 : (B.o.resS S).symm (0, l.κ S γ) ∈ ratMx D S.rank B.V₀.rank := by
    refine (B.o.mem_ratL_resS S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hrat γ hγ⟩
  obtain ⟨γ₂, hγ₂⟩ := r2
  obtain ⟨γ₁, hγ₁⟩ := r1
  have q2 := h₂.quasi γ₂ ((B'.o.resT S).symm (v, a))
  have q1 := h₁.quasi γ₁ ((B.o.resS S).symm (u, l.κ S a))
  have e2 : ratW B'.V₀ S γ₂ = (B'.o.resT S).symm (0, γ) := hγ₂
  have e1 : ratW S B.V₀ γ₁ = (B.o.resS S).symm (0, l.κ S γ) := hγ₁
  rw [e2, ← map_add (f := _), Prod.mk_add_mk, zero_add, B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ContrComb.symplOH_zero_left, zero_add] at q2
  rw [e1, ← map_add (f := _), Prod.mk_add_mk, zero_add, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ContrComb.symplOH_zero_left, zero_add, hκ, neg_neg] at q1
  rw [hadd, q2, q1]
  have e : ψ (-symplOH S B'.L γ a) * ψ (symplOH S B'.L γ a) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (f₂ ((B'.o.resT S).symm (v, a)) * f₁ ((B.o.resS S).symm (u, l.κ S a))) * e

theorem contr_isBiSmooth : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiSmooth (contr l S vL f₁ f₂) := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂ n L L' hL hL' h0 h0' u v
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  have hκ : Continuous (l.κ S) := (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.1
  have k₁ := (locSm_theta h₁ ((ContrComb.extL B.o).comp L) ((ContrComb.continuous_extL B.o).comp hL)
    fun t => extL_fin B.o _ (h0 t)).comp (φ := fun w : WO S B'.L => (B.o.resS S).symm (u, l.κ S w))
    ((B.o.continuous_resS_symm S).comp (continuous_const.prodMk hκ))
  have k₂ := (locSm_theta h₂ ((ContrComb.extR B'.o).comp L') ((ContrComb.continuous_extR B'.o).comp hL')
    fun t => extR_fin B'.o _ (h0' t)).comp (φ := fun w : WO S B'.L => (B'.o.resT S).symm (v, w))
    ((B'.o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id))
  have k : LocSm fun (w : WO S B'.L) (t : Fin n → ℝ) =>
      f₂ ((B'.o.resT S).symm (v + L' t, w)) * f₁ ((B.o.resS S).symm (u + L t, l.κ S w)) := by
    convert k₂.mul k₁ using 5 with w t w t
    · rw [AddMonoidHom.comp_apply, ContrComb.extR_apply, ← map_add (f := _), Prod.mk_add_mk, add_zero]
    · rw [AddMonoidHom.comp_apply, ContrComb.extL_apply, ← map_add (f := _), Prod.mk_add_mk, add_zero]
  exact contDiff_integral vL k fun γ hγ w t => integrand_periodic l S h₁ h₂ _ _ γ hγ w

end GlobalTheory.ContrSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSeminormSubTendstoZeroOfWordsUnif
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem eLpNorm_sub_tendsto_of_unif {X : Type} [MeasurableSpace X] (ν : Measure X) (hν : ν Set.univ = 1)
    (g : ℕ → X → ℂ) (f : X → ℂ) (hm : ∀ j, AEStronglyMeasurable (g j - f) ν)
    (h : TendstoUniformly g f Filter.atTop) :
    Filter.Tendsto (fun j => eLpNorm (g j - f) 2 ν) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  filter_upwards [Metric.tendstoUniformly_iff.1 h δ hδ0'] with j hj
  have hb : ∀ᵐ x ∂ν, ‖(g j - f) x‖ ≤ δ := Filter.Eventually.of_forall fun x => by
    have := (hj x).le
    rwa [dist_comm, dist_eq_norm] at this
  refine (eLpNorm_le_of_ae_bound (hm j) hb).trans ?_
  simpa [hν] using hδ.le

theorem wordAct_heisDer_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f - g) =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f - GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih, GlobalTheory.Size.wordAct_cons, GlobalTheory.Size.wordAct_cons, sub_eq_add_neg, sub_eq_add_neg,
      ← neg_one_smul ℂ, ← neg_one_smul ℂ (GlobalTheory.Size.heisDer ψ θ a _)]
    simp only [GlobalTheory.Size.heisDer]
    rw [GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l hf)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Size.theta_word hψ hθ l hg)), GlobalTheory.Size.dRho_smul]

theorem sobO_sub_tendsto_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (u : ℕ → WO S T → ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ j, IsThetaFunO ψ S T (u j)) → (∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) Filter.atTop) → ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ u f hf hu hl d
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have key : ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), Filter.Tendsto
      (fun j => GlobalTheory.Size.l2O μ 𝓕 (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j - f))) Filter.atTop (nhds 0) := by
    intro l
    simp only [wordAct_heisDer_sub hψ hθ (hu _) hf l, GlobalTheory.Size.l2O]
    exact eLpNorm_sub_tendsto_of_unif _ (by rw [Measure.restrict_apply_univ]; exact hμ.2.2) _ _
      (fun j => ((GlobalTheory.Size.theta_word hψ hθ l (hu j)).cont.sub
        (GlobalTheory.Size.theta_word hψ hθ l hf).cont).aestronglyMeasurable) (hl l)
  have := tendsto_finsetSum (Finset.range (d + 1)) fun k _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
      fun a _ => key (List.ofFn a)
  simp only [Finset.sum_const_zero] at this
  exact this

end GlobalTheory.ThetaDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMemSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaceChainStepDatum_mem_schwartzBruhat : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  first | exact @GlobalTheory.SBTwist.phiQ_mem_SB | exact GlobalTheory.SBTwist.phiQ_mem_SB | (intros; apply GlobalTheory.SBTwist.phiQ_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumSupportEqValuativeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaceChainStepDatumSupport_eq_valuative : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r = {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin r) : Set (GL (Fin r) (Fv D.host.F v))) ∧ (∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation (Fv D.host.F v) (x i j) < 1} ∧ {y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ 1} = {x | ∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1} := by
  first | exact @GlobalTheory.NrmVol.suppQ_eq_valuative | exact GlobalTheory.NrmVol.suppQ_eq_valuative | (intros; apply GlobalTheory.NrmVol.suppQ_eq_valuative <;> assumption)
end

