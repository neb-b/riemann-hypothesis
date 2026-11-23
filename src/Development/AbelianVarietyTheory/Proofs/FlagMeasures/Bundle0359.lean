module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentiableAtOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGap
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiStatOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesStepBoundOfCountingHypotheses
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem stepBoundAt_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ)
    (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  intro B Cg n₀ d p q b hn₀ hC
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  have hK := countHyp_isKTypeOf_lowKSub B Cg n₀ d p q b hn₀ hC
  obtain ⟨hD, -, -, -, -, -, -, -, hlam, -⟩ := hC
  refine GlobalTheory.StepGlob.stepBoundAt_of_local B b (fun v => ?_)
  obtain ⟨hpar, hds, -, -⟩ := hD v
  have hU : IsURepOn (UJset (B.I.ε v)) (B.σ v) := hds.2.2.1
  have h120v : 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hrk v]; exact h120
  have heig := _root_.GlobalTheory.DSId.LowCharGap.lowChar B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hpar hds h (hgap v) h120v
  exact ⟨hU, GlobalTheory.StepBoundOneRep.stepBound_of_eigen B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) b hU
    (hK v) heig (hlam v)⟩

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ESSingleCoeffCentral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabIdem

theorem ES_single_coeff_central : ∀ (D : D7) (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) →
    (∀ γ, (ES {t}).coeff γ = serCoef t γ) ∧ ∀ b, ES {t} * b = b * ES {t} := by
  intro D t _
  have e : (ES {t} : MonoidAlgebra ℂ (G0g D.nd)) = GlobalTheory.RowLev.zTup D t := GlobalTheory.RowLev.ES_singleton (D := D) t
  refine ⟨fun γ => ?_, fun b => ?_⟩
  · rw [e]; rfl
  · rw [e]; exact GlobalTheory.RowLev.zTup_comm t b

end GlobalTheory.LabIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapRankOneFactorisationTranslateSpan
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.BeRankOne

theorem exists_rankOne_of_hermitian_nonneg_operatorKernel {H Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (V : Set H) (B : H → H → (Wp →L[ℂ] Wp)) (l₀ : H → Wp)
    (hc : ∀ v ∈ V, ∀ ξ : Wp, ∃ c : ℂ, ∀ u ∈ V, B u v ξ = c • l₀ u)
    (hadj : ∀ u ∈ V, ∀ v ∈ V, ContinuousLinearMap.adjoint (B u v) = B v u)
    (hpos : ∀ v ∈ V, ∀ ξ : Wp, 0 ≤ (⟪ξ, B v v ξ⟫_ℂ).re ∧ (⟪ξ, B v v ξ⟫_ℂ).im = 0)
    (hne : ∃ u ∈ V, ∃ v ∈ V, ∃ ξ : Wp, B u v ξ ≠ 0) :
    ∃ t : ℂ, (∃ u ∈ V, t • l₀ u ≠ 0) ∧ ∀ u ∈ V, ∀ v ∈ V, B u v = rk1 (t • l₀ u) (t • l₀ v) := by
  classical
  obtain ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩ := hne
  choose! cf hcf using hc

  have hadj' : ∀ u ∈ V, ∀ v ∈ V, ∀ ξ η : Wp, ⟪η, B u v ξ⟫_ℂ = ⟪B v u η, ξ⟫_ℂ := by
    intro u hu v hv ξ η
    rw [← hadj u hu v hv, ContinuousLinearMap.adjoint_inner_left]

  obtain ⟨u₀, hu₀, hl₀⟩ : ∃ u₀ ∈ V, l₀ u₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne₁ (by rw [hcf v₁ hv₁ ξ₁ u₁ hu₁, h u₁ hu₁, smul_zero])
  have hnpos : 0 < ‖l₀ u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hl₀) 2
  have hN0 : ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hself : ⟪l₀ u₀, l₀ u₀⟫_ℂ = ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

  obtain ⟨lam, hcol⟩ : ∃ lam : ℂ, ∀ v ∈ V, ∀ ξ : Wp, cf v ξ = lam * ⟪l₀ v, ξ⟫_ℂ := by
    refine ⟨starRingEnd ℂ (cf u₀ (l₀ u₀)) / ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ), fun v hv ξ => ?_⟩
    have h := hadj' u₀ hu₀ v hv ξ (l₀ u₀)
    rw [hcf v hv ξ u₀ hu₀, hcf u₀ hu₀ (l₀ u₀) v hv, inner_smul_right, inner_smul_left, hself] at h
    rw [div_mul_eq_mul_div, eq_div_iff hN0, mul_comm (cf v ξ)]
    rw [mul_comm] at h
    exact h
  have hB : ∀ u ∈ V, ∀ v ∈ V, ∀ ξ : Wp, B u v ξ = (lam * ⟪l₀ v, ξ⟫_ℂ) • l₀ u := by
    intro u hu v hv ξ
    rw [hcf v hv ξ u hu, hcol v hv ξ]

  have hq := hpos u₀ hu₀ (l₀ u₀)
  have he : ⟪l₀ u₀, B u₀ u₀ (l₀ u₀)⟫_ℂ = lam * (((‖l₀ u₀‖ ^ 2) * (‖l₀ u₀‖ ^ 2) : ℝ) : ℂ) := by
    rw [hB u₀ hu₀ u₀ hu₀, inner_smul_right, hself]
    push_cast
    ring
  rw [he, Complex.re_mul_ofReal, Complex.im_mul_ofReal] at hq
  have hmm : 0 < ‖l₀ u₀‖ ^ 2 * ‖l₀ u₀‖ ^ 2 := mul_pos hnpos hnpos
  have him : lam.im = 0 := (mul_eq_zero.mp hq.2).resolve_right hmm.ne'
  have hre : 0 ≤ lam.re := by
    by_contra h
    push Not at h
    linarith [mul_neg_of_neg_of_pos h hmm, hq.1]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hne₁
    rw [hB u₁ hu₁ v₁ hv₁ ξ₁, h0, zero_mul, zero_smul]
  have hrepos : 0 < lam.re := by
    refine lt_of_le_of_ne hre (fun h => hlam0 ?_)
    exact Complex.ext (by simpa using h.symm) (by simpa using him)

  refine ⟨((Real.sqrt lam.re : ℝ) : ℂ), ⟨u₀, hu₀, smul_ne_zero ?_ hl₀⟩, fun u hu v hv => ?_⟩
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hrepos)
  have ht : starRingEnd ℂ ((Real.sqrt lam.re : ℝ) : ℂ) * ((Real.sqrt lam.re : ℝ) : ℂ) = lam := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hre]
    exact Complex.ext (by simp) (by simp [him])
  ext η
  rw [hB u hu v hv η, rankOneInnerOperator_apply, inner_smul_left, smul_smul]
  congr 1
  rw [mul_right_comm, ht]

theorem isBesselMapSm_smul {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ}
    {ψ : Mat k r → ℂ} {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (hl : IsBesselMapSm z ψ σ π l) (t : ℂ) : IsBesselMapSm z ψ σ π (fun u => t • l u) := by
  unfold Formalism.MainNotions.S.IsBesselMapSm Formalism.MainNotions.S.IsCWCont at *
  obtain ⟨hadd, hsm, heq, C, Ws, hWs, hb⟩ := hl
  refine ⟨?_, ?_, ?_, ‖t‖ * C, Ws, hWs, ?_⟩
  · intro v hv w hw
    show t • l (v + w) = t • l v + t • l w
    rw [hadd v hv w hw, smul_add]
  · intro c v hv
    show t • l (c • v) = c • (t • l v)
    rw [hsm c v hv, smul_comm]
  · intro h hh m hm v hv
    show t • l (σ (h * m) v) = ψ m • π h (t • l v)
    rw [heq h hh m hm v hv, map_smul, smul_comm]
  · intro v hv
    show ‖t • l v‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v hv) (norm_nonneg t)

end GlobalTheory.SgInf.BeRankOne

theorem GlobalTheory.SgInf.exists_isEll_DD : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → MultOne z (psiGen k r z c) σ π → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → NonVan z (psiGen k r z c) σ π w μG ν → ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hsm hM1 ν hq hNV
  obtain ⟨-, hU, -, -, hHG, -, -, hDec, -⟩ := id hStd
  obtain ⟨-, -, -, hHS, -⟩ := id hSide
  obtain ⟨hinv, -, hDV, -, hVsm⟩ := _root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hU
  have hsmDD : ∀ v ∈ DD σ w, v ∈ smoothVecs (k := k) (r := r) σ :=
    fun v hv => (hVsm hsm).1 v (hDV hv)
  have hae := GlobalTheory.SgInf.WUnfold.ae_mem_GG hHG hHS hq

  have hne : ∃ u ∈ (DD σ w : Set H), ∃ v ∈ (DD σ w : Set H), ∃ ξ : Wp,
      be (psiGen k r z c) π μS σ u v ξ ≠ 0 := by
    by_contra hz
    push Not at hz
    obtain ⟨W, hWG, hWν, hWeq, hWfin, hWne, hWfix⟩ := hNV
    have hW0 : ∀ y ∈ GG k r, W y = 0 := by
      intro y hy
      rw [← hWfix y hy,
        (_root_.GlobalTheory.SgInf.KernelRe.kernel_rconv k r σ w a μG d z c π μS hStd hSide ν hq W hWG hWν hWeq hWfin y hy).2,
        integral_eq_zero_of_ae, smul_zero]
      filter_upwards [hae] with g hg
      exact hz _ (mem_DD σ w hy) _ (mem_DD σ w hg) _
    apply hWne
    show (∫⁻ x, (‖W (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂ν) = 0
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae] with x hx
    simp [hW0 _ hx]
  obtain ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩ := hne
  obtain ⟨l₀, hB₀, hl₀⟩ := _root_.GlobalTheory.SgInf.exists_besselExt k r σ w a μG d z c π μS hStd hSide hsm v₁ hv₁ ξ₁

  have hcol : ∀ v ∈ (DD σ w : Set H), ∀ ξ : Wp, ∃ b : ℂ, ∀ u ∈ (DD σ w : Set H),
      be (psiGen k r z c) π μS σ u v ξ = b • l₀ u := by
    intro v hv ξ
    obtain ⟨l, hB, hl⟩ := _root_.GlobalTheory.SgInf.exists_besselExt k r σ w a μG d z c π μS hStd hSide hsm v hv ξ
    obtain ⟨b, hb | hb⟩ := hM1 l l₀ hB hB₀
    · exact ⟨b, fun u hu => by rw [← hl u hu]; exact hb u (hsmDD u hu)⟩
    · have hb0 : b ≠ 0 := by
        rintro rfl
        apply hne₁
        rw [← hl₀ u₁ hu₁, hb u₁ (hsmDD u₁ hu₁), zero_smul]
      refine ⟨b⁻¹, fun u hu => ?_⟩
      rw [← hl u hu, hb u (hsmDD u hu), inv_smul_smul₀ hb0]
  obtain ⟨t, ⟨u₂, hu₂, hne₂⟩, hrk⟩ := GlobalTheory.SgInf.BeRankOne.exists_rankOne_of_hermitian_nonneg_operatorKernel (DD σ w : Set H)
    (be (psiGen k r z c) π μS σ) l₀ hcol
    (fun u hu v hv =>
      (_root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hinv hDec u hu v hv).2.2.1)
    (fun v hv ξ => by
      have h := _root_.GlobalTheory.SgInf.normIdentity_besselCoef k r σ w a μG d z c π μS hStd hSide ν hq v hv v hv v hv ξ
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩)
    ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩
  refine ⟨fun u => t • l₀ u, ?_⟩
  unfold GlobalTheory.SgInf.IsEll
  exact ⟨GlobalTheory.SgInf.BeRankOne.isBesselMapSm_smul hB₀ t, ⟨u₂, hu₂, hne₂⟩, hrk⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory


open Classical in
theorem equivFinsuppOfBasisLeft_lTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] [DecidableEq ι]
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : M ⊗[K] N) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem AL_eq_zero_of_compAt (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L)
    (h : ∀ v, ReciprocityTheory.Aut.compAt L v a = 0) : a = 0 := by
  classical
  set K := maximalRealSubfield L
  let b := Module.finBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := AFplus L) b
  have hc : ∀ i, e a i = 0 := by
    intro i
    refine RestrictedProduct.ext _ _ (fun v => ?_)
    have h1 : ∀ x, ReciprocityTheory.Aut.compAt L v x =
        LinearMap.lTensor L (ReciprocityTheory.Aut.evalAt L v).toLinearMap x := by
      intro x
      simp only [ReciprocityTheory.Aut.compAt]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add (f := _)] at *; rw [hx, hy]
    have h2 := equivFinsuppOfBasisLeft_lTensor b (ReciprocityTheory.Aut.evalAt L v).toLinearMap a i
    rw [← h1 a, h v, map_zero, Finsupp.zero_apply] at h2
    exact h2.symm
  have : e a = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.IsotConjFix

open Formalism.IndefR.principalLevelFrame

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem rt_apply (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) (g : Formalism.AUTREP.GAf L n) :
    Formalism.L2.NG.rt L n h f g = f (g * h) := rfl

theorem range_equivariantMap_stable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (h : Formalism.AUTREP.GAf L n) (y : A) (hy : y ∈ LinearMap.range Φ) :
    ρ h y ∈ LinearMap.range Φ := by
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hy
  exact ⟨_, hΦ h f⟩

theorem zero_or_inj {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) : Φ = 0 ∨ Function.Injective Φ := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (LinearMap.ker Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [hΦ h f, hf, map_zero]
  rcases σ.irr K hle hst with hK | hK
  · right
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hf, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    exact (Submodule.mem_bot _).2 (Subtype.ext hm)
  · left
    apply LinearMap.ext
    intro f
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    simpa using hg

theorem inf_bot_or_le {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (W : Submodule ℂ A) (hW : ∀ h, ∀ y ∈ W, ρ h y ∈ W) :
    LinearMap.range Φ ⊓ W = ⊥ ∨ LinearMap.range Φ ≤ W := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (W.comap Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hf ⊢
    rw [hΦ h f]
    exact hW h _ hf
  rcases σ.irr K hle hst with hK | hK
  · left
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf, LinearMap.mem_range] at hy
    obtain ⟨⟨f, rfl⟩, hy⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hy, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    have e : f = 0 := Subtype.ext hm
    rw [e, map_zero]
    exact Submodule.zero_mem _
  · right
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨f, rfl⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    exact hg

def Indep {J : Type} (R : J → Submodule ℂ A) (t : Finset J) : Prop :=
  ∀ v : J → A, (∀ j ∈ t, v j ∈ R j) → ∑ j ∈ t, v j = 0 → ∀ j ∈ t, v j = 0

theorem select {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {J : Type} [DecidableEq J] (R : J → Submodule ℂ A)
    (hst : ∀ j h, ∀ y ∈ R j, ρ h y ∈ R j)
    (hirr : ∀ j (W : Submodule ℂ A), (∀ h, ∀ y ∈ W, ρ h y ∈ W) → R j ⊓ W = ⊥ ∨ R j ≤ W) (s : Finset J) :
    ∃ t ⊆ s, Indep R t ∧ ⨆ j ∈ t, R j = ⨆ j ∈ s, R j := by
  have stab : ∀ t : Finset J, ∀ h, ∀ y ∈ ⨆ j ∈ t, R j, ρ h y ∈ ⨆ j ∈ t, R j := by
    intro t h y hy
    have hle : (⨆ j ∈ t, R j) ≤ (⨆ j ∈ t, R j).comap (ρ h) := by
      refine iSup₂_le fun j hj => ?_
      intro z hz
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj) (hst j h z hz)
    exact hle hy
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, subset_rfl, fun v _ _ j hj => by simp at hj, rfl⟩
  | insert k s hk ih =>
    obtain ⟨t, hts, hind, heq⟩ := ih
    rcases hirr k (⨆ j ∈ t, R j) (stab t) with hd | hle
    · have hkt : k ∉ t := fun h => hk (hts h)
      refine ⟨insert k t, Finset.insert_subset_insert k hts, ?_, ?_⟩
      · intro v hv hsum j hj
        rw [Finset.sum_insert hkt] at hsum
        have hvk : v k = 0 := by
          have h1 : v k ∈ R k ⊓ ⨆ j ∈ t, R j := by
            refine Submodule.mem_inf.2 ⟨hv k (Finset.mem_insert_self k t), ?_⟩
            have e : v k = -∑ j ∈ t, v j := eq_neg_of_add_eq_zero_left hsum
            rw [e]
            refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
            exact le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj (hv j (Finset.mem_insert_of_mem hj))
          rw [hd] at h1
          exact (Submodule.mem_bot _).1 h1
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hvk
        · rw [hvk, zero_add] at hsum
          exact hind v (fun i hi => hv i (Finset.mem_insert_of_mem hi)) hsum j hj
      · rw [Finset.iSup_insert, Finset.iSup_insert, heq]
    · refine ⟨t, hts.trans (Finset.subset_insert k s), hind, ?_⟩
      rw [Finset.iSup_insert, ← heq, sup_eq_right.2 hle]

theorem fix_sum_of_mem {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n}
    (P : (σ.S →ₗ[ℂ] A) → Prop) (U : Set (Formalism.AUTREP.GAf L n)) {ι : Type} [Fintype ι] (b : ι → ℂ)
    (lf : ι → Formalism.AUTREP.GAf L n)
    (H : ∀ ψ ∈ σ.S, (∀ κ ∈ U, Formalism.L2.NG.rt L n κ ψ = ψ) → ∑ i, b i • Formalism.L2.NG.rt L n (lf i) ψ = ψ)
    (x : A) (hx : x ∈ ⨆ (Φ : σ.S →ₗ[ℂ] A) (_ : IsEqvA ρ σ Φ ∧ P Φ), LinearMap.range Φ)
    (hU : ∀ κ ∈ U, ρ κ x = x) : ∑ i, b i • ρ (lf i) x = x := by
  classical
  let J := {Φ : σ.S →ₗ[ℂ] A // IsEqvA ρ σ Φ ∧ P Φ}
  let R : J → Submodule ℂ A := fun j => LinearMap.range j.1
  rw [iSup_subtype'] at hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  obtain ⟨t, -, hind, heq⟩ := select (ρ := ρ) R (fun j h y hy => range_equivariantMap_stable j.2.1 h y hy)
    (fun j W hW => inf_bot_or_le j.2.1 W hW) s
  rw [← heq] at hs
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hs
  have hψ : ∀ j : J, ∃ ψ : σ.S, j.1 ψ = μ j := fun j => LinearMap.mem_range.1 (μ j).2
  choose ψ hψ using hψ
  have hx' : x = ∑ j ∈ t, j.1 (ψ j) := by
    rw [← hμ]
    exact Finset.sum_congr rfl fun j _ => (hψ j).symm
  have hfix : ∀ j ∈ t, ∀ κ ∈ U, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = j.1 (ψ j) := by
    intro j hj κ hκ
    have h0 := hind (fun j => j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ - j.1 (ψ j))
      (fun j _ => Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)) ?_ j hj
    · exact sub_eq_zero.1 h0
    · rw [Finset.sum_sub_distrib]
      have e : ∑ j ∈ t, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = ρ κ x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hx', map_sum]
        exact Finset.sum_congr rfl fun j _ => j.2.1 κ (ψ j)
      rw [e, hU κ hκ, ← hx', sub_self]
  have hterm : ∀ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) = j.1 (ψ j) := by
    intro j hj
    rcases zero_or_inj j.2.1 with h0 | hinj
    · simp [h0]
    · have hψfix : ∀ κ ∈ U, Formalism.L2.NG.rt L n κ ((ψ j : σ.S) : Formalism.AUTREP.GAf L n → ℂ) = ψ j :=
        fun κ hκ => congrArg Subtype.val (hinj (hfix j hj κ hκ))
      have hH := H _ (ψ j).2 hψfix
      have e : ∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S) = ψ j := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simpa using hH
      calc ∑ i, b i • ρ (lf i) (j.1 (ψ j))
          = j.1 (∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S)) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul, j.2.1 (lf i) (ψ j)]
        _ = j.1 (ψ j) := by rw [e]
  calc ∑ i, b i • ρ (lf i) x = ∑ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) := by
        rw [hx']
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, Finset.smul_sum]
        exact Finset.sum_comm
    _ = x := by
        rw [Finset.sum_congr rfl hterm, ← hx']

end Gen

theorem isotIn_conjT_fix_sum : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : Formalism.L2.NG.FinTyp D.host.E n) (U : Set (GAf D.host.E n)) (ι : Type) [Finite ι] (a : ι → ℂ) (lf : ι → GAf D.host.E n), (∀ φ ∈ π.S, (∀ κ ∈ U, Formalism.L2.NG.rt D.host.E n κ φ = φ) → ∑ᶠ i, a i • Formalism.L2.NG.rt D.host.E n (lf i) φ = φ) → ∀ S ∈ isotIn ρ C (FinTyp.conjT π), (∀ κ ∈ U, ρ κ S = S) → ∑ᶠ i, star (a i) • ρ (lf i) S = S := by
  intro D n A _ _ ρ C π U ι _ a lf hyp S hS hU
  haveI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  refine fix_sum_of_mem (σ := FinTyp.conjT π) (fun Φ => LinearMap.range Φ ≤ C) U (fun i => star (a i)) lf ?_ S hS hU
  intro ψ hψ hfix
  have hφ : (fun g => star (ψ g)) ∈ π.S := hψ
  have h1 := hyp _ hφ (fun κ hκ => by rw [← conj_rt, hfix κ hκ])
  rw [finsum_eq_sum_of_fintype] at h1
  funext g
  have h2 := congrArg star (congrFun h1 g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', star_star, rt_apply] at h2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rt_apply]
  exact h2

end GlobalTheory.IsotConjFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
section
namespace GlobalTheory.Mass

theorem siegelMassRatio_holds : Formalism.HermitianLatticesTheory.SiegelMassRatio :=
  Formalism.HermitianLattices.Ext.L3.siegelMassRatio_of_LI binary_hermitian_represents Formalism.HermitianLattices.Ext.L3.liStat

end GlobalTheory.Mass
end

