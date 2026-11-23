module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0102
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterIntegralOrthogonality
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Orth

variable {D : D7}

theorem trA_incA_eq (e : D.host.E) :
    trA (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  have h : LinearMap.mulLeft (AF D.host.F) (incA D e) =
      LinearMap.baseChange (AF D.host.F) (LinearMap.mulLeft D.host.F e) := by
    ext b
    simp [TensorProduct.AlgebraTensorModule.curry_apply, incA, inclR, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
  simp only [trA, Algebra.trace_apply]
  change LinearMap.trace _ _ (LinearMap.mulLeft (AF D.host.F) (incA D e)) =
    algebraMap _ _ (LinearMap.trace _ _ (LinearMap.mulLeft D.host.F e))
  rw [h, LinearMap.trace_baseChange]

theorem trA_smul_half (x : AF D.host.F) :
    trA (x • half D) = x := by
  have hE := D.host.toHostAx.der.finrank_E
  have hF := D.host.toHostAx.der.finrank_F
  have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
  have htow := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF] at hpos htow
    rw [hE] at htow
    have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by
      rw [htow]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  have hhalf : trA (half D) = 1 := by
    rw [half, trA_incA_eq]
    have : (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2) := by
      rw [map_div₀, map_one, map_ofNat]
    rw [this, Algebra.trace_algebraMap, h2]
    norm_num
  have hlin : trA (x • half D) = x * trA (half D) := by
    simp only [trA, map_smul, smul_eq_mul]
  rw [hlin, hhalf, mul_one]

theorem inner_rat_eq (V : HSp D) {s : ℕ} (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y : Mx D V.rank s) :
    GlobalTheory.StdUnn.inner V (rat q) y = rat (qᴴ * V.gram) ⬝ y := by
  simp only [GlobalTheory.StdUnn.inner]
  rw [← rat_conjTranspose, gA, ← Matrix.mul_assoc, ← rat_mul]

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {s : ℕ} (x y u : Mx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y + u)))) =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x y))) * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x u))) := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.trace_add, trA, map_add (f := _), AddChar.map_add_eq_mul]

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) {γ : Mx D V.rank s} (hγ : γ ∈ ratMx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) γ))) = 1 := by
  obtain ⟨g, rfl⟩ := mem_ratMx.mp hγ
  have htr : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E), Matrix.trace (rat M) = incA D (Matrix.trace M) := by
    intro n M
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rat, Matrix.trace, map_sum]
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) * rat g))) = 1
  rw [← rat_mul, htr, trA_incA_eq]
  exact hψ.2.2.1 _

theorem exists_chi_ne_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    {q : Matrix (Fin V.rank) (Fin s) D.host.E} (hq : q ≠ 0) :
    ∃ u : Mx D V.rank s, ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) u))) ≠ 1 := by
  obtain ⟨x, hx⟩ := hψ.2.2.2
  have hM : qᴴ * V.gram ≠ 0 := by
    intro h
    apply hq
    have h1 : qᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right V.gram qᴴ (gram_isUnit_det V), h, Matrix.zero_mul]
    simpa using congrArg Matrix.conjTranspose h1
  obtain ⟨i, j, hij⟩ : ∃ i j, (qᴴ * V.gram) i j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hM (Matrix.ext hne)
  have key : ∀ (A : Mx D s V.rank) (c : AE D), Matrix.trace (A * Matrix.single j i c) = A i j * c := by
    intro A c
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  refine ⟨Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D)), ?_⟩
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) *
      Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D))))) ≠ 1
  rw [key, show rat (qᴴ * V.gram) i j = incA D ((qᴴ * V.gram) i j) from rfl, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ hij, map_one, one_mul, trA_smul_half]
  exact hx

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  intro D ψ hψ V s μs 𝓕s hcov q
  constructor
  · rintro rfl
    have h0 : ∀ y : Mx D V.rank s, ψ (trA (Matrix.trace (inner V (rat (0 : Matrix (Fin V.rank) (Fin s) D.host.E)) y))) = 1 := by
      intro y
      simp [GlobalTheory.StdUnn.inner, rat_zero, adj_zero, trA]
    simp_rw [h0]
    rw [MeasureTheory.setIntegral_const]
    simp [Measure.real, hcov.2.2]
  · intro hq
    obtain ⟨u, hu⟩ := exists_chi_ne_one hψ V hq
    set φ : Mx D V.rank s → ℂ := fun y => ψ (trA (Matrix.trace (inner V (rat q) y))) with hφ
    have hper : ∀ γ ∈ ratMx D V.rank s, ∀ a, φ (γ + a) = φ a := by
      intro γ hγ a
      simp only [hφ]
      rw [chi_add, chi_rat hψ V q hγ, one_mul]
    have h1 := covolOne_integral_add hcov φ hper u
    have h2 : ∀ a, φ (a + u) = φ u * φ a := by
      intro a
      simp only [hφ]
      rw [chi_add, mul_comm]
    simp only [h2] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have h3 : (φ u - 1) * ∫ y in 𝓕s, φ y ∂μs = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hu
    · exact h

end GlobalTheory.CompanionTheory.EisUnfold.Orth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSupportSplitCentreFactor
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

namespace GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre

section Abstract

variable {X G : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fibreIntegral (F : X × ℝ → ℂ) (hF : Continuous F) (hs : HasCompactSupport F) (r : ℂ) :
    ∃ f₁ : CompactlySupportedContinuousMap X ℂ, ∀ x, f₁ x = r * ∫ t, F (x, t) := by
  have hK : IsCompact (Prod.snd '' tsupport F) := hs.isCompact.image continuous_snd
  have hK₁ : IsCompact (Prod.fst '' tsupport F) := hs.isCompact.image continuous_fst
  have hcont : Continuous fun x : X => ∫ t, F (x, t) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support (f := fun x t => F (x, t)) hK ?_ ?_
    · exact hF.continuousOn
    · intro p x _ hx
      by_contra h
      exact hx ⟨(p, x), subset_tsupport _ h, rfl⟩
  refine ⟨⟨⟨fun x => r * ∫ t, F (x, t), continuous_const.mul hcont⟩, ?_⟩, fun x => rfl⟩
  refine HasCompactSupport.intro hK₁ fun x hx => ?_
  have h0 : ∀ t, F (x, t) = 0 := by
    intro t
    by_contra h
    exact hx ⟨(x, t), subset_tsupport _ h, rfl⟩
  simp [h0]

theorem integral_eq_of_map (e : X × ℝ ≃ₜ G) (ν : Measure X) [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (μ : Measure G) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map e (ν.prod volume) = c • μ) (f : G → ℂ) (hf : Continuous f) (hs : HasCompactSupport f)
    (f₁ : CompactlySupportedContinuousMap X ℂ)
    (hf₁ : ∀ x, f₁ x = (c.toReal : ℂ)⁻¹ * ∫ t, f (e (x, t)))
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : G → K) (w : X → K)
    (hW : Continuous W) (hw : ∀ x t, W (e (x, t)) = w x) :
    ∫ g, f g • W g ∂μ = ∫ x, f₁ x • w x ∂ν := by
  have hr : c.toReal ≠ 0 := (ENNReal.toReal_pos hc0 hct).ne'
  have hrC : (c.toReal : ℂ) ≠ 0 := by exact_mod_cast hr
  have hFc : Continuous fun p : X × ℝ => f (e p) := hf.comp e.continuous
  have hFs : HasCompactSupport fun p : X × ℝ => f (e p) := hs.comp_homeomorph e
  have hint : Integrable (fun p : X × ℝ => f (e p) • W (e p)) (ν.prod volume) :=
    (hFc.smul (hW.comp e.continuous)).integrable_of_hasCompactSupport hFs.smul_right
  have h1 : c.toReal • ∫ g, f g • W g ∂μ = ∫ p, f (e p) • W (e p) ∂(ν.prod volume) := by
    rw [← integral_smul_measure, ← hmap]
    exact e.measurableEmbedding.integral_map _
  have h2 : ∫ p, f (e p) • W (e p) ∂(ν.prod volume) = ∫ x, (∫ t, f (e (x, t))) • w x ∂ν := by
    rw [integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hw]
    exact integral_smul_const _ _
  have h3 : ∫ x, f₁ x • w x ∂ν = (c.toReal : ℂ)⁻¹ • ∫ x, (∫ t, f (e (x, t))) • w x ∂ν := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf₁, mul_smul]
  rw [h3, ← h2, ← h1, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ hrC, one_smul]

end Abstract

theorem exists_normOne_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ → Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (normOneGL (K := E) (n := a)) ℂ, ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W → (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν := by
  intro E _ _ _ a ha μ _ ν _ c hc0 hct hmap f hf hs
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have hfun : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e := by
    funext p
    exact (he p.1 p.2).symm
  rw [hfun] at hmap
  obtain ⟨f₁, hf₁⟩ := exists_fibreIntegral (fun p : normOneGL (K := E) (n := a) × ℝ => f (e p))
    (hf.comp e.continuous) (hs.comp_homeomorph e) ((c.toReal : ℂ)⁻¹)
  refine ⟨f₁, fun K _ _ _ W hW hinv => ?_⟩
  set_option synthInstance.maxHeartbeats 200000 in
    exact integral_eq_of_map e ν μ c hc0 hct hmap f hf hs f₁ hf₁ W (fun x => W (x : GA E a)) hW
      (fun x t => by rw [he, hinv])

end GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinity
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_moved (h : IsCMExt F E σ) : ∃ θ : E, σ θ ≠ θ := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc' := h.2.1
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hc y] at this
  simpa using this.symm

theorem im_ne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) (τ : E →+* ℂ) : (τ θ).im ≠ 0 := by
  intro h0
  apply hθ
  apply τ.injective
  rw [h.2.2.2]
  exact Complex.conj_eq_iff_im.2 h0

theorem linInd_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) :
    LinearIndependent F ![(1 : E), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : s • (1 : E) + t • σ θ = 0 := by
    have := congrArg σ hst
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgHom.commutes, map_one, map_zero] at this ⊢
    exact this
  have h2 : t • (σ θ - θ) = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact add_left_cancel (h1.trans hst.symm)
  have ht : t = 0 := by
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3) hθ
  subst ht
  refine ⟨?_, rfl⟩
  simpa using hst

def basisOne (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : Module.Basis (Fin 2) F E :=
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  basisOfLinearIndependentOfCardEqFinrank (linInd_one h hθ) (by rw [h.2.2.1]; simp)

theorem basisOne_zero (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 0 = 1 := by
  simp [basisOne]

theorem basisOne_one (h : IsCMExt F E σ) {θ : E} (hθ : σ θ ≠ θ) : basisOne h hθ 1 = θ := by
  simp [basisOne]

end Field

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordHomeo (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

def planeHomeo {W : Type} (t : W → ℂ) (ht : ∀ w, (t w).im ≠ 0) : (Fin 2 → W → ℝ) ≃ₜ (W → ℂ) where
  toFun f w := (f 0 w : ℂ) + (f 1 w : ℂ) * t w
  invFun g := ![fun w => (g w).re - (g w).im / (t w).im * (t w).re, fun w => (g w).im / (t w).im]
  left_inv f := by
    funext k w
    have := ht w
    fin_cases k
    · simp
      field_simp
      ring
    · simp
      field_simp
  right_inv g := by
    funext w
    have := ht w
    apply Complex.ext
    · simp
    · simp
      field_simp
  continuous_toFun := by
    refine continuous_pi fun w => ?_
    have h0 : Continuous fun f : Fin 2 → W → ℝ => f 0 w := (continuous_apply w).comp (continuous_apply 0)
    have h1 : Continuous fun f : Fin 2 → W → ℝ => f 1 w := (continuous_apply w).comp (continuous_apply 1)
    exact (Complex.continuous_ofReal.comp h0).add ((Complex.continuous_ofReal.comp h1).mul continuous_const)
  continuous_invFun := by
    refine continuous_pi fun k => continuous_pi fun w => ?_
    have hr : Continuous fun g : W → ℂ => (g w).re := Complex.continuous_re.comp (continuous_apply w)
    have hi : Continuous fun g : W → ℂ => (g w).im := Complex.continuous_im.comp (continuous_apply w)
    fin_cases k
    · exact hr.sub ((hi.div_const _).mul continuous_const)
    · exact hi.div_const _

end Top

section Map

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_hom (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (hc : ∀ x w, ((e (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = τ w (algebraMap F E x)) :
    ∃ Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ),
      ∀ a x w, Θ (a ⊗ₜ[F] x) w = (e a w : ℂ) * τ w x := by
  letI : Algebra F (InfinitePlace F → ℂ) :=
    (Pi.ringHom fun w => (τ w).comp (algebraMap F E)).toAlgebra
  let fA : Ainf F →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom fun w =>
        Complex.ofRealHom.comp ((Pi.evalRingHom (fun _ => ℝ) w).comp (e : Ainf F →+* (InfinitePlace F → ℝ)))
      commutes' := fun x => funext fun w => hc x w }
  let fE : E →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := Pi.ringHom τ
      commutes' := fun _ => rfl }
  exact ⟨(Algebra.TensorProduct.productMap fA fE).toRingHom, fun a x w => by
    simp [Algebra.TensorProduct.productMap_apply_tmul, fA, fE]
    rfl⟩

end Map

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM in
theorem exists_isCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)),
  (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∃ (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)),
    IsCoord σ e τ Θ := by
  intro F E _ _ _ _ _ σ h ρ e hρ he hx
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨θ, hθ⟩ := exists_moved h
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph
  let b := basisOne h hθ
  let H : (Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → ℂ) :=
    (coordHomeo (Ainf F) b).trans ((Homeomorph.piCongrRight fun _ => eH).trans
      (planeHomeo (fun w => τ w θ) (fun w => im_ne_zero h hθ (τ w))))
  have hH : ∀ y, H y = Θ y := by
    intro y
    have hy : y = (Algebra.TensorProduct.basis (Ainf F) b).repr y 0 ⊗ₜ[F] (1 : E) +
        (Algebra.TensorProduct.basis (Ainf F) b).repr y 1 ⊗ₜ[F] θ := by
      conv_lhs => rw [← (Algebra.TensorProduct.basis (Ainf F) b).sum_repr y]
      rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
        basisOne_zero, basisOne_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp
    funext w
    conv_rhs => rw [hy, map_add (f := _), Pi.add_apply, hΘ, hΘ, map_one, mul_one]
    rfl
  have hbij : Function.Bijective Θ := by
    have : (Θ : Ainf F ⊗[F] E → _) = H := funext fun y => (hH y).symm
    rw [this]
    exact H.bijective
  refine ⟨τ, RingEquiv.ofBijective Θ hbij, ?_, ?_, ?_, ?_⟩
  · have : ((RingEquiv.ofBijective Θ hbij : Ainf F ⊗[F] E ≃+* _) : Ainf F ⊗[F] E → _) = H :=
      funext fun y => (hH y).symm
    rw [this]
    exact H.isHomeomorph
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (Ainf F) σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := by simp [sigR]
      rw [this, hΘ, hΘ, h.2.2.2, map_mul, Complex.conj_ofReal]
      rfl
    | add y y' hy hy' => simp only [map_add (f := _), Pi.add_apply, hy, hy']
  · intro x w
    simp only [RingEquiv.ofBijective_apply]
    rw [hΘ, map_one]
    simp
  · intro z w
    simp only [RingEquiv.ofBijective_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have h1 : τ w x + conj (τ w x) = ((ρ w (Algebra.trace F E x) : ℝ) : ℂ) := by
        rw [hρ, ← hτ, ← GlobalTheory.GaussMean.OneVec.add_sigma h, map_add (f := _), h.2.2.2]
        rfl
      rw [GlobalTheory.GaussMean.OneVec.trace_tmul, map_mul, Pi.mul_apply, hx, hΘ, map_mul, Complex.conj_ofReal,
        Complex.ofReal_mul, ← h1]
      ring
    | add y y' hy hy' =>
      simp only [map_add (f := _), Pi.add_apply, Complex.ofReal_add, hy, hy']
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegralStatement
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_integral : PositivityTheory.PfSWUS.SchInf.DensInt := by
  first | exact @GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | exact GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | (intros; apply GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergentStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_convergent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧ ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.godement_sum | exact GlobalTheory.CompanionTheory.GodementH.godement_sum | (intros; apply GlobalTheory.CompanionTheory.GodementH.godement_sum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaarStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_vector_measure_isAddHaar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ), (nuInf E k).IsAddHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | exact GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | (intros; apply GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure <;> assumption)
end

