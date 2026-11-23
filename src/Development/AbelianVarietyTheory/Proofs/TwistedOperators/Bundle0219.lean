module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightRealFrameElementLeHsPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameHeight

def EntryBd {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : ℝ, ∀ g i j, ‖f g i j‖ ≤ c * (1 + Formalism.REAL.hs g)

variable {n : ℕ} {f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}

theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs; positivity

theorem entryBd_id : EntryBd (fun g : Matrix (Fin n) (Fin n) ℂ => g) := by
  refine ⟨1, fun g i j => ?_⟩
  have h1 : ‖g i j‖ ^ 2 ≤ Formalism.REAL.hs g := by
    unfold Formalism.REAL.hs
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖g i j‖ - 1), hs_nonneg g]

theorem EntryBd.conjTranspose (h : EntryBd f) : EntryBd fun g => (f g)ᴴ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g i j => by simpa [conjTranspose_apply] using hc g j i⟩

theorem EntryBd.const_mul (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => P * f g := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(∑ i, ∑ k, ‖P i k‖) * |c|, fun g i j => ?_⟩
  have h0 := hs_nonneg g
  show ‖(P * f g) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ k, ‖P i k‖ * (|c| * (1 + Formalism.REAL.hs g)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hc g k j).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith))) (norm_nonneg _)
    _ = (∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖)
          (fun _ _ => by positivity) (Finset.mem_univ i)) (by positivity)
    _ = _ := by ring

theorem EntryBd.mul_const (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => f g * P := by
  simpa using (h.conjTranspose.const_mul Pᴴ).conjTranspose

theorem frame_mem {D : D7} {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.MainNotions.S.UJset (A.ε τ)) :
    (A.fr τ)⁻¹ * k * A.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (A.ε τ) * k = Formalism.REAL.Jm (A.ε τ) := hk
  have h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← A.fr_gram τ]
  calc _ = (A.fr τ)ᴴ * (kᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * k) *
        A.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

theorem height_elt_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau), ∃ (C : ℝ) (m : ℕ), ∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), GlobalTheory.Grow.height V (A.elt θ τ g) ≤ C * (1 + Formalism.REAL.hs g) ^ m := by
  intro D θ hθ V A τ
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow V hθ
  have b1 := (entryBd_id.const_mul (A.fr τ)⁻¹).mul_const (A.fr τ)
  obtain ⟨c2, h2⟩ := (b1.conjTranspose.const_mul (gramAt D V τ)⁻¹).mul_const (gramAt D V τ)
  obtain ⟨c1, h1⟩ := b1
  refine ⟨(∑ _ρ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (|c1| + |c2| + 2)) ^ d, d, fun g hg => ?_⟩
  have hu := frame_mem A τ hg
  have s1 := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
  have s2 := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hu s1
  have h0 := hs_nonneg g
  refine (hd _ s1.1).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by unfold normInf; positivity) ?_ d
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have a1 := mul_nonneg (abs_nonneg c1) h0
  have a2 := mul_nonneg (abs_nonneg c2) h0
  by_cases e : ρ = τ
  · subst e
    rw [s1.2.1, s2.2.1]
    have e1 := (h1 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith))
    have e2 := (h2 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c2) (by linarith))
    nlinarith
  · rw [s1.2.2 ρ e, s2.2.2 ρ e]
    have : ‖(1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    nlinarith [abs_nonneg c1, abs_nonneg c2]

end GlobalTheory.FrameHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasure
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TorCentTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}
  {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k]


omit [FiniteDimensional F E] [TopologicalSpace k] [IsTopologicalRing k] in
theorem isScalarTower_base : IsScalarTower k (k ⊗[F] E) (k ⊗[F] Fld P) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change c ⊗ₜ[F] (1 : Fld P) = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) (c ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

theorem continuous_mulMat (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) : Continuous (mulMat φ) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : ContinuousAdd (k ⊗[F] E) := IsModuleTopology.toContinuousAdd k _
  haveI := isScalarTower_base (k := k) (P := P)
  refine continuous_matrix fun i j => ?_
  have e : ∀ l, mulMat φ l i j = φ (l * φ.symm (Pi.single j 1)) i := fun l => by
    rw [← mulMat_mulVec, φ.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [e]
  exact IsModuleTopology.continuous_of_linearMap (((LinearMap.proj i).comp (φ.toLinearMap.comp
    (LinearMap.mulRight (k ⊗[F] E) (φ.symm (Pi.single j 1))))).restrictScalars k)

theorem torUnit_val (t : Tor P k) : (torUnit t).1 = (matHom k (star' P) (one₁ P) t).1 0 0 :=
  Matrix.det_fin_one _

theorem continuous_torUnit : Continuous fun t : Tor P k => (torUnit t).1 := by
  simp only [torUnit_val]
  exact (Units.continuous_val.comp (isEmbedding_matHom k (star' P) (one₁ P)).continuous).matrix_elem 0 0

theorem matHom_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (matHom k σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl

theorem torUnit_eq {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (torUnit t).1 = φ.symm ((matHom k σ J (torEmb h t)).1 *ᵥ φ 1) := by
  rw [matHom_torEmb, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_one]

theorem continuous_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) : Continuous (torEmb h) := by
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  refine (isEmbedding_matHom k σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun t => (matHom k σ J (torEmb h t)).1
    simp only [matHom_torEmb]
    exact (continuous_mulMat φ).comp continuous_torUnit
  · change Continuous fun t => (matHom k σ J (torEmb h t))⁻¹.1
    simp only [← map_inv, matHom_torEmb]
    exact (continuous_mulMat φ).comp (continuous_torUnit.comp continuous_inv)

theorem continuous_back (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) :
    Continuous fun g : HA k σ J => φ.symm ((matHom k σ J g).1 *ᵥ φ 1) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  haveI := isScalarTower_base (k := k) (P := P)
  haveI : ContinuousAdd (k ⊗[F] Fld P) := IsModuleTopology.toContinuousAdd k _
  have h1 : Continuous (φ.symm.toLinearMap.restrictScalars k) := IsModuleTopology.continuous_of_linearMap _
  refine h1.comp (Continuous.matrix_mulVec ?_ continuous_const)
  exact Units.continuous_val.comp (isEmbedding_matHom k σ J).continuous

theorem torEquiv_cent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ e : Tor P k ≃ₜ* cent (gam h), (∀ t, (e t).1 = torEmb h t) ∧ ∀ dt : Measure (Tor P k), centMeas h dt = dt.map e := by
  intro F E _ _ _ _ _ σ hCM r n P J hJ k _ _ _ _ _ x φ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  obtain ⟨-, -, hinj, hrange⟩ := _root_.GlobalTheory.TrEll.gam_charpoly_regular_cent F E σ hCM r n P J hJ k x φ h
  let e0 : Tor P k ≃* cent (gam h) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  have he : ∀ t, (e0 t).1 = torEmb h t := fun t => rfl
  have hs : ∀ s, torEmb h (e0.symm s) = s.1 := fun s => by rw [← he, e0.apply_symm_apply]
  have hback : ∀ s, (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0 = φ.symm ((matHom k σ J s.1).1 *ᵥ φ 1) :=
    fun s => by rw [← torUnit_val, GlobalTheory.TorCentTop.torUnit_eq h, hs]
  let e : Tor P k ≃ₜ* cent (gam h) :=
    { e0 with
      continuous_toFun := continuous_induced_rng.2 (GlobalTheory.TorCentTop.continuous_torEmb h)
      continuous_invFun := by
        refine (isEmbedding_matHom k (star' P) (one₁ P)).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0
          simp only [hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp continuous_subtype_val
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s))⁻¹.1 0 0
          simp only [← map_inv, hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp (continuous_subtype_val.comp continuous_inv) }
  refine ⟨e, fun t => rfl, fun dt => ?_⟩
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  have eh : (k ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → k) :=
    let b := (Algebra.TensorProduct.basis k (Module.finBasis F E)).equivFun
    { b.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap }
  haveI : T2Space (k ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : T2Space (GL (Fin n) (k ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (HA k σ J) := (isEmbedding_matHom k σ J).t2Space
  have hset : (cent (gam h) : Set (HA k σ J)) = {g | gam h * g = g * gam h} := by
    ext g; simp [cent, Subgroup.mem_centralizer_iff]
  have hclosed : IsClosed (cent (gam h) : Set (HA k σ J)) := by
    rw [hset]; exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hf : (torEmb h : Tor P k → HA k σ J) = Subtype.val ∘ e := funext fun t => rfl
  unfold centMeas
  rw [hf, ← Measure.map_map measurable_subtype_coe (map_continuous e).measurable]
  exact (MeasurableEmbedding.subtype_coe hclosed.measurableSet).comap_map _

end GlobalTheory.TorCentTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIntegralModelOfCover
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.ZetaTransfer

theorem transfer {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [TopologicalSpace H] [MeasurableSpace H]
    [OpensMeasurableSpace H] {ν : Measure G} {μ : Measure H} {π : G → H} {c : NNReal} (hc : c ≠ 0)
    (hq : Topology.IsQuotientMap π) (hm : Measurable π) (hmap : Measure.map π ν = c • μ) {f : H → ℂ} {k : G → ℂ}
    (hk : Continuous k) (hf : ∀ g, f (π g) = k g) (hi : Integrable k ν) :
    Integrable f μ ∧ ∫ h, f h ∂μ = (((c : ℝ)⁻¹ : ℝ) : ℂ) * ∫ g, k g ∂ν := by
  have hcomp : f ∘ π = k := funext hf
  have hfc : Continuous f := by
    rw [hq.continuous_iff, hcomp]
    exact hk
  have hfm : AEStronglyMeasurable f (Measure.map π ν) := hfc.aestronglyMeasurable
  have hint : Integrable f (Measure.map π ν) := by
    rw [integrable_map_measure hfm hm.aemeasurable, hcomp]
    exact hi
  have hμ : μ = (c⁻¹ : NNReal) • Measure.map π ν := by
    rw [hmap, smul_smul, _root_.inv_mul_cancel₀ hc, one_smul]
  refine ⟨?_, ?_⟩
  · rw [hμ]
    exact hint.smul_measure_nnreal
  · rw [hμ, integral_smul_nnreal_measure, integral_map hm.aemeasurable hfm]
    simp only [hf, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv]

theorem zetaLaw_of_cover : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (br : Bool) (e : Ix p q ≃ Fin W.rank) (e' : Ix r s ≃ Fin V.rank) (u : kfin N τ → (X.ds p q lam).HK.V) (K : ℝ), ARi X lam lam' → (∀ v, UnitHW (X.ds p q lam) (blattner lam) v → Integrable (eFun (X.ds p q lam) v) (X.grp p q).haar) → KTie (X.ds p q lam) N τ lam c br false e u → SignCompat (M.ε τ) e' → (m : ℚ) = 2 * c → Coef (X.fock p q r s) B pt ip κ (phiFr (N.fr τ) br e) m K → (∀ Φ, IsJoint M τ A pt N B Φ → CJoint (fockAct1 p q r s) (fockAct2 p q r s) (blattner lam) (blattner lam') (κ Φ)) → ZetaLaw M τ A pt N B ip := by
  intro D V S M W S' N τ ι Z A B pt ip X p q r s lam lam' κ c m br e e' u K hA hI hT hS hm hC hJ
  intro Φ hΦ v hv μ hμ
  obtain ⟨hsc, -, -⟩ := hT.ord
  obtain ⟨π, c0, hc0, humat, hq, hπm, hmap⟩ :=
    _root_.GlobalTheory.ArchRec.cover_haar_map p q W.rank (X.grp p q) (N.ε τ) e br μ hsc hμ
  have huv : UnitHW (X.ds p q lam) (blattner lam) (u v) := (hT.hi v).1 hv
  have huv1 : ‖(X.ds p q lam).ι (u v)‖ = 1 := by
    obtain ⟨-, h⟩ := huv
    exact h
  have hv1 : ‖(v : N.H τ)‖ = 1 := by
    obtain ⟨h, -⟩ := hv
    exact h
  obtain ⟨hK, hC1, hC2⟩ := hC
  obtain ⟨-, hA2⟩ := hA
  obtain ⟨c', hc', hJHW⟩ :=
    (_root_.GlobalTheory.ArchRec.Joint.joint_harmonics X p q r s (blattner lam) (blattner lam')).2.1 (κ Φ) (hJ Φ hΦ)
  obtain ⟨hIntC, hEqC, hPosC, hCpt⟩ := hA2 _ (u v) hJHW huv

  have hFc : ∀ x, Continuous fun g : (X.grp p q).G => (X.fock p q r s).π (g, 1) x := by
    intro x
    have h1 := (X.fock p q r s).7 x
    have h2 := GlobalTheory.FockEmbExp.continuous_emb (X.fock p q r s)
    have h3 : Continuous fun g : (X.grp p q).G => ((g, 1) : (X.grp p q).G × (X.grp r s).G) := by fun_prop
    exact h1.comp (h2.comp h3)
  have hmc : Continuous fun g => mcoef (X.ds p q lam) (u v) g := by
    show Continuous fun g => ⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ
    exact continuous_const.inner ((X.ds p q lam).U.cont _)
  have hsqc : Continuous fun g : (X.grp p q).G => (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m :=
    (GlobalTheory.RealPar.Cover.continuous_sq (T := X.grp p q)).zpow₀ m fun g => Or.inl (X.grp p q |>.sq g).ne_zero
  have hsq : ∀ g : (X.grp p q).G,
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * star ((((X.grp p q).sq g : ℂˣ) : ℂ) ^ m) = 1 := by
    intro g
    have h1 := GlobalTheory.RealPar.Cover.norm_sq (T := X.grp p q) g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, _root_.norm_zpow, h1, _root_.one_zpow]
    norm_num

  have hcoef : ∀ g, ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ =
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g := by
    intro g
    rw [humat g]
    exact hT.coef m hm g v v

  have hip : ∀ g, ip (B ((N.fr τ)⁻¹ * umat (π g) * N.fr τ) (pt Φ)) (pt Φ) =
      (K : ℂ) * (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m *
        ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι (κ Φ))⟫_ℂ := by
    intro g
    rw [humat g]
    exact hC2 g Φ Φ
  have hscal : ∀ g, ⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
      (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ =
      (c' : ℂ) ^ 2 * ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι (κ Φ))⟫_ℂ := by
    intro g
    rw [map_smul, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  have hc2 : ((c' : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hc'.ne')
  have hc2' : ((c' : ℂ) ^ 2)⁻¹ * (c' : ℂ) ^ 2 = 1 := _root_.inv_mul_cancel₀ hc2

  have hkc : Continuous fun g : (X.grp p q).G => (K : ℂ) * ((c' : ℂ) ^ 2)⁻¹ *
      (⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
        (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g)) :=
    continuous_const.mul ((continuous_const.inner (hFc _)).mul hmc.star)
  have hki : Integrable (fun g : (X.grp p q).G => (K : ℂ) * ((c' : ℂ) ^ 2)⁻¹ *
      (⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
        (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g))) (X.grp p q).haar :=
    hIntC.const_mul _
  have hfk : ∀ g, (fun g' : Formalism.REAL.UJ (N.ε τ) => ip (B (ofFr N τ (umat g')) (pt Φ)) (pt Φ) *
      star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g')) (π g) =
      (K : ℂ) * ((c' : ℂ) ^ 2)⁻¹ *
      (⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
        (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g)) := by
    intro g
    show ip (B ((N.fr τ)⁻¹ * umat (π g) * N.fr τ) (pt Φ)) (pt Φ) *
      star ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ = _
    rw [hip g, hcoef g, hscal g, _root_.star_mul']
    linear_combination
      ((K : ℂ) * ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι (κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g)) * (hsq g - hc2')
  obtain ⟨hfi, hfe⟩ := transfer (f := (fun g' : Formalism.REAL.UJ (N.ε τ) => ip (B (ofFr N τ (umat g')) (pt Φ)) (pt Φ) *
      star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g'))) hc0 hq hπm hmap hkc hfk hki
  rw [integral_const_mul, hEqC] at hfe

  have hk1c : Continuous fun g : (X.grp p q).G =>
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g := hsqc.mul hmc
  have hfd : ((X.ds p q lam).fdeg : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (X.ds p q lam).fdeg_pos.ne'
  have hk1i : Integrable (fun g : (X.grp p q).G =>
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g) (X.grp p q).haar := by
    refine ((hI (u v) huv).const_mul ((X.ds p q lam).fdeg : ℂ)⁻¹).mono hk1c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => le_of_eq ?_)
    show _ = ‖((X.ds p q lam).fdeg : ℂ)⁻¹ * (((X.ds p q lam).fdeg : ℂ) * star (mcoef (X.ds p q lam) (u v) g))‖
    rw [← mul_assoc, _root_.inv_mul_cancel₀ hfd, one_mul, norm_star, _root_.norm_mul, _root_.norm_zpow,
      GlobalTheory.RealPar.Cover.norm_sq, _root_.one_zpow, one_mul]
  have hk1f : ∀ g, (fun g' : Formalism.REAL.UJ (N.ε τ) =>
      Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g') (π g) =
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g := hcoef
  refine ⟨(transfer (f := (fun g' : Formalism.REAL.UJ (N.ε τ) => Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g')) hc0 hq hπm hmap hk1c hk1f hk1i).1, hfi, ?_, ?_⟩
  · refine ⟨(c0 : ℝ)⁻¹ * ((K : ℝ) * (c' ^ 2)⁻¹ *
      (‖opE (X.grp p q) (fun g => (X.fock p q r s).π (g, 1)) (eFun (X.ds p q lam) (u v))
          ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))‖ ^ 2 / (X.ds p q lam).fdeg)), ?_, ?_⟩
    · have h0 : (0 : ℝ) < c0 := lt_of_le_of_ne c0.2 (fun h => hc0 (NNReal.coe_eq_zero.mp h.symm))
      have h1 := (X.ds p q lam).fdeg_pos
      positivity
    · rw [hfe]
      push_cast
      ring
  · intro hall d hd
    have hs0 : r = 0 ∨ s = 0 := by
      right
      by_contra hs
      have h := hS (Sum.inr ⟨0, Nat.pos_of_ne_zero hs⟩)
      rw [hall] at h
      simp at h
    obtain ⟨hopE, hEq1⟩ := hCpt hs0
    rw [hopE] at hEqC

    have hn : ‖(X.fock p q r s).ι ((c' : ℂ) • κ Φ)‖ ^ 2 = 1 := by
      have h := hEqC.symm.trans hEq1
      have h' : ‖(X.fock p q r s).ι ((c' : ℂ) • κ Φ)‖ ^ 2 / (X.ds p q lam).fdeg =
          ((X.ds p q lam).fdeg)⁻¹ := by exact_mod_cast h
      have hfd' := (X.ds p q lam).fdeg_pos
      field_simp at h'
      linarith
    have hn' : (c' : ℂ) ^ 2 * ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).ι (κ Φ)⟫_ℂ = 1 := by
      rw [map_smul, _root_.norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc', _root_.mul_pow] at hn
      rw [inner_self_eq_norm_sq_to_K]
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) hn
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one] at h2
      exact h2

    obtain ⟨hd0, hd1⟩ := hd
    have hsch := (X.ds p q lam).schur ((X.ds p q lam).ι (u v)) ((X.ds p q lam).ι (u v))
    have hk2c : Continuous fun g : (X.grp p q).G =>
        ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_const.inner ((X.ds p q lam).U.cont _)).norm.pow 2)
    have hk2i : Integrable (fun g : (X.grp p q).G =>
        ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ))
        (X.grp p q).haar := hsch.1.ofReal
    have hk2f : ∀ g, (fun g' : Formalism.REAL.UJ (N.ε τ) =>
        Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g' *
          star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g')) (π g) =
        ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      show ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ * star ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ = _
      rw [hcoef g, _root_.star_mul']
      have hm2 : mcoef (X.ds p q lam) (u v) g * star (mcoef (X.ds p q lam) (u v) g) =
          ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
        show ⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ *
          star ⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ = _
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      linear_combination (mcoef (X.ds p q lam) (u v) g * star (mcoef (X.ds p q lam) (u v) g)) * hsq g + hm2
    have hfd2 := (transfer (f := (fun g' : Formalism.REAL.UJ (N.ε τ) => Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g' *
          star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g'))) hc0 hq hπm hmap hk2c hk2f hk2i).2
    beta_reduce at hfd2
    rw [integral_complex_ofReal, hsch.2, huv1, (hd1 v v v v).2, inner_self_eq_norm_sq_to_K, hv1] at hfd2
    rw [hfe, hopE, hn, hC1 Φ Φ, eq_inv_of_mul_eq_one_right hn']
    have hd0' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd0.ne'
    have hc0' : ((c0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hc0)
    push_cast at hfd2 ⊢
    linear_combination (-(K : ℂ) * ((c' : ℂ) ^ 2)⁻¹) * hfd2

end GlobalTheory.ArchRec.ZetaTransfer
end

