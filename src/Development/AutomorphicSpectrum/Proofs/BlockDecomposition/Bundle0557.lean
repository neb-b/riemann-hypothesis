module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem sq_norm_toLp {X : Type*} [MeasurableSpace X] {m : Measure X} {F : X → ℂ} (h : MemLp F 2 m) :
    ENNReal.ofReal (‖h.toLp F‖ ^ 2) = ∫⁻ q, ‖F q‖ₑ ^ 2 ∂m := by
  have h1 := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := m) (p := 2) (by norm_num) h.aestronglyMeasurable
  have h2 : ENNReal.ofReal ‖h.toLp F‖ = eLpNorm F 2 m := by
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal h.ne]
  rw [ENNReal.ofReal_pow (norm_nonneg _), h2]
  simpa using h1

theorem exists_extend {S H K : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (A : S →ₗ[ℂ] H) (B : S →ₗ[ℂ] K)
    (hd : DenseRange A) (r : ℝ) (hn : ∀ s, ‖B s‖ = r * ‖A s‖) :
    ∃ Φ : H →L[ℂ] K, (∀ s, Φ (A s) = B s) ∧ ∀ F, ‖Φ F‖ = r * ‖F‖ := by
  have h1 : ∀ s, (B.extendOfNorm A) (A s) = B s := fun s =>
    LinearMap.extendOfNorm_eq hd ⟨r, fun s => (hn s).le⟩ s
  refine ⟨B.extendOfNorm A, h1, fun F => ?_⟩
  exact hd.induction_on F (isClosed_eq (by fun_prop) (by fun_prop)) fun s => by rw [h1, hn]

theorem exists_extend_equivariant {S H K X : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (A : S →ₗ[ℂ] H)
    (B : S →ₗ[ℂ] K) (hd : DenseRange A) (r : ℝ) (hn : ∀ s, ‖B s‖ = r * ‖A s‖) (π : X → H →L[ℂ] H)
    (ρ : X → K →L[ℂ] K) (t : X → S → S) (hπ : ∀ x s, π x (A s) = A (t x s)) (hρ : ∀ x s, ρ x (B s) = B (t x s)) :
    ∃ Φ : H →L[ℂ] K, (∀ F, ‖Φ F‖ = r * ‖F‖) ∧ ∀ x F, Φ (π x F) = ρ x (Φ F) := by
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extend A B hd r hn
  refine ⟨Φ, hΦn, fun x F => ?_⟩
  refine hd.induction_on F (isClosed_eq ?_ ?_) fun s => ?_
  · exact Φ.continuous.comp (π x).continuous
  · exact (ρ x).continuous.comp Φ.continuous
  · rw [hπ, hΦ, hΦ, hρ]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem lintegral_resQ (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a)))
    [ν.IsHaarMeasure] (c : ENNReal)
    (hmap : Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ)
    (φ : GA E a → ℂ) (hc : Continuous φ) (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (hz : ∀ t g, φ (splitCentre E a t * g) = φ g) :
    ∫⁻ q, ‖resQ φ q‖ₑ ^ 2 ∂(RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν) =
      c * ∫⁻ q, ‖descend (latticeGL E a) φ q‖ₑ ^ 2 ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) := by
  have hd := GlobalTheory.T.fundamental_domain_split_centre_product E a ha μ
  have hL : LeftInv (latticeGL E a) φ := leftInv_latticeGL hl hz
  rw [RightCosetSpace.lintegral_quotientMeasure, lintegral_quotMeasure hd]
  simp only [resQ_mk hl, hL.descend_mk]
  rw [← GlobalTheory.T.integral_split_centre_invariant E a ha μ ν c hmap φ hc hz, Measure.restrict_smul, lintegral_smul_measure]
  rfl

def cuspidalL2Functions (μ : Measure (GA E a)) [μ.IsHaarMeasure] : Submodule ℂ (GA E a → ℂ) where
  carrier := {φ | φ ∈ cuspCont E a ∧ MemL2Quotient (latticeGL E a) μ φ}
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' := fun {φ ψ} h h' => ⟨add_mem h.1 h'.1, fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g),
    h.2.2.add h'.2.2⟩
  smul_mem' := fun z φ h => ⟨Submodule.smul_mem _ z h.1, fun γ hγ g => congrArg (z • ·) (h.2.1 γ hγ g),
    h.2.2.const_smul z⟩

section Maps

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure]

def toL2cusp : cuspidalL2Functions μ →ₗ[ℂ] L2cusp μ where
  toFun φ := ⟨φ.2.2.toL2, toL2_mem_cuspidal φ.2.2 φ.2.1⟩
  map_add' φ ψ := Subtype.ext (MemLp.toLp_add φ.2.2.2 ψ.2.2.2)
  map_smul' z φ := Subtype.ext (MemLp.toLp_const_smul z φ.2.2.2)

theorem coe_toL2cusp (φ : cuspidalL2Functions μ) : (toL2cusp μ φ : L2 (latticeGL E a) μ) = φ.2.2.toL2 := rfl

theorem denseRange_toL2cusp : DenseRange (toL2cusp μ) := by
  rw [DenseRange, Subtype.dense_iff]
  intro y hy
  refine closure_mono ?_ (show y ∈ closure (cuspContinuousL2 μ : Set (L2 (latticeGL E a) μ)) from hy)
  rintro F ⟨φ, hφ, e⟩
  have h2 := memL2_of_ae_eq (leftInv_of_mem_cuspCont hφ) e
  refine ⟨toL2cusp μ ⟨φ, hφ, h2⟩, ⟨_, rfl⟩, ?_⟩
  rw [coe_toL2cusp]
  exact l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (h2.lift_toL2_ae_eq.trans e.symm)


variable {μ ν} in
def toCusp (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν)) :
    cuspidalL2Functions μ →ₗ[ℂ] cuspidalL2 ν where
  toFun φ := ⟨(hm φ).toLp _, GlobalTheory.T.cuspidal_restrict_mem_cuspidal_l2 E a ν φ.1 φ.2.1 (hm φ)⟩
  map_add' φ ψ := Subtype.ext (MemLp.toLp_add (hm φ) (hm ψ))
  map_smul' z φ := Subtype.ext (MemLp.toLp_const_smul z (hm φ))

variable {μ ν} in
theorem coe_toCusp (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν))
    (φ : cuspidalL2Functions μ) :
    (toCusp hm φ : Lp ℂ 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν)) = (hm φ).toLp _ := rfl

end Maps

end GlobalTheory.CompanionTheory.CuspTransfer
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ν : Measure (normOneGL (K := E) (n := a))} [ν.IsHaarMeasure]

def trFn (x : GA E a) (φ : cuspidalL2Functions μ) : cuspidalL2Functions μ :=
  ⟨fun g => φ.1 (g * x), mul_right_mem_cuspCont φ.2.1 x, φ.2.2.mul_right x⟩

theorem Rcusp_toL2cusp (x : GA E a) (φ : cuspidalL2Functions μ) : Rcusp μ x (toL2cusp μ φ) = toL2cusp μ (trFn x φ) :=
  Subtype.ext (right_translate_toL2 φ.2.2 x)

theorem cuspRep_toCusp (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν))
    (x : normOneGL (K := E) (n := a)) (φ : cuspidalL2Functions μ) : cuspRep ν x (toCusp hm φ) = toCusp hm (trFn (x : GA E a) φ) := by
  refine Subtype.ext (Lp.ext ?_)
  have e0 : ((cuspRep ν x (toCusp hm φ) : cuspidalL2 ν) : Lp ℂ 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν)) =
      RightCosetSpace.rightRegularRep (rationalGLOne (K := E) (n := a)) ν x (toCusp hm φ) := rfl
  rw [e0, coe_toCusp, coe_toCusp]
  refine (RightCosetSpace.coeFn_rightRegularRep _ ν x _).trans ?_
  refine (((RightCosetSpace.measurePreserving_rightMul ν x).quasiMeasurePreserving.ae_eq_comp
    (hm φ).coeFn_toLp).trans ?_).trans (hm (trFn (x : GA E a) φ)).coeFn_toLp.symm
  refine Filter.Eventually.of_forall fun q => ?_
  obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
  simp only [Function.comp_apply, RightCosetSpace.rightMul_mk]
  rw [resQ_mk φ.2.1.2.1]
  exact (resQ_mk (φ := (trFn (x : GA E a) φ).1) (fun γ g => by
    simp only [trFn, mul_assoc, φ.2.1.2.1]) y).symm

theorem memLp_resQ (ha : 0 < a) (c : ENNReal) (hct : c ≠ ⊤)
    (hmap : Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ)
    (φ : cuspidalL2Functions μ) : MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν) := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    (continuous_resQ φ.2.1.1 φ.2.1.2.1).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [lintegral_resQ ha μ ν c hmap φ.1 φ.2.1.1 φ.2.1.2.1 φ.2.1.2.2.1, ← sq_norm_toLp φ.2.2.2]
  exact ENNReal.mul_lt_top hct.lt_top ENNReal.ofReal_lt_top

theorem norm_toCusp (ha : 0 < a) (c : ENNReal)
    (hmap : Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ)
    (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν))
    (φ : cuspidalL2Functions μ) : ‖toCusp hm φ‖ = Real.sqrt c.toReal * ‖toL2cusp μ φ‖ := by
  have h3 : ‖toCusp hm φ‖ ^ 2 = c.toReal * ‖toL2cusp μ φ‖ ^ 2 := by
    have h4 := lintegral_resQ ha μ ν c hmap φ.1 φ.2.1.1 φ.2.1.2.1 φ.2.1.2.2.1
    rw [← sq_norm_toLp (hm φ), ← sq_norm_toLp φ.2.2.2] at h4
    have h5 := congrArg ENNReal.toReal h4
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h5
    exact h5
  rw [← Real.sqrt_sq (norm_nonneg (toCusp hm φ)), h3, Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.CompanionTheory.CuspTransfer
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ν : Measure (normOneGL (K := E) (n := a))} [ν.IsHaarMeasure]

theorem exists_transfer_op (ha : 0 < a) (c : ENNReal) (hct : c ≠ ⊤)
    (hmap : Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ) :
    ∃ Φ : L2cusp μ →L[ℂ] cuspidalL2 ν, (∀ F, ‖Φ F‖ = Real.sqrt c.toReal * ‖F‖) ∧
      ∀ (x : normOneGL (K := E) (n := a)) (F : L2cusp μ), Φ (Rcusp μ (x : GA E a) F) = cuspRep ν x (Φ F) :=
  have hm := memLp_resQ (μ := μ) (ν := ν) ha c hct hmap
  exists_extend_equivariant (toL2cusp μ) (toCusp hm) (denseRange_toL2cusp μ) (Real.sqrt c.toReal)
    (norm_toCusp ha c hmap hm) (fun x : normOneGL (K := E) (n := a) => Rcusp μ (x : GA E a)) (fun x => cuspRep ν x)
    (fun x => trFn (x : GA E a)) (fun x s => Rcusp_toL2cusp _ s) (fun x s => cuspRep_toCusp hm x s)

end GlobalTheory.CompanionTheory.CuspTransfer
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem comp_repOp_eq_integrated {G Y H K : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] {m : Measure G} [IsFiniteMeasureOnCompacts m] [Group Y] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {n : Measure Y} [IsFiniteMeasureOnCompacts n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {π : G →* (H →L[ℂ] H)} (hU : IsUnitaryRep π) (ρ : UnitaryRep Y K) (ι : Y → G) (Φ : H →L[ℂ] K)
    (hact : ∀ y v, Φ (π (ι y) v) = ρ y (Φ v)) {f : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (f₁ : CompactlySupportedContinuousMap Y ℂ)
    (h₁ : ∀ v, ∫ g, f g • Φ (π g v) ∂m = ∫ y, f₁ y • Φ (π (ι y) v) ∂n) :
    Φ ∘L repOp π m f = ρ.integrated n (UnitaryRep.ccToL1 n f₁) ∘L Φ := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 := hU.isRepOp (μ := m) hf hfc v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h2.2, ← Φ.integral_comp_comm h2.1,
    UnitaryRep.integrated_ccToL1_apply]
  simp only [map_smul]
  rw [h₁]
  exact integral_congr_ae (.of_forall fun x => by simp only [hact])

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ν : Measure (normOneGL (K := E) (n := a))} [ν.IsHaarMeasure]

theorem comp_repOp_eq (Φ : L2cusp μ →L[ℂ] cuspidalL2 ν)
    (hact : ∀ (x : normOneGL (K := E) (n := a)) (F : L2cusp μ), Φ (Rcusp μ (x : GA E a) F) = cuspRep ν x (Φ F))
    {f : GA E a → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (f₁ : CompactlySupportedContinuousMap (normOneGL (K := E) (n := a)) ℂ)
    (h₁ : ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W →
      (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν) :
    Φ ∘L repOp (Rcusp μ) μ f = (cuspRep ν).integrated ν (UnitaryRep.ccToL1 ν f₁) ∘L Φ :=
  comp_repOp_eq_integrated (isUnitaryRep_Rcusp μ) (cuspRep ν) (fun x : normOneGL (K := E) (n := a) => (x : GA E a)) Φ hact hf hfc f₁
    fun v => h₁ (cuspidalL2 ν) (fun g => Φ (Rcusp μ g v)) (Φ.continuous.comp ((isUnitaryRep_Rcusp μ).continuous_apply v))
      (fun t g => by simp only [map_mul, Rcusp_splitCentre, one_mul])

end GlobalTheory.CompanionTheory.CuspTransfer
end

namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem transfer : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
      (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a))) [ν.IsHaarMeasure],
      ∃ (Φ : L2cusp μ →L[ℂ] GroundTheory.Automorphic.CuspidalSpectrum.cuspidalL2 ν) (c : ℝ), 0 < c ∧ (∀ F, ‖Φ F‖ = c * ‖F‖) ∧
        ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f →
          ∃ f₁ : CompactlySupportedContinuousMap (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) ℂ,
            Φ ∘L repOp (Rcusp μ) μ f = (GroundTheory.Automorphic.CuspidalSpectrum.cuspRep ν).integrated ν
              (GroundTheory.Automorphic.UnitaryRep.ccToL1 ν f₁) ∘L Φ := fun E _ _ _ a ha μ _ _ ν _ =>
  (GlobalTheory.T.haar_measure_norm_one_product E a ha μ ν).elim fun c h =>
    (exists_transfer_op ha c h.2.1 h.2.2).elim fun Φ h' =>
      ⟨Φ, Real.sqrt c.toReal, Real.sqrt_pos.2 (ENNReal.toReal_pos h.1 h.2.1), h'.1, fun f hf hfc =>
        (GlobalTheory.T.compact_support_split_centre_factor E a ha μ ν c h.1 h.2.1 h.2.2 f hf hfc).elim fun f₁ h₁ =>
          ⟨f₁, comp_repOp_eq Φ h'.2 hf hfc f₁ fun K _ _ _ W => h₁ K W⟩⟩

end GlobalTheory.CompanionTheory.CuspTransfer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicative
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula

theorem relIndex_split {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (A B : AddSubgroup G) (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * A.relIndex (B ⊓ f.ker) := by
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ f.ker).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have h2 : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.mp hx
      obtain ⟨a, ha, k, hk, rfl⟩ := AddSubgroup.mem_sup.mp hx1
      refine AddSubgroup.mem_sup.mpr ⟨a, ha, k, AddSubgroup.mem_inf.mpr ⟨?_, hk⟩, rfl⟩
      have := B.sub_mem hx2 (hAB ha)
      simpa using this
    · refine sup_le (le_inf le_sup_left hAB) (le_inf ?_ inf_le_left)
      exact inf_le_right.trans le_sup_right
  have h3 : A.relIndex (A ⊔ (B ⊓ f.ker)) = A.relIndex (B ⊓ f.ker) :=
    AddSubgroup.relIndex_sup_left _ _
  have h4 := AddSubgroup.relIndex_mul_relIndex A ((A ⊔ f.ker) ⊓ B) B
    (le_inf le_sup_left hAB) inf_le_right
  rw [AddSubgroup.inf_relIndex_right, h2, h3] at h4
  rw [h1, ← h4, mul_comm]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_castSucc_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a b : Fin m) :
    blk σ c u d a.castSucc b.castSucc = c a b := by
  simp [blk]

theorem blk_castSucc_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a : Fin m) :
    blk σ c u d a.castSucc (Fin.last m) = u a := by
  simp [blk]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin (m + 1) → E) (i : Fin m) :
    (blk σ c u d).mulVec y i.castSucc
      = c.mulVec (fun j => y j.castSucc) i + y (Fin.last m) * u i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk_castSucc_castSucc,
    blk_castSucc_last]
  ring

variable [NumberField E]

def proj (E : Type) [Field E] [NumberField E] (m : ℕ) :
    (Fin (m + 1) → E) →ₗ[𝓞 E] (Fin m → E) :=
  LinearMap.funLeft (𝓞 E) E Fin.castSucc

@[simp] theorem proj_apply (m : ℕ) (v : Fin (m + 1) → E) (i : Fin m) :
    proj E m v i = v i.castSucc := rfl

theorem snoc_mem_intVec {m : ℕ} {y : Fin m → E} (hy : y ∈ intVec E m) (o : 𝓞 E) :
    (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E o) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨o, by simp⟩
  · obtain ⟨p, hp⟩ := hy j
    exact ⟨p, by simp [hp]⟩

theorem proj_mem_intVec {m : ℕ} {y : Fin (m + 1) → E} (hy : y ∈ intVec E (m + 1)) :
    proj E m y ∈ intVec E m := fun i => hy i.castSucc

theorem map_proj_intVec (m : ℕ) : (intVec E (m + 1)).map (proj E m) = intVec E m := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact proj_mem_intVec hy
  · intro y hy
    refine ⟨_, snoc_mem_intVec hy 0, ?_⟩
    funext i
    simp

theorem intVec_le_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : intVec E m ≤ lam c := le_sup_left

theorem mulVec_mem_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) {y : Fin m → E}
    (hy : y ∈ intVec E m) : c.mulVec y ∈ lam c :=
  Submodule.mem_sup_right ⟨y, hy, rfl⟩

theorem map_proj_lam {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) :
    (lam (blk σ c u d)).map (proj E m) = lam c ⊔ Submodule.span (𝓞 E) {u} := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, z, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨o, ho⟩ := hy (Fin.last m)
    have e : proj E m (x + (blk σ c u d).mulVecLin.restrictScalars (𝓞 E) y)
        = (proj E m x + c.mulVec (proj E m y)) + o • u := by
      funext i
      have := blk_mulVec_castSucc σ c u d y i
      simp only [proj_apply, Pi.add_apply, map_add (f := _), LinearMap.restrictScalars_apply,
        Matrix.mulVecLin_apply, Pi.smul_apply, Algebra.smul_def, ho]
      rw [this, add_assoc]
      rfl
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)))
    exact Submodule.add_mem _ (intVec_le_lam c (proj_mem_intVec hx))
      (mulVec_mem_lam c (proj_mem_intVec hy))
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [← map_proj_intVec m]
      exact Submodule.map_mono (intVec_le_lam _)
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E 0)),
        mulVec_mem_lam _ (snoc_mem_intVec hy 0), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) 0 (algebraMap (𝓞 E) E 1)),
        mulVec_mem_lam _ (snoc_mem_intVec (Submodule.zero_mem _) 1), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp [show (fun _ : Fin m => (0 : E)) = 0 from rfl]

theorem relIndex_lam_sup {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) :
    (lam c).toAddSubgroup.relIndex (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = Ideal.absNorm (tor c u) := by
  let φ : 𝓞 E →+ (Fin m → E) := (LinearMap.toSpanSingleton (𝓞 E) _ u).toAddMonoidHom
  have hsup : (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = (lam c).toAddSubgroup ⊔ (⊤ : AddSubgroup (𝓞 E)).map φ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
      exact AddSubgroup.add_mem_sup ha ⟨t, trivial, rfl⟩
    · refine sup_le (fun x hx => Submodule.mem_sup_left hx) ?_
      rintro _ ⟨t, -, rfl⟩
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have hcomap : (lam c).toAddSubgroup.comap φ = (tor c u).toAddSubgroup := by
    ext t
    change t • u ∈ lam c ↔ t ∈ tor c u
    rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  rw [hsup, AddSubgroup.relIndex_sup_left, ← AddSubgroup.relIndex_comap, hcomap,
    AddSubgroup.relIndex_top_right]
  exact (Ideal.absNorm_eq_index _).symm

def lastInc (E : Type) [Field E] [NumberField E] (m : ℕ) : E →+ (Fin (m + 1) → E) :=
  (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m)).toAddMonoidHom

theorem comap_lastInc_intVec (m : ℕ) :
    (intVec E (m + 1)).toAddSubgroup.comap (lastInc E m)
      = (1 : Submodule (𝓞 E) E).toAddSubgroup := by
  ext x
  change (Pi.single (Fin.last m) x : Fin (m + 1) → E) ∈ intVec E (m + 1) ↔
    x ∈ (1 : Submodule (𝓞 E) E)
  rw [Submodule.mem_one]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h (Fin.last m)
    exact ⟨o, by simpa using ho⟩
  · rintro ⟨o, rfl⟩ i
    by_cases hi : i = Fin.last m
    · subst hi
      exact ⟨o, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hi]⟩

theorem map_lastInc_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).toAddSubgroup.map (lastInc E m)
      = (lam C).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine AddSubgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [AddMonoidHom.mem_ker]
    funext i
    simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last]
  · intro hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hv
    rw [AddMonoidHom.mem_ker] at h2
    have hv' : lastInc E m (v (Fin.last m)) = v := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [lastInc]
      · have := congrFun h2 j
        simp only [LinearMap.toAddMonoidHom_coe, proj_apply, Pi.zero_apply] at this
        simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last, this]
    refine ⟨v (Fin.last m), ?_, hv'⟩
    change lastInc E m (v (Fin.last m)) ∈ lam C
    rw [hv']
    exact h1

theorem delta_blk (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    delta (blk σ c u d) = delta c * Ideal.absNorm (tor c u) * idx E (lastFib (blk σ c u d)) := by
  have hC := (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index E (m + 1) (blk σ c u d)).2
  have hc := (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index E m c).2
  have hsplit := relIndex_split (proj E m).toAddMonoidHom (intVec E (m + 1)).toAddSubgroup
    (lam (blk σ c u d)).toAddSubgroup (intVec_le_lam (blk σ c u d))
  have hA : (intVec E (m + 1)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (intVec E m).toAddSubgroup := by
    rw [← map_proj_intVec m]; rfl
  have hB : (lam (blk σ c u d)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup := by
    rw [← map_proj_lam σ c u d]; rfl
  have hmul := AddSubgroup.relIndex_mul_relIndex (intVec E m).toAddSubgroup
    (lam c).toAddSubgroup (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
    (intVec_le_lam c) (fun x hx => Submodule.mem_sup_left hx)
  have hfib : (intVec E (m + 1)).toAddSubgroup.relIndex
      ((lam (blk σ c u d)).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker)
      = idx E (lastFib (blk σ c u d)) := by
    rw [← map_lastInc_lastFib, ← AddSubgroup.relIndex_comap, comap_lastInc_intVec]
    rfl
  rw [hC, hc, hsplit, hA, hB, hfib, ← hmul, relIndex_lam_sup]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimum
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue

theorem discInf : DiscInf := by
  intro E _ _ _ M V hV τ
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := M) τ) (((M : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := GlobalTheory.DiscLocEx.exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CompanionTheory.EGlue

end
end

