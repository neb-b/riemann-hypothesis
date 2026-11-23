module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoboundaryOfInvariantUnitaryStepConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOneVectorStepCompatibleChangeOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerMeasureIndependentOfPath
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsGaugeOfIsCMExt
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCompatible_smul {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin M → E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (Hstab (AF F) σ J x)}
    {ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)} (h : IsCompatible F E σ M J x μ μ' ν) (c k : ℝ≥0) :
    IsCompatible F E σ M J x ((k * c) • μ) (c • μ') (k • ν) := by
  intro f hf sec hsec
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [h f hf sec hsec]
  simp only [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  push_cast
  ring

theorem StepRel.smul [NumberField E] (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} {s : StdMeas b} {M : ℕ}
    {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E} {β : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (hS : StepData σ J x β B J') (h : StepRel s σ J x β B J' μ μ') (c : ℝ≥0) : StepRel s σ J x β B J' (c • μ) (c • μ') := by
  intro ν hν e he
  have hc := isCompatible_smul (h ν hν e he) c 1
  have hm := ((_root_.GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) M J x β B J' hS).2.2 e he).2.measurable
  simpa only [one_mul, one_smul, Measure.map_smul c hm.aemeasurable] using hc

end Scale

theorem smul_haar_inj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] (μ : Measure G) [μ.IsHaarMeasure] {c c' : ℝ≥0}
    (h : c • μ = c' • μ) : c = c' := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : μ K ≠ 0 :=
    (μ.measure_pos_of_nonempty_interior ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have htop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure G => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos htop).1 h2)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem stepData_unique {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    {a a' : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' J'' : Matrix (Fin M) (Fin M) E}
    (h : StepData σ J x a B J') (h' : StepData σ J x a' B J'') : a = a' ∧ J' = J'' := by
  obtain ⟨-, -, h1, -, h2, -⟩ := h
  obtain ⟨-, -, h1', -, h2', -⟩ := h'
  exact ⟨(algebraMap F E).injective (h1.symm.trans h1'), h2.trans h2'.symm⟩

theorem exists_const (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b)
    (G : GaugeFam F E σ) (hG : G.IsHaar) :
    ∃ c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) →
      Matrix (Fin (M + 1)) (Fin M) E → ℝ≥0ˣ,
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((c M J x B : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have key : ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
      (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      2 ≤ M → StepData σ J x a B J' →
      ∃ u : ℝ≥0ˣ, StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    intro M J x a B J' hM hS
    haveI : (G.μ M J').IsHaarMeasure := hG M J' hS.2.2.2.2.2
    haveI : (G.μ (M + 1) J).IsHaarMeasure := hG (M + 1) J hS.1
    obtain ⟨⟨μ, hμ, hrel⟩, -⟩ :=
      _root_.GlobalTheory.GaugeEx.exists_unique_stepRel F E σ hσ d b s M J x a B J' (G.μ M J') hM hS inferInstance
    haveI := hμ
    refine ⟨Units.mk0 (Measure.haarScalarFactor μ (G.μ (M + 1) J))
      (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ?_⟩
    rw [Units.val_mk0, ← Measure.isMulLeftInvariant_eq_smul]
    exact hrel
  refine ⟨fun M J x B => if h : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J')
    then h.choose else 1, ?_⟩
  intro M J x a B J' hM hS
  have hex : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    obtain ⟨u, hu⟩ := key M J x a B J' hM hS
    exact ⟨u, a, J', hM, hS, hu⟩
  simp only [dif_pos hex]
  obtain ⟨a₀, J₀, -, hS₀, hR₀⟩ := hex.choose_spec
  obtain ⟨rfl, rfl⟩ := stepData_unique hS₀ hS
  exact hR₀

theorem exists_std_family (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b) :
    ∃ (G : GaugeFam F E σ) (α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → ℝ≥0ˣ), G.IsHaar ∧ G.BasisInv ∧
      (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
        α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) =
          α M J) ∧
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) ((α M J' : ℝ≥0) • G.μ M J') := by
  classical
  obtain ⟨G, hH, hB⟩ := _root_.GlobalTheory.GaugeRef.exists_isHaar_basisInv F E σ hσ
  obtain ⟨c, hc⟩ := exists_const hσ s G hH
  refine (_root_.GlobalTheory.GaugeAlg.exists_coboundary F E σ hσ ℝ≥0ˣ c ?inv ?coc).elim fun α hα => ?main
  case main =>
    obtain ⟨hαinv, hαstep⟩ := hα
    refine ⟨G, α, hH, hB, hαinv, ?_⟩
    intro M J x a B J' hM hS
    have r := (hc M J x a B J' hM hS).smul hσ hS (α M J' : ℝ≥0)
    rw [smul_smul] at r
    rw [hαstep M J x a B J' hM hS, Units.val_mul, mul_comm]
    exact r
  case inv =>
    intro M J x a B J' x₂ B₂ P Q hM hS hx hPB
    obtain ⟨J₂, hJ₂⟩ : ∃ J₂, J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *
        J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) := ⟨_, rfl⟩
    obtain ⟨J₂', hJ₂'⟩ : ∃ J₂', J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) *
        J' * (Q : Matrix (Fin M) (Fin M) E) := ⟨_, rfl⟩
    rw [← hJ₂]
    obtain ⟨⟨eP, heP⟩, hmapP⟩ := hB (M + 1) J J₂ P hS.1 hJ₂
    obtain ⟨⟨eQ, heQ⟩, hmapQ⟩ := hB M J' J₂' Q hS.2.2.2.2.2 hJ₂'
    obtain ⟨hS₂, hR₂⟩ := _root_.GlobalTheory.GaugeEx.stepRel_basis F E σ hσ _ b s M J J₂ x a B J' x₂ B₂ J₂' P Q eP eQ _ _ hS hJ₂
      hJ₂' hx hPB heP heQ (hc M J x a B J' hM hS)
    have hmP := ((_root_.GlobalTheory.GaugeFrameBasis.frame_basis F E σ (AF F) (M + 1) J J₂ P hJ₂).2 eP heP).1.measurable
    rw [Measure.map_smul _ hmP.aemeasurable, hmapP eP heP, hmapQ eQ heQ] at hR₂
    have hR₃ := hc M J₂ x₂ a B₂ J₂' hM hS₂
    have hHaar₂ : (G.μ M J₂').IsHaarMeasure := hH M J₂' hS₂.2.2.2.2.2
    have huniq := (_root_.GlobalTheory.GaugeEx.exists_unique_stepRel F E σ hσ _ b s M J₂ x₂ a B₂ J₂' (G.μ M J₂') hM hS₂ hHaar₂).2 _ _
      hR₃ hR₂
    haveI : (G.μ (M + 1) J₂).IsHaarMeasure := hH (M + 1) J₂ hS₂.1
    exact Units.ext (smul_haar_inj _ huniq)
  case coc =>
    intro M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ hM h1 h1' h2 h2' hBC
    haveI : (G.μ M J₀).IsHaarMeasure := hH M J₀ h1'.2.2.2.2.2
    haveI : (G.μ (M + 1 + 1) J).IsHaarMeasure := hH _ J h1.1
    have r1 := (hc (M + 1) J x₁ a₁ B₁ J₁ (by omega) h1).smul hσ h1 (c M J₁ y₁ C₁ : ℝ≥0)
    have r2 := (hc (M + 1) J x₂ a₂ B₂ J₂ (by omega) h2).smul hσ h2 (c M J₂ y₂ C₂ : ℝ≥0)
    have heq := _root_.GlobalTheory.GaugeSquare.square F E σ hσ _ b s M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀
      (G.μ M J₀) _ _ _ _ hM h1 h1' h2 h2' hBC inferInstance (hc M J₁ y₁ b₁ C₁ J₀ hM h1') r1
      (hc M J₂ y₂ b₂ C₂ J₀ hM h2') r2
    rw [smul_smul, smul_smul] at heq
    have he := smul_haar_inj _ heq
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, mul_comm, he, mul_comm]

theorem exists_isGauge_of_isCMExt (hσ : IsCMExt F E σ) : ∃ G : GaugeFam F E σ, G.IsGauge := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI : IsTotallyReal F := hσ.1
  obtain ⟨s⟩ := GlobalTheory.T.nonempty_standardLocalHaarMeasures F E _ (Module.finBasis F E)
  obtain ⟨G, α, hH, hB, hαinv, hstep⟩ := exists_std_family hσ s
  obtain ⟨κ, hκ0, hκ⟩ := _root_.GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std F E σ hσ _ _ s
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.GaugeEx.CharZero.exists_isCharAF F
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℝ≥0, K = fun M => ∏ i ∈ Finset.range (M + 1), κ i := ⟨_, rfl⟩
  have hK0 : ∀ M, K M ≠ 0 := fun M => by
    rw [hK]; exact Finset.prod_ne_zero_iff.2 fun i _ => hκ0 i
  have hKs : ∀ M, K (M + 1) = κ (M + 1) * K M := fun M => by
    rw [hK]; simp only [Finset.prod_range_succ (n := M + 1)]; ring
  refine ⟨⟨fun M J => (K M * α M J : ℝ≥0) • G.μ M J⟩, ?_, ?_, ?_⟩
  · intro M J hJ
    haveI : (G.μ M J).IsHaarMeasure := hH M J hJ
    exact Measure.IsHaarMeasure.nnreal_smul _ (mul_ne_zero (hK0 M) (α M J).ne_zero)
  · intro M J J' P hJ hJ'
    obtain ⟨⟨e, he⟩, hmap⟩ := hB M J J' P hJ hJ'
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    show ((K M * α M J : ℝ≥0) • G.μ M J).map e' = (K M * α M J' : ℝ≥0) • G.μ M J'
    have hm := ((_root_.GlobalTheory.GaugeFrameBasis.frame_basis F E σ (AF F) M J J' P hJ').2 e' he').1.measurable
    rw [Measure.map_smul _ hm.aemeasurable, hmap e' he', hJ', hαinv M J P hJ]
  · intro M J J' x β B hM hJ hβ hx hB' hJ'' hJ'
    have hS : StepData σ J x β B J' := ⟨hJ, hβ, hx, hB', hJ'', hJ'⟩
    obtain ⟨ν, hν, -⟩ := _root_.GlobalTheory.GaugeEx.existsUnique_isStdX F E σ hσ _ _ s (M + 1) J β hM hJ hβ
    obtain ⟨e, he, -⟩ := (_root_.GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) M J x β B J' hS).2.1
    refine ⟨⟨ψ, hψ⟩, fun ψ' hψ' => ?_⟩
    have hX := hκ (M + 1) J β ψ' ν (by omega) hJ hβ hψ' hν
    refine ⟨⟨_, (hX _).2 rfl⟩, fun νX hνX => ?_⟩
    rw [(hX νX).1 hνX]
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    have hc := isCompatible_smul (hstep M J x β B J' (by omega) hS ν hν e' he') (K M) (κ (M + 1))
    convert hc using 1
    · show ((K (M + 1) * α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) = _
      rw [smul_smul, hKs, mul_assoc]
    · show ((K M * α M J' : ℝ≥0) • G.μ M J').map e'.symm = _
      have hm := ((_root_.GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) M J x β B J' hS).2.2 e' he').2.measurable
      simp only [Measure.map_smul _ hm.aemeasurable, smul_smul]

end GlobalTheory.GaugeEx


open Formalism.BasicNotions Formalism.MainNotions.G in
theorem GlobalTheory.GaugeEx.exists_isGauge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ G : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.GaugeFam F E cm.sig, G.IsGauge := by
  intro F E _ _ _ _ _ _ cm
  have hσ : IsCMExt F E cm.sig :=
    ⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩
  exact exists_isGauge_of_isCMExt hσ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlock
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.QuotDual

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K]

abbrev restBlock (k : ι → ℕ) (τ : ι) (g : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (g τ).submatrix Subtype.val Subtype.val

theorem restBlock_mul {O : Subring K} (τ : ι) (g : Mat m K) {h : Mat m K} (hh : Par k O h) :
    restBlock k τ (g * h) = restBlock k τ g * restBlock k τ h := by
  ext i j
  simp only [Matrix.submatrix_apply, Pi.mul_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin (m τ) => k τ ≤ (l : ℕ)) (by simp)
    (fun l => g τ i.1 l * h τ l j.1)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_).symm
  have hl' : (l : ℕ) < k τ := by simpa using hl
  have hj := j.2
  rw [(hh τ).2.2.2 l j.1 hl' (by show (l : ℕ) < j.1; omega), mul_zero]

theorem restBlock_one (τ : ι) : restBlock k τ (1 : Mat m K) = 1 :=
  Matrix.submatrix_one _ Subtype.val_injective

theorem restBlock_inv_mul {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    restBlock k τ g⁻¹ * restBlock k τ g = 1 := by
  rw [← restBlock_mul τ _ hg, Mat.inv_mul hg.det_ne, restBlock_one]

theorem restBlock_inv {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    (restBlock k τ g)⁻¹ = restBlock k τ g⁻¹ :=
  Matrix.inv_eq_left_inv (restBlock_inv_mul τ hg)

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem span_mul_le {J : Type} [Fintype J] (O : Subalgebra F Ω) (P B : Matrix J J Ω) (hP : ∀ i j, P i j ∈ O) :
    Submodule.span O (Set.range (P * B)) ≤ Submodule.span O (Set.range B) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨P i l, hP i l⟩, ?_⟩
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]

variable {M : RatModel F Ω} {S : Fr M m k} {A₀ : Mat m Ω}

theorem par_generic (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
  (Fr.mem_iff h₀).1 (Fr.mem_genericPoint hA)

theorem det_dualBlock_ne (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    (dualBlock k τ A₀ A).det ≠ 0 := by
  have h := par_generic h₀ hA
  have e := congrArg Matrix.det (restBlock_inv_mul τ h)
  rw [Matrix.det_mul, Matrix.det_one] at e
  show ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose.det ≠ 0
  rw [Matrix.det_transpose, restBlock_inv τ h]
  exact left_ne_zero_of_mul_eq_one e

theorem span_dualBlock_le (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) ≤
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  have hg := (Fr.mem_iff hA).1 hA'
  have e : A' * A₀⁻¹ = (A' * A⁻¹) * (A * A₀⁻¹) := by
    rw [← mul_assoc, mul_assoc A', Mat.inv_mul (Fr.det_ne hA), mul_one]
  have e2 : dualBlock k τ A₀ A' = (restBlock k τ (A' * A⁻¹)⁻¹).transpose * dualBlock k τ A₀ A := by
    show ((restBlock k τ (A' * A₀⁻¹))⁻¹).transpose = _ * ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose
    rw [e, restBlock_mul τ _ (par_generic h₀ hA), Matrix.mul_inv_rev, Matrix.transpose_mul, restBlock_inv τ hg]
  rw [e2]
  exact span_mul_le _ _ _ fun i j => (hg.inv τ).1 _ _

theorem span_dualBlock_eq (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) =
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) :=
  le_antisymm (span_dualBlock_le τ h₀ hA hA') (span_dualBlock_le τ h₀ hA' hA)

theorem exists_lat_dualBlock (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) :
    ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  refine ⟨⟨fun z => Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ (S.nonempty z).some)), fun z => ?_⟩,
    fun z A hA => ⟨det_dualBlock_ne τ h₀ hA, span_dualBlock_eq τ h₀ hA (S.nonempty z).some_mem⟩⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc z
  have hm : ∀ z' ∈ U, A ∈ S.S z' := fun z' hz' => (hU z' hz' A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  exact ⟨U, dualBlock k τ A₀ A, hz, det_dualBlock_ne τ h₀ (hm z hz),
    fun z' hz' => span_dualBlock_eq τ h₀ (hm z' hz') (S.nonempty z').some_mem⟩

end GlobalTheory.FlagBundle.QuotDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocEmbExist

variable {E : Type} [Field E] [NumberField E]

theorem isIntegral_or_isIntegral_inv (w : HeightOneSpectrum (𝓞 E)) (x : GlobalTheory.LocDict.Kbar w) :
    IsIntegral (w.adicCompletionIntegers E) x ∨ IsIntegral (w.adicCompletionIntegers E) x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl isIntegral_zero
  let K := w.adicCompletion E
  let L : IntermediateField K (GlobalTheory.LocDict.Kbar w) := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hy0 : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let f : L →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w := L.val.restrictScalars _
  have hf : Function.Injective f := L.val.injective
  have key : ∀ z : L, IsIntegral (w.adicCompletionIntegers E) (z : GlobalTheory.LocDict.Kbar w) ↔
      Valued.v (Algebra.norm K z) ≤ 1 := fun z => by
    rw [← GlobalTheory.CNorm.isIntegral_iff_valued_norm_le_one E w L z]
    exact isIntegral_algHom_iff f hf
  have hyx : ((y⁻¹ : L) : GlobalTheory.LocDict.Kbar w) = x⁻¹ := by simp [y]
  have hmul : Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  rcases le_total (Valued.v (Algebra.norm K y)) 1 with h | h
  · exact Or.inl ((key y).2 h)
  · right
    rw [← hyx]
    refine (key _).2 ?_
    calc Valued.v (Algebra.norm K y⁻¹) = 1 * Valued.v (Algebra.norm K y⁻¹) := (one_mul _).symm
      _ ≤ Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) := mul_le_mul' h le_rfl
      _ = 1 := hmul

def intValRing (w : HeightOneSpectrum (𝓞 E)) : ValuationSubring (GlobalTheory.LocDict.Kbar w) where
  toSubring := (integralClosure (w.adicCompletionIntegers E) (GlobalTheory.LocDict.Kbar w)).toSubring
  mem_or_inv_mem' x := isIntegral_or_isIntegral_inv w x

theorem isIntegral_algebraMap_iff (w : HeightOneSpectrum (𝓞 E)) (e : E) :
    IsIntegral (w.adicCompletionIntegers E) (algebraMap E (GlobalTheory.LocDict.Kbar w) e) ↔
      w.valuation E e ≤ 1 := by
  let K := w.adicCompletion E
  have h1 : algebraMap E (GlobalTheory.LocDict.Kbar w) e = algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) :=
    IsScalarTower.algebraMap_apply E K _ e
  let f : K →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w :=
    (IsScalarTower.toAlgHom K K (GlobalTheory.LocDict.Kbar w)).restrictScalars _
  rw [h1, show algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) = f (algebraMap E K e) from rfl,
    isIntegral_algHom_iff f f.toRingHom.injective, IsIntegrallyClosed.isIntegral_iff (K := K)]
  have hv : Valued.v (algebraMap E K e) = w.valuation E e :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
  constructor
  · rintro ⟨y, hy⟩
    have h := y.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    change Valued.v (y : K) ≤ 1 at h
    rw [show (y : K) = algebraMap E K e from hy, hv] at h
    exact h
  · intro h
    refine ⟨⟨algebraMap E K e, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv]
    exact h

theorem valuation_lt_one_iff_of_mem_iff {Ω : Type} [Field Ω] [Algebra E Ω] (B : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (hB : ∀ e : E, algebraMap E Ω e ∈ B ↔ w.valuation E e ≤ 1) (e : E) :
    B.valuation (algebraMap E Ω e) < 1 ↔ w.valuation E e < 1 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have ha : algebraMap E Ω e ≠ 0 := (map_ne_zero _).2 he
  have h1 : B.valuation (algebraMap E Ω e) < 1 ↔ ¬ B.valuation (algebraMap E Ω e⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)), not_le]
  have h2 : w.valuation E e < 1 ↔ ¬ w.valuation E e⁻¹ ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 he)), not_le]
  rw [h1, h2, ValuationSubring.valuation_le_one_iff, hB]

end GlobalTheory.LocEmbExist

namespace GlobalTheory.LocDict

theorem exists_isLocEmb : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ ι : Ω →ₐ[E] Kbar w, IsLocEmb A w ι := by
  intro E Ω _ _ _ _ _ A w h
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let ι₀ : Ω →ₐ[E] Kbar w := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let A₀ : ValuationSubring Ω := (GlobalTheory.LocEmbExist.intValRing w).comap ι₀.toRingHom
  have hA₀ : ∀ z, z ∈ A₀ ↔ IsIntegral (w.adicCompletionIntegers E) (ι₀ z) := fun _ => Iff.rfl
  have hE : ∀ e : E, algebraMap E Ω e ∈ A₀ ↔ w.valuation E e ≤ 1 := fun e => by
    rw [hA₀, ι₀.commutes]
    exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff w e
  have hP : IsPlaceOver A₀ w := fun x => by
    rw [GlobalTheory.LocEmbExist.valuation_lt_one_iff_of_mem_iff A₀ w hE]
    exact w.valuation_lt_one_iff_mem (K := E) x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hP h
  refine ⟨ι₀.comp (σ.symm : Ω →ₐ[E] Ω), fun z => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA₀]
  rfl

end GlobalTheory.LocDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfIsotypicCommutingSubgroupsStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (H : ι → Type) [∀ v, Group (H v)] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (ρ : Representation ℂ G V) (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v)), Nontrivial V → (∀ v, (σ v).IsIrreducible) → (∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b)) → (∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤) → ∃ F : MultilinearMap (RingHom.id ℂ) Wv V, F ≠ 0 ∧ ∀ v (h : H v) (x : ∀ u, Wv u), ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))) := by
  intro ι _ _ G V _ _ _ H _ Wv _ _ _ ρ s σ hV hirr hcomm hspan
  have hfac : ∀ v, ∃ Φ : Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V,
      (∀ h, Φ (σ v h) = ρ (s v h)) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ (s v h))) → ∀ A, Commute T (Φ A) :=
    fun v => _root_.GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners
      (H v) (Wv v) V (σ v) (ρ.comp (s v)) (hirr v) (hspan v)
  choose Φ hΦσ hΦc using hfac
  have hΦcomm : ∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B) := by
    intro u v huv A B
    have h1 : ∀ b, Commute (ρ (s v b)) (Φ u A) := by
      intro b
      exact hΦc u _ (fun a => (hcomm v u (Ne.symm huv) b a).map ρ) A
    exact hΦc v (Φ u A) (fun b => (h1 b).symm) B
  have hnt : ∀ v, Nontrivial (Wv v) :=
    fun v => ((GlobalTheory.CuspRep.isIrreducible_iff _).1 (hirr v)).1
  have hw : ∀ v, ∃ w : Wv v, w ≠ 0 := fun v => exists_ne 0
  choose w hw0 using hw
  have hl : ∀ v, ∃ ℓ : Module.Dual ℂ (Wv v), ℓ (w v) = 1 := by
    intro v
    have hn : w v ∉ (⊥ : Submodule ℂ (Wv v)) := by simpa using hw0 v
    obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    exact ⟨(f (w v))⁻¹ • f, by simp [hf]⟩
  choose ℓ hℓ using hl
  obtain ⟨y, hy0, hy⟩ := _root_.GlobalTheory.commuting_endAlgebras_common_fixed_vector
    ι Wv V Φ w ℓ hV hℓ hΦcomm
  obtain ⟨F, hFw, hF⟩ := GlobalTheory.exists_multilinear_of_commuting_endAlgHom
    ι Wv V Φ w ℓ y hΦcomm hy
  refine ⟨F, fun h0 => hy0 ?_, fun v h x => ?_⟩
  · rw [← hFw, h0]
    rfl
  · rw [← hΦσ v h]
    exact hF v (σ v h) x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteMult

theorem topMult_and_extV_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Formalism.IndefR.RecTie.TopMultH R ∧ ∀ i t, Function.Injective (R.extV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h
  refine ⟨?_, fun i t => extV_injective R h.models.HV i t⟩
  intro t
  exact range_top R h.models.inf h.models.cX h.models.prX h.models.HX t

end GlobalTheory.DefiniteMult
end

