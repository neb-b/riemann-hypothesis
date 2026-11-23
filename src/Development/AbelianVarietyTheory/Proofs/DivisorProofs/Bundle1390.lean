module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormula
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mixTop_slot_smul_sub_sub {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (A B D : _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r) (s : ℂ) (j : Fin n) :
    _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (s • (A - B) - D) B j) =
      s * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (A - B) B j) +
        (-1) * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A D B j) := by
  rw [← _root_.GlobalTheory.GoodTop.mixTop_position_linear, neg_one_smul, ← sub_eq_add_neg]


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integral_cutTop_sub : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) = ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  have hstokes := _root_.GlobalTheory.GoodTop.integral_mixTop_position_eq_zero S U K G₀ G₁ ρ c hU hK hKU
    hS hG₀ hG₁ hconn hcurv hρ hρK
  have hF₁ := _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hF₀ := (_root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth U K G₀ ρ hU hK hKU hG₀ hρ
    hρK).mono_set (fun v hv => ((mem_offHyp_iff (S := S)).1 hv).1)
  have hT := _root_.GlobalTheory.GoodTop.integrableOn_corrC S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hpt : ∀ v, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v =
      ∑ j, _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ v)
        ((ρ v : ℂ) • (_root_.GlobalTheory.GoodTop.curvAt G₁ v - _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
          _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ v) (_root_.GlobalTheory.GoodTop.curvAt G₀ v) j) := by
    intro v
    simp_rw [mixTop_slot_smul_sub_sub]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      _root_.GlobalTheory.GoodTop.sum_mixTop_position_sub]
    unfold _root_.GlobalTheory.GoodTop.corrC
    ring
  have hzero : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun j _ => (hstokes j).1]
    exact Finset.sum_eq_zero fun j _ => (hstokes j).2
  have hsplit : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) =
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
    have hsub : IntegrableOn (fun v =>
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v))
        (_root_.GlobalTheory.GoodTop.offHyp S U) := hF₁.sub hF₀
    exact (integral_sub hsub hT).trans (congrArg (· - _) (integral_sub hF₁ hF₀))
  rw [← setIntegral_congr_set (_root_.GlobalTheory.GoodTop.offHyp_ae_eq S U)]
  linear_combination hzero - hsplit

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureProdOfAddGroups
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

theorem isIsogDeg_of_isFinite_of_finrank_origin :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (φ : A ⟶ A), IsMonHom φ → IsFinite φ.left → ∀ d : ℕ,
    φ.left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) = d →
    GlobalTheory.IwLevel.IsIsogDeg φ d := by
  intro k _ _ A _ hA φ _ hfin d hd
  obtain ⟨hflat, hsurj⟩ := GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A hA φ inferInstance hfin
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have : LocallyOfFinitePresentation (φ.left ≫ A.hom) := by
    rw [Over.w]; infer_instance
  have := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp φ.left A.hom
  refine ⟨hfin, hflat, hsurj, fun y => ?_⟩
  rw [← hd]
  exact (Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace y _

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.AdeleUnitModule

open scoped Pointwise ENNReal

theorem map_smul_eq_inv_smul {G A : Type} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [ContinuousConstSMul G A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (g : G) :
    μ.map (fun x => g • x) = ((distribHaarChar A g : ℝ≥0∞))⁻¹ • μ := by
  have h1 : DomMulAct.mk g⁻¹ • μ = μ.map (fun x => g • x) := by
    ext s hs
    rw [Measure.domSMul_apply, Measure.map_apply (measurable_const_smul g) hs, Set.preimage_smul]
    simp
  have h2 := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk g⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ g⁻¹, map_inv (distribHaarChar A)] at h2
  rw [← h1, h2, ENNReal.smul_def, ENNReal.coe_inv (distribHaarChar_pos).ne']

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

theorem distribHaarChar_eq_absE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [SecondCountableTopology (AE F E)] [T2Space (AE F E)]
    (t : (AE F E)ˣ) : distribHaarChar (AE F E) t = absE F E t := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  let φ : AE F E ≃ₜ+ AdeleRing (𝓞 E) E :=
    { (adeleTensorAlgEquivLeft F E).toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearMap }
  haveI : SecondCountableTopology (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.secondCountableTopology
  haveI : T2Space (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.isEmbedding.t2Space
  have h1 : distribHaarChar (AdeleRing (𝓞 E) E) (GlobalTheory.IdeleLogHom.toE F E t) = distribHaarChar (AE F E) t :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport φ t (GlobalTheory.IdeleLogHom.toE F E t) (fun x => by
      change adeleTensorAlgEquivLeft F E ((t : AE F E) * x) = _
      rw [map_mul]
      rfl)
  apply NNReal.eq
  rw [← h1, GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.IdeleLogHom.absE_eq_ideleModule]

theorem map_mul_eq_absE_inv_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ [MeasurableSpace (AE F E)] [BorelSpace (AE F E)] (ν : Measure (AE F E)), ν.IsAddHaarMeasure →
  ∀ t : (AE F E)ˣ, ν.map (fun x => (t : AE F E) * x) = ((absE F E t : ENNReal))⁻¹ • ν := by
  intro F E _ _ _ _ _ σ _ _ _ ν _ t
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have h := map_smul_eq_inv_smul ν t
  rw [distribHaarChar_eq_absE] at h
  exact h

end GlobalTheory.AdeleUnitModule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFormsEquicontinuousOnBand
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Pointwise

namespace GlobalTheory.HCF.Equi

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL' : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf')

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absDetA_eq (g : GA E a) :
    absDetA g = (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) := by
  unfold absDetA
  exact GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) _


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  rw [absDetA_eq, absDetA_eq, absDetA_eq, map_mul, map_mul, Positive.val_mul]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_absDetA : Continuous (absDetA (E := E) (a := a)) := by
  have e : (absDetA (E := E) (a := a)) =
      fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GroundTheory.Automorphic.AdelicGLn.det E a g) : ℝ) :=
    funext absDetA_eq
  rw [e]
  exact continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp
    (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))

theorem continuous_along (ψ : Sm E a) (g : GA E a) : Continuous fun z : GL (Fin a) (Cinf E) => ψ.1 (g * infGL E a z) := by
  have h := (ψ.2 g).continuousOn
  have h2 : Continuous fun z : GL (Fin a) (Cinf E) => chart ψ.1 g (toL z.val) :=
    h.comp_continuous (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)) : _) fun z => val_mem_invSet z
  exact h2.congr fun z => chart_val ψ.1 g z

theorem equicontinuous_band : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ),
    FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ U ∈ 𝓝 (1 : GA E a), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ g ∈ band E a, ∀ u ∈ U, g * u ∈ band E a → ‖φ.1 (g * u) - φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin a) (Cinf E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  set μ : Measure (GL (Fin a) (Cinf E)) := Measure.haar
  obtain ⟨α, hαc, hαs, hα⟩ := _root_.GlobalTheory.HCAlphaGL.exists_alpha E a L hL W hW X hX N μ inferInstance
  have hint : ∀ (ψ : Sm E a) (g : GA E a), Integrable (fun y => ψ.1 (g * infGL E a y) * α y) μ := fun ψ g =>
    ((continuous_along ψ g).mul hαc).integrable_of_hasCompactSupport hαs.mul_left

  have hrep : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g,
      ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hα x hx
    | zero => intro g; change ∫ z, (0 : ℂ) * α z ∂μ = 0; simp
    | add x y _ _ hx hy =>
      intro g
      change ∫ z, (x.1 (g * infGL E a z) + y.1 (g * infGL E a z)) * α z ∂μ = x.1 g + y.1 g
      simp_rw [add_mul]
      rw [integral_add (hint x g) (hint y g), hx, hy]
    | smul c x _ hx =>
      intro g
      change ∫ z, (c * x.1 (g * infGL E a z)) * α z ∂μ = c * x.1 g
      simp_rw [mul_assoc]
      rw [integral_const_mul, hx]

  have hfix : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ k ∈ L, ∀ x, φ.1 (x * finGL E a k) = φ.1 x := by
    intro φ hφ k hk x
    induction hφ using Submodule.span_induction with
    | mem ψ hψ => exact congrArg (fun f : Sm E a => f.1 x) (hψ.2.1 k hk)
    | zero => rfl
    | add ψ χ _ _ h1 h2 =>
      change ψ.1 (x * finGL E a k) + χ.1 (x * finGL E a k) = ψ.1 x + χ.1 x
      rw [h1, h2]
    | smul c ψ _ h =>
      change c * ψ.1 (x * finGL E a k) = c * ψ.1 x
      rw [h]

  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GL (Fin a) (Cinf E))
  have hKc : IsCompact (tsupport α) := hαs
  set K' := V * tsupport α with hK'
  have hK'c : IsCompact K' := hVc.mul hKc
  have hK'm : MeasurableSet K' := hK'c.measurableSet

  have hfc : Continuous fun z : GL (Fin a) (Cinf E) => absDetA (infGL E a z) :=
    continuous_absDetA.comp continuous_infGL'
  obtain ⟨B₁, hB₁⟩ := hK'c.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK'c.exists_bound_of_continuousOn
    (hfc.inv₀ fun z => (absDetA_pos _).ne').continuousOn
  set c := max 1 (max B₁ B₂) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcK : ∀ z ∈ K', c⁻¹ ≤ absDetA (infGL E a z) ∧ absDetA (infGL E a z) ≤ c := by
    intro z hz
    have hp := absDetA_pos (infGL E a z)
    have h1 := hB₁ z hz
    have h2 : ‖(absDetA (infGL E a z))⁻¹‖ ≤ B₂ := hB₂ z hz
    rw [Real.norm_of_nonneg hp.le] at h1
    rw [Real.norm_of_nonneg (inv_nonneg.2 hp.le)] at h2
    refine ⟨?_, h1.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
    rw [inv_le_comm₀ (by positivity) hp]
    exact h2.trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.HCF.norm_le_of_band_wide E a L hL W hW X hX N c hc1
  set C' := |C| + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set m := μ.real K' with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ := ε / (C' * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : C' * δ * (m + 1) = ε := by rw [hδ]; field_simp

  obtain ⟨v, hv, hvK⟩ := hK'c.mem_uniformity_of_prod (f := fun p x => α (p⁻¹ * x)) (s := Set.univ) (q := 1)
    (by exact (hαc.comp (continuous_fst.inv.mul continuous_snd)).continuousOn) (Set.mem_univ _)
    (Metric.dist_mem_uniformity hδ0)
  rw [nhdsWithin_univ] at hv

  refine ⟨{u | Matrix.GeneralLinearGroup.map (pInf E) u ∈ v ∩ V ∧ Matrix.GeneralLinearGroup.map (pFin E) u ∈ L}, ?_, ?_⟩
  · change ((Matrix.GeneralLinearGroup.map (pInf E)) ⁻¹' (v ∩ V) ∩
      (Matrix.GeneralLinearGroup.map (pFin E)) ⁻¹' (L : Set _)) ∈ 𝓝 (1 : GA E a)
    refine Filter.inter_mem ?_ ?_
    · exact continuous_mapInf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact Filter.inter_mem hv hV1)
    · exact continuous_mapFin.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hL.mem_nhds L.one_mem)
  intro φ hφ M hM g hg u hu _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 one_mem_band)
  set y := Matrix.GeneralLinearGroup.map (pInf E) u with hy
  set k := Matrix.GeneralLinearGroup.map (pFin E) u with hk
  have hyv : y ∈ v := hu.1.1
  have hyV : y ∈ V := hu.1.2
  have hkL : k ∈ L := hu.2
  have hgu : φ.1 (g * u) = φ.1 (g * infGL E a y) := by
    rw [← infGL_mul_finGL u, ← mul_assoc, hfix φ hφ k hkL]
  rw [hgu]

  have e1 : φ.1 (g * infGL E a y) = ∫ z, φ.1 (g * infGL E a z) * α (y⁻¹ * z) ∂μ := by
    rw [← hrep φ hφ (g * infGL E a y),
      ← integral_mul_left_eq_self (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) y]
    congr 1
    funext x
    simp [map_mul, mul_assoc]
  have hi1 : Integrable (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) μ :=
    ((continuous_along φ g).mul (hαc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hαs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)))
  have e2 : φ.1 (g * infGL E a y) - φ.1 g = ∫ z, φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z) ∂μ := by
    rw [e1, ← hrep φ hφ g, ← integral_sub hi1 (hint φ g)]
    simp_rw [mul_sub]
  rw [e2]

  have hpt : ∀ z, ‖φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z)‖ ≤ K'.indicator (fun _ => C' * M * δ) z := by
    intro z
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, norm_mul]
      have hd := hcK z hz
      have hg' := hg
      obtain ⟨hg1, hg2⟩ := hg'
      have hb1 : c⁻¹ ≤ absDetA (g * infGL E a z) := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have hb2 : absDetA (g * infGL E a z) ≤ 2 * c := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have h1 : ‖φ.1 (g * infGL E a z)‖ ≤ C' * M :=
        (hC φ hφ M hM _ hb1 hb2).trans (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_abs_self C]) hM0)
      have h2 : ‖α (y⁻¹ * z) - α z‖ ≤ δ := by
        have := hvK y hyv z hz
        simp only [inv_one, one_mul, Set.mem_setOf_eq] at this
        rw [← dist_eq_norm]; exact this.le
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hz]
      have hz1 : α z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz ⟨1, mem_of_mem_nhds hV1, z, h, one_mul z⟩
      have hz2 : α (y⁻¹ * z) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hz ⟨y, hyV, y⁻¹ * z, h, mul_inv_cancel_left y z⟩
      simp [hz1, hz2]
  have hint' : Integrable (K'.indicator (fun _ => C' * M * δ)) μ :=
    (integrableOn_const (C := C' * M * δ) hK'c.measure_lt_top.ne).integrable_indicator hK'm
  refine (norm_integral_le_of_norm_le hint' (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_indicator_const _ hK'm, smul_eq_mul, ← hm]
  have : 0 ≤ C' * M * δ := by positivity
  calc m * (C' * M * δ) ≤ (m + 1) * (C' * M * δ) := by nlinarith
    _ = ε * M := by rw [← hδe]; ring

end GlobalTheory.HCF.Equi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixPreservesFormStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_matrix_preserves_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), hA σ J x x = 0 → hA σ J u x = 0 → c - cA σ c = -hA σ J u u → (nmat σ J x u c)ᵀ * incM F J * (nmat σ J x u c).map (cA σ) = incM F J := by
  first | exact @GlobalTheory.UnipMass.nmat_unitary | exact GlobalTheory.UnipMass.nmat_unitary | (intros; apply GlobalTheory.UnipMass.nmat_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTrStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  first | exact @GlobalTheory.ArchRhoPure.rho_pureA_schrF | exact GlobalTheory.ArchRhoPure.rho_pureA_schrF | (intros; apply GlobalTheory.ArchRhoPure.rho_pureA_schrF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_space_add_signature_exists : ∀ (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool), A.SigOK → (∀ τ, A.sig τ = (p, q)) → ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧ ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  first | exact @GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature | exact GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature | (intros; apply GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecompositionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → form σ W.J H'.x H'.x = 0 → form σ W.J H'.y H'.y = 0 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0) → (∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) → ∀ g ∈ unip σ W H', ∃ (b : Fin d₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧ mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  first | exact @GlobalTheory.UnipMass.StdMat.unip_eq_nmat | exact GlobalTheory.UnipMass.StdMat.unip_eq_nmat | (intros; apply GlobalTheory.UnipMass.StdMat.unip_eq_nmat <;> assumption)
end

