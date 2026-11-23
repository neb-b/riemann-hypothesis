module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPerfectFreeFiniteComplex
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLocalizedIntegersIdealInField
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Bundle0001
public import GroundTheory.GlobalFields.IdeleGroups.UnitBound
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPair
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem exists_finPair : GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (V : HSp D), ∃ μ 𝓕, FinPair V μ 𝓕 := by
  intro hV D V
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
  obtain ⟨hr, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ
  exact ⟨_, 𝓕, hμ, hr, h𝓕, (GlobalTheory.CuspDecay.measure_lt_top hV V _ 𝓕 hμ h𝓕).ne⟩

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexPrimitiveLineBundleCechFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw

theorem exists_free_complex_of_primitive_cech : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ F : LB B.left, F.IsLB → (∃ u : LB.Gen (abelian₂ B F), u.IsGen) → ∀ P : Perf B.hom F, ∃ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] ((Fin P.a → A) ⧸ LinearMap.range P.D₀.transpose.mulVecLin)) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ i, (g < i ∨ ¬ Triv (F.pull π)) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (K : Type) [Field K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K] (cechLB f' (F.pull π) D).homology i) := by
  intro A _ _ _ B _ _ hB hP g hg F hF hu P
  obtain ⟨u, hu⟩ := hu
  have := hB.smooth
  have := hB.proper
  obtain ⟨H, hH, m, s, hs⟩ := id hP
  have hD := (VeryAmpleCharts.compact_quasiSeparated_isAffineOpen A _ B.hom H m s hH hs).2.2
  have hD₁ := fun i => (hs.2 i).1
  obtain ⟨C, ψ, h0, hfin, -, hproj, -, -, hq⟩ := exists_finite_projective_complex_quasiIso.{0, 0}
    (cechLB B.hom F fun i => nonzeroLocus (s i)) (Fintype.card (Fin (m + 1)))
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X B.hom hF hD)
    (cechLB_homology_finite_of_affine_cover A _ B.hom F _ _ hF inferInstance hP hD₁ hs.1)
  have hC : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i) := fun i => by
    have := hfin i
    have := hproj i
    exact ⟨Module.free_of_flat_of_isLocalRing, hfin i⟩
  refine ⟨C, hC, ⟨_, h0⟩, SecKernel.nonempty_equiv_of_model ψ hF hs.1 hD hq hC P, ?_, ?_⟩
  · intro K _ _ φ X' π f' hX i hi
    let t := Spec.map (CommRingCat.ofHom φ)
    let B' := (Over.pullback t).obj B
    have : IsCommMonObj B' := Functor.isCommMonObj_obj
    have hB' : IsAbelianScheme B' := Out.TLinPf.isAb_pullback t B hB
    have sq : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
    have hP' : IsProjBy B'.hom := isProjBy_baseChange _ _ φ _ _ _ _ _ sq hP
    have hF' := LB.isLB_pull hF (pullback.fst B.hom t)
    have ha := fun j => isAffineOpen_preimage_of_isPullback sq (hD₁ j)
    have hc := PerfOfModel.iSup_preimage (pullback.fst B.hom t) hs.1
    have hq' : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ) :=
      letI := φ.toAlgebra
      hq K
    refine (exactAt_iff_of_quasiIsoAt
      (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ ≫ (cechLBBaseChangeIso hF sq hD).hom) i).2 ?_
    rcases hi with hi | hi
    · have := isIntegral_left_of_isAbelianScheme_field B' hB'
      have := hB'.proper
      have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n := g)
      exact cechLB_exactAt_of_dim_lt K B'.left B'.hom g _
        (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) sq hg) hP' inferInstance hF' _ _ ha hc i hi
    · obtain ⟨U, ⟨c⟩⟩ := GtBaseChange.exists_lamChart t B F
      exact _root_.GlobalTheory.PrimVan.acyclic_cechLB_of_primitive K B' hB' hP' _ hF' ⟨_, GtBaseChange.genPull_isGen c hu⟩
        (fun h => hi (CubeOpen.triv_comp (hX.isoIsPullback _ _ sq).hom (hX.isoIsPullback_hom_fst _ _ sq) h))
        _ _ ha hc i
  · intro K _ φ X' π f' hX κ _ _ D hDa hDc i
    have hq' : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ) :=
      letI := φ.toAlgebra
      hq K
    let χ := ((ModuleCat.extendScalars φ).mapHomologicalComplex _).map ψ ≫ (cechLBBaseChangeIso hF hX hD).hom
    have : QuasiIso χ := inferInstance
    have e₁ := (isoOfQuasiIsoAt χ i).toLinearEquiv
    have : IsSeparated f' := MorphismProperty.of_isPullback (P := @IsSeparated) hX inferInstance
    obtain ⟨e₂⟩ := cechLB_homology_equiv_of_affine_covers K X' f' (F.pull π) (Fin (m + 1))
      (fun j => π ⁻¹ᵁ nonzeroLocus (s j)) κ D (LB.isLB_pull hF π) inferInstance
      (fun j => isAffineOpen_preimage_of_isPullback hX (hD₁ j))
      (PerfOfModel.iSup_preimage π hs.1) hDa hDc i
    exact ⟨e₁.trans e₂⟩

end GlobalTheory.AbLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLocalizedIntegersIdealInFieldStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_localized_integers_ideal_in_field : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum ℤ) (K : Set L), 0 ∈ K →
    (∀ a ∈ K, ∀ b ∈ K, a + b ∈ K) →
    (∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K) →
    (∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a)) →
    ∃ g ∈ K, ∀ a ∈ K, ∃ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) ∧ a = c * g := by
  first | (exact @GlobalTheory.LocIntPrincipal.exists_generator) | (exact GlobalTheory.LocIntPrincipal.exists_generator) | (intros; apply GlobalTheory.LocIntPrincipal.exists_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeLatticeGermSystem
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AwayOrb.Cpt
open scoped RestrictedProduct
variable {p : ℕ} [Fact p.Prime]

theorem eventually_int_of_isCompact (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ w in Filter.cofinite, ∀ x ∈ K, AfP.eval w x ∈ w.1.adicCompletionIntegers ℚ := by
  let U : Finset (AwayP p) → Set (AfP p) := fun F =>
    {f : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] |
      ∀ i, i ∉ F → f.1 i ∈ (i.1.adicCompletionIntegers ℚ : Set (i.1.adicCompletion ℚ))}
  have hU : ∀ F, IsOpen (U F) := fun F =>
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun i => i ∉ F)
  have hcov : K ⊆ ⋃ F, U F := by
    intro x _
    have hx := x.2
    rw [Filter.eventually_cofinite] at hx
    refine Set.mem_iUnion.2 ⟨hx.toFinset, fun i hi => ?_⟩
    by_contra h
    exact hi (hx.mem_toFinset.2 h)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  let S : Finset (AwayP p) := t.biUnion id
  rw [Filter.eventually_cofinite]
  refine S.finite_toSet.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨x, hxK, hxw⟩ := hw
  obtain ⟨F, hF, hxF⟩ := Set.mem_iUnion₂.1 (ht hxK)
  by_contra hwS
  exact hxw (hxF w fun hwF => hwS (Finset.mem_biUnion.2 ⟨F, hF, hwF⟩))

theorem repr_map_eval (G : HTGroup p) (w : AwayP p) (x : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr
        (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) x) i =
      AfP.eval w ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul r c =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]

theorem continuous_coord (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_coord_inv (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_sim (G : HTGroup p) :
    Continuous fun x : G.GAf => (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)

theorem continuous_sim_inv (G : HTGroup p) :
    Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)

theorem eventually_mem_intPts (G : HTGroup p) (Ω : Set G.GAf) (hΩ : IsCompact Ω) :
    ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i) ∈
        w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord_inv G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h3 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim G))
  have h4 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim_inv G))
  filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4 h hh
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e := repr_map_eval G w (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i
    have := hw1 i h hh
    rw [← e] at this
    exact this
  · have e := repr_map_eval G w ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C) i
    have := hw2 i h hh
    rw [← e] at this
    exact this
  · exact hw3 _ (Set.mem_image_of_mem _ hh)
  · exact hw4 _ (Set.mem_image_of_mem _ hh)

end GlobalTheory.AwayOrb.Cpt

theorem GlobalTheory.AwayOrb.eventually_compL_mem_intPts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf),
    IsCompact Ω → ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w :=
  fun _ _ G Ω hΩ => GlobalTheory.AwayOrb.Cpt.eventually_mem_intPts G Ω hΩ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulIsAdicIntegralInTensorBasisStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_smul_isAdicIntegralInTensorBasis : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  first | (exact @GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (exact GlobalTheory.AdicSpan.exists_int_smul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_int_smul_isIntB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlaces
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.PlaceIso

theorem denseRange_algebraMap_completion : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), DenseRange (algebraMap F w.Completion) := by
  intro F _ _ w y
  have h := InfinitePlace.Completion.denseRange_coe w y
  convert h using 2
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(WithAbs.equiv w.1).symm x, ?_⟩
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨WithAbs.equiv w.1 x, ?_⟩
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]

theorem exists_isotropic_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  intro F E _ _ _ _ _ σ hσ M J hM hJ S₁ S₂ ε hε hnc
  classical
  have key : (∃ w ∈ S₁, ∃ u : Fin M → w.Completion ⊗[F] E, u ≠ 0 ∧ hR w.Completion σ J u u = 0) ∨
      (∃ v ∈ S₂, ∃ u : Fin M → Fv F v ⊗[F] E, u ≠ 0 ∧ hR (Fv F v) σ J u u = 0) := by
    by_contra hno
    push_neg at hno
    apply hnc
    apply _root_.GlobalTheory.SUSuppCompact.isCompact_SUSupp_of_bounded F E σ hσ M J hJ S₁ S₂ ε hε
    · intro w hw
      letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
      exact _root_.GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic F E σ hσ w.Completion M J hJ (fun u hu => by
        by_contra h
        exact hno.1 w hw u h hu)
    · intro v hv
      letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
      haveI := Formalism.BasicNotions.Examples₂.LocF.proper v
      exact _root_.GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic F E σ hσ (Fv F v) M J hJ (fun u hu => by
        by_contra h
        exact hno.2 v hv u h hu)
  rcases key with ⟨w, hw, u, hu0, hu⟩ | ⟨v, hv, u, hu0, hu⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
    refine ⟨{w}, ∅, ε', Finset.singleton_subset_iff.2 hw, Finset.empty_subset _,
      Or.inl (Finset.singleton_nonempty w), hε', ?_⟩
    intro x y hx hy
    letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      _root_.GlobalTheory.PlaneNorm.exists_rational_middle_vector F E σ hσ w.Completion (denseRange_algebraMap_completion F w) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht1⟩, ⟨h2, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht2⟩⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
    refine ⟨∅, {v}, ε', Finset.empty_subset _, Finset.singleton_subset_iff.2 hv,
      Or.inr (Finset.singleton_nonempty v), hε', ?_⟩
    intro x y hx hy
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      _root_.GlobalTheory.PlaneNorm.exists_rational_middle_vector F E σ hσ (Fv F v) (HeightOneSpectrum.denseRange_algebraMap F v) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, _root_.GlobalTheory.NormFin.idem_norm_eq_of_local F E σ v ε' hε' _ ht1⟩, ⟨h2, _root_.GlobalTheory.NormFin.idem_norm_eq_of_local F E σ v ε' hε' _ ht2⟩⟩
end GlobalTheory.PlaceIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIxOfMemEigAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem exists_ix_of_mem_eigAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m), A3.fam3.Ok3 s → ∀ (x : (A3.rowI A3.A.μ0).OpIx → K) (f : (A3.A.fam.R A3.A.μ0).S.Forms), f ≠ 0 → f ∈ (A3.A.fam.R A3.A.μ0).ZHg A3.A.X → f ∈ Formalism.L2.Col.eigAt (A3.rowI A3.A.μ0).opAll x → ∃ p : A3.fam3.base3.Ix, (A3.rowI A3.A.μ0).HasRes3 p.1 x := by
  classical
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 h x f hf0 hfZ hfx
  have hB : (A3.A.fam.R A3.A.μ0).Ok s := h.ok2.what₂ A3.A.μ0
  have hD : (A3.rowI A3.A.μ0).Ok3 := h.what₂ A3.A.μ0
  have hs := (A3.rowI A3.A.μ0).splitOver_opAll hB hD

  have hfZH : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
    le_eigSum_elim (A3.A.fam.R A3.A.μ0).op (A3.rowI A3.A.μ0).opI hD.comm hs _ (by exact hfZ.1)
  have hHB : Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => x (Sum.inl i)) := by
    by_contra hn
    have hf2 : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
      Formalism.L2.Col.eigAt_le_eigSum (C := fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i))) hn hfx
    exact hf0 (Submodule.disjoint_def.1 (Formalism.L2.Col.disjoint_eigSum hD.comm fun y h1 h2 => h2 h1) f hfZH hf2)
  choose c hc using hHB
  let Sg : Pl0 → K[X] := fun P0 => if hP : ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 then c hP.choose else 1
  have hSg : ∀ P, Sg ((A3.A.fam.R A3.A.μ0).pl P) = c P := by
    intro P
    have hP : ∃ P', (A3.A.fam.R A3.A.μ0).pl P' = (A3.A.fam.R A3.A.μ0).pl P := ⟨P, rfl⟩
    simp only [Sg, dif_pos hP]
    rw [hB.pl_inj hP.choose_spec]
  let e : I0 × Ty → K := fun k0 => if hP : ∃ P, (A3.rowI A3.A.μ0).plI P = k0.1 then x (Sum.inr (hP.choose, k0.2)) else 0
  have he : ∀ (P : (A3.rowI A3.A.μ0).PlI) (y : Ty), e ((A3.rowI A3.A.μ0).plI P, y) = x (Sum.inr (P, y)) := by
    intro P y
    have hP : ∃ P', (A3.rowI A3.A.μ0).plI P' = (A3.rowI A3.A.μ0).plI P := ⟨P, rfl⟩
    simp only [e, dif_pos hP]
    rw [hD.plI_inj hP.choose_spec]
  have hres : (A3.rowI A3.A.μ0).HasRes3 (Sg, e) x := by
    refine ⟨fun P => ?_, fun k => (he k.1 k.2).symm⟩
    show _ = Sg ((A3.A.fam.R A3.A.μ0).pl P) * (A3.A.fam.R A3.A.μ0).blockProd P
    rw [hSg P, mul_comm]
    exact hc P

  set a0 := goodAt A3.A.fam.X (⊥ : Subgroup G) 1 with ha0
  have hidem : a0 * a0 = a0 :=
    (good_at_spec K A3.A.fam.v0 h.ok2.conj G A3.A.fam.X h.ok2.irr (⊥ : Subgroup G) 1).idem
  have hfix : (A3.A.fam.R A3.A.μ0).S.gaOp (A3.A.fam.R A3.A.μ0).r a0 f = f := by
    obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hfZ.2
    have hid' : a0 * goodAt A3.A.X (⊥ : Subgroup G) 1 = goodAt A3.A.X (⊥ : Subgroup G) 1 := hidem
    rw [← hg, ← BlockDat.gaOp_mul, hid']
  obtain ⟨u0, hu0⟩ := (A3.A.fam.R A3.A.μ0).exists_vE_of_fix (Lvl.full A3.A.fam.X) hfix
  have hmem : (Sg, e) ∈ (A3.rowI A3.A.μ0).ixFin3 A3.A.fam.X := by
    rw [(A3.rowI A3.A.μ0).mem_ixFin3 hD.comm]
    refine ⟨fun P0 hP0 => ?_, fun P0 hP0 y => ?_, ?_⟩
    · have hP : ¬ ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show Sg P0 = 1
      simp only [Sg, dif_neg hP]
    · have hP : ¬ ∃ P, (A3.rowI A3.A.μ0).plI P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show e (P0, y) = 0
      simp only [e, dif_neg hP]
    · intro hbot
      have hu0mem : u0 ∈ (A3.A.fam.R A3.A.μ0).inV0 (Lvl.full A3.A.fam.X) ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum (Sg, e)) := by
        rw [BlockDat.mem_goodPart_iff, hu0]
        exact Formalism.L2.Col.eigAt_le_eigSum (C := (A3.rowI A3.A.μ0).HasRes3 (Sg, e)) hres hfx
      rw [hbot, Submodule.mem_bot] at hu0mem
      apply hf0
      rw [← hu0, hu0mem, Matrix.mulVec_zero, map_zero]
  exact ⟨⟨(Sg, e), hmem⟩, hres⟩

end GlobalTheory.Div
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentation
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRep


set_option maxHeartbeats 1000000 in
theorem exists_cusp_rep : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  intro D G _ T κ i lev _ hL hW
  have hnat := fun f (hf : f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) => ((mem_cusp _ _ _ _ _ _).1 hf).1.1
  exact ⟨{ toFun := fun g => (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev g).restrict (hW g)
           map_one' := LinearMap.ext fun F => Subtype.ext
             (actL_one _ _ _ hL.total hL.func hL.one (hnat _ F.2))
           map_mul' := fun g g' => LinearMap.ext fun F => Subtype.ext
             (actL_mul _ _ _ hL.total hL.func hL.mul g g' (hnat _ F.2)) },
    fun _ _ => rfl⟩

end GlobalTheory.LevelRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisAtPrimeOfIsLatticeStatement
section
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localBasis_at_prime_of_isLattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E → ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧ ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  exact @GlobalTheory.exists_local_basis_of_isLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixAdjoinTensorUnramifiedOfCommuteSeparStatement
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrixAdjoinTensorUnramified_of_commute_separable : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r), Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := by
  first | (exact @GlobalTheory.PolyTensorCommutant.exists_phi_eq) | (exact GlobalTheory.PolyTensorCommutant.exists_phi_eq) | (intros; apply GlobalTheory.PolyTensorCommutant.exists_phi_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOneStatement
section
open Matrix GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  first | (exact @GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (exact GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (intros; apply GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumConjClasses
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_conj_classes : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  first | (exact @GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (exact GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (intros; apply GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer  <;> assumption)
end

