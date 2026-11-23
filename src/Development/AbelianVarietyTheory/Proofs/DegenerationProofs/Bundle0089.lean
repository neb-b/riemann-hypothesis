module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem spMap_factor_jK {V Ω : Type} [CommRing V] [IsDomain V] [Field Ω] (φ : V →+* Ω)
    (hi : Function.Injective φ) : ∃ r, spMap φ = r ≫ Out.jK V := by
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing V) hi), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsFractionRing.lift_algebraMap hi x).symm

theorem range_comp_ι_subset {X Y : Scheme.{0}} (U : Y.Opens) (f : X ⟶ U.toScheme) :
    Set.range (f ≫ U.ι) ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact (f x).2

theorem field_point_factor_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V) :
    (∃ r, q = r ≫ spMap (IsLocalRing.residue V)) ∨ ∃ r, q = r ≫ Out.jK V := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  by_cases h : RingHom.ker φ.hom = ⊥
  · exact Or.inr (spMap_factor_jK φ.hom ((RingHom.injective_iff_ker_eq_bot _).2 h))
  · have hp : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime _
    have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal V :=
      IsLocalRing.eq_maximalIdeal (hp.isMaximal h)
    refine Or.inl ⟨spMap (Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) φ.hom
      fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem isSemiAbelian_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (H : Over (Sp V)) [GrpObj H] [hc : IsCommMonObj H] (hs : Smooth H.hom) (hsep : IsSeparated H.hom)
    (hq : QuasiCompact H.hom)
    (h₁ : IsSemiAbelian ((Over.pullback (spMap (IsLocalRing.residue V))).obj H))
    (h₂ : IsSemiAbelian ((Over.pullback (Out.jK V)).obj H)) : IsSemiAbelian H := by
  have key : ∀ (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V), ∃ (T : Scheme.{0}) (r : Sp Ω ⟶ T) (f : T ⟶ Sp V),
      q = r ≫ f ∧ IsSemiAbelian ((Over.pullback f).obj H) := by
    intro Ω _ q
    rcases field_point_factor_dvr V Ω q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨_, r, _, hr, h₁⟩
    · exact ⟨_, r, _, hr, h₂⟩
  refine ⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩
  · obtain ⟨T, r, f, rfl, h⟩ := key K q
    have hg : GeometricallyConnected (pullback.snd H.hom f) := h.geomConnected
    rw [← (pullbackLeftPullbackSndIso H.hom f r).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K r
  · obtain ⟨T, r, f, rfl, h⟩ := key Ω q
    obtain ⟨E⟩ := h.fibres Ω r
    have : IsMonHom (pullCompIso r f H).symm.hom := inferInstanceAs (IsMonHom (pullCompIso r f H).inv)
    exact ⟨torusExtOfIso (pullCompIso r f H).symm E⟩

namespace Core

variable (C : Core)

theorem isPullback_a : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
  have h : IsPullback C.a (𝟙 _) C.G.ι (C.a ≫ C.G.ι) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using h.paste_vert C.cart

theorem isOpenImmersion_a : IsOpenImmersion C.a :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.isPullback_a.flip inferInstance

theorem range_a : Set.range C.a = C.GG.hom ⁻¹' C.U := by
  have h := C.isPullback_a
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    h.isoPullback.hom.surjective.range_comp, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

theorem isNoetherian_Z : IsNoetherian C.Z := by
  have := C.lft
  have := C.qc
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : CompactSpace C.Z := QuasiCompact.compactSpace_of_compactSpace C.π
  exact {}

theorem isNoetherian_P : IsNoetherian C.P.left := by
  have := C.isNoetherian_Z
  have := C.proper
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian C.P.hom
  have : CompactSpace C.P.left := QuasiCompact.compactSpace_of_compactSpace C.P.hom
  exact {}

theorem surjective_GG : Surjective C.GG.hom :=
  ⟨fun z => ⟨C.e z, by
    change (C.e ≫ C.G.ι ≫ C.P.hom) z = z
    rw [C.e_sec]; rfl⟩⟩

theorem nonempty_A : Nonempty C.A.left := by
  obtain ⟨z, hz⟩ := C.ne
  have := C.ab.geomConnected
  exact ⟨(C.A.hom.surjective ⟨z, hz⟩).choose⟩

theorem isIntegral_G : IsIntegral C.G.toScheme := by
  have : Nonempty C.G.toScheme := C.nonempty_A.map C.a
  exact isIntegral_of_isOpenImmersion C.G.ι

theorem flat_P : Flat (C.P.hom ≫ C.π) := by
  have := C.isNoetherian_P
  have := C.isOpenImmersion_a
  have := C.nonempty_A
  have := C.flat
  have := C.ab.smooth
  have : TopologicalSpace.NoetherianSpace C.A.left :=
    (C.a ≫ C.G.ι).isOpenEmbedding.isInducing.noetherianSpace
  have : IsDominant (C.a ≫ C.G.ι) :=
    ⟨(C.a ≫ C.G.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsSchemeTheoreticallyDominant (C.a ≫ C.G.ι) := .of_isDominant _
  have : Flat ((C.a ≫ C.G.ι) ≫ C.P.hom ≫ C.π) := by
    rw [← Category.assoc, C.cart.w]
    infer_instance
  exact flat_of_isSchemeTheoreticallyDominant
    (fun _ _ inst h => (@Module.Flat.flat_iff_torsion_eq_bot_of_isBezout ℤ _ _ _ inst.toModule _ _).mpr h)
    (C.a ≫ C.G.ι) _

variable {C} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)


include τ in
theorem Test.cl : C.Cl y := by
  have hi : Function.Injective ((OO p).subtype.comp τ.j) := (OO p).subtype_injective.comp τ.j_inj
  obtain ⟨r, hr⟩ := spMap_factor_jK _ hi
  have e : gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := (Spec.map_comp _ _).symm.trans hr
  have e' : gPt p ≫ y = (r ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold Cl
  rw [e']
  exact range_comp_ι_subset _ _

theorem Test.charZero : CharZero τ.V :=
  RingHom.charZero ((OO p).subtype.comp τ.j)

theorem Test.isSemiAbelian : IsSemiAbelian τ.H := by
  obtain ⟨S, hS⟩ := τ.split
  have := τ.smooth
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact isSemiAbelian_of_fibres_dvr τ.V τ.H (SmoothOfRelativeDimension.smooth C.g _) τ.sep τ.qc
    (isSemiAbelian_of_isGt _ S _ hS)
    (isSemiAbelian_of_isAbelianScheme _ (PolPull.isAbelianScheme_of_isGrpPullback C.ab τ.φ_cart))

end Core

theorem core_basic : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  intro C
  have := C.proper
  have := C.isNoetherian_P
  have := C.flat_P
  have := C.surjective_GG
  have : TopologicalSpace.NoetherianSpace C.G.toScheme := C.G.ι.isOpenEmbedding.isInducing.noetherianSpace
  refine ⟨inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom)), C.isIntegral_G, ?_, C.flat_P, C.isOpenImmersion_a,
    C.isPullback_a, C.range_a, C.isNoetherian_Z, C.isNoetherian_P, inferInstance,
    fun p _ y τ => ⟨τ.cl, τ.charZero, τ.isSemiAbelian⟩⟩
  change Flat ((C.G.ι ≫ C.P.hom) ≫ C.π)
  rw [Category.assoc]
  infer_instance

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinatesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSections_proportional_of_coordinates : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ) (I J : Type) [Fintype J] (t : I → SecA A F k) (s : J → SecA A F k) (b : Matrix I J F), (∀ x : TFK (R := R) F ⟶ A.A, ∃ v : J → F, b.mulVec v ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) s (show Sp F ⟶ _ from (ptSecT A.A x).left) v ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A x).left) (b.mulVec v)) → ∃ c : F, ∀ i, ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j) = kf R F c • SecM.ofSec A.A (t i) := by
  first | exact @GlobalTheory.ZH.SecProp.proportional_of_crd | exact GlobalTheory.ZH.SecProp.proportional_of_crd | (intros; apply GlobalTheory.ZH.SecProp.proportional_of_crd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionAbelianPartBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.VeryAmpleMove

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

theorem immBy_pull {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (ψ : Y ⟶ X) [IsIso ψ] (hq : ψ ≫ p = q) {L : LB X} {M : LB Y}
    (hL : L.IsLB) (hM : M.IsLB) (H : LBIso M (L.pull ψ)) {J : Type} (s : J → L.Sec) (J₀ : Set J)
    (hs : ImmBy p L s J₀) : ∃ t : J → M.Sec, ImmBy q M t J₀ := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨hcov, hs⟩ := hs
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hL hM (s i)
  have loc : ∀ i, Out.nonzeroLocus (s' i) = ψ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hM y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨s', ?_, fun i hi => ?_⟩
  · simp only [loc]
    rw [← Scheme.Hom.preimage_top ψ, ← hcov]
    simp only [Scheme.Hom.preimage_iSup]
  obtain ⟨haff, r, hr, hsurj⟩ := hs i hi
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hL (ψ y)
    have hm : ψ y ∈ Out.nonzeroLocus (s i) ⊓ L.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have hsur := VeryAmpleCharts.appLE_surjective (ψ := ψ) _ _ (loc i)
    have hc : ∀ a, (ψ.appLE _ _ (loc i).le).hom (constFn p (Out.nonzeroLocus (s i)) a) =
        constFn q (Out.nonzeroLocus (s' i)) a := fun a => by
      subst hq
      unfold constFn
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
      erw [Scheme.Hom.appLE_comp_appLE]
    have e := congrArg (Subring.map (ψ.appLE _ _ (loc i).le).hom) hsurj
    rw [RingHom.map_closure, ← RingHom.range_eq_map, RingHom.range_eq_top.2 hsur, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at e
    rw [← e]
    congr 2
    exact congrArg Set.range (funext fun a => (hc a).symm)

theorem immBy_lbPow (hA : Out.AmpleSt) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ)
    (hN : 4 ≤ N) : ∃ (m : ℕ) (s : Fin m → (lbPow P.L N).Sec), ImmBy P.A.hom (lbPow P.L N) s Set.univ := by
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hA K P N hN
  refine ⟨m + 1, s, by simpa using hcov, fun i _ => ?_⟩
  obtain ⟨haff, r, hr, hf⟩ := hs i
  refine ⟨haff, r, hr, top_le_iff.1 fun f _ => ?_⟩
  obtain ⟨F, rfl⟩ := hf f
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  | add F G hF hG =>
    rw [MvPolynomial.eval₂_add]
    exact add_mem (hF trivial) (hG trivial)
  | mul_X F j hF =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem (hF trivial) (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

theorem exists_immBy_abelianPart : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∃ (m : ℕ) (t : Fin m → Φ.N₀.Sec), ImmBy Φ.E.B.hom Φ.N₀ t Set.univ) := by
  intro hL _ k _ _ Φ N hN P
  obtain ⟨m, s, hs⟩ := immBy_lbPow hL.ample k P.PB N hN
  have : IsIso P.β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.β.hom))
  obtain ⟨t, ht⟩ := immBy_pull P.β.hom.left (Over.w P.β.hom) (DVR.linComb_isLB _ P.PB.isLB _ _) Φ.isLB P.w₀ s _ hs
  exact ⟨m, t, ht⟩

end GlobalTheory.VeryAmpleMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_normalised_mulByN_iso : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  first | exact @GlobalTheory.ZH.MulExtend.exists_gen_mulRel | exact GlobalTheory.ZH.MulExtend.exists_gen_mulRel | (intros; apply GlobalTheory.ZH.MulExtend.exists_gen_mulRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_sections_from_integral_model : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  first | exact @GlobalTheory.ZH.IntegralCarry.exists_carry | exact GlobalTheory.ZH.IntegralCarry.exists_carry | (intros; apply GlobalTheory.ZH.IntegralCarry.exists_carry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitTheta

theorem exists_pull_one {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (θ : LB.Sec L) :
    ∃ th : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval th ρ z J = gs (ρ ≫ f) z _ (θ.f (J (ρ ≫ f))) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤ f ⁻¹ᵁ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  let u : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) := fun j =>
    (Y.presheaf.map (homOfLE (le j)).op).hom ((f.app _).hom (θ.f (j 0)))
  have hu : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) j, ρ z ∈ LB.wchart L (fun _ : Fin 1 => f) j →
      gs ρ z _ (u j) = gs (ρ ≫ f) z _ (θ.f (j 0)) := fun Z ρ z j h =>
    (gs_res ρ z _ h _).trans (gs_pull ρ f z _ (le j h) _)
  refine ⟨⟨u, fun j j' => fn_ext fun y hy => ?_⟩, fun Z ρ z J hJ => hu Z ρ z _ (hJ.mem (fun _ : Fin 1 => f) ρ)⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val
      (gm_linComb L (fun _ : Fin 1 => f) (fun _ => 1) (𝟙 Y) y j j' hy.1 hy.2))) (gs_res (𝟙 Y) y _ hy _))).symm)
  rw [Fin.prod_univ_one, zpow_one]
  exact (hu _ (𝟙 Y) y j hy.1).trans ((gs_compat θ (𝟙 Y ≫ f) y (le j hy.1) (le j' hy.2)).trans
    (congrArg (_ * ·) (hu _ (𝟙 Y) y j' hy.2).symm))

theorem exists_good_point_of_sec : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  intro hB hG S P θ κ _ _ r n hn hκ ⟨z, hz, p, hp⟩ b
  obtain ⟨th, hth⟩ := exists_pull_one P.L (snd (Over.mk r) P.A).left θ
  have hne : SecM.ofSec P.A (a := 1) (T := Over.mk r) th ≠ 0 := fun e => by
    obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback r P.A.hom) p z hp
    let y' : (Over.mk r ⊗ P.A).left := y
    obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB y' (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
    have h₁ : (𝟙 _ ≫ (snd (Over.mk r) P.A).left) y' ∈ nonzeroLocus θ := by
      rw [Category.id_comp]; exact hy ▸ hz
    have h₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ y' (hJ _)).1 h₁
    rw [← hth _ _ y' J hJ] at h₂
    have h₃ : th.f (fun _ => J (𝟙 _ ≫ (snd (Over.mk r) P.A).left)) = 0 :=
      congrArg (fun s : SecM P.A P.L 1 (Over.mk r) => s.1 _) e
    rw [sval, h₃] at h₂
    exact not_isUnit_zero ((congrArg IsUnit (GlobalTheory.UT.ExactTerm.gs_zero' _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk r) P.A).left) (𝟙 _)))).mp h₂)
  obtain ⟨x, hx, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hG hB P r hn hκ th hne b
  refine ⟨x, hx, fun q _ => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h₁ : IsUnit (sval th (ptSecT P.A (b * x)).left q J) := hu q J hJ
  have e : (ptSecT P.A (b * x)).left ≫ (snd (Over.mk r) P.A).left = (b * x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [hth _ _ q J hJ, e] at h₁
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ q (hJ _)).2 h₁

end GlobalTheory.UnitTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem exists_projBundle_closure : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  intro o Ω _ _ _ _ M Ω' _ _ φ J _ EE s hM ⟨j₀, hj₀⟩ hs
  obtain ⟨n, t, e, m, v, ht, hv⟩ := GlobalTheory.T.exists_projective_lattice_twist_generated o Ω M hM J EE
  obtain ⟨i₀, hi₀⟩ := ht.1 (genericPoint M.Z)
  obtain ⟨k₀, hk₀⟩ : ∃ k, pairing φ s (v k) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨c, hc⟩ := EE.exists_eq_sum_pairing (φ := φ) s (hv _ i₀ hi₀) j₀
    exact hj₀ (by simp [hc, pairing_div, h])
  let τ : Fin (n + 1) × Fin m → Ω' := fun q => φ (t q.1) * pairing φ s (v q.2)
  have hφ0 : φ (t i₀) ≠ 0 := (map_ne_zero φ).2 hi₀.1
  have hτ0 : τ (i₀, k₀) ≠ 0 := mul_ne_zero hφ0 hk₀
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (Fin (n + 1) × Fin m) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨(i₀, k₀)⟩).ne'
  let ε : Fin (N + 1) ≃ Fin (n + 1) × Fin m := (Fintype.equivFinOfCardEq hN).symm
  obtain ⟨M', hcl, hproj⟩ := exists_isCl_isProjOver o Ω' N (fun l => τ (ε l)) ⟨ε.symm (i₀, k₀), by simpa using hτ0⟩ (by
    set K := Subfield.closure (Set.range (algebraMap o Ω') ∪ {x | ∃ i j, x = τ (ε j) / τ (ε i)})
    have hK : ∀ q, τ q / τ (i₀, k₀) ∈ K := fun q =>
      Subfield.subset_closure (Or.inr ⟨ε.symm (i₀, k₀), ε.symm q, by simp⟩)
    obtain ⟨V, hV, hD, hR⟩ := ht.2 i₀ hi₀.1
    have h1 : ∀ x, φ x ∈ K := map_mem_of_ringOn hV ⟨genericPoint M.Z, hD ▸ hi₀⟩ fun x hx => by
      rw [hR] at hx
      induction hx using Algebra.adjoin_induction with
      | mem _ h =>
        obtain ⟨i, rfl⟩ := h
        simpa [τ, mul_div_mul_right _ _ hk₀] using hK (i, k₀)
      | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, (φ.commutes r).symm⟩)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    refine EE.eq_top_of_pairing_mem hs (hv _ i₀ hi₀) hk₀ h1 fun k => ?_
    rw [pairing_div, mul_div_assoc]
    exact mul_mem (inv_mem (h1 _)) (by simpa [τ, mul_div_mul_left _ _ hφ0] using hK (i₀, k)))
  have hd : ∀ z, ∃ i k, M'.Div (fun i => φ (t i)) i z ∧ M'.Div (fun k => pairing φ s (v k)) k z := fun z => by
    obtain ⟨l, hl⟩ := hcl.1 z
    exact ⟨(ε l).1, (ε l).2, div_mul_prod_iff.1 ((div_comp_iff ε.surjective).1 hl)⟩
  obtain ⟨f, hf⟩ := ht.exists_isHom (M' := M') (φ := φ) fun z => (hd z).imp fun _ h => h.choose_spec.1
  refine ⟨M', f, hf, hproj, fun W B hW hne hB => ?_⟩
  exact charts_of_universal EE hs ht.1 hv hf (fun z => (hd z).choose_spec.imp fun _ h => h.2)
    (fun N' hN' => hcl.exists_isHom fun z => by
      obtain ⟨q, hq⟩ := hN' z
      obtain ⟨l, rfl⟩ := ε.surjective q
      exact ⟨l, (div_comp_iff (t := τ) ε.surjective).2 hq⟩) W B hW hne hB

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBasesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secOn_power_of_local_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  first | exact @GlobalTheory.ZH.exists_secOn_genVal_of_bases | exact GlobalTheory.ZH.exists_secOn_genVal_of_bases | (intros; apply GlobalTheory.ZH.exists_secOn_genVal_of_bases <;> assumption)
end

