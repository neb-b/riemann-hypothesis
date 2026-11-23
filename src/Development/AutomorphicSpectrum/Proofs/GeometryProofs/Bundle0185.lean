module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenericFibreIntersectionPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0027

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValue
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem chart_point : ∀ (X : AlgebraicGeometry.Scheme.{0}) (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (A : Subring Ω) (T : CDVR) (evT : A →+* T.Fr) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range) → (∀ a : A, ∃ b : A, evT b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩)) → ∃ (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (h : genPt ξ ⤳ centre zV), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zV, h⟩ ∧ FinRd.Roots.ReadsPt ξ A T evT zV := by
  intro X Ω _ ξ K _ J _ y hall tie A T evT c hc hr hint hfrac
  classical
  have hx : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨U, hU, hmem⟩ := tie.affine c hx
  have hCeq : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) =
      Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) :=
    (TiePrimes.adjoin_eq hc).trans (Algebra.adjoin_range_eq_range_aeval ℤ _).symm

  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordMap.inChart_genPt tie.gen _ c hx specializes_rfl⟩
  let e : Γ(X, U) →+* Ω := (genMap ξ ⟨genPt ξ, specializes_rfl⟩).comp (X.presheaf.germ U _ hgU).hom
  have he : ∀ {p : X} (hp : p ∈ U) (t : Γ(X, U)), genMap ξ ⟨p, hall p⟩ (X.presheaf.germ U p hp t) = e t := by
    intro p hp t
    show _ = genMap ξ ⟨genPt ξ, specializes_rfl⟩ (X.presheaf.germ U _ hgU t)
    rw [RootHt.ArchC.genMap_germ U (hall p) hp t, RootHt.ArchC.genMap_germ U specializes_rfl hgU t]
  have hC : ∀ t, e t ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) := fun t => by
    rw [← hCeq]
    exact (tie.ring c hx (e t)).2 fun p hp =>
      ⟨X.presheaf.germ U p.1 ((hmem p.1).2 ⟨p.2, hp⟩) t, he _ t⟩

  let S : Subring Ω := ((algebraMap T.V T.Fr).range.comap evT).map A.subtype
  have hCS : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩), a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact ⟨⟨_, hr j.1 j.2⟩, hint j.1 j.2, rfl⟩
    | algebraMap n => simpa using intCast_mem S n
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hAm : ∀ t, e t ∈ A := fun t => by
    obtain ⟨b, -, hb⟩ := hCS _ (hC t)
    rw [← hb]
    exact b.2
  let e' : Γ(X, U) →+* A := e.codRestrict A hAm
  let ev : Γ(X, U) →+* T.Fr := evT.comp e'
  have hev : ∀ t, ev t ∈ (algebraMap T.V T.Fr).range := fun t => by
    obtain ⟨b, hb, hb'⟩ := hCS _ (hC t)
    have : b = e' t := Subtype.ext hb'
    show evT (e' t) ∈ _
    rw [← this]
    exact hb

  obtain ⟨g, hg⟩ : ∃ g : Γ(X, U) →+* T.V, (algebraMap T.V T.Fr).comp g = ev := by
    have hι : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let eV : T.V ≃+* (algebraMap T.V T.Fr).range :=
      RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
        ⟨fun a b h => hι (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    refine ⟨eV.symm.toRingHom.comp (ev.codRestrict _ hev), RingHom.ext fun t => ?_⟩
    exact congrArg Subtype.val (eV.apply_symm_apply (ev.codRestrict _ hev t))
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hcV : centre (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Spec (CommRingCat.of T.V) ⟶ X) ∈ U :=
    h0 (Set.mem_univ (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint T.V)))
  obtain ⟨hV, hinV⟩ := (hmem _).1 hcV
  refine ⟨_, hV, hinV, ?_⟩

  have hz : gen T (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) =
      Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec := by
    rw [gen, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  obtain ⟨hcz, hgerm⟩ := RootHt.ArchC.point_of_ringHom hU ev
  obtain ⟨hgz, hchz⟩ := (hmem _).1 hcz
  have hval : ∀ a : A, (a : Ω) ∈ regAt ξ ⟨_, hgz⟩ →
      ValAt ξ (Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec) (a : Ω) (evT a) := by
    intro a ha
    refine RootHt.ArchC.val_of_fractions hU hcz hgz ev hgerm ha fun t₁ t₂ h => ?_
    rw [he hcz, he hcz] at h
    have h' : a * e' t₂ = e' t₁ := Subtype.ext h
    have h'' := congrArg evT h'
    rwa [map_mul] at h''
  have hreg : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩),
      a ∈ regAt ξ ⟨_, hgz⟩ := fun a ha =>
    (tie.ring c hx a).1 (hCeq ▸ ha) _ hchz
  intro a
  rw [hz]
  refine hval a ?_
  obtain ⟨b, hb0, hbC, habC⟩ := hfrac a
  obtain ⟨h', s, hs1, hs2⟩ := hval b (hreg _ hbC)
  obtain ⟨s₂, hs₂⟩ := hreg _ habC
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' _).map_nonunit s (by
    rw [hs2]
    exact isUnit_iff_ne_zero.2 hb0)
  obtain ⟨u, rfl⟩ := hu
  have hb1 : (b : Ω) * genMap ξ ⟨_, hgz⟩ (↑u⁻¹ : X.presheaf.stalk _) = 1 := by
    rw [← hs1, ← map_mul, Units.mul_inv, map_one]
  refine ⟨s₂ * ↑u⁻¹, ?_⟩
  rw [map_mul, hs₂, _root_.mul_assoc, hb1, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrLieModelLattice
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
private theorem exists_unitary_diagonal_of_isHermitian {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X)
    (c : centre (FinRd.Roots.gen T zV) ⤳ centre zV) :
    X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV) =
      Scheme.stalkClosedPointTo zV ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
  have c' := IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) (IsLocalRing.closedPoint T.Fr))
  have e2 := Scheme.stalkClosedPointTo_comp (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) zV
  have e3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap T.V T.Fr))
  have e4 := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of T.V)
  have e4' : (stalkClosedPointIso (CommRingCat.of T.V)).inv =
      (Scheme.ΓSpecIso (CommRingCat.of T.V)).inv ≫
        (Spec (CommRingCat.of T.V)).presheaf.germ ⊤ (IsLocalRing.closedPoint _) trivial := by
    rw [← e4, Iso.inv_hom_id_assoc]
  have e6 := TopCat.Presheaf.germ_stalkSpecializes (Spec (CommRingCat.of T.V)).presheaf
    (U := ⊤) (y := IsLocalRing.closedPoint _) trivial c'
  have e5 : (Spec (CommRingCat.of T.V)).presheaf.stalkSpecializes c' ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) =
      (stalkClosedPointIso (CommRingCat.of T.V)).hom ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
    rw [← Iso.inv_comp_eq, e4', Category.assoc]
    erw [reassoc_of% e6]
    erw [e3]
    rw [Iso.inv_hom_id_assoc]
  change X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV) = _
  rw [e2]
  erw [Scheme.Hom.stalkSpecializes_stalkMap_assoc zV _ _ c']
  rw [e5, Scheme.stalkClosedPointTo, Category.assoc]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice : ∀ (X : AlgebraicGeometry.Scheme.{0}) (G : CategoryTheory.Over X) [CategoryTheory.GrpObj G] [CategoryTheory.IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (L₀ : Type) [AddCommGroup L₀] [Module Ω L₀] (M : LieModel G ξ L₀) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel G (FinRd.Roots.gen T zV) EC) (A : Subring Ω) (evT : A →+* T.Fr), IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (h : genPt ξ ⤳ centre zV), genPt ξ ⤳ centre (FinRd.Roots.gen T zV) → FinRd.Roots.ReadsPt ξ A T evT zV → ∀ (L : Lat ξ L₀) (r : ℕ) (b e : Fin r → L₀) (Tm : Matrix (Fin r) (Fin r) Ω) (w : Fin r → EC) (hT : ∀ i j, Tm i j ∈ A), L.IsFrameAt b ⟨centre zV, h⟩ → (∀ i, b i = ∑ j, Tm i j • e j) → (∀ j, M.ValAt (FinRd.Roots.gen T zV) (e j) (MC.pt (w j))) → M.fibAt L zV MC = Submodule.span T.V (Set.range fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • w j) := by
  intro X G _ _ Ω _ ξ L₀ _ _ M T zV EC _ _ _ _ MC A evT hX _ h hz hR L r b e Tm w hT hF hb hw
  obtain ⟨-, hF2⟩ := hF
  have c : centre (FinRd.Roots.gen T zV) ⤳ centre zV :=
    zV.base.hom.map_specializes (IsLocalRing.specializes_closedPoint _)
  have hK : ∀ s, (Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom
      (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) s) =
      algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom s) := by
    intro s
    have := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (exists_unitary_diagonal_of_isHermitian T zV c)) s
    first
      | exact this
      | simpa only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] using this
  have hsc : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      ∀ s : X.presheaf.stalk (centre (FinRd.Roots.gen T zV)),
        M.ValAt (FinRd.Roots.gen T zV) (genMap ξ ⟨centre (FinRd.Roots.gen T zV), hz⟩ s • x)
          (MC.pt ((Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom s • y)) := by
    intro x y hxy s
    have := LieModel.ValAt.smul hxy hz s
    rwa [← LieModel.pt_smul] at this
  have hzero : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) := by
    intro x y hxy
    have := hsc hxy 0
    rw [map_zero, zero_smul] at this
    erw [map_zero, zero_smul] at this
    exact this
  have hsum : ∀ (s : Finset (Fin r)) (f : Fin r → L₀) (g : Fin r → EC),
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) →
      (∀ j ∈ s, M.ValAt (FinRd.Roots.gen T zV) (f j) (MC.pt (g j))) →
        M.ValAt (FinRd.Roots.gen T zV) (∑ j ∈ s, f j) (MC.pt (∑ j ∈ s, g j)) := by
    intro s f g h0 hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, MC.add]
      exact LieModel.ValAt.add (hf a (Finset.mem_insert_self a s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hA : ∀ (a : A) (j : Fin r),
      M.ValAt (FinRd.Roots.gen T zV) ((a : Ω) • e j) (MC.pt (evT a • w j)) := by
    intro a j
    obtain ⟨h1, s, hs1, hs2⟩ := hR a
    have := hsc (hw j) s
    rw [hs1, hs2] at this
    exact this
  have hv : ∀ i, M.ValAt (FinRd.Roots.gen T zV) (b i)
      (MC.pt (∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
    intro i
    rw [hb i]
    exact hsum _ _ _ (hzero (hw i)) (fun j _ => hA ⟨Tm i j, hT i j⟩ j)
  unfold LieModel.fibAt
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w' ⟨h', x, hx, hxv⟩
    have hx' : x ∈ Submodule.span (regAt ξ ⟨centre zV, h⟩) (Set.range b) := by
      rw [← hF2]
      exact hx
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx'
    choose s hs using fun i => RingHom.mem_range.mp (cf i).2
    have key : M.ValAt (FinRd.Roots.gen T zV) x
        (MC.pt (∑ i, algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom (s i)) •
          ∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
      rw [← hcf]
      refine hsum _ _ _ (hzero hxv) fun i _ => ?_
      have := hsc (hv i) (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) (s i))
      rw [LieTangent.genMap_specializes ⟨centre zV, h⟩ hz c, hK, hs i] at this
      rw [Subring.smul_def]
      exact this
    have hw' := MC.inj (LieModel.ValAt.unique hX hxv key)
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨h, b i, ?_, hv i⟩
    rw [hF2]
    exact Submodule.subset_span ⟨i, rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValue
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

theorem mem_range_of_valV_le_one {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {x : K'} (h : valV V x ≤ 1) : x ∈ (algebraMap V K').range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one K' x fun v => ?_
  have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
    apply HeightOneSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal v.isMaximal
  rw [hv]
  exact h

theorem valV_algebraMap_le_one {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (a : V) : valV V (algebraMap V K' a) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ a

theorem vV_nonneg_iff {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {x : K'} (hx : x ≠ 0) : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
  have h := WithZero.log_le_log (valV_ne_zero (V := V) hx) (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0)
  rw [← h, WithZero.log_one, vV]
  omega

theorem absT_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ), 0 < e → 0 < ramOverZ la → (∀ x y : T.Fr, FinRd.absT p la T e (x * y) = FinRd.absT p la T e x * FinRd.absT p la T e y) ∧ FinRd.absT p la T e 1 = 1 ∧ (∀ x : T.Fr, x ≠ 0 → 0 < FinRd.absT p la T e x) ∧ ∀ x : T.Fr, FinRd.absT p la T e x ≤ 1 ↔ x ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H l c p _ la T e he hr
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : (0 : ℝ) < (e : ℝ) * (ramOverZ la : ℝ) := by
    have h1 : (0 : ℝ) < e := by exact_mod_cast he
    have h2 : (0 : ℝ) < (ramOverZ la : ℝ) := by exact_mod_cast hr
    exact mul_pos h1 h2
  have h0 : FinRd.absT p la T e (0 : T.Fr) = 0 := by simp [FinRd.absT]
  have hne : ∀ x : T.Fr, x ≠ 0 → FinRd.absT p la T e x =
      (p : ℝ) ^ (-((vV T.V x : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ)))) := by
    intro x hx
    simp [FinRd.absT, hx]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    by_cases hx : x = 0
    · subst hx; simp [h0]
    by_cases hy : y = 0
    · subst hy; simp [h0]
    rw [hne _ (mul_ne_zero hx hy), hne _ hx, hne _ hy, vV_mul hx hy, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  · rw [hne _ one_ne_zero]
    have : vV T.V (1 : T.Fr) = 0 := by simp [vV]
    simp [this]
  · intro x hx
    rw [hne _ hx]
    exact Real.rpow_pos_of_pos hp0 _
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [h0]
    rw [hne _ hx, ← Real.rpow_zero (p : ℝ), Real.rpow_le_rpow_left_iff hp]
    have hiff : -((vV T.V x : ℝ) / ((e : ℝ) * (ramOverZ la : ℝ))) ≤ 0 ↔ 0 ≤ vV T.V x := by
      rw [neg_nonpos, le_div_iff₀ hd, zero_mul]
      exact_mod_cast Iff.rfl
    rw [hiff, vV_nonneg_iff hx]
    constructor
    · exact mem_range_of_valV_le_one
    · rintro ⟨a, rfl⟩
      exact valV_algebraMap_le_one a

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri

theorem independent_and_triangular : ∀ (Ω : Type) [Field Ω] (L : Type) [AddCommGroup L] [Module Ω L] (r : ℕ) (b b₀ : Fin r → L) (Tm : Matrix (Fin r) (Fin r) Ω), LinearIndependent Ω b → (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) → (∀ i, b i = ∑ j, Tm i j • b₀ j) → LinearIndependent Ω b₀ ∧ ∀ i j, i < j → Tm i j = 0 := by
  intro Ω _ L _ _ r b b₀ Tm hb hflag hT
  have hspan : Submodule.span Ω (Set.range b₀) = Submodule.span Ω (Set.range b) := by
    have h := hflag r
    unfold flagStep at h
    have e1 : b₀ '' {k : Fin r | (k : ℕ) < r} = Set.range b₀ := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    have e2 : b '' {k : Fin r | (k : ℕ) < r} = Set.range b := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    rw [e1, e2] at h
    exact h.symm
  have hb₀ : LinearIndependent Ω b₀ := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range b₀))
    rw [hspan, finrank_span_eq_card hb]
  refine ⟨hb₀, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h := hflag ((i : ℕ) + 1)
    unfold flagStep at h
    rw [← h]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  obtain ⟨c, hc, hcb⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp hmem
  have hsum : ∑ k, (c k - Tm i k) • b₀ k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hT i, ← hcb, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · simp
    · intro k
      simp
  have h0 : c j - Tm i j = 0 := (Fintype.linearIndependent_iff.mp hb₀) (fun k => c k - Tm i k) hsum j
  have hcj : c j = 0 := by
    by_contra hne
    have hsupp := (Finsupp.mem_supported Ω c).mp hc
    have hj : j ∈ ({k : Fin r | (k : ℕ) < (i : ℕ) + 1} : Set (Fin r)) :=
      hsupp (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
    have hj' : (j : ℕ) < (i : ℕ) + 1 := hj
    have hij' : (i : ℕ) < (j : ℕ) := hij
    omega
  rw [hcj, zero_sub, neg_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonemptyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
theorem _root_.GlobalTheory.T.generic_points_finite_nonempty :
    _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)),
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := Comps.model_nonempty Y (Comps.moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨Comps.finite_maximal_points Y.X, Comps.nonempty_maximal_points Y.X⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open SheetDecomposition.PF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  intro II hII K _ ρ _ K' _ ρ' _ κ v P' d r G Jf L L' N hv hP' hP hJ hL hLL' hN
  have hA : IsArithVar P' (d + r + 1) := by rwa [Nat.add_right_comm] at hP'
  have hs : ∀ j, IsSmoothHerm (Fin.append L' N j) := fun j => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]
      exact GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hv (hLL' j) (hL j)
    · rw [Fin.append_right]
      exact hN j
  have h := _root_.GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula ⟨II, hII⟩ II hII.1 K ρ K' ρ' κ v P' (d + 1) r G Jf
    (Fin.snoc (α := fun _ => HermLine ρ) L (cst ρ)) (Fin.snoc (α := fun _ => HermLine ρ') L' (cst ρ')) N hv hP' hP hJ
    (LevelTowerAlt.snoc_cst_smooth L hL)
    (fun j => by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last, Fin.snoc_last]
        refine ⟨?_, fun z => rfl⟩
        show (0 : K' → ℤ) = pullDeg κ 0
        funext k
        by_cases hk : ∃ a, κ a = k
        · obtain ⟨a, rfl⟩ := hk
          exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
        · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm
      · simpa using hLL' j)
    hN
  rw [LevelTowerAlt.ii_cst_int hII.1 hP L hL, ← position_eq, ii_cast hII.1 _ hA _ (LevelTowerAlt.snoc_cst_smooth _ hs), LevelTowerAlt.ii_cst_int hII.1 hA _ hs,
    mul_neg, neg_inj] at h
  exact h
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTwoTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GenTors

theorem exists_finite_ext_torusExtension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :=
  PositivityTheory.Xgn.stratum_generic_torsion_points

end GlobalTheory.CompanionTheory.Ar.GenTors
end

