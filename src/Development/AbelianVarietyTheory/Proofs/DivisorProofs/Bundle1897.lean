module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

noncomputable section
namespace GlobalTheory.GeomIrrComp

theorem residue_germ_injective {X : Scheme.{0}} [IsReduced X] (V : X.Opens) (x : X) (hx : x ∈ V)
    (hgen : ∀ y ∈ V, x ⤳ y) : Function.Injective (X.presheaf.germ V x hx ≫ X.residue x).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro s hs
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro y hy
  have hxy := hgen y (X.basicOpen_le s hy)
  have hxb : x ∈ X.basicOpen s := hxy.mem_open (X.basicOpen s).isOpen hy
  rw [Scheme.mem_basicOpen _ _ _ hx] at hxb
  exfalso
  have := hxb.map (X.residue x).hom
  rw [CommRingCat.comp_apply] at hs
  rw [hs] at this
  exact not_isUnit_zero this

theorem residue_comp_appTop {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (x : X) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x =
      Spec.preimage (X.fromSpecResidueField x ≫ g) := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  simp only [Spec.map_comp, Category.assoc]
  rw [← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id, Scheme.fromSpecResidueField, Category.assoc]

theorem irreducibleSpace_pullback_of_isDomain {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F)
    (V : X.Opens) (hV : IsAffineOpen V) (k : Type) [Field k] (f : F →+* k) :
    letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) :=
  GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor g V hV k f

theorem irreducibleSpace_pullback_of_cover {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F)
    (k : Type) [Field k] (f : F →+* k) (U : X.Opens) (hU : IsIrreducible (U : Set X))
    (hV : ∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) :
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) :=
  _root_.GlobalTheory.irreducibleSpace_pullback_of_cover h k f U hU hV

theorem irreducibleSpace_pullback_affine {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Sp F) [LocallyOfFiniteType g] (x : X)
    (hac : letI := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
      ∀ a : X.residueField x, IsAlgebraic F a → a ∈ (algebraMap F (X.residueField x)).range)
    (V : X.Opens) (hV : IsAffineOpen V) (hx : x ∈ V) (hgen : ∀ y ∈ V, x ⤳ y)
    (k : Type) [Field k] (f : F →+* k) : IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) := by
  let φ : CommRingCat.of F ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op
  letI : Algebra F Γ(X, V) := φ.hom.toAlgebra
  letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
  letI : Algebra F k := f.toAlgebra
  have hft : Algebra.FiniteType F Γ(X, V) := by
    have h1 : (g.appLE ⊤ V le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨⊤, isAffineOpen_top (Sp F)⟩ ⟨V, hV⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2
    have e : φ = (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appLE ⊤ V le_top := by
      simp [φ, Scheme.Hom.appLE]
    have h3 : φ.hom.FiniteType := by rw [e]; exact h1.comp h2
    exact h3
  let j : Γ(X, V) →ₐ[F] X.residueField x :=
    { toRingHom := (X.presheaf.germ V x hx ≫ X.residue x).hom
      commutes' := fun c => by
        have e := congrArg (fun m => m.hom c) (residue_comp_appTop g x)
        have e2 : φ ≫ X.presheaf.germ V x hx ≫ X.residue x = (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
            g.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
          simp [φ]
        change (φ ≫ X.presheaf.germ V x hx ≫ X.residue x).hom c = _
        rw [e2]
        exact e }
  have hd := GlobalTheory.GeomConn.isDomain_tensor j (residue_germ_injective V x hx hgen) hac k
  exact irreducibleSpace_pullback_of_isDomain g V hV k f hd

theorem irreducibleSpace_pullback {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Sp F) [LocallyOfFiniteType g] (x : X)
    (hac : letI := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
      ∀ a : X.residueField x, IsAlgebraic F a → a ∈ (algebraMap F (X.residueField x)).range)
    (U : X.Opens) (hx : x ∈ U) (hgen : ∀ y ∈ U, x ⤳ y)
    (k : Type) [Field k] (f : F →+* k) : IrreducibleSpace ↑(pullback (U.ι ≫ g) (spMap f)) := by
  have hU : IsIrreducible (U : Set X) := by
    have hc : closure (U : Set X) = closure {x} := by
      apply le_antisymm
      · rw [isClosed_closure.closure_subset_iff]
        exact fun y hy => specializes_iff_mem_closure.mp (hgen y hy)
      · exact closure_mono (Set.singleton_subset_iff.mpr hx)
    rw [← isIrreducible_iff_closure, hc]
    exact isIrreducible_singleton.closure
  refine irreducibleSpace_pullback_of_cover g k f U hU fun y hy => ?_
  obtain ⟨V, hVa, hyV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hy
  refine ⟨V, hVU, hyV, irreducibleSpace_pullback_affine g x hac V hVa ((hgen y hy).mem_open V.isOpen hyV)
    (fun z hz => hgen z (hVU hz)) k f⟩

theorem algClosed_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hac : FnAlgClosed (Xo := Xo) (c := c)) (Z : Comp Xo c)
    (a : kap Z) (ha : IsAlgebraic c.F a) : a ∈ (algebraMap c.F (kap Z)).range := by
  have hb : IsAlgebraic c.F (algebraMap (kap Z) (Om Z) a) := ha.algebraMap
  obtain ⟨b, hb'⟩ := hac Z _ hb
  refine ⟨b, (algebraMap (kap Z) (Om Z)).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  exact hb'

end GlobalTheory.GeomIrrComp


open GlobalTheory.GeomIrrComp in
theorem GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), FnAlgClosed (Xo := Xo) (c := c) → ∀ Z : Comp Xo c,
    ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f)) := by
  intro E _ _ _ H Dw l Xo c hac Z
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI : Smooth (strK (Xo := Xo) (c := c)) := inferInstance
  haveI : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.isNormalScheme_of_smooth strK
  haveI : LocallyOfFiniteType (strK (Xo := Xo) (c := c)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) := LocallyOfFiniteType.isLocallyNoetherian strK
  haveI : IsReduced (Xo.XF c) := GlobalTheory.IsNormalScheme.isReduced
  refine ⟨GlobalTheory.IsNormalScheme.component Z, rfl, fun k _ f => ?_⟩
  have hZc : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hg : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) := by
    have := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  exact irreducibleSpace_pullback strK (genPt Z) (fun a ha => algClosed_kap hac Z a ha)
    (GlobalTheory.IsNormalScheme.component Z) hg.mem (fun y hy => hg.specializes hy) k f
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompLevelStab

theorem mem_iff_of_inv {X : Scheme.{0}} (Z : Set X) (hZ : IsClopen Z) (hI : IsIrreducible Z) (f g : X ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (x : X) (hx : x ∈ Z) (hfx : f.base x ∈ Z) (y : X) : f.base y ∈ Z ↔ y ∈ Z := by
  have hgf : ∀ z, g.base (f.base z) = z := fun z => by
    have := congrArg (fun h : X ⟶ X => h.base z) hfg
    simpa using this
  have A : f.base '' Z ⊆ Z :=
    (hI.image _ f.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ ⟨_, ⟨x, hx, rfl⟩, hfx⟩
  have B : g.base '' Z ⊆ Z :=
    (hI.image _ g.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ
      ⟨_, ⟨f.base x, hfx, rfl⟩, by rw [hgf]; exact hx⟩
  exact ⟨fun h => hgf y ▸ B ⟨_, h, rfl⟩, fun h => A ⟨y, h, rfl⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def mv (γ : LevelAut Dw l) : Xo.X ⟶ Xo.X := (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose

theorem mv_spec (γ : LevelAut Dw l) : ∃ ν : SABMap Xo.univ.t Xo.univ.t (mv hpq hA Xo γ),
    IsIso (mv hpq hA Xo γ) ∧ IsLevMove (mv hpq hA Xo γ) ν (liftLa γ) LinearMap.id :=
  (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose_spec

theorem x_move (c : Coeff l) (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    (move Xo c γ y).x = y.x ≫ mv hpq hA Xo γ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact (GlobalTheory.LevelActionLaws.frMove_transfer hpq hA Xo c γ i h (GlobalTheory.LevDesc.levR_move hpq hA γ y)).1

theorem mv_over (γ : LevelAut Dw l) : mv hpq hA Xo γ ≫ Xo.s = Xo.s := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact h.1

theorem mv_mul (c : Coeff l) (γ δ : LevelAut Dw l) : mv hpq hA Xo (γ * δ) = mv hpq hA Xo γ ≫ mv hpq hA Xo δ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  obtain ⟨ν', i', h'⟩ := mv_spec hpq hA Xo δ
  obtain ⟨ν₂, i₂, h₂⟩ := mv_spec hpq hA Xo (γ * δ)
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ ν ν'
  have hc : IsLevMove (mv hpq hA Xo γ ≫ mv hpq hA Xo δ) μ (liftLa (γ * δ)) LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, h'.1, h.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub γ δ a), hμ, ← Category.assoc, h.2.1,
        Category.assoc, h'.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a = (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (γ * δ) i₂ inferInstance h₂ hc).1

theorem mv_one (c : Coeff l) : mv hpq hA Xo 1 = 𝟙 Xo.X := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo 1
  obtain ⟨ι, hι, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).1
  have hc : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h hc).1

end Moves

section Base

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l) (c : Coeff l)

def mvF (γ : LevelAut Dw l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ mv hpq hA Xo γ) (pullback.snd _ _) (by
    rw [Category.assoc, mv_over, pullback.condition])

theorem mvF_fst (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ mv hpq hA Xo γ :=
  pullback.lift_fst _ _ _

theorem mvF_snd (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem mvF_mul (γ δ : LevelAut Dw l) : mvF hpq hA Xo c (γ * δ) = mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c δ := by
  apply pullback.hom_ext
  · rw [mvF_fst, Category.assoc, mvF_fst, ← Category.assoc, mvF_fst, Category.assoc, mv_mul hpq hA Xo c]
  · rw [mvF_snd, Category.assoc, mvF_snd, mvF_snd]

theorem mvF_one : mvF hpq hA Xo c 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mvF_fst, mv_one hpq hA Xo c, Category.comp_id, Category.id_comp]
  · rw [mvF_snd, Category.id_comp]

theorem mvF_inv_comp (γ : LevelAut Dw l) : mvF hpq hA Xo c γ⁻¹ ≫ mvF hpq hA Xo c γ = 𝟙 _ := by
  rw [← mvF_mul, inv_mul_cancel, mvF_one]

theorem mvF_comp_inv (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c γ⁻¹ = 𝟙 _ := by
  rw [← mvF_mul, mul_inv_cancel, mvF_one]

theorem ptF_move (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ptF (move Xo c γ y) = ptF y ≫ mvF hpq hA Xo c γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, mvF_fst, ← Category.assoc]
    simp only [ptF, pullback.lift_fst]
    exact x_move hpq hA Xo c γ y
  · rw [Category.assoc, mvF_snd]
    simp only [ptF, pullback.lift_snd]

variable (Z : Comp Xo c)

def stab : Subgroup (LevelAut Dw l) where
  carrier := {h | ∀ x, (mvF hpq hA Xo c h⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))}
  one_mem' := fun x => by rw [inv_one, mvF_one]; rfl
  mul_mem' := by
    intro a b ha hb x
    rw [Set.mem_setOf_eq] at ha hb
    rw [mul_inv_rev, mvF_mul, Scheme.Hom.comp_apply, ha, hb]
  inv_mem' := by
    intro a ha x
    rw [Set.mem_setOf_eq] at ha
    have e : (mvF hpq hA Xo c a⁻¹).base ((mvF hpq hA Xo c a).base x) = x := by
      have := congrArg (fun f : Xo.XF c ⟶ Xo.XF c => f.base x) (mvF_comp_inv hpq hA Xo c a)
      simpa using this
    rw [inv_inv, ← ha, e]

end Base

section Restrict

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

theorem mem_V₀ (x : Xo.XF c) : x ∈ Y.j ⁻¹ᵁ barComp Y Z ↔ x ∈ (Z : Set (Xo.XF c)) := j_mem_barComp Z x

theorem le_V₀ (g : LevelAut Dw l) (hg : ∀ x, (mvF hpq hA Xo c g).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))) :
    Y.j ⁻¹ᵁ barComp Y Z ≤ mvF hpq hA Xo c g ⁻¹ᵁ (Y.j ⁻¹ᵁ barComp Y Z) := fun x hx =>
  (mem_V₀ Y Z _).2 ((hg x).2 ((mem_V₀ Y Z x).1 hx))

theorem inv_mem_stab {h : LevelAut Dw l} (hh : h ∈ stab hpq hA Xo c Z) :
    ∀ x, (mvF hpq hA Xo c h).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) := by
  have h2 := (stab hpq hA Xo c Z).inv_mem hh
  change ∀ x, (mvF hpq hA Xo c h⁻¹⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) at h2
  simpa only [inv_inv] using h2

def resAut (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) : Aut (V₀ Y Z) where
  asIso :=
    { hom := (mvF hpq hA Xo c h⁻¹).resLE _ _ (le_V₀ Y Z h⁻¹ hh)
      inv := (mvF hpq hA Xo c h).resLE _ _ (le_V₀ Y Z h (inv_mem_stab Z hh))
      hom_inv_id := by
        rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
          Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_inv_comp, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
          Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_comp_inv, Category.comp_id, Category.id_comp] }

theorem resAut_ι (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) :
    (resAut Y Z h hh).asIso.hom ≫ i₀ Y Z = i₀ Y Z ≫ mvF hpq hA Xo c h⁻¹ :=
  Scheme.Hom.resLE_comp_ι _ _

def resHom (S : Subgroup (LevelAut Dw l)) : ↥(S ⊓ stab hpq hA Xo c Z) →* Aut (V₀ Y Z) :=
  MonoidHom.mk' (fun g => resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2) fun a b => by
    apply Aut.ext
    apply Iso.ext
    change (resAut Y Z (a * b).1 (Subgroup.mem_inf.1 (a * b).2).2).asIso.hom =
      (resAut Y Z b.1 (Subgroup.mem_inf.1 b.2).2).asIso.hom ≫
        (resAut Y Z a.1 (Subgroup.mem_inf.1 a.2).2).asIso.hom
    rw [← cancel_mono (i₀ Y Z), Category.assoc, resAut_ι, resAut_ι,
      ← Category.assoc, resAut_ι, Category.assoc, ← mvF_mul, Subgroup.coe_mul, mul_inv_rev]

theorem j₀_s₀ : j₀ Y Z ≫ s₀ Y Z = i₀ Y Z ≫ pullback.snd _ _ ≫ spMap (RingHom.id c.F) := by
  show j₀ Y Z ≫ (barComp Y Z).ι ≫ Y.s = _
  rw [← Category.assoc, j₀_ι, Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ,
    Y.jQ_over]

end Restrict

theorem stab_acts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  intro E _ _ _ H Dw l Xo c Y Z hpq hl S
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  refine ⟨S ⊓ stab hpq hA Xo c Z, resHom (hpq := hpq) (hA := hA) Y Z S, inf_le_left, ⟨fun g => ?_, ?_⟩, ?_⟩
  · show (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).asIso.hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z
    rw [j₀_s₀, ← Category.assoc, resAut_ι, Category.assoc, ← Category.assoc (mvF _ _ _ _ _), mvF_snd]
  · intro g R _ _ y v hv
    show v ≫ (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).asIso.hom ≫ i₀ Y Z = _
    rw [resAut_ι, ← Category.assoc, hv, ← ptF_move]
    rfl
  · intro h hS y hy hy'
    refine Subgroup.mem_inf.2 ⟨hS, ?_⟩
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h1 := hy' pt
    rw [ptF_move hpq hA Xo c, Scheme.Hom.comp_apply] at h1
    exact mem_iff_of_inv _ (TrivOrderTieCompare.isClopen_comp Z) Z.2.1 (mvF hpq hA Xo c h⁻¹) (mvF hpq hA Xo c h)
      (mvF_inv_comp hpq hA Xo c h) _ (hy pt) h1

end GlobalTheory.CompLevelStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
section
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.DefPt.ArchVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_homN_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) {ξ : ℝ} (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {G : WTZ E} (hG : G.2 = 0) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exZ Dw G)) {Z : Comp Xo c} {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ}
    (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    ∃ z ∈ framesOn U Z, homN U ξ G f z = ‖toC (evR Xo c f y)‖ := by
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ r U hU y
  refine ⟨⟨k, x.1⟩, ⟨x.2, liesOn_frBor ht hy⟩, ?_⟩
  obtain ⟨g, hg0, hgd, hchg⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := GlobalTheory.OrthoMetric.isMetric_of_isOrtho E H Dw l Xo c σ r U ξ hσ hU hpq k x (hξ k) hx
  have hm1 := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨-, hGr⟩ := GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ),
      ‖toC (t (some p) : CAt σ)‖ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
    rintro ⟨τ, i⟩
    have hs : (Real.sqrt (2 * Real.pi * ξ))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    rw [← hgd τ i, ← hs]
    exact GlobalTheory.LamT.OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _ hκ
      (fun i j hij => hg0 τ j i hij) (congrFun hGr τ).symm i
  haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hev := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ hf (CAt σ) t _ _ ht
  have hw : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = lieFacZ Dw ξ G := by
    have e : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = ∏ i, ‖toC (t i : CAt σ)‖ ^ exZ Dw G i := by
      show ‖((∏ i, (show Ix Dw → ℂˣ from t) i ^ exZ Dw G i : ℂˣ) : ℂ)‖ = _
      rw [Units.coe_prod, norm_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [Units.val_zpow_eq_zpow_val, norm_zpow]; rfl
    rw [e, Fintype.prod_option]
    simp only [hsome, exZ, hG, zpow_zero, one_mul, ← Real.rpow_intCast, ← Real.exp_mul]
    rw [← Real.exp_sum, lieFacZ, ← Finset.mul_sum, Fintype.sum_sigma]
    congr 1; ring
  have hrd : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
  rw [homN, ptN, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hx),
    hev, ← hw]
  show _ * ‖rdU U f k x.1‖ = _
  rw [hrd]
  exact (norm_mul (toC _) (toC _)).symm

theorem cInf_eq {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {ξ : ℝ} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c}
    {la : GlobalTheory.AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U ξ Z la δ) {σ : c.F →+* ℂ}
    {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ} (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    s.cInf σ = ‖toC (evR Xo c s.sig y)‖ := by
  have key : ∀ σ' : c.F →+* ℂ, goodOf c σ = σ' → ∀ y' : FrPt Xo c (CAt σ'), LiesOn Z y' →
      (GlobalTheory.LamT.IsMetric y' N fun _ => 1) → s.cInf σ = ‖toC (evR Xo c s.sig y')‖ := by
    rintro _ rfl y' hy' hN'
    have hg := goodEmb_goodOf c σ
    obtain ⟨z, hz, e⟩ := exists_homN_eq (U _) hg (hU _ hg) (hξ _ hg) hpq (G := wtOf Dw la 0) rfl s.sig_mem hy' hN'
    rw [← e, s.homN_eq hz]
  by_cases hσ : GoodEmb c σ
  · exact key σ (if_pos hσ) y hy hN
  · have hB := GlobalTheory.lawsFieldsSeparately.2.1
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (FrameNorm.conjAlg σ) y
    have hm' := GlobalTheory.LamT.isMetric_conj E H Dw l Xo c σ y y' N (fun _ => 1) hpq hy' hN
    have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
        fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hm'
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 s.sig s.sig_mem.1
      (FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
    rw [key _ (if_neg hσ) y' (liesOn_frMap hy' hy) hm', hev]
    exact Complex.norm_conj _

theorem cInf_eq_norm_div_norm_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ σ, s.cInf σ = ‖σ b‖ / ‖(P.X σ τ.1).det‖ := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b _ hb σ
  obtain ⟨-, hX, hA⟩ := P.arch σ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId c.F (CAt σ)) P.y₀
  have hu : ∀ τ', IsUnit (M := ℂ) (P.X σ τ').det := fun τ' => (hX τ').isUnit
  obtain ⟨y, hy⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (CAt σ) (fun τ' => (P.X σ τ')ᵀ) 1 z).1
    (fun τ' => show IsUnit (M := ℂ) ((P.X σ τ')ᵀ).det from (Matrix.det_transpose (P.X σ τ')).symm ▸ hu τ') isUnit_one
  have hon : LiesOn Z y := fun q => by
    have e : ptF y = ptF z := by
      apply Limits.pullback.hom_ext
      · rw [ptF, Limits.pullback.lift_fst, ptF, Limits.pullback.lift_fst, hy.1]
      · rw [ptF, Limits.pullback.lift_snd, ptF, Limits.pullback.lift_snd]
    rw [e]
    exact liesOn_frMap hz P.on q
  have h : toC (evR Xo c s.sig y) * (P.X σ τ.1).det = σ b := hb (CAt σ) z y (P.X σ) 1 hu isUnit_one hz hy
  rw [cInf_eq hD.unf hD.xi (hD.p.trans (Nat.le_add_right _ _)) s hon (hA z y hz hy), ← h, norm_mul,
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hX τ.1))]

end GlobalTheory.DefPt.ArchVal

end
end

