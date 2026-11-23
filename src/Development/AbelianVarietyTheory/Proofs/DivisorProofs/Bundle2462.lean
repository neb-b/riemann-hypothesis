module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineRefinementAlongMorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_eighthPower_groupPullback : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  first | exact @GlobalTheory.Poinc.Eq8.lbIso_eighth_pull | exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull | (intros; apply GlobalTheory.Poinc.Eq8.lbIso_eighth_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordAdjointPrimitiveOfTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.NormLam

theorem lbIso_cubeLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

theorem lbIso_lam_adj_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → LBIso (abelian₂ G P.L.L) (abelian₂ G U.LG.L) ∧ (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] P.L.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] P.L.L)) ∧ LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] P.L.L) := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw P hP
  have hwh := oG.hom w
  have hwh' := oG.hom (star w)
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hS U O o oA oG hlin a
  have hc := fun T : Over (Sp R) => GlobalTheory.PrimNorm.diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w) x.left) =
      fun x => GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act w) T x) :=
    fun T => funext fun x => GlobalTheory.PrimNorm.normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G),
      GlobalTheory.PrimNorm.postHom (oG.act w) T y * GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) (GlobalTheory.PrimNorm.postHom (oG.act w) T x) y =
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y) :=
    fun T x y => GlobalTheory.PrimNorm.diff₂_ptCls_adj hM (hadj w) x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _
      ((GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.cls U.LG.L)).symm))
    rw [hq]
    exact GlobalTheory.PrimNorm.diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have hN := cubeLB_isLB' ![𝟙 G, oG.act w] hM
  have hPL := P.L.isLB
  have cP : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x P.L.L).IsLB := fun x => cubeLB_isLB' x hPL
  have cN : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x (cubeLB G ![𝟙 G, oG.act w] U.LG.L)).IsLB :=
    fun x => cubeLB_isLB' x hN
  have cL : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x U.LG.L).IsLB := fun x => cubeLB_isLB' x hM

  have isoP : ∀ (T : Over (Sp R)) (x y : T ⟶ G), LBIso (cubeLB G ![x, y] P.L.L) (cubeLB G ![x, y] U.LG.L) :=
    fun T x y => LBIso.trans (cP _) (cN _) (cL _) (lbIso_cubeLB' _ hP) (iso T x y)
  refine ⟨isoP _ (fst G G) (snd G G), fun a => ?_, ?_⟩
  · exact LBIso.trans (cP _) (cL _) (cP _) (isoP _ _ _)
      (LBIso.trans (cL _) (cL _) (cP _) (hadj a) (isoP _ _ _).symm)
  · exact LBIso.trans hPL hN (cP _) hP (LBIso.trans hN (cN _) (cP _) (iso G (𝟙 G) (oG.act w)).symm
      (lbIso_cubeLB' _ hP).symm)

end GlobalTheory.Mum.NormLam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem lbIso_lam_of_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L' : LB G.left) (N : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L'.IsLB → N.IsLB → LBIso N (L'.pull (pullback.fst G.hom (jK R))) → ExtLam G N PP → LBIso (abelian₂ G L') PP := by
  intro R _ _ _ _ _ G _ _ hG L' N PP hL' hN hNL hE
  have hsm : Smooth G.hom := hG.smooth
  have hgc : GeometricallyConnected G.hom := hG.geomConnected
  have hsm₂ : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc₂ : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  have hgi₂ : GeometricallyIntegral (G2 G).hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hLam : (abelian₂ G L').IsLB := DVR.linComb_isLB _ hL' _ _
  have hPP : PP.IsLB := hE.1

  have hpb := isGrpPullback_pullback G (jK R)
  obtain ⟨β₂, hsq, hβ⟩ := _root_.GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G ((Over.pullback (jK R)).obj G) (pullback.fst G.hom (jK R)) hpb
  have h1 : LBIso (abelian₂ G L') ((abelian₂ G L').pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hLam)
  have h2 := hβ L' N _ (abelian₂ G L') (𝟙 _) hL' hN hLam hNL h1
  rw [Category.comp_id] at h2
  have h3 := hE.2 β₂ hsq
  have hgen : LBIso ((abelian₂ G L').pull β₂) (PP.pull β₂) :=
    LBIso.trans (pull_isLB hLam _) (DVR.linComb_isLB _ hN _ _) (pull_isLB hPP _) (LBIso.symm h2) h3

  let p1 := pullback.fst (G2 G).hom (jK R)
  let p2 := pullback.snd (G2 G).hom (jK R)
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk p2
  have wx : (p1 ≫ (fst G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (fst G G)]; exact pullback.condition
  have wy : (p1 ≫ (snd G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (snd G G)]; exact pullback.condition
  let x : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wx) (hpb.1.lift_snd _ _ _)
  let y : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wy) (hpb.1.lift_snd _ _ _)
  let i : pullback (G2 G).hom (jK R) ⟶ (G2 ((Over.pullback (jK R)).obj G)).left := (lift x y).left
  have hi : i ≫ β₂ = p1 := by
    apply pullback.hom_ext
    · show i ≫ β₂ ≫ (fst G G).left = p1 ≫ (fst G G).left
      rw [hsq.1, ← Category.assoc]
      show (lift x y ≫ fst _ _).left ≫ _ = _
      rw [lift_fst]
      exact hpb.1.lift_fst _ _ _
    · show i ≫ β₂ ≫ (snd G G).left = p1 ≫ (snd G G).left
      rw [hsq.2, ← Category.assoc]
      show (lift x y ≫ snd _ _).left ≫ _ = _
      rw [lift_snd]
      exact hpb.1.lift_fst _ _ _
  have hK : LBIso ((abelian₂ G L').pull p1) (PP.pull p1) :=
    LBIso.chartPull (chartPullSame (abelian₂ G L') (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm))
      (chartPullSame PP (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm)) hgen
  exact _root_.GlobalTheory.Mum.lbIso_of_generic_local R (G2 G) (lift η[G] η[G]).left (Over.w (lift η[G] η[G])) (abelian₂ G L') PP hLam hPP hK

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnRationalModelComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

def openRatModel {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k) (U : X.Opens) [IsIntegral U.toScheme]
    (hsep : IsSeparated s) (hlft : LocallyOfFiniteType s) (hqc : QuasiCompact (U.ι ≫ s)) :
    letI : Algebra k U.toScheme.functionField :=
      (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
    RatModel k U.toScheme.functionField :=
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  { Z := U.toScheme
    s := U.ι ≫ s
    sep := inferInstance
    lft := inferInstance
    qc := hqc
    pt := U.toScheme.fromSpecStalk (genericPoint U.toScheme)
    pt_s := by
      unfold spMap
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    gen := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, Scheme.fromSpecStalk_closedPoint⟩, ?_⟩
      rintro _ ⟨w, rfl⟩
      have : w = IsLocalRing.closedPoint U.toScheme.functionField :=
        Subsingleton.elim (α := PrimeSpectrum U.toScheme.functionField) _ _
      rw [this]
      exact Scheme.fromSpecStalk_closedPoint
    onto := fun x => by
      obtain ⟨V, h, a, rfl⟩ := U.toScheme.presheaf.germ_exist (x := genericPoint U.toScheme) x
      exact ⟨V, a, ⟨_, h⟩, GlobalTheory.FlagBundle.valF_fromSpecStalk h a⟩ }

theorem lbIso_of_ratModels : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (A B : LB X), Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → A.IsLB → B.IsLB → (∀ (Ω : Type) [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (io : M.Z ⟶ X), IsOpenImmersion io → io ≫ s = M.s → LBIso (A.pull io) (B.pull io)) → LBIso A B := by
  intro k _ _ X s A B hN hsep hlft hqc hA hB hM
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover X (irreducibleComponents X) GlobalTheory.IsNormalScheme.component
    (fun a b y ha hb => Subtype.ext (GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents a.2 b.2 ha hb))
    (fun y => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, mem_irreducibleComponent⟩) A B hA hB ?_
  intro Z
  let U := GlobalTheory.IsNormalScheme.component Z
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  have hio : IsOpenImmersion U.ι := by infer_instance
  exact hM _ (openRatModel s U hsep hlft inferInstance) U.ι hio rfl

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfPullbackChainThroughSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.LbChain

theorem lbIso_chain : ∀ {A₀ X₁ G₁ G₂ Z P Q : Scheme.{0}} (LA : LB A₀) (L₁ : LB G₁) (L₂ : LB G₂) (LZ : LB Z) (LQ : LB Q) (a : X₁ ⟶ A₀) (a' : A₀ ⟶ X₁) (f₁ : X₁ ⟶ G₁) (f₂ : G₁ ⟶ G₂) (f₃ : G₂ ⟶ Z) (ψ : P ⟶ Z) (π : P ⟶ Q) (t : A₀ ⟶ P), LA.IsLB → L₁.IsLB → L₂.IsLB → LZ.IsLB → LQ.IsLB → a' ≫ a = 𝟙 A₀ → LBIso (LA.pull a) (L₁.pull f₁) → LBIso L₁ (L₂.pull f₂) → LBIso L₂ (LZ.pull f₃) → LBIso (LZ.pull ψ) (LQ.pull π) → t ≫ ψ = a' ≫ f₁ ≫ f₂ ≫ f₃ → LBIso LA (LQ.pull (t ≫ π)) := by
  intro A₀ X₁ G₁ G₂ Z P Q LA L₁ L₂ LZ LQ a a' f₁ f₂ f₃ ψ π t hA h₁ h₂ hZ hQ hs e₁ e₂ e₃ e₄ ht
  have E0 : LBIso LA (LA.pull (a' ≫ a)) :=
    LBIso.chartPull (chartPullUnpull LA (a' ≫ a) hs) (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hA _))
  have E1 : LBIso (LA.pull (a' ≫ a)) (L₁.pull (a' ≫ f₁)) := GlobalTheory.GenSpread.lbIso_pull_comp a' rfl rfl e₁
  have E2 : LBIso (L₁.pull (a' ≫ f₁)) (L₂.pull (a' ≫ f₁ ≫ f₂)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₂ (a' ≫ f₁) (by simp)
  have E3 : LBIso (L₂.pull (a' ≫ f₁ ≫ f₂)) (LZ.pull (t ≫ ψ)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₃ (a' ≫ f₁ ≫ f₂) (by rw [ht]; simp)
  have E4 : LBIso (LZ.pull (t ≫ ψ)) (LQ.pull (t ≫ π)) := GlobalTheory.GenSpread.lbIso_pull_comp t rfl rfl e₄
  exact LBIso.trans hA (pull_isLB hA _) (pull_isLB hQ _) E0
    (LBIso.trans (pull_isLB hA _) (pull_isLB h₁ _) (pull_isLB hQ _) E1
      (LBIso.trans (pull_isLB h₁ _) (pull_isLB h₂ _) (pull_isLB hQ _) E2
        (LBIso.trans (pull_isLB h₂ _) (pull_isLB hZ _) (pull_isLB hQ _) E3 E4)))

end GlobalTheory.LbChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPowMultipleDegreeDescendsNormal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH

namespace GlobalTheory.UMin.NormIso

def toFld (K : Type) [Field K] : ((Sp K).presheaf.stalk (IsLocalRing.closedPoint K))ˣ →* Kˣ :=
  Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom

theorem toFld_gm {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    (toFld K (gm x _ U a)).val = valF x U a.val := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x U hU
  refine Eq.trans ?_ ((congrArg (fun φ => φ.hom a.val) e).trans (GlobalTheory.Points.valR_eq x U hU _).symm)
  exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((gm_val x _ U h a).trans
    (Scheme.Hom.germ_stalkMap_apply x U (IsLocalRing.closedPoint K) h a.val).symm)

theorem toFld_gm_spMap {K K' : Type} [Field K] [Field K'] (σ : K →+* K') {X : Scheme.{0}} (x : Sp K ⟶ X)
    (U : X.Opens) (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    toFld K' (gm (spMap σ ≫ x) _ U a) = Units.map σ.toMonoidHom (toFld K (gm x _ U a)) := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  apply Units.ext
  rw [toFld_gm (spMap σ ≫ x) U (hU (x := spMap σ (IsLocalRing.closedPoint K')) trivial)]
  show _ = σ (toFld K (gm x _ U a)).val
  rw [toFld_gm x U h]
  exact GlobalTheory.Points.valR_spMap_comp σ x U hU _

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] {M : RatModel k Ω}

theorem pt_mem {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) : M.pt (IsLocalRing.closedPoint Ω) ∈ U :=
  M.top_le_preimage_pt hU (x := IsLocalRing.closedPoint Ω) trivial

theorem unit_ext_pt {U : M.Z.Opens} {a b : Γ(M.Z, U)ˣ}
    (h : M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = toFld Ω (gm M.pt _ U b)) : a = b := by
  by_cases hU : (U : Set M.Z).Nonempty
  · have e := congrArg Units.val (h (pt_mem hU))
    rw [toFld_gm _ _ (pt_mem hU), toFld_gm _ _ (pt_mem hU)] at e
    exact Units.ext (M.valF_injective hU e)
  · exact unit_ext fun x hx => absurd ⟨x, hx⟩ hU

theorem exists_unit {U : M.Z.Opens} (c : Ωˣ) (h : ∀ z ∈ U, c.val ∈ M.O z ∧ (c⁻¹).val ∈ M.O z) :
    ∃ a : Γ(M.Z, U)ˣ, M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = c := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).1)
    obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).2)
    have e : f * g = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, M.res_apply, M.res_apply, hf, hg, c.mul_inv])
    exact ⟨⟨f, g, e, (mul_comm _ _).trans e⟩, fun hp => Units.ext ((toFld_gm _ _ hp _).trans hf)⟩
  · exact ⟨1, fun hp => absurd ⟨_, hp⟩ hU⟩

variable {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] {M' : RatModel k Ω'}
  {π : M'.Z ⟶ M.Z}

theorem norm_mem_O [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) {W : M'.Z.Opens}
    (hW : π ⁻¹ᵁ U ≤ W) (f : Γ(M'.Z, W)) : Algebra.norm Ω (valF M'.pt W f) ∈ M.O z := by
  have hH : M.IsHom M' (IsScalarTower.toAlgHom k Ω Ω') π := hπ
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle' : π ⁻¹ᵁ V ≤ W := fun y hy => hW (hle hy)
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have hne' : ((π ⁻¹ᵁ V : M'.Z.Opens) : Set M'.Z).Nonempty := by
    refine ⟨M'.pt (IsLocalRing.closedPoint Ω'), ?_⟩
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ V
    rw [hπ]
    exact M.top_le_preimage_pt hne (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hfin : (π.app V).hom.Finite := IsFinite.finite_app π V hV
  have hint := hfin.to_isIntegral (resG M'.Z hle' f)
  let ρ : Γ(M.Z, V) →+* M.O z := (M.res V hne).codRestrict (M.O z) fun a => by
    rw [M.res_apply]; exact RatModel.valF_mem_O hzV a
  have hc : (algebraMap (M.O z) Ω').comp ρ = (M'.res _ hne').comp (π.app V).hom := by
    ext a
    show algebraMap Ω Ω' (M.res V hne a) = M'.res _ hne' (π.app V a)
    rw [M.res_apply, M'.res_apply, hH.valF_app hne]
    rfl
  have h1 : IsIntegral (M.O z) (valF M'.pt W f) := by
    obtain ⟨P, hP, hP0⟩ := hint
    refine ⟨P.map ρ, hP.map ρ, ?_⟩
    rw [Polynomial.eval₂_map, hc, ← M'.valF_resG hle' hne', ← M'.res_apply _ hne', ← Polynomial.hom_eval₂, hP0,
      map_zero]
  have := M.isIntegrallyClosed_O hN z
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm Ω h1)
  exact hy ▸ y.2

theorem lbIso_lbPow_finrank [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) (A B : LB M.Z) (e : ℕ)
    (H : LBIso (A.pull π) (B.pull π)) :
    LBIso (lbPow A (Module.finrank Ω Ω' * e)) (lbPow B (Module.finrank Ω Ω' * e)) := by
  obtain ⟨w, hw⟩ := H
  set d := Module.finrank Ω Ω' * e with hd
  let N : Ω'ˣ →* Ωˣ := Units.map (Algebra.norm Ω)
  have hNa : ∀ c : Ωˣ, N (Units.map (algebraMap Ω Ω').toMonoidHom c) = c ^ Module.finrank Ω Ω' := fun c =>
    Units.ext (Algebra.norm_algebraMap c.val)
  have hle : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), π ⁻¹ᵁ ((LB.div (lbPow B d) (lbPow A d)).U p) ≤
      (LB.div (B.pull π) (A.pull π)).U p := fun p y hy =>
    ⟨mem_pull.2 (mem_powChart.1 hy.1), mem_pull.2 (mem_powChart.1 hy.2)⟩
  have hpt : ∀ {U : M.Z.Opens}, M.pt (IsLocalRing.closedPoint Ω) ∈ U →
      π (M'.pt (IsLocalRing.closedPoint Ω')) ∈ U := fun {U} h => by
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ U
    rw [hπ]
    exact M.top_le_preimage_pt ⟨_, h⟩ (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hex : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), ∃ a : Γ(M.Z, (LB.div (lbPow B d) (lbPow A d)).U p)ˣ,
      M.pt (IsLocalRing.closedPoint Ω) ∈ (LB.div (lbPow B d) (lbPow A d)).U p →
      toFld Ω (gm M.pt _ _ a) = N (toFld Ω' (gm M'.pt _ _ (w.s p))) ^ e := fun p => by
    refine exists_unit _ fun z hz => ?_
    have hp := hle p (hpt (pt_mem ⟨z, hz⟩))
    have key : ∀ u : Γ(M'.Z, (LB.div (B.pull π) (A.pull π)).U p)ˣ,
        (N (toFld Ω' (gm M'.pt _ _ u)) ^ e).val ∈ M.O z := fun u => by
      rw [Units.val_pow_eq_pow_val]
      refine pow_mem ?_ e
      show Algebra.norm Ω (toFld Ω' (gm M'.pt _ _ u)).val ∈ _
      rw [toFld_gm _ _ hp]
      exact norm_mem_O hN hπ hz (hle p) _
    refine ⟨key _, ?_⟩
    rw [← inv_pow, ← map_inv, ← map_inv, ← map_inv]
    exact key _
  choose s hs using hex
  refine ⟨⟨s⟩, fun p q => unit_ext_pt fun hy => ?_⟩
  have hy' : M'.pt (IsLocalRing.closedPoint Ω') ∈ (LB.div (B.pull π) (A.pull π)).U p ⊓
      (LB.div (B.pull π) (A.pull π)).U q := ⟨hle p (hpt hy.1), hle q (hpt hy.2)⟩
  have e₁ := congrArg (gm M'.pt (IsLocalRing.closedPoint Ω') _) (hw p q)
  rw [gm_res _ _ _ hy', map_mul, gm_res _ _ _ hy'] at e₁
  replace e₁ := e₁.trans (congrArg (· * _) (gm_div (A.pull π) (B.pull π) _ _ p q hy'))
  rw [gm_pull_g B π _ _ _ _ hy'.1.1 hy'.2.1, gm_pull_g A π _ _ _ _ hy'.1.2 hy'.2.2, hπ] at e₁
  have e₂ := congrArg (fun u => N (toFld Ω' u) ^ e) e₁
  simp only [map_mul, map_inv] at e₂
  have hB : M.pt (IsLocalRing.closedPoint Ω) ∈ B.U (p.1 PUnit.unit) ⊓ B.U (q.1 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.1, mem_powChart.1 hy.2.1⟩
  have hA : M.pt (IsLocalRing.closedPoint Ω) ∈ A.U (p.2 PUnit.unit) ⊓ A.U (q.2 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.2, mem_powChart.1 hy.2.2⟩
  rw [toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hB, toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hA, hNa, hNa] at e₂
  rw [gm_res _ _ _ hy, map_mul, gm_res _ _ _ hy]
  refine Eq.trans ?_ (congrArg (fun u => toFld Ω (u * _)) (gm_div (lbPow A d) (lbPow B d) _ _ p q hy)).symm
  rw [gm_lbPow_g d _ _ _ _ hy.1.1 hy.2.1, gm_lbPow_g d _ _ _ _ hy.1.2 hy.2.2, map_mul, map_mul, map_inv, map_pow,
    map_pow, hs p hy.1, hs q hy.2, e₂, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]

theorem lbIso_lbPow_of_pull : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'] (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z) (A B : LB M.Z) (d : ℕ), Geo.Tor.IsNormalScheme M.Z → IsFinite π → M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt → A.IsLB → B.IsLB → Module.finrank Ω Ω' ∣ d → LBIso (A.pull π) (B.pull π) → LBIso (lbPow A d) (lbPow B d) := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ M' π A B d hN _ hπ _ _ ⟨e, he⟩ H
  subst he
  exact lbIso_lbPow_finrank hN hπ A B e H

end GlobalTheory.UMin.NormIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionNatural
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem lineBundleLiftObstruction_natural_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (L' : LB Z₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff t₀))), L.IsLB → L'.IsLB → LBIso L' (L.pull f₀) → IsObL S α L c → IsObL S' α L' c' → IsExtendedPullbackDegTwo R₁ h c c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L L' c c' hL hL' hiso hc hc'
  obtain ⟨C, _, _, G, hGb, hG⟩ := hc
  obtain ⟨C', _, _, G', hG'b, hG'⟩ := hc'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hKb⟩ := _root_.GlobalTheory.LBObs.exists_pair_refine X₀ Z₀ f₀ C C' G G' hGb hG'b
  have h1 := _root_.GlobalTheory.LBObs.obAt_refine R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G (K ⋙ pairSnd f₀) H θ hG
  have h2 := _root_.GlobalTheory.LBObs.obAt_pairPull R R₀ I hI π hπ hk R₁ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L c D K h1
  have h3 := _root_.GlobalTheory.LBObs.obAt_refine R R₀ I hI π hπ hk R₁ α Z₀ t₀ S' L' c' C' D G' (K ⋙ pairFst f₀) H' θ' hG'
  have h4 := _root_.GlobalTheory.LBObsUniq.obAt_eq_of_iso R R₀ I hI π hπ hk R₁ α Z₀ t₀ S' L' (L.pull f₀) D (K ⋙ pairFst f₀) _ _ hL'
    (pull_isLB hL f₀) hiso h3 h2
  apply GlobalTheory.LBObs.PairInj.restrict_pair_injective R₀ R₁ X₀ Z₀ t₀ f₀ D K hKb
  refine h4.symm.trans ?_
  have e : ∀ {E : Type} [Category.{0} E] {E' : Type} [Category.{0} E'] (F : E ⥤ CommAlgCat.{0} R₀) (G : E' ⥤ E)
      (T : E') (x : R₁ ⊗[R₀] F.obj (G.obj T)), (extMap R₁ (CoefMap.restrict F G)).α T x = x := by
    intro E _ E' _ F G T x
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul y b => rfl
    | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c'
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  congr 1
  refine Subtype.ext ?_
  funext T T' T'' φ ψ
  exact (e _ _ _ _).trans ((e (OPair f₀ t₀) K _ _).trans (e (OAff t₀) (pairFst f₀) _ _)).symm

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChangeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_model_change : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ModelChange := by
  first | exact @GlobalTheory.ModelChg.modelChange | exact GlobalTheory.ModelChg.modelChange | (intros; apply GlobalTheory.ModelChg.modelChange <;> assumption)
end

