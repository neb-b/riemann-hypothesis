module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfFormalBiextension
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem cartHyp_of_formalBiextension : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  exact _root_.GlobalTheory.RowLaw.cartHyp_of_rlaw C V d I (Fin dd) (Y.raw p) (_root_.GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p)
    (_root_.GlobalTheory.hasProj_pairData C V O dd Y d I p) (_root_.GlobalTheory.TeichPair.hasTeich C V O dd Y d I p)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtensionSplitSpecialFibrePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitPoint

theorem exists_extend {V W Ω : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [Field Ω] [IsAlgClosed Ω] (β : V →+* Ω) (hβ : ∀ a ∈ maximalIdeal V, β a = 0) :
    ∃ β' : W →+* Ω, β'.comp (algebraMap V W) = β ∧ ∀ a ∈ maximalIdeal W, β' a = 0 := by
  have hm : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V) (maximalIdeal W))
  have : IsLocalHom (algebraMap V W) := ((IsLocalRing.local_hom_tfae (algebraMap V W)).out 5 1).1 hm
  have : IsLocalHom β := ⟨fun a ha => by
    by_contra h
    exact ha.ne_zero (hβ a h)⟩
  let : Algebra (ResidueField V) Ω := (ResidueField.lift β).toAlgebra
  have : Algebra.IsIntegral V (ResidueField W) :=
    ⟨fun x => by
      obtain ⟨y, rfl⟩ := residue_surjective x
      exact (Algebra.IsIntegral.isIntegral (R := V) y).map (IsScalarTower.toAlgHom V W (ResidueField W))⟩
  have : Algebra.IsIntegral (ResidueField V) (ResidueField W) := Algebra.IsIntegral.tower_top V
  let g : ResidueField W →ₐ[ResidueField V] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g.toRingHom.comp (residue W), RingHom.ext fun a => ?_, fun a ha => ?_⟩
  · exact g.commutes (residue V a)
  · show g (residue W a) = 0
    rw [(residue_eq_zero_iff a).2 ha, map_zero]

theorem polAt_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K K' : Type} [Field K] [Field K'] {j : Sp K ⟶ S} (hp : GlobalTheory.LN.PolAt t j) (j' : Sp K' ⟶ S') (g : Sp K' ⟶ Sp K)
    (h : j' ≫ f = g ≫ j) : GlobalTheory.LN.PolAt t' j' := by
  have hN := pull_isLB t'.PP.isLB (pullback.fst t'.G.hom j')
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom j)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := g) (f := j)
    (((isGrpPullback_pullback t'.G j').comp m.cart).congr h rfl) (isGrpPullback_pullback t.G j) t.PP.isLB hM hN
    (GlobalTheory.Ex.UnifModel.iso_pull (GlobalTheory.Ex.UnifModel.iso_of_map m) _ rfl) ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hp.1,
    amplePt _ _ g _ _ φ hφ _ _ hM hN e hp.2.1 hp.2.2⟩

theorem exists_split_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ t : SAB H (Sp V), GlobalTheory.LN.PolAt t (Out.jK V) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (β : V →+* Ω), (∀ a ∈ maximalIdeal V, β a = 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V →+* W) (β' : W →+* Ω) (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap f)), GlobalTheory.LN.CDvr W ∧ β'.comp f = β ∧ (∀ a ∈ maximalIdeal W, β' a = 0) ∧ GlobalTheory.LN.PolAt t' (Out.jK W) ∧ GlobalTheory.LN.SplitOver t'.G (maximalIdeal W) := by
  intro E _ _ _ H V _ _ _ ⟨d, hc, h0⟩ t hp Ω _ _ β hβ
  let F := AlgebraicClosure (FractionRing V)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  obtain ⟨W, dW, cW, fW, hsp⟩ := GlobalTheory.Ex.UnifModel.exists_split V F t.G t.semi
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap V W)) t
  obtain ⟨β', h₁, h₂⟩ := exists_extend (W := W) β hβ
  have i : Function.Injective (algebraMap V W) := fun _ _ h =>
    FaithfulSMul.algebraMap_injective V F (congrArg (fun z : W => (z : F)) h)
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp i
  let gm : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, β', _, m,
    ⟨dW, cW, charZero_of_injective_algebraMap i⟩, h₁, h₂, polAt_pullback m hp _ (spMap gm) ?_, hsp⟩
  exact (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
    (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm

end GlobalTheory.SplitPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralFramedPointModelPolarisedGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem polAt_of_intData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), GlobalTheory.LN.PolAt I.G (Out.jK T.V) := by
  intro E _ _ _ H Dw l Xo c T io y I
  let := io.toAlgebra
  have hN := LB.isLB_pull I.G.PP.isLB (pullback.fst I.G.G.hom (Out.jK T.V))
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := Out.jK T.V)
    ((isGrpPullback_pullback I.G.G (Out.jK T.V)).congr (Category.id_comp _).symm rfl) I.m2.cart
    I.G.PP.isLB I.t'.PP.isLB hN ⟨idIso _, idIso_isGen hN⟩ (GlobalTheory.Ex.UnifModel.iso_of_map I.m2)
  have g := hφ.comp I.m1.cart
  have e' := GlobalTheory.Ex.UnifModel.iso_comp hN I.t'.PP.isLB Xo.univ.t.PP.isLB e (GlobalTheory.Ex.UnifModel.iso_of_map I.m1)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g.1 Xo.univ.proper,
    amplePt _ _ _ _ _ _ g _ _ Xo.univ.t.PP.isLB hN e' Xo.univ.ample Xo.univ.ktriv⟩

end GlobalTheory.AlphaPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NotNondegenerateOfDegenerateSeriesDirectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_nondegenerate_of_degenerate_series_direction : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (d : ℕ) (F : Fin d → PS Ω 2 d) (ph1 ph2 : PS Ω 3 d) (P : PtFam s G d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![pt Ω d 0, 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph2 = 1 → IsPtLaw s G F P → IsPtUniv s G P → IsPtCube s G c F ph1 ph2 P → Degenerate p F ph2 → ¬ NonDeg p s G c := by
  first | exact @GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate | exact GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate | (intros; apply GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate <;> assumption)
end

