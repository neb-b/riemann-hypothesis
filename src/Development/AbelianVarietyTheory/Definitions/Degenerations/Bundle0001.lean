module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HomExtSt : Prop := ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
  ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
    ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f

def Match {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R]
    (f : O' →+* R) (u : R) (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E))
    (φ : P.P.A.left ⟶ a.D₀.P.A.left) (he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A) (w : LB.Iso P.P.L (a.D₀.P.L.pull φ))
    (e : a.D₀.X ≃ₗ[𝓞 E] P.X) : Prop :=
  letI := H.starRing
  IsGrpPullback P.P.A a.D₀.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.P.A) (fun _ => 1)) P.rig
      (rigPullOf φ (spMap f) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (oP.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.c (e y)).left ≫ φ = spMap f ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F),
      (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
      uF = algebraMap (FractionRing R) F (algebraMap R _ u) →
      ∀ y, GenRel w (LB.pullGen _ _ _ (P.psi (e y)) (jFK (R := R) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (jFK (R := O') F)) (uF ^ (a.be y y / 2))
end GlobalTheory.LN
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.AbLaw

def AlgSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R →
  IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))),
    (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) →
    (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) →
    ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left),
      IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧
      (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e))

def MorAlgSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R →
  IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), IsProjBy Y.hom → IsProjBy Z.hom → Smooth Y.hom →
    ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG I e Y).left ≫ Y.hom) →
    (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃! g : Y ⟶ Z, ∀ e, (fstG I e Y).left ≫ g.left = f e

def SecAlgSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ N : LB Y.left, N.IsLB → ∀ f : ∀ e, LB.Sec (N.pull (fstG I e Y).left), (∀ e z J, Good N z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃! s : LB.Sec (N.pull (𝟙 Y.left)), ∀ e z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J

def PicardZeroDegenerationCondition : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : PolAV (Spec (CommRingCat.of A)))
  (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) →
  ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1])

def Ega : Prop := AlgSt ∧ MorAlgSt ∧ SecAlgSt ∧ PicardZeroDegenerationCondition
end GlobalTheory.LN
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN

def PelSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
  [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (D : DegData R I) (A : PolAV (Sp (FractionRing R)))
  (U : Unif I D A t.G), U.LG = t.PP → ∃ P : PELUnif I t, P.D = D ∧ P.A = A ∧ HEq P.U U ∧ P.TorsionIso
end GlobalTheory.LN
end
end

