module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsFibIntThStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fib_normW_of_intSec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G), ∃ (Φ : Fib Xo y.x P.A) (w₀ : GlobalTheory.UT.W0 P.U.toUnifPre), GlobalTheory.UT.NormW P.U.toUnifPre w₀ Φ.ρ ∧ (∀ a : 𝓞 E, ((letI := H.starRing; P.oA.act a : P.A.A ⟶ P.A.A)).left ≫ Φ.φ = Φ.φ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra c.F F] (ψ : FractionRing V →ₐ[c.F] F) (z : FrPt Xo c F) (th : GlobalTheory.UT.SecA P.A F 1), ψ.toRingHom = algebraMap (FractionRing V) F → FrMap ψ y z → Φ.SecTie z.x z.s th → IntTh P.U.toUnifPre w₀ th := by
  first | exact @GlobalTheory.EtaVal.exists_fib_intTh | exact GlobalTheory.EtaVal.exists_fib_intTh | (intros; apply GlobalTheory.EtaVal.exists_fib_intTh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FibPointsMulEquivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulEquiv_ptO_hom_of_eq_spMap_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap (FractionRing R) F) ≫ x → ∃ tr : (ptO Xo xF ⟶ Xo.univ.t.G) ≃* (TFK (R := R) F ⟶ A.A), (∀ p, (tr p).left ≫ Φ.φ = p.left) ∧ ∀ (a : Xo.univ.t.G ⟶ Xo.univ.t.G) (a' : A.A ⟶ A.A), a'.left ≫ Φ.φ = Φ.φ ≫ a.left → ∀ p, tr (p ≫ a) = tr p ≫ a' := by
  first | exact @GlobalTheory.EtaVal.fib_points_mulEquiv | exact GlobalTheory.EtaVal.fib_points_mulEquiv | (intros; apply GlobalTheory.EtaVal.fib_points_mulEquiv <;> assumption)
end

