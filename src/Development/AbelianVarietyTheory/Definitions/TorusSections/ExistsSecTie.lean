module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

structure IntSec (Xo : Moduli Dw l) (V : Type) [CommRing V] [IsDomain V] (x : Sp (FractionRing V) ⟶ Xo.X)
    (s : LB.Sec (PPx x)) (G : SAB H (Sp V)) where
  t' : SAB H (Sp (FractionRing V))
  m1 : SABMap t' Xo.univ.t x
  m2 : SABMap t' G (spMap (algebraMap V (FractionRing V)))
  θ : LB.Sec G.PP.L
  w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)
  w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)
  σ : LB.Sec t'.PP.L
  s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)
  θ2 : LB.Sec (G.PP.L.pull m2.φ)
  rig1 : RigIso m1 w1
  rig2 : RigIso m2 w2
  maps1 : IsoMaps w1 σ s1
  maps2 : IsoMaps w2 σ θ2
  pull : PullSec m2.φ θ θ2
  gen1 : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
    ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
      s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

def IntSec.ofIntData {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    {y : letI := io.toAlgebra; FrPt Xo c T.Fr} (I : IntData Xo c T io y) :
    letI := io.toAlgebra; IntSec Xo T.V y.x y.s I.G :=
  letI := io.toAlgebra
  ⟨I.t', I.m1, I.m2, I.θ, I.w1, I.w2, I.σ, I.s1, I.θ2, I.rig1, I.rig2, I.maps1, I.maps2, I.pull, I.gen1⟩

structure Fib (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of K))) where
  φ : A.A.left ⟶ Xo.univ.t.G.left
  cart : IsGrpPullback A.A Xo.univ.t.G x φ
  ω : LB.Iso A.L (Xo.univ.t.PP.L.pull φ)
  ωgen : ω.IsGen
  ρ : LB.Gen (A.L.pull (eSec A.A))
  ρgen : ρ.IsGen
  rig : ∀ (z : Spec (CommRingCat.of K)) (JA) (J), Good A.L z JA → Good Xo.univ.t.PP.L z J →
    gw ω (eSec A.A) z (J (x ≫ eSec Xo.univ.t.G)) (JA (eSec A.A)) *
        val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _) z JA =
      val (L := Xo.univ.t.PP.L) (φ := fun _ : PUnit => eSec Xo.univ.t.G) (ε := fun _ => 1) Xo.univ.t.PP.rig x z J

section

variable {Xo : Moduli Dw l} {R : Type} [CommRing R] [IsDomain R] {x : Sp (FractionRing R) ⟶ Xo.X}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {F : Type} [Field F] [Algebra (FractionRing R) F]

def Fib.SecTie (Φ : Fib Xo x A) (xF : Sp F ⟶ Xo.X) (s : LB.Sec (PPx xF)) (th : GlobalTheory.UT.SecA A F 1) : Prop :=
  xF = jFK (R := R) F ≫ x ∧
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (r' : Z ⟶ Gx xF),
    r' ≫ (snd (Over.mk xF) Xo.univ.t.G).left = r ≫ (snd (TFK (R := R) F) A.A).left ≫ Φ.φ →
    r' ≫ (fst (Over.mk xF) Xo.univ.t.G).left = r ≫ (fst (TFK (R := R) F) A.A).left →
    ∀ (z : Z) (JA) (J), Good A.L z JA → Good Xo.univ.t.PP.L z J →
      sval (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk xF) Xo.univ.t.G).left) (ε := fun _ => 1) s r' z J =
        (gw Φ.ω (r ≫ (snd (TFK (R := R) F) A.A).left) z (J (r' ≫ (snd (Over.mk xF) Xo.univ.t.G).left))
          (JA (r ≫ (snd (TFK (R := R) F) A.A).left))).val * GlobalTheory.UT.sA th r z JA

theorem Fib.exists_secTie (Φ : Fib Xo x A) {xF : Sp F ⟶ Xo.X} (hx : xF = jFK (R := R) F ≫ x) (s : LB.Sec (PPx xF)) :
    ∃ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie xF s th := by
  subst hx

  let hm : (TFK (R := R) F ⊗ A.A).left ⟶ (Over.mk (jFK (R := R) F ≫ x) ⊗ Xo.univ.t.G).left :=
    pullback.lift (pullback.fst (TFK (R := R) F).hom A.A.hom) (pullback.snd (TFK (R := R) F).hom A.A.hom ≫ Φ.φ)
      (by simp only [Category.assoc, Φ.cart.1.w]; exact pullback.condition_assoc x)
  have hψ : ∀ _k : Fin 1, (snd (TFK (R := R) F) A.A).left ≫ Φ.φ =
      hm ≫ (snd (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left := fun _ => (pullback.lift_snd _ _ _).symm
  obtain ⟨th, hth⟩ := GlobalTheory.ConstFam.exists_secThrough (w := Φ.ω) (ε := fun _ => 1) Φ.ωgen Xo.univ.t.PP.isLB A.isLB hψ s
  refine ⟨th, rfl, ?_⟩
  intro Z r r' h1 h2 z JA J hJA hJ
  have hr : r' = r ≫ hm := by
    refine pullback.hom_ext ?_ ?_
    · change r' ≫ (fst (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left = _
      rw [h2, Category.assoc]
      exact (congrArg (r ≫ ·) (pullback.lift_fst _ _ _)).symm
    · change r' ≫ (snd (Over.mk (jFK (R := R) F ≫ x)) Xo.univ.t.G).left = _
      rw [h1, Category.assoc]
      exact (congrArg (r ≫ ·) (pullback.lift_snd _ _ _)).symm
  subst hr
  refine (GlobalTheory.ConstFam.SecThrough.sval hψ hth r hJ hJA).trans ?_
  rw [Fin.prod_univ_one, zpow_one, h1]
  simp only [GlobalTheory.ConstFam.wVal, Category.assoc]
  rfl

end

def IntTh {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] (w : GlobalTheory.UT.W0 U)
    (th : GlobalTheory.UT.SecA A F 1) : Prop :=
  w.IsGen ∧ ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ (Over.pullback (jK R)).obj G).left) (z : Z) (JA) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      sval σ (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R)) z JG =
        (gw w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z
          (JG ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 _))
          (fun _ => JA ((r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left))).val *
          GlobalTheory.UT.sA th (r ≫ (U.genF F).left) z JA

end GlobalTheory.EtaVal
