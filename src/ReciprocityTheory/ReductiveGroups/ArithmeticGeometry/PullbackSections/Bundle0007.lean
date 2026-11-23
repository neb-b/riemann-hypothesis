module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Maps

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {x0 : Sp S ⟶ Xo.X} {x0' : Sp S' ⟶ Xo.X}
  (hx : x0' = spMap ψ ≫ x0)

def bcD : overAt x0' (DualNumber S') ⟶ overAt x0 (DualNumber S) :=
  Over.homMk (spMap (dualMap ψ)) (by
    subst hx
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem list_prod_comp {T T' : Over Xo.X} (f : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

include hx in
theorem isCombAt_bc {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin k → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x0 v cf w) :
    IsCombAt x0' (fun i => spMap (dualMap ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun i => bcD ψ hx ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, ← spMap_comp_spMap, Category.assoc]
  · have e : List.ofFn (fun i => bcD ψ hx ≫ u i) = (List.ofFn u).map (bcD ψ hx ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, list_prod_comp, Over.comp_left, hp]
    rfl

end Maps

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridge
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def idIso {Y : Scheme.{0}} (M : LB Y) : LB.Iso M M := ⟨fun p => M.g p.1 p.2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

section Gx

variable {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X)

def gxLift {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    Z ⟶ Gx x :=
  (lift (Over.homMk a rfl : Over.mk (a ≫ x) ⟶ Over.mk x) (Over.homMk b w : Over.mk (a ≫ x) ⟶ Xo.univ.t.G)).left

theorem gxLift_fst {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    gxLift x a b w ≫ (fst (Over.mk x) Xo.univ.t.G).left = a := by
  rw [gxLift, ← Over.comp_left, lift_fst] <;> rfl

theorem gxLift_snd {Z : Scheme.{0}} (a : Z ⟶ Sp S) (b : Z ⟶ Xo.univ.t.G.left) (w : b ≫ Xo.univ.t.G.hom = a ≫ x) :
    gxLift x a b w ≫ (snd (Over.mk x) Xo.univ.t.G).left = b := by
  rw [gxLift, ← Over.comp_left, lift_snd] <;> rfl

theorem gx_ext {Z : Scheme.{0}} (p q : Z ⟶ Gx x)
    (h1 : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h2 : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left) : p = q := by
  have e : (Over.mk x ⊗ Xo.univ.t.G).hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  have hw : q ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom := by
    rw [e, ← Category.assoc, ← h1, Category.assoc]
  let P : Over.mk (p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk p rfl
  let Q : Over.mk (p ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk q hw
  have hPQ : P = Q := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa [P, Q] using h1
    · ext
      simpa [P, Q] using h2
  have := congrArg (fun f => f.left) hPQ
  simpa [P, Q] using this

theorem gx_w : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x := by
  exact (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm

def gxU : pullback Xo.univ.t.G.hom x ⟶ Gx x := gxLift x (pullback.snd _ _) (pullback.fst _ _) pullback.condition

def gxV : Gx x ⟶ pullback Xo.univ.t.G.hom x :=
  pullback.lift (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (gx_w x)

theorem gxU_fst : gxU x ≫ (fst (Over.mk x) Xo.univ.t.G).left = pullback.snd _ _ := by
  exact gxLift_fst x _ _ _
theorem gxU_snd : gxU x ≫ (snd (Over.mk x) Xo.univ.t.G).left = pullback.fst _ _ := by
  exact gxLift_snd x _ _ _
theorem gxV_fst : gxV x ≫ pullback.fst _ _ = (snd (Over.mk x) Xo.univ.t.G).left := by
  exact pullback.lift_fst _ _ _
theorem gxV_snd : gxV x ≫ pullback.snd _ _ = (fst (Over.mk x) Xo.univ.t.G).left := by
  exact pullback.lift_snd _ _ _

theorem gxU_gxV : gxU x ≫ gxV x = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, gxV_fst, gxU_snd, Category.id_comp]
  · rw [Category.assoc, gxV_snd, gxU_fst, Category.id_comp]

theorem gxV_gxU : gxV x ≫ gxU x = 𝟙 _ := by
  apply gx_ext x
  · rw [Category.assoc, gxU_fst, gxV_snd, Category.id_comp]
  · rw [Category.assoc, gxU_snd, gxV_fst, Category.id_comp]

theorem gs_scal (a : S) (i : Fin 1 → Xo.univ.t.PP.L.ι) {Z : Scheme.{0}} (r : Z ⟶ Gx x) (z : Z)
    (hz : r z ∈ (PPx x).U i) :
    gs r z ((PPx x).U i) (scal x a i) = cst (r ≫ (fst (Over.mk x) Xo.univ.t.G).left) z a := by
  exact (gs_res r z le_top hz _).trans (gs_pull r _ z ⊤ trivial _)

theorem scal_eq_iff (s t : LB.Sec (PPx x)) (a : S) :
    (∀ i, s.f i = scal x a i * t.f i) ↔ ∀ i, ∀ y ∈ (PPx x).U i,
      gs (𝟙 _) y _ (s.f i) = cst (fst (Over.mk x) Xo.univ.t.G).left y a * gs (𝟙 _) y _ (t.f i) := by
  constructor
  · intro h i y hy
    rw [h i, gs_mul (𝟙 _) y _ hy, gs_scal x a i (𝟙 _) y hy, Category.id_comp]
  · intro h i
    apply fn_ext
    intro y hy
    rw [gs_mul (𝟙 _) y _ hy, gs_scal x a i (𝟙 _) y hy, Category.id_comp]
    exact h i y hy

end Gx

section BC

variable {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem bcU_w : (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ≫ pullback.fst Xo.univ.t.G.hom x) ≫
    Xo.univ.t.G.hom = pullback.snd (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ≫ spMap ψ ≫ x := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]

def bcU : pullback (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) ⟶ Gx (spMap ψ ≫ x) :=
  gxLift (spMap ψ ≫ x) (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.fst _ _) (bcU_w ψ x)

theorem bcV_w : (bcPm ψ x ≫ gxV x) ≫ pullback.snd Xo.univ.t.G.hom x =
    (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Category.assoc, gxV_snd, bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left] <;> rfl

def bcV : Gx (spMap ψ ≫ x) ⟶ pullback (pullback.snd Xo.univ.t.G.hom x) (spMap ψ) :=
  pullback.lift (bcPm ψ x ≫ gxV x) (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left (bcV_w ψ x)

theorem bcU_fst : bcU ψ x ≫ (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left = pullback.snd _ _ := by
  exact gxLift_fst _ _ _ _
theorem bcU_snd : bcU ψ x ≫ (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left =
    pullback.fst _ _ ≫ pullback.fst Xo.univ.t.G.hom x := by
  exact gxLift_snd _ _ _ _
theorem bcV_fst : bcV ψ x ≫ pullback.fst _ _ = bcPm ψ x ≫ gxV x := by
  exact pullback.lift_fst _ _ _
theorem bcV_snd : bcV ψ x ≫ pullback.snd _ _ = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  exact pullback.lift_snd _ _ _

theorem bcV_snd' : bcV ψ x ≫ pullback.fst _ _ ≫ pullback.fst Xo.univ.t.G.hom x =
    (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  have hbs : bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left
      = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
    rw [bcPm, ← Over.comp_left, whiskerRight_snd]
  rw [← Category.assoc, bcV_fst, Category.assoc, gxV_fst, hbs]

theorem bcV_bcU : bcV ψ x ≫ bcU ψ x = 𝟙 _ := by
  apply gx_ext (spMap ψ ≫ x)
  · rw [Category.assoc, bcU_fst, bcV_snd, Category.id_comp]
  · rw [Category.assoc, bcU_snd, bcV_snd', Category.id_comp]

theorem bcU_bcPm : bcU ψ x ≫ bcPm ψ x = pullback.fst _ _ ≫ gxU x := by
  have hbs : bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left
      = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
    rw [bcPm, ← Over.comp_left, whiskerRight_snd]
  have hbf : bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left
      = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
    rw [bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left] <;> rfl
  apply gx_ext x
  · rw [Category.assoc, hbf, ← Category.assoc, bcU_fst, Category.assoc, gxU_fst, pullback.condition]
  · rw [Category.assoc, hbs, bcU_snd, Category.assoc, gxU_snd]

theorem bcV_gxU : bcV ψ x ≫ pullback.fst _ _ ≫ gxU x = bcPm ψ x := by
  rw [← Category.assoc, bcV_fst, Category.assoc, gxV_gxU, Category.comp_id]

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

def SecTie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) (k : ℕ)
    (F : letI := io.toAlgebra; LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo yI.1.x)))
    (σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => (k : ℤ)))) : Prop :=
  letI := io.toAlgebra
  ∃ σt : LB.Sec (LB.LinComb I.t'.PP.L (K := Fin 1) (fun _ => 𝟙 I.t'.G.left) (fun _ => (k : ℤ))),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (zp : Z ⟶ Gx yI.1.x),
      zp ≫ (snd (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.m1.φ →
      zp ≫ (fst (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.t'.G.hom →
      ∀ (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
        (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good Xo.univ.t.PP.L z J → Good I.t'.PP.L z J' →
        sval (show LB.Sec (LB.LinComb Xo.univ.t.PP.L (K := Fin 1)
            (fun _ => (snd (ptO Xo yI.1.x) Xo.univ.t.G).left) (fun _ => (k : ℤ))) from F) zp z J =
          ((gv I.w1 r z (fun _ => J (r ≫ I.m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J') ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (z : Z) (J : (Z ⟶ I.G.G.left) → I.G.PP.L.ι)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.G.PP.L z J → Good I.t'.PP.L z J' →
      sval σ (r ≫ I.m2.φ) z J =
        ((gv I.w2 r z (fun _ => J (r ≫ I.m2.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J'

def FrameTieSt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] : Prop :=
  ∀ (Tc : CDVR) (io : c.F →+* Tc.Fr) (yI : IntFr Xo c Tc io) (C : IntegralChartA3 Xo c Tc io yI),
    letI := io.toAlgebra
    ∃ x' : ∀ m, jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1 ⟶ C.I.t'.G,
      (∀ m, (x' m).left ≫ C.I.m1.φ = (C.ch.x m).left) ∧
      (∀ m, (x' m).left ≫ C.I.m2.φ =
        spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m) ≫ (C.xT m).left) ∧
      ∃ eL' : ∀ m, LB.Gen (LB.LinComb C.I.t'.PP.L (K := Fin 1) (fun _ => (x' m).left) (fun _ => (1 : ℤ))),
        ∀ (m : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1).left) (z : Z)
          (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (J' : (Z ⟶ C.I.t'.G.left) → C.I.t'.PP.L.ι)
          (J'' : (Z ⟶ C.I.G.G.left) → C.I.G.PP.L.ι),
          Good Xo.univ.t.PP.L z J → Good C.I.t'.PP.L z J' → Good C.I.G.PP.L z J'' →
          val (eL yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP m) r z J =
            gv C.I.w1 (r ≫ (x' m).left) z (fun _ => J ((r ≫ (x' m).left) ≫ C.I.m1.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J' ∧
          val (eLG C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.actT C.eT C.wPT m)
              (r ≫ spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m)) z J'' =
            gv C.I.w2 (r ≫ (x' m).left) z (fun _ => J'' ((r ≫ (x' m).left) ≫ C.I.m2.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J'

def zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) : LB.Sec (LPow A L k₂ T) := h ▸ F

theorem natCast_sq (M : ℕ) : ((M : ℤ) ^ 2) = ((M ^ 2 : ℕ) : ℤ) := (Nat.cast_pow M 2).symm

def SplitModel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj I.G.G)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem coprime_of_mod_one {g p : ℕ} (h : g % p = 1) : Nat.Coprime g p := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]

theorem g_coprime_ram (D : D7) (k : Fin 2) (p : ℕ) (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  apply coprime_of_mod_one
  rcases hp with rfl | rfl | rfl
  · have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ D.host.QS * D.host.q * D.host.d from
      (h2.mul_right _).mul_right _), hc]
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.q, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 f i ≤ ∑ i, f i := by
  unfold ext0
  have e1 : ∑ i : Fin m, (if h : (i : ℕ) < p then f ⟨i, h⟩ else 0) =
      ∑ i ∈ Finset.range m, (if h : i < p then f ⟨i, h⟩ else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) m
  have e2 : ∑ i : Fin p, f i = ∑ i ∈ Finset.range p, (if h : i < p then f ⟨i, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) p]
    exact Finset.sum_congr rfl fun i _ => by rw [dite_eq_left i.2]
  rw [e1, e2, ← Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun i => i < p)]
  have e3 : ∑ i ∈ (Finset.range m).filter (fun i => ¬ i < p), (if h : i < p then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => dif_neg (Finset.mem_filter.mp hi).2
  rw [e3, add_zero]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2) (fun _ _ _ => Nat.zero_le _)


open Classical in
theorem DF_wtA_le {D : D7} (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ Formalism.MainNotions.WeightAlgebra.DF w := by
  show ∑ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) ≤
    ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i)
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = conjEmb (DV.tauEmb D t) then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact add_le_add (sum_extendByZero_le_sum _ _) (sum_extendByZero_le_sum _ _)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

section Val

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K'] [Algebra V K'] [IsFractionRing V K']

theorem nval_nonneg_of_int (e : ℕ) {x : K'} (hx : x ∈ (algebraMap V K').range) : 0 ≤ nval V e x := by
  unfold nval
  split_ifs with h0
  · exact le_top
  · obtain ⟨y, rfl⟩ := hx
    unfold vV
    have hv : valV V ((algebraMap V K') y) ≤ 1 := by
      unfold valV
      exact HeightOneSpectrum.valuation_le_one _ y
    have hne : valV V ((algebraMap V K') y) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    have hl : ((valV V) ((algebraMap V K') y)).log ≤ 0 := by
      first
      | exact (WithZero.log_le_log hne one_ne_zero).mpr hv |>.trans_eq WithZero.log_one
      | exact WithZero.log_nonpos hv
      | exact WithZero.log_le_zero_iff.mpr hv
      | simpa using WithZero.log_mono hne hv
    have h1 : (0:ℝ) ≤ ((-(valV V ((algebraMap V K') y)).log : ℤ) : ℝ) / (e : ℝ) :=
      div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ -(valV V ((algebraMap V K') y)).log)) (Nat.cast_nonneg _)
    exact EReal.coe_nonneg.mpr h1

end Val

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

attribute [local instance 2000] Submodule.module

section Read

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem readings_holomorphic_cuspForms (hM5 : SiegelSpaceAlgebra (E := E)) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : RdHolCusp σ (laU (U σ) a n) (rdC U σ a n) := by
  intro f
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  have hf : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := h2 hσ
  let K : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | IsHolCusp (U σ).X (laU (U σ) a n) P}
      zero_mem' := by
        intro k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).1
      add_mem' := by
        intro P Q hP hQ k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.1 _ (hP k) _ (hQ k)
      smul_mem' := by
        intro z P hP k
        exact ((hM5 r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1).2.2 z _ (hP k) }
  have hle : holSub (U σ).X (laU (U σ) a n) ≤ K := Submodule.span_le.mpr (fun P hP => hP)
  exact hle hf

theorem rdC_mem_holSub {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub (U σ).X (laU (U σ) a n) := by
  have h0 : (f : Rul Xo c) ∈ cusp Xo c U a n := f.2
  have h1 := (Submodule.mem_inf.mp h0).2
  rw [Submodule.mem_iInf] at h1
  have h2 := h1 σ
  rw [Submodule.mem_iInf] at h2
  exact h2 hσ

theorem rdC_mem_holSub0 {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : cusp Xo c U a n) : rdC U σ a n f ∈ holSub0 (U σ).X (laU (U σ) a n) := by
  refine Submodule.mem_inf.mpr ⟨rdC_mem_holSub hσ a n f, ?_⟩
  intro k x hx
  simp [rdC, rdU, hx]

end Read

def JInjAt {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hd : Dom a n) : Prop :=
  JInj (T.V j T.σ₀) T.σ₀ (rdC (T.U j) T.σ₀ a n) (T.dict j T.σ₀) (T.mu j T.σ₀) (h.cuspidalL2Subspace j hj T.σ₀ T.good_σ₀ a n hd)

def JInjRd {D : D7} (T : Top D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  IndepToC (rdC (T.U j) T.σ₀ a n)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

