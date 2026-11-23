module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

section GtPoints

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

namespace DegPre

abbrev cF (χ : D.X) : TF (R := R) F ⟶ D.P.A := toUnit _ ≫ D.c χ

abbrev zeroF : TF (R := R) F ⟶ D.P.A := toUnit _ ≫ η[D.P.A]

def gtφ (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) : Fin 4 → ((TF (R := R) F).left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cF D F χ) b).left, (cF D F χ).left, b.left, (zeroF D F).left]

def gtε : Fin 4 → ℤ := ![-1, 1, 1, -1]

def cubAt (x x' y : TF (R := R) F ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left

end DegPre

structure GtPtF where
  b : TF (R := R) F ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAt D F (DegPre.cF D F χ) (DegPre.cF D F χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))

namespace GtPtF

variable {D F}

def IsZero (g : GtPtF D F) : Prop :=
  g.b = DegPre.zeroF D F ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)

def IsAdd (g g' g'' : GtPtF D F) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (DegPre.cubAt D F (DegPre.cF D F χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))

def IsNsmul (k : ℕ) (g h : GtPtF D F) : Prop :=
  ∃ gs : Fin (k + 1) → GtPtF D F, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h

def IsIota (y : D.X) (g : GtPtF D F) : Prop :=
  g.b = DegPre.cF D F y ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ)
    (LB.pullGen D.P.L _ _ (D.io y χ) (jFK (R := R) F))

end GtPtF

structure QkPt (k : ℕ) where
  y : D.X
  g : GtPtF D F
  eq : ∃ h : GtPtF D F, GtPtF.IsNsmul k g h ∧ GtPtF.IsIota y h

def QkPt.Equiv {k : ℕ} (p p' : QkPt D F k) : Prop :=
  ∃ z : D.X, p'.y = p.y + k • z ∧ ∃ h : GtPtF D F, GtPtF.IsIota z h ∧ GtPtF.IsAdd p.g h p'.g

end GtPoints

section Phi

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

namespace DegPre

def trPt (b : TF (R := R) F ⟶ D.P.A) : BF D F ⟶ BF D F :=
  lift (fst _ _) (padd D.P.A (prB D F) (fst _ _ ≫ b))

def phiφ (y α : D.X) (b : TF (R := R) F ⟶ D.P.A) : Fin 4 ⊕ Fin 4 → ((BF D F).left ⟶ D.P.A.left) :=
  Sum.elim (famφ D F (α + y)) (fun i => (trPt D F b).left ≫ famφ D F α i)

def lineφ (b : TF (R := R) F ⟶ D.P.A) : Fin 2 → ((TF (R := R) F).left ⟶ D.P.A.left) :=
  ![(zeroF D F).left, b.left]

def lineε (k : ℕ) : Fin 2 → ℤ := ![(k : ℤ), -(k : ℤ)]

def constBF (ζ : F) (W : (BF D F).left.Opens) : Γ((BF D F).left, W) :=
  ((BF D F).left.presheaf.map (homOfLE le_top).op).hom
    ((fst (TF (R := R) F) D.P.A).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ))

end DegPre

def PhiRel (k : ℕ) (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (s s' : Fam D F k) : Prop :=
  ∀ (α : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k))),
    u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (α + p.y)) (DegPre.famε k) (s'.s (α + p.y))
      (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (DegPre.trPt D F p.g.b).left
      (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k) u

def Fam.IsSmul {k : ℕ} (ζ : F) (s s' : Fam D F k) : Prop :=
  ∀ (α : D.X) (j : Fin 4 → D.P.L.ι), (s'.s α).f j = DegPre.constBF D F ζ _ * (s.s α).f j

def WeilQkIs (k : ℕ) (p p' : QkPt D F k) (ζ : F) : Prop :=
  ∀ (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε k))),
    w.IsGen → w'.IsGen →
    ∀ s s₁ s₂ s₃ s₄ : Fam D F k,
      PhiRel D F k p' w' s s₁ → PhiRel D F k p w s₁ s₂ →
      PhiRel D F k p w s s₃ → PhiRel D F k p' w' s₃ s₄ →
      Fam.IsSmul D F ζ s₄ s₂

end Phi

section QkToAk

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev TFK : Over (TK R).left := Over.mk (jFK (R := R) F)

def QkToAk (P' : PolAV (TK R).left) (k : ℕ)
    (E : LB.Sec (LPow P'.A P'.L (k : ℤ) (TFK (R := R) F)) → Fam D F k → Prop)
    (p : QkPt D F k) (x : TFK (R := R) F ⟶ P'.A) : Prop :=
  x ^ k = 1 ∧
    ∀ θ : ThetaGrp P'.A P'.L (k : ℤ) (TFK (R := R) F), θ.pt = x →
      ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w.IsGen ∧
        ∀ (t t' : LB.Sec (LPow P'.A P'.L (k : ℤ) (TFK (R := R) F))) (s s' : Fam D F k),
          E t s → E t' s' → IsActOf P'.A P'.L (k : ℤ) θ t t' → PhiRel D F k p w s s'

end QkToAk

section Bridge

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

namespace DegPre

abbrev jFR : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) := jFK (R := R) F ≫ jK R

abbrev BFo : Over (Spec (CommRingCat.of F)) := (Over.pullback (jFR (R := R) F)).obj D.P.A

end DegPre

end Bridge

end ReciprocityTheory.ChartRestriction.G.Out
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

namespace GeneratorPullback

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def finProdGen {J : Type} [Fintype J] (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := J × K) (fun p => φ p.1 p.2) (fun p => ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : J × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s _)

variable {X' : Scheme.{0}} (L' : LB X') {J : Type} [Fintype J]

lemma mapsAt_le_b (pr : J → (X' ⟶ X)) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jN, jL) ≤
      LB.wchart L (fun i => p ≫ pr i) jN := by
  intro x hx
  first
  | exact Set.mem_iInter.2 fun i => Set.mem_iInter.1 hx.2 i
  | exact Set.mem_iInter.2 fun i => Set.mem_iInter.1 hx.1 i

lemma mapsAt_le_a (pr : J → (X' ⟶ X)) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jN, jL) ≤
      LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) := by
  intro x hx
  first
  | exact Set.mem_iInter.2 fun _ => hx.1
  | exact Set.mem_iInter.2 fun _ => hx.2

def MapsAt (pr : J → (X' ⟶ X)) (w : LB.Iso L' (LB.LinComb L pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun _ => n))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAt_le_b L L' pr p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAt_le_a L L' pr p jN jL) (a.s (fun _ => jL))

end GeneratorPullback

section Pow

variable {S : Scheme.{0}}

structure IsPowPolAV (P' P : PolAV S) (j : ℕ) extends IsPowGrp P'.A P.A j where
  w : LB.Iso P'.L (boxLB P.L pr)
  w_gen : w.IsGen

end Pow

section PowDeg

variable {R : Type} [CommRing R] [IsDomain R]

structure IsPowDeg (D' D : DegPre R) (j : ℕ) where
  pw : IsPowGrp D'.P.A D.P.A j
  w : LB.Iso D'.P.L (boxLB D.P.L pw.pr)
  w_gen : w.IsGen
  w_rig : ∃ b : LB.Gen (LB.LinComb D.P.L (K := Fin j)
      (fun i => eSec D'.P.A ≫ (pw.pr i).left) (fun _ => 1)),
    GeneratorPullback.MapsAt D.P.L D'.P.L (fun i => (pw.pr i).left) w (eSec D'.P.A) 1 D'.rig b ∧
    LB.Gen.Corr D.P.L _ _ _ _ b
      (GeneratorPullback.finProdGen D.P.L (J := Fin j) (fun _ _ => eSec D.P.A) (fun _ _ => 1) (fun _ => D.rig))
  xe : D'.X ≃+ (Fin j → D.X)
  c_pr : ∀ (x : D'.X) (i : Fin j), D'.c x ≫ pw.pr i = D.c (xe x i)
  w_psi : ∀ x : D'.X, ∃ b : LB.Gen (LB.LinComb D.P.L (K := Fin j)
      (fun i => D'.xK x ≫ (pw.pr i).left) (fun _ => -1)),
    GeneratorPullback.MapsAt D.P.L D'.P.L (fun i => (pw.pr i).left) w (D'.xK x) (-1) (D'.psi x) b ∧
    LB.Gen.Corr D.P.L _ _ _ _ b
      (GeneratorPullback.finProdGen D.P.L (J := Fin j) (fun i _ => D.xK (xe x i)) (fun _ _ => -1)
        (fun i => D.psi (xe x i)))

end PowDeg

section UnifPow

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

structure UnifPowOf {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j)
    (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) where
  gen_pr : ∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom
  wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)
  wL_gen : wL.IsGen
  wL_rig : ∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j)
      (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)),
    GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧
    LB.Gen.Corr U.LG.L _ _ _ _ b
      (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))
  q_pr : ∀ (e : ℕ) (i : Fin j),
    (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) =
      (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q

end UnifPow

end ReciprocityTheory.ChartRestriction.G.Out
end
end

