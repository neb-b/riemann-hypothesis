module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

namespace GeneratorPullback

section Lin

variable {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

def SecLin (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ} (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) →
    (Y'.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ LB.wchart L φ₁ j₁)).op).hom
        (s₁.f j₁) =
      ∑ i, resTop _ (c i) *
        (Y'.presheaf.map (homOfLE (inf_le_right.trans
          (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
          LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤
            h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom ((s₂ i).f j₂))

end Lin

section IsoRel

variable {Y Y' X₁ X₂ Z₁ Z₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂)

abbrev isoW (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (m : Y' ⟶ Y) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁)
    (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂) (p : (PUnit.{1} → L₂.ι) × (PUnit.{1} → L₁.ι))
    (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι) : Y'.Opens :=
  m ⁻¹ᵁ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U p ⊓
    h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) j₁ ⊓ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) j₂

def IsoRelM (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y)
    (k : ℕ) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂)
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))) : Prop :=
  h₁ ≫ g₁ = m ≫ f₁ ∧ h₂ ≫ g₂ = m ≫ f₂ ∧
  ∀ (p : (PUnit.{1} → L₂.ι) × (PUnit.{1} → L₁.ι)) (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι),
    j₁ 0 = p.2 PUnit.unit → j₂ 0 = p.1 PUnit.unit →
    (Y'.presheaf.map (homOfLE (inf_le_right :
        isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) j₂)).op).hom
        ((h₂.app _).hom (b.f j₂)) =
      (res (inf_le_left.trans inf_le_left :
          isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ m ⁻¹ᵁ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U p)
          (pullU m _ (w.s p))).val ^ k *
      (Y'.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) j₁)).op).hom
        ((h₁.app _).hom (a.f j₁))

end IsoRel

end GeneratorPullback

section ExpansionF

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

namespace UnifPre

variable (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev GF : Over (TK R).left := TFK (R := R) F ⊗ (Over.pullback (jK R)).obj G

abbrev gFK : (GF (G := G) F).left ⟶ G.left :=
  (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R)

abbrev genF : GF (G := G) F ⟶ TFK (R := R) F ⊗ A.A :=
  lift (fst _ _) (snd _ _ ≫ U.gen.hom)

abbrev SecGF (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => gFK (G := G) F) (fun _ => (k : ℤ)))

def ExpandsG (k : ℕ) (σ' : U.SecGF F k) (s : Fam D.toPre F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F)
    (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : Fin n → ∀ α : D.toPre.X, D.toPre.SecB k α),
    (∀ i e, U.ExpandsAt e k (σ i) (f i)) ∧
    GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => gFK (G := G) F) (fun _ => (k : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)) ∧
    ∀ α : D.toPre.X,
      GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
        (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))

def ExpandsF (k : ℕ)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Fam D.toPre F k) : Prop :=
  ∃ σ' : U.SecGF F k,
    GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
      (snd (TFK (R := R) F) A.A).left (U.genF F).left t
      (gFK (G := G) F) (𝟙 _) σ' ∧
    U.ExpandsG F k σ' s

end UnifPre

end ExpansionF

end ReciprocityTheory.ChartRestriction.G.Out
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
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
variable (T : Over (Spec (CommRingCat.of R)))

namespace DegPre

abbrev cT (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

abbrev zeroT : T ⟶ D.P.A := toUnit T ≫ η[D.P.A]

def gtφT (b : T ⟶ D.P.A) (χ : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cT D T χ) b).left, (cT D T χ).left, b.left, (zeroT D T).left]

def cubAtT (x x' y : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left

end DegPre

structure GtPt where
  b : T ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ'))
      (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))

namespace GtPt

variable {D T}

def IsZero (g : GtPt D T) : Prop :=
  g.b = DegPre.zeroT D T ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)

def IsAdd (g g' g'' : GtPt D T) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (DegPre.cubAtT D T (DegPre.cT D T χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))

def IsNsmul (k : ℕ) (g h : GtPt D T) : Prop :=
  ∃ gs : Fin (k + 1) → GtPt D T, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h

def IsPull {T' : Over (Spec (CommRingCat.of R))} (h : T'.left ⟶ T.left) (g : GtPt D T)
    (g' : GtPt D T') : Prop :=
  g'.b.left = h ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) h)

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def IsPullF (x : Spec (CommRingCat.of F) ⟶ T.left) (g : GtPt D T) (g' : GtPtF D F) : Prop :=
  g'.b.left = x ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) x)

end GtPt

end GtPoints

section OnW

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (W : (Spec (CommRingCat.of R)).Opens)

abbrev TW : Over (Spec (CommRingCat.of R)) := Over.mk W.ι

abbrev overW (T : Over W.toScheme) : Over (Spec (CommRingCat.of R)) := (Over.map W.ι).obj T

structure PsiOn where
  psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit)
    (fun _ => (toUnit (TW W) ≫ D.c χ).left) (fun _ => -1))
  psi_gen : ∀ χ, (psi χ).IsGen
  psi_eq : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (psi χ) (jK R ∣_ W))
    (LB.pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι)

namespace DegPre

def rigW := LB.pullGen D.P.L _ _ D.rig (toUnit (TW W)).left

end DegPre

namespace PsiOn

variable {D W}

def tau (ψW : PsiOn D W) (a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi (a + b)) (LB.invGen D.P.L _ _ (ψW.psi a)))
      (LB.invGen D.P.L _ _ (ψW.psi b)))
    (LB.invGen D.P.L _ _ (D.rigW W))

end PsiOn

def GtPt.IsIotaW {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W)
    {T : Over W.toScheme} (y : D.X) (g : GtPt D (overW W T)) : Prop :=
  g.b = DegPre.cT D (overW W T) y ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ)
    (LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom)

structure QkPtW (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) where
  y : D.X
  g : GtPt D (overW W T)
  eq : ∃ h : GtPt D (overW W T), GtPt.IsNsmul k g h ∧ GtPt.IsIotaW ψW y h

namespace QkPtW

variable {D W} {ψW : PsiOn D W} {k : ℕ} {T : Over W.toScheme}

def IsAdd (p p' p'' : QkPtW D W ψW k T) : Prop :=
  p''.y = p.y + p'.y ∧ GtPt.IsAdd p.g p'.g p''.g

def IsPull {T' : Over W.toScheme} (h : T' ⟶ T) (p : QkPtW D W ψW k T) (p' : QkPtW D W ψW k T') :
    Prop :=
  p'.y = p.y ∧ GtPt.IsPull h.left p.g p'.g

def IsPullF (F : Type) [Field F] [Algebra (FractionRing R) F]
    (x : Spec (CommRingCat.of F) ⟶ T.left) (p : QkPtW D W ψW k T) (p' : QkPt D F k) : Prop :=
  p'.y = p.y ∧ GtPt.IsPullF F x p.g p'.g

end QkPtW

end OnW

end ReciprocityTheory.ChartRestriction.G.Out
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Theta1
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.InhVV

open Semi Inh

variable (S : Scheme.{0}) (T : Over S)

def rig1 : LB.Gen ((zeroPolAV S).L.pull (eSec (zeroPolAV S).A)) := ⟨fun _ => 1⟩

def one1 (x : T ⟶ (zeroPolAV S).A) (k : ℤ) :
    LB.Gen (LB.LinComb (zeroPolAV S).L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k)) :=
  ⟨fun _ => 1⟩

def theta1 (k : ℤ) : ThetaGrp (zeroPolAV S).A (zeroPolAV S).L k T where
  pt := 1
  φ := ⟨fun _ => 1⟩
  isGen := by
    intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]

def oneSec (a : ℤ) (T : Over S) : LB.Sec (LPow (zeroPolAV S).A (zeroPolAV S).L a T) :=
  ⟨fun _ => 1, by
    intro i j
    erw [linComb_triv_g]
    simp only [Units.val_one, map_one]
    exact (_root_.one_mul _).symm⟩

end ReciprocityTheory.ChartRestriction.G.Out.InhVV
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowSt2
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

structure UnifPowOf2 {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j)
    (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G)
    extends UnifPowOf pD pA pG U' U where

  t_pr : ∀ (e : ℕ) (x : D'.toPre.X),
    ∃ hψ : ∀ (i : Fin j) (k : Fin 4),
        D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫
          (pD.pw.pr i).left =
        ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫
          D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k,
      LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x)
        (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i =>
          GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left
            ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i)
            ((U.gt e).t (pD.xe x i))))

end ReciprocityTheory.ChartRestriction.G.Out
end
end

