module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def stdSymp (g : ℕ) (i j : Fin (2 * g)) : ℤ :=
  if (i : ℕ) < g ∧ (j : ℕ) = (i : ℕ) + g then 1
  else if (j : ℕ) < g ∧ (i : ℕ) = (j : ℕ) + g then -1 else 0

variable {S : Scheme.{0}}

abbrev baseOver (S : Scheme.{0}) : Over S := Over.mk (𝟙 S)

def linComb {A : Over S} [GrpObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    T ⟶ A :=
  (List.ofFn fun i => y i ^ a i).prod

structure Level (P : PolAV S) (k : ℕ) (ze : Γ(S, ⊤)ˣ) where

  pt : Fin (2 * P.g) → (baseOver S ⟶ P.A)

  prim : IsPrimitiveRoot ze k

  torsion : ∀ i, pt i ^ k = 1

  indep : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * P.g) → Fin k),
    linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c' i : ℕ)) →
    c = c'

  span : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A), y ^ k = 1 →
    ∃ c : Fin (2 * P.g) → Fin k,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) = y

  pairing : ∀ i j, WeilIs P.A P.L k (pt i) (pt j) (ze ^ stdSymp P.g i j)

def Level.toPt {P : PolAV S} {k : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P k ze)
    (a : Fin (2 * P.g) → ZMod k) : baseOver S ⟶ P.A :=
  linComb lev.pt (fun i => (a i).val)

end ReciprocityTheory.ChartRestriction.G.Out
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

section Unif

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)

namespace DegPre

variable (D : DegPre R)

def Oφ {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A p (toUnit T ≫ D.c χ)).left, (toUnit T ≫ D.c χ).left, p.left,
    (toUnit T ≫ η[D.P.A]).left]

def prBe (e : ℕ) : (Over.map (thick R I e)).obj (thickObj R I e D.P.A) ⟶ D.P.A :=
  Over.homMk (pullback.fst D.P.A.hom (thick R I e)) pullback.condition

end DegPre

def Oε : Fin 4 → ℤ := ![1, -1, -1, 1]

def Oinvε : Fin 4 → ℤ := ![-1, 1, 1, -1]

def fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ G :=
  Over.homMk (pullback.fst G.hom (thick R I e)) pullback.condition

def charGen {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {Z : Scheme.{0}} (L : LB Z)
    (χ : X) : LB.Gen (LB.LinComb L (Y := (splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim
      PEmpty.elim) where
  s := fun _ => res (fun x _ => show (fst (splitTorus S X) G).left.base x ∈ (⊤ : TopologicalSpace.Opens _)
      from trivial) (pullU (fst (splitTorus S X) G).left ⊤ (charUnit S X χ))

structure GtCoord (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] where
  q : thickObj R I e G ⟶ thickObj R I e D.P.A
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surj : Surjective q.left
  q_affine : IsAffineHom q.left
  i : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ thickObj R I e G
  i_hom : IsMonHom i
  isKernel : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A])
  t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L
    (D.Oφ ((Over.map (thick R I e)).map q ≫ D.prBe I e) χ) Oinvε)
  t_gen : ∀ χ, (t χ).IsGen
  t_mul : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
        (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ')
          ((Over.map (thick R I e)).map q ≫ D.prBe I e))).left))
    (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))
  t_unit : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (t χ) (eSec (thickObj R I e G))) (LB.oneGen D.P.L)
  t_weight : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (t χ)
      (lift (fst (splitTorus _ D.X) (thickObj R I e G) ≫ i) (snd _ _) ≫ μ[thickObj R I e G]).left)
    (LB.mulGen D.P.L _ _ _ _ (charGen D.X (thickObj R I e G) D.P.L χ)
      (LB.pullGen D.P.L _ _ (t χ) (snd (splitTorus _ D.X) (thickObj R I e G)).left))

namespace GtCoord

variable {I} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

abbrev pG (g : GtCoord I D e G) : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.P.A :=
  (Over.map (thick R I e)).map g.q ≫ D.prBe I e

end GtCoord

end Unif

section UnifPre

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)

structure UnifPre (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  gen : (Over.pullback (jK R)).obj G ≅ A.A
  gen_hom : IsMonHom gen.hom
  LG : RigLB G
  cubG : CubicalStr G LG
  symG : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])
  symG_gen : symG.IsGen
  symG_rig : LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ symG (eSec G)) (LB.oneGen LG.L)
  ext : ∃ w : LB.Iso (A.L.pull gen.hom.left) (LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen
  gt : ∀ e : ℕ, GtCoord I D.toPre e G
  gt_q : ∀ e : ℕ, thickMap R I e G ≫ (gt (e + 1)).pG.left = (gt e).pG.left
  gt_t : ∀ (e : ℕ) (χ : D.toPre.X), LB.Gen.Corr D.toPre.P.L _ _ _ _
    (LB.pullGen D.toPre.P.L _ _ ((gt (e + 1)).t χ) (thickMap R I e G)) ((gt e).t χ)
  w : ∀ e : ℕ, LB.Iso (LG.L.pull (fstG I e G).left) (D.toPre.P.L.pull (gt e).pG.left)
  w_gen : ∀ e, (w e).IsGen
  w_rig : ∀ (e : ℕ) (p : (PUnit → D.toPre.P.L.ι) × (PUnit → LG.L.ι))
    (V : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))).Opens)
    (h₁ : V ≤ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (gt e).pG.left).U p.1 ⊓ (LG.L.pull (fstG I e G).left).U p.2))
    (h₂ : V ≤ thick R I e ⁻¹ᵁ (LG.L.pull (eSec G)).U p.2)
    (h₃ : V ≤ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U p.1),
    res h₁ (pullU (eSec (thickObj R I e G)) _ ((w e).s p)) *
      res h₂ (pullU (thick R I e) _ (LG.rig.s p.2)) =
      res h₃ (pullU (thick R I e) _ (D.toPre.rig.s p.1))
  w_even : ∀ (e : ℕ) (jS : Fin 2 → LG.L.ι) (jT : Fin 2 → D.toPre.P.L.ι),
    LB.Coh LG.L (fun k => (fstG I e G).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) jS →
    LB.Coh D.toPre.P.L
      (fun k => (gt e).pG.left ≫ (![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] : Fin 2 → _) k) jT →
    ∀ (V : (thickObj R I e G).left.Opens)
      (h₁ : V ≤ (gt e).pG.left ⁻¹ᵁ (LB.LinComb D.toPre.P.L (K := Fin 2)
        ![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] ![1, -1]).U jT)
      (h₂ : V ≤ (D.toPre.P.L.pull (gt e).pG.left).U (fun _ => jT 1) ⊓
        (LG.L.pull (fstG I e G).left).U (fun _ => jS 1))
      (h₃ : V ≤ (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.toPre.P.L.pull (gt e).pG.left).U (fun _ => jT 0) ⊓
        (LG.L.pull (fstG I e G).left).U (fun _ => jS 0)))
      (h₄ : V ≤ (fstG I e G).left ⁻¹ᵁ (LB.LinComb LG.L (K := Fin 2)
        ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS),
      res h₁ (pullU (gt e).pG.left _ (D.toPre.sym.s jT)) *
        res h₂ ((w e).s (fun _ => jT 1, fun _ => jS 1)) =
      res h₃ (pullU (ι[thickObj R I e G]).left _ ((w e).s (fun _ => jT 0, fun _ => jS 0))) *
        res h₄ (pullU (fstG I e G).left _ (symG.s jS))
  w_cub : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → LG.L.ι) (jM : thK → D.toPre.P.L.ι),
    LB.Coh LG.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL →
    LB.Coh D.toPre.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ (gt e).pG)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ (gt e).pG)
        ((Over.map (thick R I e)).map (x 2) ≫ (gt e).pG))).left ≫
          thφ D.toPre.P.A (x3 D.toPre.P.A) k) jM →
    ∀ (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ (gt e).pG)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ (gt e).pG)
          ((Over.map (thick R I e)).map (x 2) ≫ (gt e).pG))).left ⁻¹ᵁ
            (Theta D.toPre.P.A D.toPre.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G LG.L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.toPre.P.L.pull (gt e).pG.left).U (fun _ => jM k) ⊓
          (LG.L.pull (fstG I e G).left).U (fun _ => jL k))),
      res hB (pullU _ _ (D.toPre.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          ((w e).s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (cubG.t.s jL))
  w_compat : ∀ (e : ℕ) (p : (PUnit → D.toPre.P.L.ι) × (PUnit → LG.L.ι))
    (V : (thickObj R I e G).left.Opens)
    (h₁ : V ≤ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (gt (e + 1)).pG.left).U p.1 ⊓
      (LG.L.pull (fstG I (e + 1) G).left).U p.2))
    (h₂ : V ≤ (D.toPre.P.L.pull (gt e).pG.left).U p.1 ⊓ (LG.L.pull (fstG I e G).left).U p.2),
    res h₁ (pullU (thickMap R I e G) _ ((w (e + 1)).s p)) = res h₂ ((w e).s p)

end UnifPre

end ReciprocityTheory.ChartRestriction.G.Out
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

section Act

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

structure RingAct (O : Type) [Ring O] where

  act : O → (A ⟶ A)
  hom : ∀ a, IsMonHom (act a)
  map_one : act 1 = 𝟙 A
  map_mul : ∀ a b, act (a * b) = act b ≫ act a
  map_add : ∀ a b, act (a + b) = padd A (act a) (act b)

def rosatiφ (f g : A ⟶ A) : Fin 6 → ((A ⊗ A).left ⟶ A.left) :=
  ![(padd A (fst A A ≫ f) (snd A A)).left, (fst A A ≫ f).left, (snd A A).left,
    (padd A (fst A A) (snd A A ≫ g)).left, (fst A A).left, (snd A A ≫ g).left]

def rosatiε : Fin 6 → ℤ := ![1, -1, -1, -1, 1, 1]

def RosatiAdj (L : LB A.left) (f g : A ⟶ A) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 6)
        (fun i => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) rosatiε), t.IsGen

abbrev zero2 : (𝟙_ (Over S)).left ⟶ (A ⊗ A).left := (lift η[A] η[A]).left

end Act

structure PolAV.OAct (O : Type) [Ring O] [StarRing O] {S : Scheme.{0}} (P : PolAV S)
    extends RingAct P.A O where
  rosati : ∀ a : O, RosatiAdj P.A P.L (act a) (act (star a))

namespace DegPre

variable {R : Type} [CommRing R] [IsDomain R]

def pt2 (D : DegPre R) (y y' : D.X) : (TK R).left ⟶ (D.P.A ⊗ D.P.A).left :=
  (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D.c y')).left

def TauBal (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X) : Prop :=
  ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
    ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau (a y) y') (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (D.tau y (a' y'))

structure OAct (O : Type) [Ring O] [StarRing O] (D : DegPre R) [Module O D.X] where
  onB : D.P.OAct O
  c_lin : ∀ (a : O) (y : D.X), D.c (a • y) = D.c y ≫ onB.act a
  tau_bal : ∀ a : O, D.TauBal (onB.act a) (onB.act (star a)) (fun y => a • y) (fun y => star a • y)

end DegPre

abbrev DegData.OAct (O : Type) [Ring O] [StarRing O] {R : Type} [CommRing R] [IsDomain R]
    {I : Ideal R} (D : DegData R I) [Module O D.toPre.X] := D.toPre.OAct O

namespace Inh

def zeroOAct (O : Type) [Ring O] [StarRing O] (S : Scheme.{0}) : (zeroPolAV S).OAct O where
  act := fun _ => 𝟙 _
  hom := fun _ => inferInstance
  map_one := rfl
  map_mul := fun _ _ => (Category.id_comp _).symm
  map_add := fun _ _ => toUnit_unique _ _
  rosati := fun _ _ => ⟨⊤, trivial, ⟨fun _ => 1⟩, by
    intro i j; erw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]⟩

end Inh

end ReciprocityTheory.ChartRestriction.G.Out
end
end

