module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def scal {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : R) :
    Γ(Y, ⊤) :=
  p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

abbrev resTop {Y : Scheme.{0}} (W : Y.Opens) (c : Γ(Y, ⊤)) : Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom c

abbrev H0 {Y : Scheme.{0}} (L : LB Y) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ)))

namespace GeneratorPullback

variable {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

def SecScal (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (c : Γ(Y', ⊤)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) →
    (Y'.presheaf.map (homOfLE (inf_le_right.trans
        (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤
          h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom (s₂.f j₂)) =
      resTop _ c *
      (Y'.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ LB.wchart L φ₁ j₁)).op).hom
        (s₁.f j₁)

end GeneratorPullback

namespace DegPre

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def famφB (α : D.X) : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![𝟙 _, (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left, (toUnit D.P.A ≫ D.c α).left,
    (toUnit D.P.A ≫ η[D.P.A]).left]

abbrev SecB (k : ℕ) (α : D.X) : Type := LB.Sec (LB.LinComb D.P.L (famφB D α) (famε k))

end DegPre

def CohAll {X Y : Scheme.{0}} (L : LB X) {Idx : Type} (φ : Idx → (Y ⟶ X)) (j : Idx → L.ι) : Prop :=
  ∀ a b, φ a = φ b → j a = j b

section Expansion

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

namespace UnifPre

variable (U : UnifPre I D A G)

abbrev SecK (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)))

abbrev expW (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) :
    (thickObj R I e G).left.Opens :=
  (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U p ⊓
    (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁ ⊓
    S.inf (fun α => (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) ⊓
      LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG α) (jt α))

lemma expW_le_f (e : ℕ) (p) (j₁) {S : Finset D.toPre.X} (jf jt) {α : D.toPre.X} (hα : α ∈ S) :
    U.expW e p j₁ S jf jt ≤ (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) :=
  inf_le_right.trans ((Finset.inf_le hα).trans inf_le_left)

lemma expWeight_le_chart_weight (e : ℕ) (p) (j₁) {S : Finset D.toPre.X} (jf jt) {α : D.toPre.X} (hα : α ∈ S) :
    U.expW e p j₁ S jf jt ≤ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG α) (jt α) :=
  inf_le_right.trans ((Finset.inf_le hα).trans inf_le_right)

def ExpandsAt (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) : Prop :=
  ∃ S : Finset D.toPre.X,
    (∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) ∧
    ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      j₁ 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res (inf_le_left.trans inf_le_left :
          U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
          U.expW e p j₁ S jf jt ≤
            (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
          (((fstG I e G).left.app _).hom (σ.f j₁)) =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val

def Expands (k : ℕ) (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k) : Prop :=
  ∃ (r : R) (_ : r ≠ 0)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α),
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r) ∧
    (∀ α : D.toPre.X,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r)) ∧
    ∀ e : ℕ, U.ExpandsAt e k σ f

def ExpBij (k : ℕ) : Prop :=
  (∀ s : U.SecK k, ∃! F : Fam D.toPre (FractionRing R) k, U.Expands k s F) ∧
    ∀ F : Fam D.toPre (FractionRing R) k, ∃! s : U.SecK k, U.Expands k s F

end UnifPre

end Expansion

structure Unif {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    extends UnifPre I D A G where
  expand : ∀ k : ℕ, 1 ≤ k → toUnifPre.ExpBij k

end ReciprocityTheory.ChartRestriction.G.Out
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

def TorusEndOf {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : Prop :=
  ∀ χ : X, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) = charUnit S X (h χ)

structure UnifPre.OLinear (O : Type) [Ring O] [StarRing O] {D : DegData R I}
    [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) : Prop where
  ext : ∀ a : O, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a
  q_lin : ∀ (e : ℕ) (a : O), (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
    (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a)
  i_lin : ∀ (e : ℕ) (a : O), ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
      splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
    TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
      (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i

end ReciprocityTheory.ChartRestriction.G.Out
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def negT (T : Over S) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ (GrpObj.inv : A ⟶ A))

def negLB (L : LB A.left) (k : ℤ) (T : Over S) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k]

def powφ {T : Over S} (x : T ⟶ A) (n : ℕ) : Fin n × Fin 2 → ((T ⊗ A).left ⟶ A.left) :=
  fun p => (translT A (x ^ (p.1 : ℕ))).left ≫ (![(snd T A).left, (translPt A x).left] p.2)

def powε (k : ℤ) (n : ℕ) : Fin n × Fin 2 → ℤ := fun p => ![k, -k] p.2

def powGen (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) :
    LB.Gen (LB.LinComb L (powφ A θ.pt n) (powε k n)) where
  s := fun j => ∏ j₀ : Fin n,
    res ((fun _ hy => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (j₀, b)) :
        LB.wchart L (powφ A θ.pt n) j ≤
          LB.wchart L (fun b => (translT A (θ.pt ^ (j₀ : ℕ))).left ≫
            (![(snd T A).left, (translPt A θ.pt).left] b)) (fun b => j (j₀, b)))
      ((LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j₀ : ℕ))).left).s (fun b => j (j₀, b)))

def symGen (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T)
    (nu : LB.Gen (negLB A L k T)) :=
  LB.mulGen L _ _ _ _
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) nu)
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ θ.φ (negT A T).left)
      (LB.invGen L _ _ (LB.pullGen L _ _ nu (translT A θ.pt⁻¹).left)))

structure SymLift (L : LB A.left) (k : ℤ) (n : ℕ) {T : Over S} (x : T ⟶ A)
    (θ : ThetaGrp A L k T) : Prop where

  pt_eq : θ.pt = x

  pow_eq : LB.Gen.Corr L _ _ _ _ (powGen A L k θ n) (LB.oneGen L)

  sym : ∃ nu : LB.Gen (negLB A L k T), nu.IsGen ∧ LB.Gen.Corr L _ _ _ _ (symGen A L k θ nu) (LB.oneGen L)

def LPow (L : LB A.left) (a : ℤ) (T : Over S) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => a)

def liftFun {T : Over S} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) : Γ((T ⊗ A).left, W) :=
  ((T ⊗ A).left.presheaf.map (homOfLE le_top).op).hom ((fst T A).left.appTop.hom r)

theorem chart_le_zero (L : LB A.left) {T : Over S} (m : T ⊗ A ⟶ A) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, m.left] j ≤ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0

theorem chart_le_pull (L : LB A.left) {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A)
    (hm : ψ ≫ snd T A = m) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, m.left] j ≤
      ψ.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1) := by
  intro y hy
  have h1 : m.left.base y ∈ (L.U (j 1) : Set A.left) := Set.mem_iInter.1 hy 1
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun _ => h1

def IsTwistPull (L : LB A.left) {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A)
    (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]))
    (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) : Prop :=
  ∀ j : Fin 2 → L.ι,
    ((T ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L m j)).op).hom (s'.f (fun _ => j 0)) =
      (show Γ((T ⊗ A).left, LB.wchart L ![(snd T A).left, m.left] j) from (α.s j).val) *
        ((T ⊗ A).left.presheaf.map (homOfLE (chart_le_pull A L ψ m hm j)).op).hom
          ((ψ.left.app _).hom (s.f (fun _ => j 1)))

def IsActOf (L : LB A.left) (k : ℤ) {T : Over S} (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)) : Prop :=
  IsTwistPull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) k k θ.φ s s'

def IsGenSec (L : LB A.left) (a : ℤ) {T : Over S} (th : LB.Sec (LPow A L a T)) : Prop :=
  ∀ s : LB.Sec (LPow A L a T), ∃ r : Γ(T.left, ⊤), ∀ j, s.f j = liftFun A _ r * th.f j

def ptSecT {T : Over S} (z : T ⟶ A) : T ⟶ T ⊗ A := lift (𝟙 T) z

theorem val_le (L : LB A.left) {T : Over S} (z : T ⟶ A) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => z.left) j ≤
      (ptSecT A z).left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := by
  intro y hy
  have h1 : z.left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have e : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun i => by
    rw [Subsingleton.elim i 0]; exact h1

def IsValueAt (L : LB A.left) (a : ℤ) {T : Over S} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v : Γ(T.left, ⊤)) : Prop :=
  ∀ j : Fin 1 → L.ι,
    (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) =
      (T.left.presheaf.map (homOfLE le_top).op).hom v * (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from (τ.s j).val)

def mulT (T : Over S) (k : ℕ) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ^ k)

def IsThetaPtOver (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left)
      (fun _ => (k : ℤ) ^ 2)))
    (U : I → ThetaGrp P.A P.L ((k : ℤ) ^ 2) T) (s2 : I → LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T))
    (w : I → Γ(T.left, ⊤)) (u : Γ(T.left, ⊤)ˣ),
    IsGenSec P.A P.L 1 th ∧ α.IsGen ∧ τ.IsGen ∧
    IsTwistPull P.A P.L (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α th s1 ∧
    (∀ i, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) (U i)) ∧
    (∀ i, IsActOf P.A P.L ((k : ℤ) ^ 2) (U i) s1 (s2 i)) ∧
    (∀ i, IsValueAt P.A P.L ((k : ℤ) ^ 2) (s2 i) 1 τ (w i)) ∧
    ∀ i, v i = (u : Γ(T.left, ⊤)) * w i

def IsThetaPt (P : PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v : I → Γ(T.left, ⊤)) : Prop :=
  Odd k ∧ IsUnit (k : Γ(T.left, ⊤)) ∧ ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    IsThetaPtOver P k (fun i => overResι V ≫ x i) (fun i => V.ι.appTop.hom (v i))

def IsVVGen (P : PolAV S) (N m : ℕ) {T : Over S} (t : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L N T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : ThetaGrp P.A P.L N T),
    α.IsGen ∧ IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s1 ∧
    IsActOf P.A P.L N U s1 t

def InVVOver (P : PolAV S) (N m : ℕ) {T : Over S} (s : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∃ (n : ℕ) (r : Fin n → Γ(T.left, ⊤)) (t : Fin n → LB.Sec (LPow P.A P.L N T)),
    (∀ l, IsVVGen P N m (t l)) ∧ ∀ j, s.f j = ∑ l, liftFun P.A _ (r l) * (t l).f j

theorem chart_le_res (L : LB A.left) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (a : ℤ) (j : Fin 1 → L.ι) :
    (LPow A L a T').U j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j := by
  intro y hy
  have h1 : (snd T' A).left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have e : h.left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, hh]
  rw [← e] at h1
  exact Set.mem_iInter.2 fun i => by
    rw [Subsingleton.elim i 0]; exact h1

def IsPullSec (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
    (hh : h ≫ snd T A = snd T' A) (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) : Prop :=
  ∀ j, s'.f j = ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom
    ((h.left.app _).hom (s.f j))

def InVV (P : PolAV S) (N m : ℕ) {T : Over S} (s : LB.Sec (LPow P.A P.L N T)) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ sV : LB.Sec (LPow P.A P.L N (overRes V)),
    IsPullSec P.A P.L N (overResι V ▷ P.A) (whiskerRight_snd _ _) s sV ∧ InVVOver P N m sV

def IsEvT (P : PolAV S) (N : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => (N : ℤ))))
    (s : LB.Sec (LPow P.A P.L N T)) (w : I → Γ(T.left, ⊤)) : Prop :=
  ∀ i, IsValueAt P.A P.L N s (x i) (τ i) (w i)

end ReciprocityTheory.ChartRestriction.G.Out
end
end

