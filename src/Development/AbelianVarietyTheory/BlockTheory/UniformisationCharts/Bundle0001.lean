module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.TorusPointForms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.BaseChangeCharts
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

section FamBaseChange

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def overHom {S X Y : Scheme.{0}} (a : X ⟶ S) (b : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ b = a) :
    Over.mk a ⟶ Over.mk b := Over.homMk h w

omit [IsDomain R] in
lemma specMap_algebraMap_self (K : Type) [CommRing K] :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

def specFK : TF (R := R) F ⟶ TF (R := R) (FractionRing R) :=
  overHom (X := Spec (CommRingCat.of F)) (Y := Spec (CommRingCat.of (FractionRing R))) _ _
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
    (congrArg (fun z => Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫ z)
      ((congrArg (fun z => z ≫ jK R) (specMap_algebraMap_self (FractionRing R))).trans
        (Category.id_comp _)))

def bcB : DegPre.BF D F ⟶ DegPre.BF D (FractionRing R) := specFK (R := R) F ▷ D.P.A

lemma bcB_prB : bcB D F ≫ DegPre.prB D (FractionRing R) = DegPre.prB D F := by
  simp [bcB]

lemma bcB_famφ (α : D.X) (i : Fin 4) :
    (bcB D F).left ≫ DegPre.famφ D (FractionRing R) α i = DegPre.famφ D F α i := by
  have hu : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A,
      bcB D F ≫ toUnit _ ≫ x = toUnit _ ≫ x := fun x => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases i
  · exact congrArg (·.left) (bcB_prB D F)
  · have : bcB D F ≫ padd D.P.A (DegPre.prB D (FractionRing R)) (toUnit _ ≫ D.c α) =
        padd D.P.A (DegPre.prB D F) (toUnit _ ≫ D.c α) := by
      unfold padd
      rw [← Category.assoc, comp_lift, bcB_prB, hu]
    exact congrArg (·.left) this
  · exact congrArg (·.left) (hu (D.c α))
  · exact congrArg (·.left) (hu η[D.P.A])

lemma chart_le_bcB (α : D.X) (j : Fin 4 → D.P.L.ι) :
    LB.wchart D.P.L (DegPre.famφ D F α) j ≤
      (bcB D F).left ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D (FractionRing R) α) j := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : (DegPre.famφ D F α i).base y ∈ (D.P.L.U (j i) : Set D.P.A.left) :=
    Set.mem_iInter.1 hy i
  rw [← bcB_famφ D F α i] at h1
  exact h1

def FamComb (k : ℕ) {n : ℕ} (c : Fin n → F) (f : Fin n → Fam D (FractionRing R) k)
    (s : Fam D F k) : Prop :=
  ∀ (α : D.X) (j : Fin 4 → D.P.L.ι),
    @id Γ((DegPre.BF D F).left, LB.wchart D.P.L (DegPre.famφ D F α) j) ((s.s α).f j) =
      ∑ i, DegPre.constBF D F (c i) (LB.wchart D.P.L (DegPre.famφ D F α) j) *
        ((DegPre.BF D F).left.presheaf.map (homOfLE (chart_le_bcB D F α j)).op).hom
          (((bcB D F).left.app (LB.wchart D.P.L (DegPre.famφ D (FractionRing R) α) j)).hom
            (((f i).s α).f j))

end FamBaseChange

section Expansion

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def Ident (U : UnifPre I D A G) : Type :=
  {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))) // w.IsGen}

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev AF (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) : Scheme.{0} :=
  (TFK (R := R) F ⊗ A.A).left

abbrev SecF (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (k : ℕ) : Type :=
  LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))

def toGK (U : UnifPre I D A G) : AF F A ⟶ pullback G.hom (jK R) :=
  (snd (TFK (R := R) F) A.A ≫ U.gen.inv).left

lemma toGK_gen (U : UnifPre I D A G) :
    toGK F U ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left := by
  have : (snd (TFK (R := R) F) A.A ≫ U.gen.inv) ≫ U.gen.hom = snd (TFK (R := R) F) A.A := by
    simp
  exact congrArg (·.left) this

abbrev cmpW (U : UnifPre I D A G) (a : U.LG.L.ι) (b : A.L.ι) : (AF F A).Opens :=
  toGK F U ⁻¹ᵁ ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => a) ⊓
    (A.L.pull U.gen.hom.left).U (fun _ => b))

lemma cmpW_le_L (U : UnifPre I D A G) (k : ℕ) (a : U.LG.L.ι) (b : A.L.ι) :
    cmpW F U a b ≤ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U (fun _ => b) := by
  intro y hy
  have h1 : (toGK F U ≫ U.gen.hom.left).base y ∈ (A.L.U b : Set A.A.left) :=
    Set.mem_iInter.1 hy.2 PUnit.unit
  rw [toGK_gen] at h1
  exact Set.mem_iInter.2 fun _ => h1

lemma cmpW_le_LG (U : UnifPre I D A G) (a : U.LG.L.ι) (b : A.L.ι) :
    cmpW F U a b ≤ toGK F U ⁻¹ᵁ
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => a) := by
  intro y hy
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 PUnit.unit

def SecComb (U : UnifPre I D A G) (w : Ident U) (k : ℕ) {n : ℕ} (c : Fin n → F)
    (σ : Fin n → U.SecK k) (t : SecF F A k) : Prop :=
  ∀ (a : U.LG.L.ι) (b : A.L.ι),
    @id Γ(AF F A, cmpW F U a b) (pullU (toGK F U) _ (w.1.s (fun _ => a, fun _ => b))).val ^ k *
      ((AF F A).presheaf.map (homOfLE (cmpW_le_L F U k a b)).op).hom (t.f (fun _ => b)) =
    ∑ i, @id Γ(AF F A, cmpW F U a b) (liftFun A.A (T := TFK (R := R) F) (cmpW F U a b)
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) *
      ((AF F A).presheaf.map (homOfLE (cmpW_le_LG F U a b)).op).hom
        (((toGK F U).app _).hom ((σ i).f (fun _ => a)))

def ExpandsF (U : UnifPre I D A G) (w : Ident U) (k : ℕ) (t : SecF F A k)
    (s : Fam D.toPre F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → U.SecK k)
    (f : Fin n → Fam D.toPre (FractionRing R) k),
    (∀ i, U.Expands k (σ i) (f i)) ∧ SecComb F U w k c σ t ∧ FamComb D.toPre F k c f s

end Expansion

end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.PairingRatioBijection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def scal : F →+* Γ(Spec (CommRingCat.of F), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

def trPt (b : TF (R := R) F ⟶ D.P.A) : D.BF F ⟶ D.BF F :=
  lift (fst _ _) (padd D.P.A (D.prB F) (fst _ _ ≫ b))

abbrev lineAt (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : LB (TF (R := R) F).left :=
  LB.LinComb D.P.L (K := PUnit) (fun _ => b.left) (fun _ => (k : ℤ))

def LineGen (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : Type :=
  {t : LB.Gen (lineAt D F k b) // t.IsGen}

def phφ (b : TF (R := R) F ⟶ D.P.A) (y α : D.X) : Fin 4 ⊕ Fin 4 → ((D.BF F).left ⟶ D.P.A.left) :=
  Sum.elim (D.famφ F (α + y)) (fun i => (trPt D F b).left ≫ D.famφ F α i)

def phMult (k : ℕ) (g : GtPt D F) (t : LineGen D F k g.base) (α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g.form α) (LB.invGen D.P.L _ _ t.1))
    (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit (TF (R := R) F)).left) k)

variable {D F}

def IsPh {k : ℕ} (p : QPair D F k) (t : LineGen D F k p.1.2.base) (s s' : Fam D F k) : Prop :=
  ∀ α : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k)),
    u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (D.zF F).left) (phMult D F k p.1.2 t α) ∧
    GeneratorPullback.SecRel D.P.L (D.famφ F (α + p.1.1)) (DegPre.famε k) (s'.s (α + p.1.1))
      (D.famφ F α) (DegPre.famε k) (s.s α) (trPt D F p.1.2.base).left
      (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k) u

def FamSmul {k : ℕ} (c : F) (s s' : Fam D F k) : Prop :=
  ∀ α j, (s'.s α).f j = liftFun D.P.A (T := TF (R := R) F) _ (scal F c) * (s.s α).f j

def FamAdd {k : ℕ} (s s' s'' : Fam D F k) : Prop :=
  ∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j

variable (R F) in
abbrev TKF (R : Type) [CommRing R] [IsDomain R]
    (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Over (Spec (CommRingCat.of (FractionRing R))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))

variable (F) in
abbrev SecA (F : Type) [Field F] [Algebra (FractionRing R) F]
    (P : PolAV (Spec (CommRingCat.of (FractionRing R)))) (k : ℕ) : Type :=
  LB.Sec (LPow P.A P.L (k : ℤ) (TKF R F))

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))}

structure IsLinBij {k : ℕ} (E : SecA F P k → Fam D F k → Prop) : Prop where
  existsUnique_right : ∀ σ, ∃! s, E σ s
  existsUnique_left : ∀ s, ∃! σ, E σ s
  add : ∀ σ σ' σ'' s s' s'', E σ s → E σ' s' → E σ'' s'' →
    (∀ j, σ''.f j = σ.f j + σ'.f j) → FamAdd s s' s''
  smul : ∀ (c : F) σ σ' s s', E σ s → E σ' s' →
    (∀ j, σ'.f j = liftFun P.A (T := TKF R F) _ (scal F c) * σ.f j) → FamSmul c s s'

def Intertwines {k : ℕ} (E : SecA F P k → Fam D F k → Prop)
    (θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F)) (p : QPair D F k) (t : LineGen D F k p.1.2.base) :
    Prop :=
  ∀ σ σ' s s', E σ s → E σ' s' → (IsActOf P.A P.L (k : ℤ) θ σ σ' ↔ IsPh p t s s')

def IsImage {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (p : QPair D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  1 ≤ k ∧ D.TauBimult ∧ IsLinBij E ∧ x ^ k = 1 ∧
    (∀ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x → ∃ t, Intertwines E θ p t) ∧
    (∀ t, ∃ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x ∧ Intertwines E θ p t)

def IsImageQ {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (a : Qk D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  ∀ p : QPair D F k, Qk.mk p = a → IsImage E p x

variable (D F)

variable (P)

end GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
end
end

