module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.t_E3Cut

def Hyp : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A9 ∧ B1 ∧ B2 ∧ B4 ∧ C3 ∧ C4

def RE (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop := Eqv _ (sch.map (Spec.map f)) (tw q i)

def BC (q : ℕ) (i : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RE q i φ'

def Et : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.Etale

def IE : MorphismProperty CommRingCat.{0} := MorphismProperty.ind.{0} Et

def AlgRes : MorphismProperty CommRingCat.{0} := fun A C f =>
  ∀ Q : Ideal C, Q.IsPrime → ∀ c : C, ∃ p : Polynomial A, (∃ n, f.hom (p.coeff n) ∉ Q) ∧ p.eval₂ f.hom c ∈ Q

def SpS {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  ∀ r : Ideal A, r.IsPrime → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap f.hom = r

abbrev pC (A : CommRingCat.{0}) : A ⟶ CommRingCat.of (Polynomial A) := CommRingCat.ofHom Polynomial.C

def Good (q : ℕ) (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) : Prop :=
  ∀ (B : CommRingCat.{0}) (c : A ⟶ B), Et c → BC q i k (t ≫ c)

theorem RE.comp {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f) (hg : RE q i g) :
    RE q i (f ≫ g) := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  rw [h]; exact (hg n).comp (hf n)

theorem RE.of_comp_left {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f)
    (hfg : RE q i (f ≫ g)) : RE q i g := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff _ (hf n)).1 this

theorem RE.of_comp_right {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hg : RE q i g)
    (hfg : RE q i (f ≫ g)) : RE q i f := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff' (hg n) _).1 this

theorem RE.of_isIso (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) [IsIso f] : RE q i f := fun n => by
  have h1 : ∀ x, pull _ (sch.map (Spec.map (inv f))) (tw q i) n (pull _ (sch.map (Spec.map f)) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull _ (sch.map (Spec.map f)) (tw q i) n (pull _ (sch.map (Spec.map (inv f))) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem BC.of_one {q : ℕ} {i : ℤ} {A Y C Y' : CommRingCat.{0}} {φ : A ⟶ Y} {c : A ⟶ C} {w : Y ⟶ Y'} {φ' : C ⟶ Y'}
    (h : IsPushout φ c w φ') (hr : RE q i φ') : BC q i φ c := fun _ _ ψ h' => by
  rw [← h.inr_isoIsPushout_hom _ _ h']
  exact hr.comp (RE.of_isIso q i _)

def AlgResProps : Prop :=
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)) ∧
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes (f ≫ g) → AlgRes g) ∧
  (∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), f.hom.IsIntegral → AlgRes f) ∧
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
    AlgRes (CommRingCat.ofHom (algebraMap A B))

def IEComp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

def LocIE : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
  IE (CommRingCat.ofHom (algebraMap A B))

def SHExists : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A), r.IsPrime →
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ ∀ a : A, a ∈ r ↔ ¬ IsUnit (f.hom a)

def AICSH : Prop := ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → SH T

def AICExt : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ Function.Injective g.hom ∧ AIC D

def DomCover : Prop := ∀ (C : CommRingCat.{0}), AIC C → ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧ AIC (Localization.AtPrime r)

def HensInt : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] (f : A →+* B),
  f.IsIntegral → (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → Nonempty (HenselianLocalRing B)

def SHTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → SH Z

def IntClos : Prop := ∀ {A C : CommRingCat.{0}} (c : A ⟶ C) [IsDomain C], SH A → AIC C → AlgRes c →
  ∃ (B : CommRingCat.{0}) (b : A ⟶ B) (j : B ⟶ C), b ≫ j = c ∧ b.hom.IsIntegral ∧ Function.Injective j.hom ∧ IsLocalRing B ∧
    AIC B ∧ ∀ z : C, ∃ s y : B, s ≠ 0 ∧ j.hom s * z = j.hom y

def SHSection : Prop := ∀ (A : CommRingCat.{0}), SH A → ∀ {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ s : Spec A ⟶ V, s ≫ g = 𝟙 _

def Coprod : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (X : ι → Scheme.{0}) (n : ℤ),
  Function.Bijective fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x

def ZarLocal : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X),
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U → Eqv R (sch.map (g ∣_ V)) F) → Eqv R (sch.map g) F

def Limit : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), Et c → BC q i φ c) → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), IE c → BC q i φ c

def Stalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop,
  (∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)) →
  (∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → ∃ (D : CommRingCat.{0}) (g : C ⟶ D), g.hom.IsIntegral ∧ SpS g ∧ P D (c ≫ g) ∧
    ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
      BC q i φ (c ≫ g ≫ o)) →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BC q i φ c

def SHEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B → RE q i f

def EtaleBaseChangeFractionFieldIndEtaleOverPolynomial : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [Field K] [Algebra T K]
  [IsFractionRing T K], AIC T → IsUnit (q : T) → ∀ (X : CommRingCat.{0}) (h : CommRingCat.of (Polynomial T) ⟶ X), IE h →
  BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ h)

def ULAStalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C) [IsDomain C] [IsLocalRing C], AIC C → AlgRes c → BC q i (pC A ≫ h) c

def ULA : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), AlgRes c → BC q i (pC A ≫ h) c

def Step : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A), IsUnit (q : T) →
  AlgRes k → Good q i k t → Good q i k (t ≫ pC A)

def Base : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T))) (𝟙 _)

def Global : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K),
  (∀ n : ℕ, Good q i k (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T))) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p], Eqv _ (sch.map (pullback.fst p (Spec.map k))) (tw q i)

theorem Good.of_equiv {q : ℕ} {i : ℤ} {T K A A' : CommRingCat.{0}} {k : T ⟶ K} {t : T ⟶ A} (h : Good q i k t)
    (e : A ≃+* A') (t' : T ⟶ A') (ht : t ≫ CommRingCat.ofHom e.toRingHom = t') : Good q i k t' := fun B c hc => by
  rw [← ht, Category.assoc]
  exact h B _ (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) hc)

theorem goal_of (h1 : AlgResProps) (h2 : Base) (h3 : Step) (h4 : Global) : LateralTheory.E.EtaleChapterEThree := by
  intro a1 a2 a3 a4 a5 _ _ a9 _ _ b1 b2 _ b4 _ _ _ _ c3 c4 _ _ _ _ _ _ q _ T _ _ _ hT hq X p _ i
  have H : Hyp := ⟨a1, a2, a3, a4, a5, a9, b1, b2, b4, c3, c4⟩
  refine h4 H q i _ (fun n => ?_) p
  induction n with
  | zero =>
    refine (h2 H q i T hT hq).of_equiv (MvPolynomial.isEmptyRingEquiv T (Fin 0)).symm _ ?_
    ext x; simp
  | succ n ih =>
    refine (h3 H q i _ _ hq (h1.2.2.2.2.2 T _ (nonZeroDivisors T)) ih).of_equiv
      (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_
    ext1
    exact RingHom.ext fun x => (MvPolynomial.finSuccEquiv T n).symm.commutes x

end LateralTheory.E.t_E3Cut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleGroupHomologySlantOfDeltaCochain
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

abbrev BX (Γ : Type) [Group Γ] (X : Scheme.{0}) : Spc := cst (SingleObj Γ) ⨯ sch.obj X

def slantHom (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    (free R).obj (yoneda.obj X) ⟶ (free R).obj ((BX Γ X).obj (op (SimplexCategory.mk m))) :=
  c.sum fun g r => (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g)

def slantV (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    ((chains R).obj (sch.obj X)).X 0 ⟶ ((chains R).obj (BX Γ X)).X (-(m : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) (i' := 0) (by simp)).hom ≫ slantHom R X c ≫
    (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (BX Γ X))).extendXIso
      ComplexShape.embeddingDownNat (i := m) (i' := -(m : ℤ)) (by simp)).inv

def slantCo (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    Cochain ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
  Cochain.single (slantV R X c) (-(m : ℤ))

abbrev bd (R : Type) [CommRing R] {Γ : Type} [Group Γ] {m : ℕ} (b : (Fin (m + 1) → Γ) →₀ R) : (Fin m → Γ) →₀ R :=
  groupHomology.inhomogeneousChains.d (Rep.trivial R Γ R) m b

def Faces : Prop := ∀ (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (g : Fin (m + 1) → Γ),
  grpPt X g ≫ (BX Γ X).δ 0 = grpPt X (fun i => g i.succ) ∧
  ∀ j : Fin (m + 1), grpPt X g ≫ (BX Γ X).δ j.succ = grpPt X (j.contractNth (· * ·) g)

def HomD : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R),
  slantHom R X b ≫ ((chainsN R).obj (BX Γ X)).d (m + 1) m = slantHom R X (bd R b)

def DeltaCo : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}),
  (∀ c : (Fin 0 → Γ) →₀ R, δ (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) (slantCo R X c) = 0) ∧
  ∀ (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R), δ (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ)) (slantCo R X b) = slantCo R X (bd R b)

section
variable (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ}

theorem slantHom_zero : slantHom R X (0 : (Fin m → Γ) →₀ R) = 0 := Finsupp.sum_zero_index

theorem slantHom_single (g : Fin m → Γ) (r : R) :
    slantHom R X (Finsupp.single g r) = (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g) :=
  Finsupp.sum_single_index (zero_smul (ULift.{1} R) _)

theorem slantHom_add (c c' : (Fin m → Γ) →₀ R) : slantHom R X (c + c') = slantHom R X c + slantHom R X c' :=
  Finsupp.sum_add_index' (fun _ => zero_smul (ULift.{1} R) _)
    (fun _ r s => add_smul (ULift.up r : ULift.{1} R) (ULift.up s) _)

theorem slantV_add (c c' : (Fin m → Γ) →₀ R) : slantV R X (c + c') = slantV R X c + slantV R X c' := by
  unfold slantV
  rw [slantHom_add]
  erw [Preadditive.add_comp, Preadditive.comp_add]

theorem slantCo_v (c : (Fin m → Γ) →₀ R) : (slantCo R X c).v 0 (-(m : ℤ)) (zero_add _) = slantV R X c :=
  Cochain.single_v _ _ _

theorem slantCo_v_ne (c : (Fin m → Γ) →₀ R) (p p' : ℤ) (h : p + -(m : ℤ) = p') (hp : p ≠ 0) :
    (slantCo R X c).v p p' h = 0 := Cochain.single_v_eq_zero _ _ _ _ _ hp

theorem slantCo_add (c c' : (Fin m → Γ) →₀ R) : slantCo R X (c + c') = slantCo R X c + slantCo R X c' := by
  ext p p' h : 1
  by_cases hp : p = 0
  · subst hp
    obtain rfl : p' = -(m : ℤ) := by omega
    rw [Cochain.add_v, slantCo_v, slantCo_v, slantCo_v, slantV_add]
  · rw [Cochain.add_v, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, add_zero]

theorem slantCo_zero : slantCo R X (0 : (Fin m → Γ) →₀ R) = 0 := by
  have h := slantCo_add R X (0 : (Fin m → Γ) →₀ R) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem isSlant_iff (c : (Fin m → Γ) →₀ R) (z) : IsSlant R X c z ↔ z.1 = slantCo R X c := by
  constructor
  · rintro ⟨h1, h2⟩
    ext p p' h : 1
    by_cases hp : p = 0
    · subst hp
      obtain rfl : p' = -(m : ℤ) := by omega
      rw [slantCo_v]; exact h2
    · rw [slantCo_v_ne _ _ _ _ _ _ hp]; exact h1 p p' h hp
  · intro h
    refine ⟨fun p p' hh hp => ?_, ?_⟩
    · rw [h]; exact slantCo_v_ne _ _ _ _ _ _ hp
    · rw [h]; exact slantCo_v _ _ _

end

theorem closed (h : DeltaCo) (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) :
    δ (-(m : ℤ)) (-(m : ℤ) + 1) (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m c)) = 0 := by
  cases m with
  | zero => exact (h R Γ X).1 _
  | succ m =>
    have h1 := (h R Γ X).2 m (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)
    have h2 : bd R (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c) = 0 := by
      have h3 := ConcreteCategory.congr_hom
        ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).iCycles_d (m + 1) m) c
      rw [groupHomology.inhomogeneousChains.d_def] at h3
      exact h3
    rw [h2, slantCo_zero] at h1
    have h4 : ∀ k : ℤ, k = -(m : ℤ) →
        δ (-((m + 1 : ℕ) : ℤ)) k (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)) = 0 := by
      rintro _ rfl; exact h1
    exact h4 _ (by omega)

theorem exists_bd (R : Type) [CommRing R] (Γ : Type) [Group Γ] (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) (hc : groupHomology.π (Rep.trivial R Γ R) m c = 0) :
    ∃ b, bd R b = groupHomology.iCycles (Rep.trivial R Γ R) m c := by
  have e : (ShortComplex.mk _ _ ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_comp_homologyπ (m + 1) m)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyIsCokernel (m + 1) m (by simp))
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).1 e c hc
  refine ⟨b, ?_⟩
  have h3 := ConcreteCategory.congr_hom
    ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_i (m + 1) m) b
  rw [groupHomology.inhomogeneousChains.d_def] at h3
  rw [← hb]
  exact h3.symm

theorem cpre_add {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m : ℤ} (a a' : Cocycle K L m)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre (a + a') M n k h = cpre a M n k h + cpre a' M n k h := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [AddMonoidHom.add_apply, cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (Cochain.add_comp _ _ _ h)

theorem cpre_eq_zero {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m m' : ℤ} (a : Cocycle K L m)
    (hm : m' + 1 = m) (w : Cochain K L m') (hw : δ m' m w = a.1)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre a M n k h = 0 := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  have h1 : cpost K x m k h (CohomologyClass.mk a) = 0 := by
    rw [(CohomologyClass.mk_eq_zero_iff a).2 ⟨m', hm, w, hw⟩, map_zero]
  exact h1

theorem etale_group_homology_slant_of_delta_cochain (h : DeltaCo) : D3 := by
  intro R _ Γ _ X m
  let z : groupHomology.cycles (Rep.trivial R Γ R) m → Cocycle ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
    fun c => Cocycle.mk _ _ rfl (closed h R Γ X m c)
  refine ⟨fun c => ⟨z c, (isSlant_iff R X _ _).2 rfl⟩, fun F n => ?_⟩
  have hex : ∃ S, IsSlantMap R Γ X F m n S := by
    let T : groupHomology.cycles (Rep.trivial R Γ R) m →+ H R (BX Γ X) F (m + n) →+ H R (sch.obj X) F n :=
      AddMonoidHom.mk' (fun c => HK.pre R (z c) F (m + n) n (by ring)) (fun c c' => by
        have : z (c + c') = z c + z c' := Cocycle.ext (by
          change slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m (c + c')) = slantCo R X _ + slantCo R X _
          rw [map_add (f := _)]; exact slantCo_add R X _ _)
        rw [this]; exact cpre_add _ _ _ _ _ _)
    have hs : Function.Surjective (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom :=
      (ModuleCat.epi_iff_surjective (groupHomology.π (Rep.trivial R Γ R) m)).1
        (inferInstanceAs (Epi ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyπ m)))
    have hk : (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom.ker ≤ T.ker := by
      intro c hc
      obtain ⟨b, hb⟩ := exists_bd R Γ m c hc
      refine cpre_eq_zero (z c) (m' := -((m + 1 : ℕ) : ℤ)) (by omega) (slantCo R X b) ?_ _ _ _ _
      rw [(h R Γ X).2 m b, hb]; rfl
    refine ⟨AddMonoidHom.liftOfSurjective _ hs ⟨T, hk⟩, fun c z' hz' => ?_⟩
    have e : z' = z c := Cocycle.ext ((isSlant_iff R X _ _).1 hz')
    rw [e]
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨T, hk⟩ c
  unfold slantR
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem goal_of (h : DeltaCo) : LateralTheory.E.EtaleChapterDThree :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => etale_group_homology_slant_of_delta_cochain h

end LateralTheory.E.t_D3Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.FirstChernNaturality

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  simp [chains, chainsXIso, chainsN, HomologicalComplex.extendMap_f]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem freeGen_nat {P P' : PSh} (g : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R P' U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  unfold freeGen
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P')).app (op U)).hom
    ((((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) = _
  congr 1
  simp only [ModuleCat.freeMk, freeP]
  simp [ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem ev_zpull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (γ : Cocycle ((chains R).obj E') I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1 p s h U x =
      ev γ.1 p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  have hc : (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1.v (-(p : ℤ)) s h =
      ((chains R).map f).f (-(p : ℤ)) ≫ γ.1.v (-(p : ℤ)) s h := by
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by simp) h]
  unfold ev
  rw [hc, ← Category.assoc, chainsXIso_inv_nat, Category.assoc]
  exact congrArg (((chainsXIso R E' p).inv ≫ γ.1.v (-(p : ℤ)) s h).hom.app (op U)).hom
    (freeGen_nat (f.app (op (SimplexCategory.mk p))) U x)

theorem sub_nat {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  unfold Sx.sub
  exact congrFun (congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)) x

theorem lineUnit_comp {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) :
    lineUnit (f ≫ L) x = lineUnit L ((f.app (op (SimplexCategory.mk 1))).app (op U) x) := rfl

theorem etale_first_chern_class_natural_of_spec (hC1 : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle) : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassNaturalUnderPullback := by
  intro q _ E E' f L hinv
  have hinvE : Inv q E := fun U ⟨x⟩ => hinv U ⟨(f.app _).app _ x⟩
  obtain ⟨⟨γ, hγ⟩, h2⟩ := hC1 q L hinv
  rw [h2 γ hγ]
  obtain ⟨_, h2'⟩ := hC1 q (f ≫ L) hinvE
  rw [h2' (zcomp (Cocycle.ofHom ((chains _).map f)) γ (zero_add 2)) ?_]
  · rfl
  obtain ⟨g0, g1, g2⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · intro U x
    rw [ev_zpull]; exact g0 U _
  · intro U x v hv
    rw [ev_zpull]; exact g1 U _ v (by rw [hv, lineUnit_comp])
  · intro U x v w hv hw
    rw [ev_zpull]
    exact g2 U _ v w (by rw [hv, lineUnit_comp, sub_nat]) (by rw [hw, lineUnit_comp, sub_nat])

end LateralTheory.E.FirstChernNaturality
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPfEmpty
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

theorem etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme (R : Type) [CommRing R] (E : Scheme.{0}) [IsEmpty E] :
    IsZero ((free R).obj (yoneda.obj E)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _ |>.injective
  ext T : 2
  by_cases hT : IsEmpty T.unop
  · haveI := hT
    exact ((Sheaf.isTerminalOfBotCover _ T.unop
      (AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology T.unop)).isZero).eq_of_tgt _ _
  · rw [not_isEmpty_iff] at hT
    obtain ⟨t⟩ := hT
    have hP : IsEmpty ((yoneda.obj E).obj T) := ⟨fun f => isEmptyElim (f.base t)⟩
    apply IsZero.eq_of_src
    change IsZero ((ModuleCat.free (ULift.{1} R)).obj (ULift.{1} ((yoneda.obj E).obj T)))
    rw [ModuleCat.isZero_iff_subsingleton]
    haveI : IsEmpty (ULift.{1} ((yoneda.obj E).obj T)) := inferInstance
    change Subsingleton (ULift.{1} ((yoneda.obj E).obj T) →₀ ULift.{1} R)
    infer_instance

theorem leafEmptyVanish : LeafEmptyVanish := by
  intro R _ X F n
  have hE : IsEmpty (((⊥ : X.Opens) : Scheme.{0}) : Type) := by
    change IsEmpty ((⊥ : X.Opens) : Set X); simp
  have hfree := etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme R ((⊥ : X.Opens) : Scheme.{0})
  have hN : IsZero ((chainsN R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro j
    refine IsZero.eq_of_src ?_ _ _
    exact hfree
  have hC : IsZero ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) :=
    Functor.map_isZero (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) hN
  have hX : ∀ p, IsZero (((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))).X p) := fun p =>
    Functor.map_isZero (HomologicalComplex.eval _ _ p) hC
  have : Subsingleton (Cochain ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hX p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  change Subsingleton (CohomologyClass _ _ n)
  unfold CohomologyClass
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

end LateralTheory.E.E8

end
end

