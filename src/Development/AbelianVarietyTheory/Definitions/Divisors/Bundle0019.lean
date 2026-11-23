module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def CentralNilGL (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) : Prop :=
  ∀ zs : List (Module.End ℂ (Sm E a)), zs.length = N → (∀ z ∈ zs, z ∈ Zalg E a) →
    zs.foldr (fun z f => z f - χ z • f) φ = 0


variable (E a) in
def formsGL (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ))
    (N : ℕ) : Set (Sm E a) :=
  {φ | IsAutForm φ ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧ (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) ∧
    ∃ χ ∈ X, CentralNilGL χ N φ}

def CoreFiniteGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W →
      ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (formsGL E a L W X N))

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic

namespace GlobalTheory.HCA

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

abbrev glG : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ := ⊤

abbrev glL : Submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := ⊤

theorem glH : IsExpLieAlgebra (glG E a) (glL E a) := isExpLieAlgebra_top

variable {E a} [_root_.NumberField.IsTotallyComplex E]

def glRes (φ : GA E a → ℂ) (x : GA E a) : glG E a → ℂ := fun y => φ (x * infGL E a y.1)

end GlobalTheory.HCA

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg
section
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Filter Topology

noncomputable section

namespace GlobalTheory.FlagAr

open GlobalTheory.FlagPoly

variable {D : D7} (Y : ShimX D.what₂.Tau)

def setB (B : ℝ) : Finset ℕ :=
  ((Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime) ∪
    (Nat.primeFactors (2 * (NumberField.discr D.host.E).natAbs) ∪ Y.lev)

end GlobalTheory.FlagAr
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

section Ext

variable {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
variable {C C' : Type} [Category.{0} C] [Category.{0} C']

abbrev extHom {B B' : Type} [CommRing B] [Algebra R₀ B] [CommRing B'] [Algebra R₀ B'] (φ : B →ₐ[R₀] B') :
    R₁ ⊗[R₀] B →ₐ[R₁] R₁ ⊗[R₀] B' := Algebra.TensorProduct.map (AlgHom.id R₁ R₁) φ

@[reducible] def ext (F : C ⥤ CommAlgCat.{0} R₀) : C ⥤ CommAlgCat.{0} R₁ where
  obj T := CommAlgCat.of R₁ (R₁ ⊗[R₀] F.obj T)
  map a := CommAlgCat.ofHom (extHom R₁ (mp F a))
  map_id T := by
    ext x
    simp [extHom, mp_id]
  map_comp a b := by
    ext x
    simp [extHom, mp_comp]

variable {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

def coefHom (n : CoefMap (RingHom.id R₀) F F') (T : C') : F.obj (n.G.obj T) →ₐ[R₀] F'.obj T :=
  { n.α T with
    commutes' := fun r ↦ by
      have := n.smul T r 1
      simpa [Algebra.algebraMap_eq_smul_one] using this }

def extMap (n : CoefMap (RingHom.id R₀) F F') : CoefMap (RingHom.id R₁) (ext R₁ F) (ext R₁ F') where
  G := n.G
  α T := (extHom R₁ (coefHom n T) : R₁ ⊗[R₀] F.obj (n.G.obj T) →+* R₁ ⊗[R₀] F'.obj T)
  naturality {T T'} a b := by
    change extHom R₁ (coefHom n T') (extHom R₁ (mp F (n.G.map a)) b) = extHom R₁ (mp F' a) (extHom R₁ (coefHom n T) b)
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp only [Algebra.TensorProduct.map_tmul]; exact congrArg _ (n.naturality a y)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  smul T r b := map_smul (extHom R₁ (coefHom n T)) r b

variable {X X' : Scheme.{0}} {s : X ⟶ Sp R₀} {s' : X' ⟶ Sp R₀} {φ : X' ⟶ X}

def IsExtendedPullbackDegOne (h : φ ≫ s = s' ≫ spMap (RingHom.id R₀)) (c : CatCoh.H1 (ext R₁ (OAff s)))
    (c' : CatCoh.H1 (ext R₁ (OAff s'))) : Prop :=
  (extMap R₁ (pairPull h)).pull1 c = (extMap R₁ (pairRes φ s')).pull1 c'

def IsExtendedPullbackDegTwo (h : φ ≫ s = s' ≫ spMap (RingHom.id R₀)) (c : CatCoh.H2 (ext R₁ (OAff s)))
    (c' : CatCoh.H2 (ext R₁ (OAff s'))) : Prop :=
  (extMap R₁ (pairPull h)).pull2 c = (extMap R₁ (pairRes φ s')).pull2 c'

def IsPullbackH2Structure {R' : Type} [CommRing R'] {t : X' ⟶ Sp R'} {σ : R₀ →+* R'} (h : φ ≫ s = t ≫ spMap σ)
    (c : CatCoh.H2 (OAff s)) (c' : CatCoh.H2 (OAff t)) : Prop :=
  (pairPull h).pull2 c = (pairRes φ t).pull2 c'

end Ext

theorem overW {R₀ : Type} [CommRing R₀] {A B : Over (Sp R₀)} (f : A ⟶ B) :
    f.left ≫ B.hom = A.hom ≫ spMap (RingHom.id R₀) := by
  rw [Cris.spMap_id, Category.comp_id]; exact Over.w f

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

structure Aug (I : Ideal R) (π : R →+* R₀) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] where

  q : R₁ →ₐ[R₀] R₀

  k : R₁ →+ R
  mem : ∀ y, k y ∈ I
  smul : ∀ (r : R) (y : R₁), k (π r • y) = r * k y
  one : k 1 = 0
  sq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0
  inj : ∀ y, q y = 0 → k y = 0 → y = 0
  surj : ∀ i ∈ I, ∃ y, q y = 0 ∧ k y = i

variable {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

def Aug.KerQ (α : Aug I π R₁) {B₀ : Type} [CommRing B₀] [Algebra R₀ B₀] (y : R₁ ⊗[R₀] B₀) : Prop :=
  Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0

def Aug.IsSig (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀)
    (σ : R₁ ⊗[R₀] B₀ →+ B) : Prop :=
  ∀ (y : R₁) (b : B), σ (y ⊗ₜ p b) = α.k y • b

variable {C C' : Type} [Category.{0} C] [Category.{0} C']

structure Pre (I : Ideal R) (π : R →+* R₀) (F : C ⥤ CommAlgCat.{0} R₀) : Type 1 where

  B : C → CommAlgCat.{0} R

  p : ∀ T, B T →+* F.obj T
  semi : ∀ T, SemiHom π (p T)
  surj : ∀ T, Function.Surjective (p T)
  ker : ∀ T b, p T b = 0 ↔ b ∈ I.map (algebraMap R (B T))
  smooth : ∀ T, Algebra.Smooth R (B T)

  ρ : ∀ {T T' : C}, (T ⟶ T') → (B T →ₐ[R] B T')
  nat : ∀ {T T' : C} (a : T ⟶ T') (b : B T), p T' (ρ a b) = mp F a (p T b)

namespace Pre

variable {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

def IsFun (L : Pre I π F) : Prop :=
  ∀ ⦃T T' T'' : C⦄ (a : T ⟶ T') (b : T' ⟶ T'') (x : L.B T), L.ρ (a ≫ b) x = L.ρ b (L.ρ a x)

def restrict (L : Pre I π F) (G : C' ⥤ C) : Pre I π (G ⋙ F) where
  B T := L.B (G.obj T)
  p T := L.p (G.obj T)
  semi T := L.semi _
  surj T := L.surj _
  ker T := L.ker _
  smooth T := L.smooth _
  ρ a := L.ρ (G.map a)
  nat a b := L.nat (G.map a) b

def IsObs (L : Pre I π F) (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T'') : Prop :=
  ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), IsTheta I (L.p T) ((L.ρ b).comp (L.ρ a)) (L.ρ (a ≫ b)) (θ T T' T'' a b)

def IsOb2 (L : Pre I π F) (α : Aug I π R₁) (w : Glob1 F) (c : CatCoh.H2 (ext R₁ F)) : Prop :=
  ∃ (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T'')
    (σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T) (z : Z2 (ext R₁ F)),
    L.IsObs θ ∧ (∀ T, α.IsSig (L.p T) (σ T)) ∧ c = H2.mk _ z ∧
      ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''),
        α.KerQ (B₀ := F.obj T'') (z.1 T T' T'' a b) ∧ σ T'' (z.1 T T' T'' a b) = θ T T' T'' a b (w.1 T)

def IsLift (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F')
    (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) : Prop :=
  ∀ T b, L'.p T (l T b) = n.α T (L.p _ b)

def IsNat (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F')
    (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) : Prop :=
  ∀ ⦃T T' : C'⦄ (a : T ⟶ T') (b : L.B (n.G.obj T)), L'.ρ a (l T b) = l T' (L.ρ (n.G.map a) b)

def IsOb1 (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F')
    (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (α : Aug I π R₁) (w : Glob1 F) (c : CatCoh.H1 (ext R₁ F')) : Prop :=
  ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[F.obj (n.G.obj T)⁄R₀] →+ L'.B T')
    (σ : ∀ T, R₁ ⊗[R₀] F'.obj T →+ L'.B T) (z : Z1 (ext R₁ F')),
    (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a)))
      (κ T T' a)) ∧ (∀ T, α.IsSig (L'.p T) (σ T)) ∧ c = H1.mk _ z ∧
      ∀ (T T' : C') (a : T ⟶ T'), α.KerQ (B₀ := F'.obj T') (z.1 T T' a) ∧ σ T' (z.1 T T' a) = κ T T' a (w.1 _)

end Pre

def ofSys {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) : Pre I π (OAff s₀) where
  B U := S.F.obj U
  p := S.p
  semi := S.semi
  surj := S.surj
  ker := S.ker
  smooth := S.smooth
  ρ a := mp S.F a
  nat a b := S.nat a b

theorem ofSys_isFun {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) : (ofSys S).IsFun :=
  fun _ _ _ a b x ↦ mp_comp S.F a b x

theorem Pre.IsFun.restrict {F : C ⥤ CommAlgCat.{0} R₀} {L : Pre I π F} (h : L.IsFun) (G : C' ⥤ C) :
    (L.restrict G).IsFun := fun _ _ _ a b x ↦ by
  change L.ρ (G.map (a ≫ b)) x = L.ρ (G.map b) (L.ρ (G.map a) x)
  rw [G.map_comp]; exact h _ _ x

def pairPre {X₀ Y₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) (φ : X₀ ⟶ Y₀) : Pre I π (OPair φ s₀) :=
  (ofSys S).restrict (pairFst φ)

def FormSt : Prop :=
  ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    Par A.hom ∧ Module.Projective R₀ (GlobForm A.hom) ∧
      ∀ (w : GlobForm A.hom) (wm w₁ w₂ : GlobForm (A ⊗ A).hom), IsPullForm (overW μ[A]) w wm →
        IsPullForm (overW (fst A A)) w w₁ → IsPullForm (overW (snd A A)) w w₂ → wm = w₁ + w₂

def PrimitiveStructureSheafDegTwoVanish : Prop :=
  ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (c : CatCoh.H2 (OAff A.hom)) (c₁ c₂ : CatCoh.H2 (OAff (A ⊗ A).hom)), IsPullbackH2Structure (overW μ[A]) c (c₁ + c₂) →
      IsPullbackH2Structure (overW (fst A A)) c c₁ → IsPullbackH2Structure (overW (snd A A)) c c₂ → c = 0

def AxesVanishingStructureSheafDegOne : Prop :=
  ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ c : HO1 (A ⊗ A).hom, IsPullO (overW (lift (𝟙 A) 1)) c 0 → IsPullO (overW (lift 1 (𝟙 A))) c 0 → c = 0

def PrimitiveExtendedDegTwoVanish : Prop :=
  ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) →
    ∀ (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (c : CatCoh.H2 (ext R₁ (OAff A.hom))) (c₁ c₂ : CatCoh.H2 (ext R₁ (OAff (A ⊗ A).hom))),
      IsExtendedPullbackDegTwo R₁ (overW μ[A]) c (c₁ + c₂) → IsExtendedPullbackDegTwo R₁ (overW (fst A A)) c c₁ → IsExtendedPullbackDegTwo R₁ (overW (snd A A)) c c₂ → c = 0

def AxesVanishingExtendedDegOne : Prop :=
  ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) →
    ∀ (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ c : CatCoh.H1 (ext R₁ (OAff (A ⊗ A).hom)), IsExtendedPullbackDegOne R₁ (overW (lift (𝟙 A) 1)) c 0 →
      IsExtendedPullbackDegOne R₁ (overW (lift 1 (𝟙 A))) c 0 → c = 0

def UnobDim : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A

end GlobalTheory.Obs
end
end

