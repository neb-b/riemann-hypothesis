module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

abbrev Pt (X : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D] : Type := SpAlg R D ⟶ X

abbrev Fn0 (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → D

abbrev Fn1 (X : Over (Sp R)) : Type 1 :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'], (D →ₐ[R] D') → Pt X D → D'

abbrev Fn2 (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → Pt X D → D

section Basic

variable {X : Over (Sp R)} {K : Type}

def Sm (W : K → X.left.Opens) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : Prop :=
  ∃ i, ⊤ ≤ x.left ⁻¹ᵁ W i


variable (X) in
def whole : Unit → X.left.Opens := fun _ ↦ ⊤

theorem sm_whole {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : Sm (whole X) x := ⟨(), fun _ _ ↦ trivial⟩

def IsCoc (W : K → X.left.Opens) (f : Fn1 X) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (D'' : Type) [CommRing D'']
    [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'') (x : Pt X D), Sm W x →
    f D D'' (ψ.comp φ) x = ψ (f D D' φ x) + f D' D'' ψ (spOver φ ≫ x)

def IsCob (W : K → X.left.Opens) (f : Fn1 X) (k : Fn0 X) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D),
    Sm W x → f D D' φ x = k D' (spOver φ ≫ x) - φ (k D x)

def Fn1.neg (f : Fn1 X) : Fn1 X := fun D _ _ D' _ _ φ x ↦ -f D D' φ x

def Fn1.add (f f' : Fn1 X) : Fn1 X := fun D _ _ D' _ _ φ x ↦ f D D' φ x + f' D D' φ x

def Cohom (W : K → X.left.Opens) (f f' : Fn1 X) : Prop := ∃ k : Fn0 X, IsCob W (f.add f'.neg) k

def Fn1.zero (X : Over (Sp R)) : Fn1 X := fun _ _ _ _ _ _ _ _ ↦ 0

theorem Pt.w {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) :
    x.left ≫ X.hom ≫ 𝟙 _ = spMap (algebraMap R D) := by
  rw [Category.comp_id]; exact Over.w x

abbrev trivAt {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : Thick (dp0 R) (X.hom ≫ 𝟙 _) :=
  Thick.triv D x.left x.w

def trivMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    trivAt x ⟶ trivAt (spOver φ ≫ x) := Thick.trivHom φ rfl

def fv (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) : Fn1 X := fun _ _ _ _ _ _ φ x ↦ ev f (trivMap φ x)


open Classical in
def evU {Y : Scheme.{0}} {D : Type} [CommRing D] (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) : D :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then evalAt x U h a else 0

def dl {D : Type} [CommRing D] (u : DualNumber D) : D := u.snd * Ring.inverse u.fst

def epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    DualNumber D →ₐ[R] DualNumber D' :=
  DualNumber.lift ⟨((TrivSqZeroExt.inlAlgHom R D' D').comp φ, DualNumber.eps), DualNumber.eps_mul_eps,
    fun _ ↦ Commute.all _ _⟩

end Basic

section Group

variable {A : Over (Sp R)} [GrpObj A] {K : Type}

def IsAdd (f : Fn1 A) (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x y : Pt A D),
    g D' (spOver φ ≫ x) (spOver φ ≫ y) - φ (g D x y) = f D D' φ (x * y) - f D D' φ x - f D D' φ y

def IsSymCoc (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D],
    (∀ x y : Pt A D, g D x y = g D y x) ∧
    ∀ x y z : Pt A D, g D y z - g D (x * y) z + g D x (y * z) - g D x y = 0

def chi (n : ℕ) (g : Fn2 A) : Fn0 A := fun D _ _ x ↦ ∑ i ∈ Finset.range n, g D (x ^ i) x

end Group

section Cot

variable (R) (D : Type) [CommRing D] [Bialgebra R D]

@[reducible] def cotOp : Module Rᵐᵒᵖ (Cot R D) := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

attribute [local instance] cotOp

theorem cotCentral : IsCentralScalar R (Cot R D) := ⟨fun _ _ ↦ rfl⟩

theorem cotTower : IsScalarTower R Rᵐᵒᵖ (Cot R D) := ⟨fun r s m ↦ by
  change (r • s).unop • m = r • s.unop • m
  rw [MulOpposite.unop_smul, smul_eq_mul, mul_smul]⟩

attribute [local instance] cotCentral cotTower

abbrev cotExt : SqExt R := SqExt.ofModule R R (Cot R D)

def cotPt : D →ₐ[R] (cotExt R D).C :=
  AlgHom.ofLinearMap
    (Algebra.linearMap R (TrivSqZeroExt R (Cot R D)) ∘ₗ Coalgebra.counit +
      TrivSqZeroExt.inrHom R (Cot R D) ∘ₗ AugCot.d (Bialgebra.counitAlgHom R D))
    (by
      have h : AugCot.d (Bialgebra.counitAlgHom R D) 1 = 0 := by
        simpa using AugCot.d_algebraMap (Bialgebra.counitAlgHom R D) 1
      simp [h])
    (fun x y ↦ by
      have h := AugCot.d_mul (Bialgebra.counitAlgHom R D) x y
      ext
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · simp [TrivSqZeroExt.algebraMap_eq_inl, h, add_comm])

def cotSnd : (cotExt R D).C →ₗ[R] Cot R D := TrivSqZeroExt.sndHom R (Cot R D)


variable {R D} in
def cotVal {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (y : Pt X D) : Cot R D :=
  let y' : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  cotSnd R D ((cotExt R D).val y'.left y'.w f - fv f D (cotExt R D).C (cotPt R D) y)

end Cot

section Can

variable {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}

structure Dat (t : G.TorsionTower A) (c : primDR A) : Type 1 where

  f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))
  cl : H1.mk _ f = c.1

  g : Fn2 A
  add : IsAdd (fv f) g

  h : ∀ n, G.A n
  res : ∀ n, fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)) = h n - G.res n (h (n + 1))

variable {t : G.TorsionTower A} {c : primDR A} (d : Dat t c)

def Dat.coc (n : ℕ) : G.A n ⊗[R] G.A n :=
  d.g (G.A n ⊗[R] G.A n) (spOver Algebra.TensorProduct.includeLeft ≫ t.y n)
      (spOver Algebra.TensorProduct.includeRight ≫ t.y n) -
    (fv d.f (G.A n) (G.A n ⊗[R] G.A n) (Bialgebra.comulAlgHom R (G.A n)) (t.y n) -
      fv d.f (G.A n) (G.A n ⊗[R] G.A n) Algebra.TensorProduct.includeLeft (t.y n) -
      fv d.f (G.A n) (G.A n ⊗[R] G.A n) Algebra.TensorProduct.includeRight (t.y n)) -
    cobOne R (G.A n) (d.h n)

def Dat.om (n : ℕ) : Cot R (G.A n) :=
  cotVal d.f (t.y n) - dUnit (R := R) (d.h n)


variable (t c) in
def IsCan (x : G.RigExt) : Prop :=
  ∃ (d : Dat t c) (z : G.cocycles) (w : G.omega), (∀ n, z.1 n = d.coc n) ∧ (∀ n, w.1 n = d.om n) ∧ x = G.rigMk (z, w)

def Dat.zero (t : G.TorsionTower A) : Dat t 0 where
  f := 0
  cl := map_zero _
  g := fun _ _ _ _ _ ↦ 0
  add := fun _ _ _ _ _ _ φ _ _ ↦ by
    change (0 : _) - φ 0 = 0 - 0 - 0
    simp
  h := 0
  res := fun n ↦ by
    change (0 : _) = 0 - G.res n 0
    simp

end Can

section Contract

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def ptV (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : Pt (A ⊗ B) (DualNumber D) :=
  lift (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x) (spOver (EpsWeil.epsMap R D) ≫ v)


variable (B) in
def pt0 {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : Pt (A ⊗ B) D := lift x 1

def chartsA (P : LB (A ⊗ B).left) : P.ι → A.left.Opens := fun i ↦ (AbDual.inl A B).left ⁻¹ᵁ P.U i

def IsChoice (P : LB (A ⊗ B).left) (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), Sm (chartsA P) x → ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j D x)

def tanCoc (P : LB (A ⊗ B).left) (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι) (v : epsR R ⟶ B) :
    Fn1 A := fun D _ _ D' _ _ φ x ↦
  let x' : Pt A D' := spOver φ ≫ x
  dl (evU (ptV v x').left (P.U (j D' x') ⊓ P.U (j D x)) (P.g (j D' x') (j D x)).val)

def sndPull (u : Fn1 (A ⊗ B)) (v : epsR R ⟶ B) : Fn1 A := fun D _ _ D' _ _ φ x ↦
  (u (DualNumber D) (DualNumber D') (epsHom φ) (ptV v x)).snd

abbrev epsExt (R D : Type) [CommRing R] [CommRing D] [Algebra R D] : SqExt R := SqExt.ofModule R D D


variable (B) in
abbrev thickAt {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) :=
  (epsExt R D).thick (pt0 B x).left (pt0 B x).w

def IsContr (z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))) (v : epsR R ⟶ B) (κ : Fn1 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D)
    (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x)
    (s' : trivAt (pt0 B (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x))
    (i' : trivAt (ptV v (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x))
    (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x)))
    (b : trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x))) (τ : thickAt B x ⟶ thickAt B (spOver φ ≫ x)),
    (∀ r, s.φ r = TrivSqZeroExt.inl r) → (∀ r, i.φ r = r) → (∀ r, s'.φ r = TrivSqZeroExt.inl r) → (∀ r, i'.φ r = r) →
    (∀ r, a.φ r = φ r) → (∀ r, b.φ r = epsHom φ r) → (∀ r, τ.φ r = epsHom φ r) →
    κ D D' φ x = TrivSqZeroExt.snd (R := D') (M := D')
      (z _ _ _ s τ - z _ _ _ a s' - z _ _ _ i τ + z _ _ _ b i')

end Contract

section Cube

variable {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] {L : RigLB H}

end Cube

end GlobalTheory.PtExt
