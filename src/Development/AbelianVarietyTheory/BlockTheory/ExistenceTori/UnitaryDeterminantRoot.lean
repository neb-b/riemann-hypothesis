module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
open scoped TensorProduct

section Adeles

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]

def IsRealIn : Prop := ∀ a : F, cc (algebraMap F E a) = algebraMap F E a

abbrev AdE : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

def IsIntF (a : FiniteAdeleRing (𝓞 F) F) : Prop := ∀ v, a v ∈ v.adicCompletionIntegers F

def intAdE : AddSubgroup (AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ o : 𝓞 E, z = a ⊗ₜ (o : E)}

variable {E}

def diagE : E →+* AdE F E := Algebra.TensorProduct.includeRight.toRingHom

def vecA {r : ℕ} (v : Fin r → E) : Fin r → AdE F E := fun i => diagE F (v i)

def latHat {r : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ x : La, z = fun i => a ⊗ₜ ι x i}

def IsUnitaryQ {r : ℕ} (Gm γ : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ x y, herm Gm (γ.mulVec x) (γ.mulVec y) = herm Gm x y

variable [hF : Fact (IsRealIn F E)]

def conjF : E →ₐ[F] E where
  toRingHom := (IsCMField.complexConj E).toRingEquiv.toRingHom
  commutes' := hF.out

def conjA : AdE F E →ₐ[F] AdE F E := Algebra.TensorProduct.map (AlgHom.id F _) (conjF F)

variable {F}

def IsUnitaryA {r : ℕ} (Gm : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  g.transpose * Gm.map (diagE F) * g.map (conjA F) = Gm.map (diagE F)

def IsDetRootA {r : ℕ} (g : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ) : Prop :=
  (x : AdE F E) = g.det * conjA F (x : AdE F E)

def IsTwist (ξ : (AdE F E)ˣ →* Circle) (N : ℕ) : Prop :=
  (∃ m : ℕ, 0 < m ∧ ∀ x, ξ x ^ m = 1) ∧
  (∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1) ∧
  (∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1) ∧
  ∀ x : (AdE F E)ˣ, (x : AdE F E) ∈ intAdE F E → ((x⁻¹ : (AdE F E)ˣ) : AdE F E) ∈ intAdE F E →
    (∃ y ∈ intAdE F E, (x : AdE F E) - 1 = N • y) → ξ x = 1

end Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r : ℕ}

section Clauses

variable {La' : Type} [AddCommGroup La'] [Module (𝓞 E) La']

def IsomEmb (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (Di : Datum H) (φ : Di.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  Function.Injective φ ∧ ∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ0 * herm Gm (φ a) (φ b))

def LatAt (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∀ v : Fin r → E, (∃ b, φ b = v) ↔ ∃ z ∈ latHat F ι, vecA F v = g.mulVec z

def MarkAt (l : Level H) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E)) (t : Dw.La →ₗ[𝓞 E] La')
    (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ z ∈ latHat F ι,
    vecA F (φ (t a)) - g.mulVec (vecA F (ι a)) = l.M • g.mulVec z

def AtClass (l : Level H) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E))
    (t : Dw.La →ₗ[𝓞 E] La') (h : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∃ γ : Matrix (Fin r) (Fin r) E, IsUnitaryQ Gm γ ∧
    LatAt ι φ (γ.map (diagE F) * h) ∧ MarkAt l ι φ t (γ.map (diagE F) * h)

end Clauses

section Value

variable [Fact (IsRealIn F E)] {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def sig0 : c.F →+* ℂ := c.F.val.toRingHom

variable {Xo c}

def AllMarked (F : Type) [Field F] [NumberField F] [Algebra F E] [Fact (IsRealIn F E)]
    (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ i, IsomEmb Gm ξ0 (Fu.Di i) (φ i) ∧ ∃ (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h ∧ AtClass l Gm ι (φ i) (Fu.t i) h ∧ IsDetRootA h x

variable (Xo c)

end Value

section Action

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))

variable {c} {c' : Coeff l}

end Action

section Row

variable {l : Level H} (Xo : Moduli Dw l) {c c' : Coeff l} {n : ℕ}

variable {Pt : Type} {G : Type} [Group G] {Tup : Type*} {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
