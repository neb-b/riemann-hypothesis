module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalRingCardinality.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
open scoped TensorProduct

section Adeles

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idHat (𝔞 : Ideal (𝓞 E)) : AddSubgroup (AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ o ∈ 𝔞, z = a ⊗ₜ ((o : 𝓞 E) : E)}

variable {F}

def IsIntUnit (y : (AdE F E)ˣ) : Prop :=
  (y : AdE F E) ∈ intAdE F E ∧ ((y⁻¹ : (AdE F E)ˣ) : AdE F E) ∈ intAdE F E

def TrivMod (ξ : (AdE F E)ˣ →* Circle) (𝔞 : Ideal (𝓞 E)) : Prop :=
  ∀ y : (AdE F E)ˣ, IsIntUnit y → (y : AdE F E) - 1 ∈ idHat F 𝔞 → ξ y = 1

def RamExactly (ξ : (AdE F E)ˣ →* Circle) (𝔣 : Ideal (𝓞 E)) : Prop :=
  𝔣 ≠ ⊥ ∧ TrivMod ξ 𝔣 ∧ ∀ P 𝔤 : Ideal (𝓞 E), P.IsPrime → 𝔣 = P * 𝔤 → ¬ TrivMod ξ 𝔤

def Generates (x : AdE F E) (𝔠 : Ideal (𝓞 E)) : Prop :=
  ∀ y, y ∈ idHat F 𝔠 ↔ ∃ z ∈ intAdE F E, y = x * z

end Adeles

section Lattices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r n : ℕ}

def barI (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

def InLevel (r M : ℕ) (PQ : Ideal (𝓞 E)) (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  (γ.map cc).transpose * γ = 1 ∧ OneMod M γ ∧
    ∃ k : ℕ, Nat.Coprime k (Ideal.absNorm PQ) ∧ ∀ i b : Fin n, r ≤ i.val → b.val < r →
      ∃ o ∈ PQ, (k : E) * γ i b = ((o : 𝓞 E) : E)

def Carries (γ : Matrix (Fin n) (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v, v ∈ L' ↔ ∃ u ∈ L, v = γ.mulVec u

end Lattices

section Record

variable {D : D7}

abbrev IdF (D : D7) : Type := (AdE D.host.F D.host.E)ˣ

def finU (D : D7) : (AE D)ˣ →* IdF D := Units.map (finPart D).toMonoidHom

variable (T : CoreJ D) {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ)

variable {T} {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)

variable (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrincipalCongruenceGamma
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrincipalCongruenceGamma

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsPrinc (X : Data E r) (M : ℕ) (γ : GL (Fin r) E) : Prop :=
  IsUStab X.Gm X.Λ γ ∧
    ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = M • y

def princ (X : Data E r) (M : ℕ) : Subgroup (GL (Fin r) E) where
  carrier := {γ | IsPrinc X M γ}
  one_mem' := by
    refine ⟨⟨fun x y => by simp, fun x => by simp⟩, fun x _ => ⟨0, X.Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨ha1, ha2⟩, ha3⟩ ⟨⟨hb1, hb2⟩, hb3⟩
    refine ⟨⟨fun x y => ?_, fun x => ?_⟩, fun x hx => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha1, hb1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha2, ← hb2]
    · obtain ⟨y, hy, e⟩ := hb3 x hx
      obtain ⟨z, hz, e'⟩ := ha3 _ ((hb2 x).1 hx)
      refine ⟨z + y, X.Λ.add_mem hz hy, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, smul_add, ← e, ← e']
      abel
  inv_mem' := by
    rintro a ⟨⟨ha1, ha2⟩, ha3⟩
    have hc : ∀ x : Fin r → E, Matrix.mulVec (a : Matrix (Fin r) (Fin r) E)
        (Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hm : ∀ x, x ∈ X.Λ ↔ Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x ∈ X.Λ := by
      intro x
      rw [ha2 (Matrix.mulVec ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x), hc]
    refine ⟨⟨fun x y => ?_, hm⟩, fun x hx => ?_⟩
    · rw [← ha1, hc, hc]
    · obtain ⟨y, hy, e⟩ := ha3 _ ((hm x).1 hx)
      refine ⟨-y, X.Λ.neg_mem hy, ?_⟩
      rw [hc] at e
      rw [smul_neg, ← e]
      abel

end Model

variable {D : D7}

def GamAt (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Prop :=
  ∀ k : (T.U j σ).Comp, princ ((T.U j σ).X k) T.Q.l.M ≤ ((T.U j σ).X k).Γ

def Gam (T : Core D) : Prop :=
  ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → GamAt T j σ

end GlobalTheory.IndefiniteRowSideFullHecke.PrincipalCongruenceGamma
end
end

