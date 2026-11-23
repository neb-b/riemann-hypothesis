module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def quotPart (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRingOver S ι)) (c : K → ℤ) : Submodule S (MRingOver S ι ⧸ V) :=
  Submodule.span S ((Ideal.Quotient.mk V) ''
    {p | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)})

def GeneratedV (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (n : K → ℤ) : Prop :=
  ∀ I : Cell K ι 0, ∃ (r : ℕ) (z : Fin r → CechC S ι (MRingOver S ι ⧸ V) 0)
    (u : Fin r → LocalizedModule (cellMon S I.1) (MRingOver S ι ⧸ V)),
    (∀ j, z j ∈ cechZc ι (quotPart S V) n 0) ∧
    (∀ j, u j ∈ locPart ι (quotPart S V) (cellMon S I.1) (-n)) ∧
    ∑ j, u j * z j I = 1

def AmpleV (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ GeneratedV S V (q • N) ∧
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (cechHc ι (quotPart S V) (e + (c * q) • N) 1)

def KAmpStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (d : ℕ)
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsProjVarF V d → NefOnF I V α → 1 ≤ b → 1 ≤ a →
    AmpleV F V (b • α + fun _ => (a : ℤ))

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def genIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) : Ideal (MRingOver ℚ ι) :=
  (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))

def GeneratesOn {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] {ι' : Type*} [Fintype ι']
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ u : ι' → Ω, (∀ j, u j ∈ chartRingZ y c) ∧
    ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = 1

def SecEqStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ τ₀ : ℕ, ∀ τ : ℕ, τ₀ ≤ τ → chartLat y (fun k => (a k : ℤ)) τ = secM y (fun k => τ * a k)

def CondStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y →
    ∃ (k : ℕ) (c : MRing ι), IsMultiHomog c (fun κ => k * a κ) ∧ aeval y c ≠ 0 ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ, aeval y c * s ∈ secM y (fun κ => (τ + k) * a κ)

def SiuZStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (I : IFamily ℚ ι),
    IsFieldIntersection I → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnF I (genIdeal y) α →
    0 < I (genIdeal y) D (fun _ => α) →
    ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
end
end

