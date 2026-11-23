module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.CapelliCentralEnveloping
section
noncomputable section

open Finset PowerSeries

namespace Formalism.CohomologicalDescent.HeightDescentMinors

section Series

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def br (c : ℤ_[l]) : O⟦X⟧ := binomialSeries O c - 1

def act (c : ℤ_[l]) (f : O⟦X⟧) : O⟦X⟧ := f.subst (br l O c)

def phi (f : O⟦X⟧) : O⟦X⟧ := f.subst ((1 + X) ^ l - 1 : O⟦X⟧)

def mu : Finset ℤ_[l] := Polynomial.nthRootsFinset (l - 1) (1 : ℤ_[l])

def pi0 : O⟦X⟧ := ∏ d ∈ mu l, br l O d

def q0 : O⟦X⟧ := pi0 l O - C (l : O)

def q : O⟦X⟧ := PowerSeries.mk fun j => ((l.choose (j + 1) : ℕ) : O)

def inc (g : O⟦X⟧) : O⟦X⟧ := g.subst (pi0 l O)

end Series

def MuFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], (mu l).card = l - 1 ∧
    (∀ x : ZMod l, x ≠ 0 → ∃! d, d ∈ mu l ∧ PadicInt.toZMod d = x) ∧
    (l ≠ 2 → ∏ d ∈ mu l, d = -1)

def QMul : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    X * q l O = (1 + X) ^ l - 1 ∧ phi l O X = X * q l O

def QRoots : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] (ζ : O),
    IsPrimitiveRoot ζ l → q l O = ∏ b ∈ Finset.Ioo 0 l, (X - C (ζ ^ b - 1))

def ActLaws : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (∀ c d : ℤ_[l], act l O c (br l O d) = br l O (d * c)) ∧
    (∀ (c d : ℤ_[l]) (f : O⟦X⟧), act l O c (act l O d f) = act l O (d * c) f) ∧
    (∀ f : O⟦X⟧, act l O 1 f = f) ∧
    (∀ f : O⟦X⟧, phi l O f = act l O (l : ℤ_[l]) f) ∧
    (∀ (c : ℤ_[l]) (f : O⟦X⟧), phi l O (act l O c f) = act l O c (phi l O f)) ∧
    (∀ (c : ℤ_[l]) (f g : O⟦X⟧), act l O c (f * g) = act l O c f * act l O c g ∧
      act l O c (f + g) = act l O c f + act l O c g) ∧
    (∀ (c : ℤ_[l]) (a : O), act l O c (C a) = C a)

def R1 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∃ w : (O⟦X⟧)ˣ, pi0 l O = (w : O⟦X⟧) * X ^ (l - 1) ∧ constantCoeff (w : O⟦X⟧) = -1

def BasisGeneral : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (w : (R⟦X⟧)ˣ), 0 < n → ∀ f : R⟦X⟧,
    ∃! g : Fin n → R⟦X⟧, f = ∑ j, (g j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ)

def DivisibilityInvariant : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    ∀ d ∈ mu l, act l O d (pi0 l O) = pi0 l O

def PowerSeriesFreeBasis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 → ∀ f : O⟦X⟧,
    ∃! g : Fin (l - 1) → O⟦X⟧, f = ∑ j, inc l O (g j) * X ^ (j : ℕ)

def RootsOfUnityInvariants : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 → ∀ f : O⟦X⟧,
    (∀ d ∈ mu l, act l O d f = f) ↔ ∃ g : O⟦X⟧, f = inc l O g

def UnitFactorQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∃ g : (O⟦X⟧)ˣ, q0 l O = (g : O⟦X⟧) * q l O ∧ constantCoeff (g : O⟦X⟧) = -1

def RootOfUnityRemainder : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] (ζ : O), l ≠ 2 →
    IsPrimitiveRoot ζ l → ∀ b ∈ Finset.Ioo 0 l, (X - C (ζ ^ b - 1)) ∣ pi0 l O - C (l : O)

def R4 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∀ (S : ℕ) (m y : O⟦X⟧), inc l O m = q l O ^ S * y → ∃ m' : O⟦X⟧, m = (X - C (l : O)) ^ S * m'

def FrobeniusCongruence : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (f : ℤ_[l]⟦X⟧),
    ∃ r : ℤ_[l]⟦X⟧, phi l ℤ_[l] f = f ^ l + C (l : ℤ_[l]) * r

def FrobeniusPiZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    ∃ r : O⟦X⟧, phi l O (pi0 l O) = pi0 l O ^ l + C (l : O) * r

def FrobeniusCharP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [CharP O l] (g : O⟦X⟧),
    phi l O (inc l O g) = inc l O (g.subst (X ^ l : O⟦X⟧))

def R6 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∀ u c : ℤ_[l], u = 1 + (l : ℤ_[l]) * c → ∃ un : O⟦X⟧,
      act l O u (pi0 l O) = pi0 l O * (1 + inc l O un * q0 l O) ∧
      (∃ e : O, constantCoeff un = algebraMap ℤ_[l] O c + (l : O) * e) ∧
      act l O u (q0 l O) = inc l O (1 + X * un) * q0 l O ∧ IsUnit (1 + X * un)

def ZpowCongGen : Prop :=
  ∀ (R : Type) [CommRing R] (x v : R) (U : Rˣ) (κ : ℤ), (U : R) = 1 + x * v →
    x ^ 2 ∣ ((U ^ κ : Rˣ) : R) - (1 + (κ : R) * (x * v))

def ThetaCongPadic : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ) (c : ℤ_[l]) (m : ℤ), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c →
    ∃ e : ℤ_[l], ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) * (-((m : ℤ_[l]) * c) + (l : ℤ_[l]) * e)

section Capelli

variable {𝒰 : Type} [Ring 𝒰] {N : ℕ}

def capA (E : Fin N → Fin N → 𝒰) (v : 𝒰) (i j : Fin N) : 𝒰 := E i j + if i = j then v else 0

def capelli (E : Fin N → Fin N → 𝒰) (u : 𝒰) : 𝒰 :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin N => capA E (u - ((j : ℕ) : 𝒰)) (σ j) j).prod

end Capelli


def C2 : Prop :=
  ∀ (k : Type) [CommRing k] (𝒰 : Type) [Ring 𝒰] [Algebra k 𝒰] (V : Type) [AddCommGroup V]
    [Module k V] [Module 𝒰 V] [IsScalarTower k 𝒰 V] (N : ℕ) (E : Fin N → Fin N → 𝒰) (u : k)
    (lam : Fin N → k) (v : V), (∀ i j, i < j → E i j • v = 0) → (∀ i, E i i • v = lam i • v) →
    capelli E (algebraMap k 𝒰 u) • v = (∏ i : Fin N, (u + lam i - ((i : ℕ) : k))) • v

def MinorsDvd {R : Type} [CommRing R] {m p : ℕ} (x : R) (t : ℕ) (P : Matrix (Fin m) (Fin p) R) :
    Prop :=
  ∀ (f : Fin t → Fin m) (g : Fin t → Fin p), StrictMono f → StrictMono g →
    x ∣ (P.submatrix f g).det

def MinorsDvdAll : Prop :=
  ∀ (R : Type) [CommRing R] (m p t : ℕ) (x : R) (P : Matrix (Fin m) (Fin p) R),
    MinorsDvd x t P ↔ ∀ (f : Fin t → Fin m) (g : Fin t → Fin p), x ∣ (P.submatrix f g).det

def MinorsDvdMul : Prop :=
  ∀ (R : Type) [CommRing R] (m n p r t : ℕ) (x : R) (G : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin p) R) (H : Matrix (Fin p) (Fin r) R),
    MinorsDvd x t P → MinorsDvd x t (G * P * H)

def DiagMinors : Prop :=
  ∀ (R : Type) [CommRing R] (n t S : ℕ) (x : R) (a : Fin n → ℕ) (G H : Matrix (Fin n) (Fin n) R),
    (∀ J : Finset (Fin n), J.card = t → S ≤ ∑ j ∈ J, a j) →
    MinorsDvd (x ^ S) t (G * Matrix.diagonal (fun j => x ^ a j) * H)

def CharpolyDiag : Prop :=
  ∀ (O L : Type) [CommRing O] [Field L] (ι : O →+* L) (n : ℕ) (Θ Γ : Matrix (Fin n) (Fin n) O)
    (lam : O) (r : Fin n → O) (G : (Matrix (Fin n) (Fin n) L)ˣ), Function.Injective ι → lam ≠ 0 →
    Γ = 1 + lam • Θ →
    Γ.map ι * (G : Matrix (Fin n) (Fin n) L) =
      (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (1 + lam * r j)) →
    Θ.charpoly = ∏ j, (Polynomial.X - Polynomial.C (r j))

def MinorRed : Prop :=
  ∀ (O k : Type) [CommRing O] [CommRing k] (red : O →+* k) (lam : O) (n t S : ℕ)
    (P : Matrix (Fin n) (Fin n) O⟦X⟧) (f g : Fin t → Fin n), red lam = 0 →
    ((P.map (PowerSeries.map red)).submatrix f g).det = PowerSeries.map red (P.submatrix f g).det ∧
    ((X - C lam) ^ S ∣ (P.submatrix f g).det →
      (X : k⟦X⟧) ^ S ∣ ((P.map (PowerSeries.map red)).submatrix f g).det)

def LinDivision : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I →
    (∀ f : O⟦X⟧, ∃ (f₁ : O⟦X⟧) (a : O), f = (X - C c) * f₁ + C a) ∧
    (∀ (f₁ f₂ : O⟦X⟧) (a₁ a₂ : O), (X - C c) * f₁ + C a₁ = (X - C c) * f₂ + C a₂ →
      f₁ = f₂ ∧ a₁ = a₂)

def LinPrime : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I →
    Prime (X - C c : O⟦X⟧)

def RootsProduct : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (s : Finset ℕ)
    (c : ℕ → O) (S : ℕ) (m : O⟦X⟧), (∀ b ∈ s, c b ∈ I) → Set.InjOn c s →
    (∀ b ∈ s, (X - C (c b)) ^ S ∣ m) → (∏ b ∈ s, (X - C (c b))) ^ S ∣ m

def RootsDescent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] (I : Ideal O)
    [IsAdicComplete I O] (ζ : O), l ≠ 2 → IsPrimitiveRoot ζ l → ζ - 1 ∈ I → ∀ (S : ℕ) (m : O⟦X⟧),
    (∀ b ∈ Finset.Ioo 0 l, (X - C (ζ ^ b - 1)) ^ S ∣ inc l O m) →
    ∃ m' : O⟦X⟧, m = (X - C (l : O)) ^ S * m'

def HeightDescent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], l ≠ 2 → ∀ (n h : ℕ)
    (P Q : Matrix (Fin n) (Fin n) O⟦X⟧),
    P.map (inc l O) * Q = (q l O ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧) →
    ∃ Q' : Matrix (Fin n) (Fin n) O⟦X⟧,
      P * Q' = ((X - C (l : O)) ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧)

end Formalism.CohomologicalDescent.HeightDescentMinors
end
end

-- bundled from Formalism.PieriBlockIdeals.Statement
section
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

open Classical

def vl (l : ℕ) (n : ℤ) : ℕ := padicValInt l n

def IlInd (l : ℕ) (xm xp mB : ℤ) : ℝ :=
  if ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB then 1 else 0

def d0 (l : ℕ) (D : ℤ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)}

def labelLHS (l k t : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (∑ ct ∈ Finset.Icc xm xp, (k : ℝ) * (vl l (ct - mB) : ℝ)) +
    ∑ ct ∈ Finset.Ioo mB xm,
      min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - mB) : ℝ)

def labelSumBound (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
    (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ)))

def LabelSum : Prop :=
  ∀ (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ), l.Prime → 0 ≤ i → 0 ≤ mB → mB < xm → xm ≤ xp →
    xp ≤ (h : ℤ) → h < l ^ 2 → l ≤ 2 * h →
    labelLHS l k t i xm xp mB ≤ labelSumBound l k t h i xm xp mB

def Linkage : Prop :=
  ∀ (l : ℕ) (K : Type) [Field K] [CharP K l] (N : ℕ) (U U' : Fin N → ℤ) (c : ℤ), l.Prime →
    (∏ a, (X + C (((U a + c : ℤ)) : K))) = ∏ a, (X + C (((U' a + c : ℤ)) : K)) →
    Multiset.map (fun a => ((U a : ℤ) : ZMod l)) Finset.univ.val =
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val

def mwCount (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ) : ℕ :=
  ((U.filter (fun u => u ∉ Finset.Icc b (b + t - 1))).filter
    (fun u => ∃ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ), x ≡ u [ZMOD (l : ℤ)])).card

def KapSum : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ) (kap : Fin t → ℤ), 0 < l → t + 2 * κ < l →
    (∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ U) → (∀ s, |kap s| ≤ (κ : ℤ)) →
    Multiset.map (fun s : Fin t => ((b + ((s : ℕ) : ℤ) - kap s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun u : ℤ => (u : ZMod l)) U.val →
    |∑ s, kap s| ≤ (mwCount l b t κ U : ℤ) * ((t : ℤ) + 2 * κ)

def WEArith : Prop :=
  ∀ (k j t q l h κ mw mwp : ℕ) (U U' : Fin (k + j + t + q) → ℤ) (kc kp : ℤ),
    StrictAnti U → StrictAnti U' → (∀ a, 0 ≤ U a) → (∀ a, U' a ≤ (h : ℤ)) →
    ∑ a, U a = ∑ a, U' a →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) +
        (l : ℤ) * kp - kc →
    |kc| ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) → |kp| ≤ (mwp : ℤ) * ((t : ℤ) + 2 * κ) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) ≤
      (q : ℤ) * h + ((l : ℤ) * mwp + mw) * ((t : ℤ) + 2 * κ)

def GatedSum : Prop :=
  ∀ (D h : ℕ) (L A k : ℝ) (P : Finset ℕ), 1 ≤ D → D ≤ h → 0 ≤ A → 0 ≤ k → (h : ℝ) < L ^ 2 →
    1 ≤ L → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, (if ((d0 l D : ℕ) : ℤ) < (D : ℤ) then min k (A / (d0 l D : ℝ)) else 0) *
        Real.log (l : ℝ) ≤
      A * (1 + Real.log (h : ℝ)) * Real.log (h : ℝ)

end Formalism.CohomologicalDescent
end
end

