module

public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002

@[expose] public section

open Finset Polynomial
open scoped Classical ComplexOrder

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)

def PrimeToPartEndo : Prop :=
  ∀ (M M' : Type) [CommMonoid M] [Monoid M'] (l : ℕ) (x y : M) (φ : M →* M'), l.Prime →
    IsOfFinOrder x → IsOfFinOrder y →
    primeToPart l (x * y) = primeToPart l x * primeToPart l y ∧
      φ (primeToPart l x) = primeToPart l (φ x)

def PowPolyExists : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (f : K[X])
    (a : ℕ), f.Monic →
    ∃ f' : K[X], f'.Monic ∧ f'.aroots L = (f.aroots L).map (fun x => x ^ a)

def ExcludedSimplify : Prop :=
  ∀ (N : ℕ) (Y : ℝ), 1 ≤ N → 1 ≤ Y →
    (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) ≤
      20 * (N : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4)

def AdmissibleCount : Prop :=
  ∀ (c₀ c X B h P A : ℝ), 0 < c₀ → (2 : ℝ) ^ 14 / c₀ ≤ c → 1 < X → Real.log X ≤ c →
    0 < B → B ≤ 4 * c ^ 3 → 0 < h → h ≤ c ^ 3 →
    c₀ * B ^ (-5 : ℤ) * X / (h * Real.log X) ≤ P → P ≤ 2 * A →
    8 * c ^ (-20 : ℤ) * X ≤ A




open Classical in
def LemmaPSubSum : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ : Equiv.Perm (Fin N) => IsSubSum σ.partition.parts a)).card ≤ 7 * N.factorial

def eqvSpace {G V ι : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (emb : ι → G) (χ : ι → ℂ) : Submodule ℂ V where
  carrier := {x | ∀ u, ρ (emb u) x = χ u • x}
  add_mem' := by
    intro x y hx hy u
    rw [map_add (f := _), hx u, hy u, smul_add]
  zero_mem' := by
    intro u
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro a x hx u
    rw [map_smul, hx u, smul_comm]


open Classical in
def twistedIdem {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ) :
    MonoidAlgebra ℂ G :=
  ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) • MonoidAlgebra.of ℂ G (u : G)

def IsIrr {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤

def CentralIdemSumOne : Prop :=
  ∀ (G I : Type) [Group G] [Fintype G] [Fintype I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, IsIrr (ρ i)) →
    (∀ i j, (∃ φ : V i ≃ₗ[ℂ] V j, ∀ g x, φ (ρ i g x) = ρ j g (φ x)) → i = j) →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (σ : Representation ℂ G W), IsIrr σ →
      ∃ i, ∃ φ : W ≃ₗ[ℂ] V i, ∀ g x, φ (σ g x) = ρ i g (φ x)) →
    ∑ i, centralIdem (ρ i) = 1

def besselEdge (s k i j : ℕ) : Prop :=
  (j = i + 1 ∧ (j < s ∨ (s ≤ i ∧ j < s + k) ∨ s + k ≤ i)) ∨ (i + 1 = s ∧ j = s + k)

def besselSet (K : Type) [Field K] (s k N : ℕ) : Set (GL (Fin N) K) :=
  {u | (∀ i, (u : Matrix (Fin N) (Fin N) K) i i = 1) ∧
    (∀ i j, j < i → (u : Matrix (Fin N) (Fin N) K) i j = 0) ∧
    ∀ i j : Fin N, s ≤ (i : ℕ) → (i : ℕ) < s + k → (j : ℕ) = s + k →
      (u : Matrix (Fin N) (Fin N) K) i j = 0}


open Classical in
def besselChar {K : Type} [Field K] (ψ₀ : AddChar K ℂ) (s k N : ℕ) (u : GL (Fin N) K) : ℂ :=
  ψ₀ (∑ i : Fin N, ∑ j : Fin N,
    if besselEdge s k i j then (u : Matrix (Fin N) (Fin N) K) i j else 0)

def besselSpace {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (ρ : Representation ℂ (GL (Fin N) K) V) (ψ₀ : AddChar K ℂ) (s k : ℕ) : Submodule ℂ V :=
  eqvSpace ρ (fun u : besselSet K s k N => (u : GL (Fin N) K))
    (fun u => besselChar ψ₀ s k N (u : GL (Fin N) K))

def GelfandGraevMultOne : Prop :=
  ∀ (K V : Type) [Field K] [Fintype K] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (N : ℕ) (ψ₀ : AddChar K ℂ) (ρ : Representation ℂ (GL (Fin N) K) V), ψ₀ ≠ 1 → IsIrr ρ →
    Module.finrank ℂ (besselSpace ρ ψ₀ 0 0) ≤ 1


open Classical in
def IrredCountUpperUnit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (d : ℕ), 1 ≤ d →
    d * ((Finset.univ : Finset (Fin d → K)).filter
      (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card
      ≤ Fintype.card K ^ d - 1

def TypeWeightU : Prop :=
  ∀ (g : ℕ) (D : Finset ℕ) (Nd n : ℕ → ℕ), 2 ≤ g → (∀ d ∈ D, 1 ≤ d) →
    (∀ d ∈ D, d * Nd d ≤ g ^ d - 1) →
    (∏ d ∈ D, ((Nd d).choose (n d) : ℝ) / ((g : ℝ) ^ d - 1) ^ (n d)) ≤
      1 / ∏ d ∈ D, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))

def ComparisonTransfer : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (T : ι → Type) [∀ v, Fintype (T v)]
    (wU wJ : ∀ v, T v → ℝ) (g : ℝ) (A : Finset (∀ v, T v)), 1 ≤ g →
    (∀ v t, 0 ≤ wU v t) → (∀ v, ∑ t, wU v t = 1) → (∀ v, ∑ t, wJ v t = 1) →
    (∀ v t, (1 - 1 / g) * wU v t ≤ wJ v t) →
    ∑ x ∈ A, ∏ v, wJ v (x v) ≤ ∑ x ∈ A, ∏ v, wU v (x v) + (Fintype.card ι : ℝ) / g


open Classical in
def sqWeight {K : Type} [Field K] [Fintype K] (f : K[X]) : ℝ :=
  ((UniqueFactorizationMonoid.normalizedFactors f).map
    (fun P => ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹)).prod


open Classical in
def sqSet (K : Type) [Field K] [Fintype K] (N : ℕ) : Finset (Fin N → K) :=
  Finset.univ.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)


open Classical in
def degType {K : Type} [Field K] (f : K[X]) : Multiset ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree

def SqMassLeOne : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (M : ℕ), ∑ c ∈ sqSet K M, sqWeight (monicOf c) ≤ 1

def SqMassLower : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ), 1 ≤ N →
    1 - 2 / (Fintype.card K : ℝ) ≤ ∑ c ∈ sqSet K N, sqWeight (monicOf c)



open Classical in
def TypeWeightExact : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (n : ℕ → ℕ), ∑ d ∈ Finset.Icc 1 N, d * n d = N →
    ∑ c ∈ (sqSet K N).filter (fun c => ∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d),
        sqWeight (monicOf c) =
      ∏ d ∈ Finset.Icc 1 N,
        (((((Finset.univ : Finset (Fin d → K)).filter
          (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d) : ℕ) : ℝ) /
          ((Fintype.card K : ℝ) ^ d - 1) ^ (n d)


open Classical in
def TypeSetWeight : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ) (A : Multiset ℕ → Prop),
    ∑ c ∈ (sqSet K N).filter (fun c => A (degType (monicOf c))), sqWeight (monicOf c) ≤
      (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ : Equiv.Perm (Fin N) => A σ.partition.parts)).card : ℝ) / (N.factorial : ℝ)


open Classical in
def SameFactorCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (δ l : ℕ),
    l.Prime → 2 ≤ δ →
    l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ →
    (((Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L))).card : ℝ) ≤
      (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4)


open Classical in
def CrossFactorCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (δ l : ℕ)
    (P' : K[X]), l.Prime → 1 ≤ δ → Irreducible P' → P'.coeff 0 ≠ 0 →
    l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ →
    (((Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      (monicOf c).coeff 0 ≠ 0 ∧ ∃ x ∈ (monicOf c).rootSet L, ∃ y ∈ P'.rootSet L,
        primeToPart l x = primeToPart l y)).card : ℝ) ≤
      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4)


open Classical in
def LocalEstimateII : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (N : ℕ),
    2 ^ 12 ≤ Fintype.card K →
    ∑ c ∈ (sqSet K N).filter (fun c => ∃ l : ℕ, l.Prime ∧ l ∉ BB (Fintype.card K) N ∧
        ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)), sqWeight (monicOf c) ≤
      23 * Real.log (Fintype.card K) / Real.sqrt (Fintype.card K)

def PrimePowerOrderShare : Prop :=
  ∀ g q₁ d : ℕ, 2 ≤ g → q₁.Prime → d.Prime → q₁ ≠ d → q₁ ≠ 2 → d ≠ 2 → 16 ≤ max q₁ d →
    16 ∣ g - 1 → q₁ ∣ g - 1 → d ∣ g - 1 →
    (∑ l ∈ (g - 1).primeFactors, ((l ^ padicValNat l (g - 1) : ℕ) : ℝ)) / ((g - 1 : ℕ) : ℝ) ≤
      1 / (4 * (min q₁ d : ℕ))

def PrimePowerOrderCount : Prop :=
  ∀ g δ : ℕ, 2 ≤ g → 4 ∣ g - 1 → 1 ≤ δ →
    ∑ l ∈ (g ^ δ - 1).primeFactors, l ^ padicValNat l (g ^ δ - 1) ≤
      δ * (g - 1) + (g ^ δ - 1) / (g - 1)


open Classical in
def LocalEstimateIII : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] (N q₁ d : ℕ)
    (c₀ : Kˣ), 1 ≤ N → q₁.Prime → d.Prime → q₁ ≠ d → q₁ ≠ 2 → d ≠ 2 → 16 ≤ max q₁ d →
    16 ∣ Fintype.card K - 1 → q₁ ∣ Fintype.card K - 1 → d ∣ Fintype.card K - 1 →
    ∑ c ∈ (sqSet K N).filter (fun c => ∃ l : ℕ, l.Prime ∧ l ≠ Fintype.card K ∧
        ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))), sqWeight (monicOf c) ≤
      1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((Fintype.card K : ℝ) - 1)


open Classical in
def LocalEstimateIV : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N a : ℕ), 0 < a → a < N →
    ∑ c ∈ (sqSet K N).filter (fun c => ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a),
      sqWeight (monicOf c) ≤ 7 / 8


open Classical in
def LocalEstimateV : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ), 100 ≤ N →
    ∑ c ∈ (sqSet K N).filter (fun c => ¬ ∃ P : K[X], Irreducible P ∧ P ∣ monicOf c ∧
        P.natDegree.Prime ∧ N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N), sqWeight (monicOf c) ≤
      1 - 1 / (5 * Real.log N)


open Classical in
def PropW : Prop :=
  ∀ (K L ι J : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L] [Fintype ι]
    [Fintype J] (N q₁ d : ℕ) (χ : ι → J → Kˣ) (P : (Fin N → K) → ℝ),
    100 ≤ N → 2 ^ 12 ≤ Fintype.card K → q₁.Prime → d.Prime → q₁ ≠ d → q₁ ≠ 2 → d ≠ 2 →
    16 ≤ max q₁ d → 16 ∣ Fintype.card K - 1 → q₁ ∣ Fintype.card K - 1 →
    d ∣ Fintype.card K - 1 →
    (∀ c, 0 ≤ P c) → ∑ c, P c = 1 → (∀ c ∈ sqSet K N, P c = sqWeight (monicOf c)) →
    ∑ x ∈ (Finset.univ : Finset (ι → Fin N → K)).filter
        (fun x => ¬ GoodAt K L N (fun v => monicOf (x v)) χ), ∏ v, P (x v) ≤
      2 * (Fintype.card ι : ℝ) / (Fintype.card K : ℝ) +
      23 * (Fintype.card ι : ℝ) * Real.log (Fintype.card K) / Real.sqrt (Fintype.card K) +
      2 * (Fintype.card ι : ℝ) * (Fintype.card J : ℝ) *
        (1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((Fintype.card K : ℝ) - 1)) +
      (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι +
      Real.exp (-(Fintype.card ι : ℝ) / (5 * Real.log N))

def ShareFromCount : Prop :=
  ∀ (ε W₁ W₂ PP₁ PP₂ D₁ D₂ Dall Dstar bad : ℝ), 0 ≤ ε → ε < 1 → 0 < Dstar →
    0 ≤ PP₁ → PP₁ ≤ W₁ → 0 ≤ PP₂ → PP₂ ≤ W₂ → |Dall - Dstar| ≤ ε * Dstar →
    |D₁ - PP₁ * Dstar| ≤ ε * (PP₁ * Dstar) → |D₂ - PP₂ * Dstar| ≤ ε * (PP₂ * Dstar) →
    bad ≤ D₁ + D₂ → bad / Dall ≤ (1 + ε) / (1 - ε) * (W₁ + W₂)

def BadRankUnion : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (p₁ p₂ : V →ₗ[k] V), p₁ ∘ₗ p₁ = p₁ → p₂ ∘ₗ p₂ = p₂ → p₁ ∘ₗ p₂ = p₂ ∘ₗ p₁ →
    Module.finrank k (LinearMap.range (p₁ + p₂ - p₁ ∘ₗ p₂)) ≤
      Module.finrank k (LinearMap.range p₁) + Module.finrank k (LinearMap.range p₂)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
