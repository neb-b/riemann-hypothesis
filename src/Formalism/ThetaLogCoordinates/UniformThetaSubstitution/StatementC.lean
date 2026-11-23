module

public import Mathlib
public import Formalism.SubspaceCounting.Bundle0001

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def eF {K σ : Type} [CommRing K] [Fintype σ] (x : σ → K) (l : ℕ) : K :=
  MvPolynomial.eval x (MvPolynomial.esymm σ K l)

def hF {K σ : Type} [CommRing K] [Fintype σ] [DecidableEq σ] (x : σ → K) (l : ℕ) : K :=
  MvPolynomial.eval x (MvPolynomial.hsymm σ K l)

def beFam {K : Type} [Field K] (Q : K) (g : ℕ) : Fin g → K :=
  fun i => Q ^ ((g : ℤ) - 1 - 2 * (i.val : ℤ))

def FFam {K : Type} [Field K] (Q : K) (t : ℕ) (m : ℕ → K) (j : ℕ) : Fin j × Fin (t + 1) → K :=
  fun x => m (x.1.val + 1) * beFam Q (t + 1) x.2

def GaussEsymm : Prop :=
  ∀ (K : Type) [Field K] (Q g l : ℕ), (Q : K) ≠ 0 →
    ((Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) = (Q : K) ^ (l * (g - l)) * eF (beFam (Q : K) g) l

def HEConvolution : Prop :=
  ∀ (K σ : Type) [CommRing K] [Fintype σ] [DecidableEq σ] (x : σ → K) (n : ℕ), 1 ≤ n →
    ∑ a ∈ range (n + 1), (-1 : K) ^ a * hF x a * eF x (n - a) = 0

def Kc {K : Type} [Field K] {M : ℕ → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) : ∀ j, M 0 →ₗ[K] M j
  | 0 => LinearMap.id
  | j + 1 => (Kk j).comp (Kc Kk j)

def Intertwine {K : Type} [Field K] {M : ℕ → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (e : ∀ j, ℕ → Module.End K (M j)) (Q : K) (t : ℕ) (m : ℕ → K)
    (J : ℕ) : Prop :=
  ∀ j, j < J → ∀ i,
    (e (j + 1) i).comp (Kk j) =
      (Kk j).comp (∑ l ∈ range (i + 1), eF (fun x => m (j + 1) * beFam Q (t + 1) x) l • e j (i - l))

def Iterate : Prop :=
  ∀ (K : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (e : ∀ j, ℕ → Module.End K (M j)) (Q : K) (t : ℕ) (m : ℕ → K)
    (J : ℕ), Intertwine Kk e Q t m J →
    ∀ j, j ≤ J → ∀ i,
      (e j i).comp (Kc Kk j) =
        (Kc Kk j).comp (∑ l ∈ range (i + 1), eF (FFam Q t m j) l • e 0 (i - l))

def Inversion : Prop :=
  ∀ (K : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (e : ∀ j, ℕ → Module.End K (M j)) (Q : K) (t : ℕ) (m : ℕ → K)
    (J : ℕ), Intertwine Kk e Q t m J →
    ∀ j, j ≤ J → ∀ r,
      (∑ l ∈ range (r + 1), ((-1 : K) ^ l * hF (FFam Q t m j) l) • e j (r - l)).comp (Kc Kk j) =
        (Kc Kk j).comp (e 0 r)

def NN (k t j : ℕ) : ℕ := k + j * (t + 1)

def NprimeZ {ι : Type} (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (i : ℕ) : ℤ :=
  ∑ s ∈ Ev, ∑ a ∈ Icc 1 i, lam s a + (i : ℤ) * ∑ s ∈ Od, wj s

def ArZ {ι : Type} (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (k r : ℕ) : ℤ :=
  ∑ s ∈ Ev, ∑ a ∈ Icc 1 r, lam s a - ∑ s ∈ Od, ∑ a ∈ Icc (k + 1 - r) k, lam s a

def PrZ {ι : Type} (Od : Finset ι) (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (k r j t ν : ℕ) : ℤ :=
  ∑ s ∈ Od, ((r : ℤ) * wj s + ∑ a ∈ Icc (k + 1 - r) k, lam s a) + (ν : ℤ) * r * j * (t + 1)

def cCoef {K ι : Type} [Field K] (pp : K) (ν : ℕ) (Ev Od : Finset ι) (lam : ι → ℕ → ℤ)
    (w : ℕ → ι → ℤ) (m : ℕ → K) (k t r j l : ℕ) : K :=
  pp ^ (NprimeZ Ev Od lam (w j) r - NprimeZ Ev Od lam (w j) (r - l)) *
    (pp ^ ν) ^ ((l : ℤ) * ((NN k t j : ℤ) - 2 * r + l)) * hF (FFam (pp ^ ν) t m j) l

def Ttil {K ι V : Type} [Field K] [AddCommGroup V] [Module K V] (pp : K) (Ev Od : Finset ι)
    (lam : ι → ℕ → ℤ) (wj : ι → ℤ) (Tm : ℕ → Module.End K V) (i : ℕ) : Module.End K V :=
  pp ^ (NprimeZ Ev Od lam wj i) • Tm i

def Zop {K ι V : Type} [Field K] [AddCommGroup V] [Module K V] (pp : K) (ν : ℕ) (Ev Od : Finset ι)
    (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m : ℕ → K) (k t r j : ℕ) (Tm : ℕ → Module.End K V) :
    Module.End K V :=
  ∑ l ∈ range (r + 1),
    ((-1 : K) ^ l * cCoef pp ν Ev Od lam w m k t r j l) • Ttil pp Ev Od lam (w j) Tm (r - l)

def ThmCi : Prop :=
  ∀ (K ι : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (Tm : ∀ j, ℕ → Module.End K (M j)) (pp : K) (ν k t r j : ℕ)
    (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m : ℕ → K),
    pp ≠ 0 → r ≤ k →
    Intertwine Kk (fun a i => ((pp ^ ν) ^ (-((i : ℤ) * ((NN k t a : ℤ) - i)))) • Tm a i)
      (pp ^ ν) t m j →
    (Zop pp ν Ev Od lam w m k t r j (Tm j)).comp (Kc Kk j) =
      pp ^ (PrZ Od lam (w j) k r j t ν) • (Kc Kk j).comp (pp ^ (ArZ Ev Od lam k r) • Tm 0 r)

end Formalism.InvariantFactorPaths.G7
