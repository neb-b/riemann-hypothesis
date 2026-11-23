module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.FibreSum
section
noncomputable section

open Finset
open scoped Classical

namespace UpperTheory.Gal.Schur

def FibreSum : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [CharZero K] (n : ℕ)
    (lam : (E →+* K) → Fin n → ℕ), ∃ k₀, ∀ k, k₀ ≤ k →
    ∀ (N : NumberField.RingOfIntegers E), N ≠ 0 → ∀ B : Finset K,
      ∃ c : (Fin k → NumberField.RingOfIntegers E) →₀ K,
        (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ N ∣ α s ∧ ∀ τ : E →+* K, ∀ b ∈ B, 1 - resO τ (α s) * b ≠ 0) ∧
        ∀ (R : Type) [CommRing R] [Algebra K R] [Algebra ℚ R] (t₀ t₁ : E →+* K), t₀ ≠ t₁ →
          ∀ (ε : (E →+* K) → ℕ) (m : ℕ) (g : (E →+* K) → Fin n → R) (y : R),
          ((∀ i, lam t₁ i = m) → (∀ i j, j ≠ i → IsUnit (g t₀ j - g t₀ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₀ j - y * g t₀ i) * Ring.inverse (g t₀ j - g t₀ i))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ ((n - 1) * m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))) ∧
          ((∀ i, lam t₀ i = m) → (∀ i j, j ≠ i → IsUnit (g t₁ j - g t₁ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₁ i - y * g t₁ j) * Ring.inverse (g t₁ i - g t₁ j))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ (m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (∑ j ∈ univ.erase i, lam t₁ j + (i : ℕ))))

theorem fibreSum_of (h : InterpNF) (h₁ : Fibre) (h₂ : FibreOff) : FibreSum := by
  intro E K _ _ _ _ n lam
  obtain ⟨k₀, hk⟩ := h E K n lam
  refine ⟨k₀, fun k hk' N hN B => ?_⟩
  obtain ⟨c, hc, hsum⟩ := hk k hk' N hN B
  refine ⟨c, hc, fun R _ _ _ t₀ t₁ ht ε m g y => ?_⟩
  have swap : ∀ C : Fin n → R,
      (c.sum fun α r => r • ∑ i,
        (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) * C i) =
      ∑ i, (∏ τ, sch (lam τ) (twist t₀ t₁ ε y i g τ)) * C i := by
    intro C
    rw [Finsupp.sum]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsum R (twist t₀ t₁ ε y i g), Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_mul_assoc]
  refine ⟨fun hm hu => ?_, fun hm hu => ?_⟩
  · rw [swap]
    exact h₁ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu
  · rw [swap]
    exact h₂ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

def MixDet : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (d d' : Fin n → R),
    ∑ i, (Matrix.of fun a j : Fin n => (if j = i then d a else d' a) * M a j).det =
      (∑ a, d a * ∏ b ∈ univ.erase a, d' b) * M.det

def vdmAway {R : Type} [CommRing R] {n : ℕ} (i : Fin n) (g : Fin n → R) : R :=
  ∏ a ∈ univ.erase i, ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b)

def PairSplit : Prop :=
  ∀ (R : Type) [CommMonoid R] (n : ℕ) (F : Fin n → Fin n → R) (i : Fin n),
    ∏ a, ∏ b ∈ Finset.Ioi a, F a b =
      (∏ a ∈ univ.erase i, ∏ b ∈ (Finset.Ioi a).erase i, F a b) *
        ∏ k ∈ univ.erase i, (if k < i then F k i else F i k)

def VdmSplit : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (g : Fin n → R) (i : Fin n),
    vdm g = (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - g k)

def PairCount : Prop :=
  ∀ (n : ℕ) (i : Fin n),
    ∑ k ∈ univ.erase i, (n - 1 - (k : ℕ)) = (n - 1).choose 2 + (i : ℕ) ∧
    ∑ a ∈ univ.erase i, ((Finset.Ioi a).erase i).card = (n - 1).choose 2

def OffClrRed : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    ∑ i, sch lam (scaleOff y i g) * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))

def OffClrPow : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    y ^ (n - 1).choose 2 *
      ∑ i, sch lam (scaleOff y i g) * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      y ^ (n - 1).choose 2 * (sch lam g * vdm g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)))

def Expand : Prop :=
  ∀ (K R π : Type) [CommRing K] [CommRing R] [Algebra K R] [Fintype π] [DecidableEq π] (n : ℕ) (x : π → R)
    (g : π → Fin n → R),
    ∏ p, detOne (x p) (g p) =
      ∑ m : π → Fin (n + 1), (∏ p, x p ^ (m p : ℕ)) *
        ∏ p, ((-1) ^ (m p : ℕ) * aeval (g p) (esymm (Fin n) K (m p)))

def DenseSub : Prop :=
  ∀ (K σ : Type) [Field K] [CharZero K] [Fintype σ] (L : AddSubgroup (σ → K)) (a : σ → K),
    Submodule.span K (L : Set (σ → K)) = ⊤ → ZDense {x | x - a ∈ L}

def SpanTop : Prop :=
  ∀ (O K ι : Type) [CommRing O] [Field K] [Fintype ι] (τ : ι → (O →+* K)), Function.Injective τ →
    ∀ (N : O), (∀ t, τ t N ≠ 0) → ∀ k : ℕ,
      Submodule.span K {x : ι × Fin k → K | ∃ β : Fin k → O, x = pt τ (fun s => N * β s)} = ⊤

def DenseOff : Prop :=
  ∀ (K σ : Type) [Field K] (D : Set (σ → K)), ZDense D → ∀ Q : MvPolynomial σ K, Q ≠ 0 →
    ZDense {x | x ∈ D ∧ eval x Q ≠ 0}

def SpanProd : Prop :=
  ∀ (K ι : Type) [CommRing K] [Fintype ι] [DecidableEq ι] (n : ℕ) (P : ι → MvPolynomial (Fin n) K),
    (∀ t, (P t).IsSymmetric) → ∃ k₀, ∀ k, k₀ ≤ k → ∃ w : (ι × Fin k → Fin (n + 1)) → K,
      ∀ (R : Type) [CommRing R] [Algebra K R] (g : ι → Fin n → R),
        ∏ t, aeval (g t) (P t) =
          ∑ m, w m • ∏ p : ι × Fin k, ((-1) ^ (m p : ℕ) * aeval (g p.1) (esymm (Fin n) K (m p)))

def eSpan (K : Type) [CommRing K] (n k : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (Set.range fun m : Fin k → Fin (n + 1) => ∏ s, esymm (Fin n) K (m s))

def ESpanMul : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ),
    (∀ k l, k ≤ l → eSpan K n k ≤ eSpan K n l) ∧
    (∀ k l P Q, P ∈ eSpan K n k → Q ∈ eSpan K n l → P * Q ∈ eSpan K n (k + l))

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.WeylTieOf
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem vdm_ne {K : Type} [Field K] {n : ℕ} (g : Fin n → K)
    (hg : Function.Injective g) : vdm g ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  refine sub_ne_zero.2 fun h => ?_
  have := hg h
  subst this
  simp at hj

private theorem num_eq {K : Type} [Field K] {n : ℕ} (l : Fin n → ℤ) (m : ℕ) (lam : Fin n → ℕ)
    (g : Fin n → K) (hl : ∀ i, l i + m = lam i) (h0 : ∀ i, g i ≠ 0) :
    (∏ k, g k) ^ m * altnZ (fun i => l i + n - 1 - (i : ℕ)) g = altn (shift lam) g := by
  unfold altnZ altn shift
  rw [← Finset.prod_pow, ← Matrix.det_mul_row (fun k => g k ^ m)]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [← zpow_natCast (g j) m, ← zpow_natCast (g j) (lam i + (n - 1 - (i : ℕ))), ← zpow_add₀ (h0 j)]
  congr 1
  have h1 := hl i
  have h2 := i.isLt
  push_cast
  omega

theorem weylTie_of : Comparison₂ → WeylTie := by
  intro hT K _ _ n l m lam g hl hg h0
  have hv := vdm_ne g hg
  have hp : (∏ k, g k) ^ m ≠ 0 := pow_ne_zero _ (prod_ne_zero_iff.mpr fun k _ => h0 k)
  rw [div_eq_div_iff hv hp, hT K n lam g, ← num_eq l m lam g hl h0]
  ring

end UpperTheory.Gal.Schur
end
end

