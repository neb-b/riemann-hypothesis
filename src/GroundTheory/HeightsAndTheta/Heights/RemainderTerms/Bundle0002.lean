module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoinvReduction

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Flag

open MvPolynomial Finset

noncomputable section

theorem injective_of_surjective_endo {R : Type*} [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφ : Function.Surjective φ) : Function.Injective φ := by
  let K : ℕ →o Ideal R := ⟨fun n => RingHom.ker (φ ^ n), fun m n hmn x hx => by
    simp only [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [add_comm, Function.iterate_add_apply, hx, iterate_map_zero]⟩
  have hsurj : ∀ n, Function.Surjective (φ^[n]) := fun n => hφ.iterate n
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr
    (isNoetherianRing_iff.mp inferInstance) K
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj n x
  have hy : y ∈ K (n + 1) := by
    show (φ ^ (n + 1)) y = 0
    rw [RingHom.coe_pow, Function.iterate_succ_apply', hx]
  rw [← hn (n + 1) (Nat.le_succ n)] at hy
  have h' : (φ ^ n) y = 0 := hy
  simpa [RingHom.coe_pow] using h'

theorem psum_mem_range (N j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    psum (Fin N) ℚ j ∈ (powerSumHom N).range := by
  refine ⟨X ⟨j - 1, by omega⟩, ?_⟩
  change powerSumHom N (X ⟨j - 1, by omega⟩) = _
  simp only [powerSumHom, aeval_X]
  congr 1
  show j - 1 + 1 = j
  omega

theorem esymm_mem_range (N k : ℕ) (hk : k ≤ N) :
    esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [esymm_zero]; exact Subalgebra.one_mem _
    have hN := mul_esymm_eq_sum (Fin N) ℚ k
    have hmem : (k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
      rw [hN]
      refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_
      refine Subalgebra.sum_mem _ (fun a ha => ?_)
      obtain ⟨ha1', ha2⟩ := Finset.mem_filter.mp ha
      have ha1 := Finset.HasAntidiagonal.mem_antidiagonal.mp ha1'
      refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
        (ih a.1 ha2 (by omega))) (psum_mem_range N a.2 (by omega) (by omega))
    have hinv : esymm (Fin N) ℚ k = C ((k : ℚ)⁻¹) * ((k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k) := by
      rw [← mul_assoc, show (k : MvPolynomial (Fin N) ℚ) = C (k : ℚ) by simp, ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), C_1, one_mul]
    rw [hinv]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem

theorem exists_powerSumHom_eq {N : ℕ} {P : MvPolynomial (Fin N) ℚ} (hP : P.IsSymmetric) :
    ∃ S, powerSumHom N S = P := by
  obtain ⟨Q, hQ⟩ := esymmAlgHom_fin_surjective ℚ (le_refl N) ⟨P, hP⟩
  have h1 : P = aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q := by
    rw [← esymmAlgHom_apply, hQ]
  have h2 : aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q ∈ (powerSumHom N).range := by
    have hsub : Algebra.adjoin ℚ (Set.range fun i : Fin N => esymm (Fin N) ℚ (i + 1)) ≤
        (powerSumHom N).range := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact esymm_mem_range N _ (by omega)
    exact hsub (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Q, rfl⟩)
  rw [h1]
  exact h2

theorem powerSumHom_isSymmetric (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    (powerSumHom N S).IsSymmetric := by
  have : powerSumHom N S ∈ symmetricSubalgebra (Fin N) ℚ := by
    have hsub : (powerSumHom N).range ≤ symmetricSubalgebra (Fin N) ℚ := by
      rintro _ ⟨T, rfl⟩
      simp only [powerSumHom]
      have : Algebra.adjoin ℚ (Set.range fun i : Fin N => psum (Fin N) ℚ (i.val + 1)) ≤
          symmetricSubalgebra (Fin N) ℚ := by
        rw [Algebra.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        exact psum_isSymmetric (Fin N) ℚ _
      exact this (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨T, rfl⟩)
    exact hsub ⟨S, rfl⟩
  exact this

theorem powerSumHom_injective (N : ℕ) : Function.Injective (powerSumHom N) := by

  let e := esymmAlgEquiv (Fin N) ℚ (n := N) (by simp)
  let π : MvPolynomial (Fin N) ℚ →ₐ[ℚ] symmetricSubalgebra (Fin N) ℚ :=
    (powerSumHom N).codRestrict _ (fun S => powerSumHom_isSymmetric N S)
  let φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ := e.symm.toAlgHom.comp π
  have hsurj : Function.Surjective φ := by
    intro T
    obtain ⟨S, hS⟩ := exists_powerSumHom_eq (e T).2
    refine ⟨S, ?_⟩
    apply e.injective
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact Subtype.ext hS
  have hinj : Function.Injective φ := injective_of_surjective_endo φ.toRingHom hsurj
  intro S T hST
  apply hinj
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext hST

theorem constantCoeff_powerSumHom (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    constantCoeff (powerSumHom N S) = constantCoeff S := by
  induction S using MvPolynomial.induction_on with
  | C a => simp [powerSumHom]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, powerSumHom, aeval_X, constantCoeff_X, mul_zero]
    simp [psum, constantCoeff_X]

end

end Flag

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace Coinv

def IsUnderStaircase {f n : ℕ} (e : Fin f × Fin n →₀ ℕ) : Prop := ∀ v, e v ≤ (v.2 : ℕ)

def staircase (f n : ℕ) : Fin f × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => (v.2 : ℕ)

def underStaircaseSpan (K : Type*) [Field K] (f n : ℕ) :
    Submodule K (MvPolynomial (Fin f × Fin n) K) :=
  Submodule.span K {P | ∃ e : Fin f × Fin n →₀ ℕ, IsUnderStaircase e ∧ P = monomial e 1}

def coinvTop (f n : ℕ) : ℕ := f * (n * (n - 1) / 2)

end Coinv

open Coinv

def CoinvStepReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (b : Fin f) (k : Fin n)
    (e : Fin f × Fin n →₀ ℕ), (k : ℕ) + 1 ≤ e (b, k) →
    ∃ (T : Finset (Fin f × Fin n →₀ ℕ)) (c : (Fin f × Fin n →₀ ℕ) → K),
      (∀ e' ∈ T, (∀ u : Fin f × Fin n, (u.1 < b ∨ (u.1 = b ∧ u.2 < k)) → e' u = e u) ∧
        e' (b, k) < e (b, k)) ∧
      monomial e (1 : K) - ∑ e' ∈ T, c e' • monomial e' (1 : K) ∈ psumIdeal K f n

def CoinvMonomialReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (e : Fin f × Fin n →₀ ℕ),
    ∃ v ∈ underStaircaseSpan K f n, monomial e (1 : K) - v ∈ psumIdeal K f n

def CoinvPolynomialReduction.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    ∃ v ∈ underStaircaseSpan K f n, H - v ∈ psumIdeal K f n

def HomogeneousComponentMul.Statement : Prop :=
  ∀ (σ R : Type) [CommSemiring R] (p a : MvPolynomial σ R) (m d : ℕ), p.IsHomogeneous m →
    homogeneousComponent d (p * a) = if m ≤ d then p * homogeneousComponent (d - m) a else 0

def CoinvIdealRepresentation.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (J : MvPolynomial (Fin f × Fin n) K),
    J ∈ psumIdeal K f n →
    ∃ a : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      J = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * a m b

def CoinvIdealComponent.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (J : MvPolynomial (Fin f × Fin n) K),
    J ∈ psumIdeal K f n → ∀ d : ℕ,
    ∃ Q : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      homogeneousComponent d J = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * Q m b

def CoinvStaircaseDegree.Statement : Prop :=
  ∀ (f n : ℕ) (e : Fin f × Fin n →₀ ℕ), IsUnderStaircase e →
    e.degree ≤ coinvTop f n ∧ (e.degree = coinvTop f n → e = staircase f n)

def CoinvStaircaseComponent.Statement : Prop :=
  ∀ (K : Type) [Field K] (f n : ℕ) (v : MvPolynomial (Fin f × Fin n) K),
    v ∈ underStaircaseSpan K f n →
    (∀ d, coinvTop f n < d → homogeneousComponent d v = 0) ∧
    ∃ c : K, homogeneousComponent (coinvTop f n) v = C c * monomial (staircase f n) 1

def CoinvAboveTop.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n d : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    H.IsHomogeneous d → coinvTop f n < d →
    ∃ Q : ℕ → Fin f → MvPolynomial (Fin f × Fin n) K,
      (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      H = ∑ m ∈ Finset.Icc 1 n, ∑ b : Fin f, bps K f n m b * Q m b

def CoinvAtTop.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f n : ℕ) (H : MvPolynomial (Fin f × Fin n) K),
    H.IsHomogeneous (coinvTop f n) →
    ∃ c : K, H - C c * monomial (staircase f n) 1 ∈ psumIdeal K f n

def CoinvAboveTopGeneral.Statement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (β ι : Type) [Fintype β] [DecidableEq β] [Fintype ι]
    [DecidableEq ι] (d : ℕ) (H : MvPolynomial (β × ι) K), H.IsHomogeneous d →
    Fintype.card β * (Fintype.card ι * (Fintype.card ι - 1) / 2) < d →
    ∃ Q : ℕ → β → MvPolynomial (β × ι) K, (∀ m b, (Q m b).IsHomogeneous (d - m)) ∧
      H = ∑ m ∈ Finset.Icc 1 (Fintype.card ι), ∑ b : β, (∑ i : ι, X (b, i) ^ m) * Q m b

def VandermondeOfHomogeneous.Statement : Prop :=
  ∀ (σ R : Type) [CommRing R] (m : ℕ) (v : Fin m → MvPolynomial σ R),
    (∀ i, (v i).IsHomogeneous 1) → (vandermondeOf v).IsHomogeneous (m * (m - 1) / 2)

def RestPolynomialHomogeneous.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock),
    (restPolynomial f r a c).IsHomogeneous (topDegree f (r + a) + 1)

def RestPolynomialHomogeneousDecomposition.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), ∃ Q : ℕ → Fin f → RootRing f (r + a),
    IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q ∧
    ∀ k τ, (Q k τ).IsHomogeneous (topDegree f (r + a) + 1 - k)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

def RestInnerTsumBound.Statement : Prop :=
  ∀ (p : ℝ) (k : ℕ) (c : ℕ → ℝ) (M : ℝ), 2 ≤ p → 1 ≤ k → (∀ n, |c n| ≤ M) →
    Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) ∧
      |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n| ≤ M * (2 * (p ^ k)⁻¹)

def RestKSumBound.Statement : Prop :=
  ∀ (p X : ℝ) (N : ℕ), 0 < p → 0 ≤ X → X ≤ 3 / 8 * p →
    ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) ≤ 1.5 * X / p ^ 2

def RestPrimeBoundOfFactor.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      (∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)) →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) →
    ∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

def RestBoundOfPrimeBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ (Q : ℕ → Fin f → RootRing f (r + a)) (s : ℕ → ℕ → Fin f → Fin f)
      (e : ℕ → ℕ → Fin f → ℕ → ℚ),
    (∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|) →
    ∀ P : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
        |restPrimeModel f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Q s e p| ≤
        1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

def OtherFactorFormula.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 2 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f ∧
      ∀ Q : ℕ → Fin f → RootRing f (r + a),
        IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
        ∀ (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ r + a) (τ τ' : Fin f), τ' ≠ τ →
          ∃ S : MvPolynomial (Fin (r + a)) ℚ,
            powerSumHom (r + a) S =
              ∑ nu ∈ partitionsOf r k,
                C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
                  aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) ∧
            restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ') =
              C₀ * k * (f * (r * a) + 1).factorial /
                  (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
                    ((r * a).factorial : ℚ) ^ (f - 2)) *
                (numStandardTable (rectangle r a) : ℚ) ^ (f - 2) *
                symmetricGroupCharacter (rectangle r a)
                  ((k - 1) :: List.replicate (r * a - (k - 1)) 1) *
                AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)

def SchurSignCoefficient.Statement : Prop :=
  ∀ (N r k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (nu : Fin r → ℕ) (s : ℚ), (s = 1 ∨ s = -1) →
    Antitone nu → ∑ i, nu i = k →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = aeval (fun i : Fin N => C s * X i) (schur (Fin N) nu) ∧
      AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) =
        s ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0

def HookTableauCount.Statement : Prop :=
  ∀ r k l : ℕ, l < k → l < r → numStandardTable (hookShape r k l) = Nat.choose (k - 1) l

def RectangleTablePos.Statement : Prop :=
  ∀ r a : ℕ, 0 < numStandardTable (rectangle r a)

def HookSumBound.Statement : Prop :=
  ∀ (r a k : ℕ) (b : (Fin r → ℕ) → ℚ), 1 ≤ k →
    (∀ nu ∈ partitionsOf r k, |b nu| ≤ numStandardTable (fun i => a + nu i)) →
    ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), |b nu| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a)

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

