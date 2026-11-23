module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CongL
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G1

def AuxiliaryInertOddPrime : Prop := ∀ d : ℕ, 0 < d → ∀ b : ℕ, ∃ (p : ℕ) (_ : Fact p.Prime), b < p ∧ IsSquare (-(d : ℚ_[p]))

def ArithK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ), 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
  ∀ (τ₀ : E →+* ℂ) (Q : Finset ℕ), (∀ q ∈ Q, ∃ _ : Fact q.Prime, IsSquare (-(d : ℚ_[q]))) →
  ∃ A : Arith E, A.τ₀ = τ₀ ∧ (∃ f : ℚ, f ≠ 0 ∧ 2 * (A.ω : E) - (A.tr : E) = (f : E) * x) ∧
    (∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → A.SplitK q) ∧ ∀ q ∈ Q, A.Good q

def ScOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Even (Module.finrank ℚ (maximalRealSubfield E)) →
  ∀ (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p), Odd n → Sc S.D S.G

def RootAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (q : ℕ), q.Prime → A.SplitK q →
  ∀ w : HeightOneSpectrum (𝓞 E), (q : 𝓞 E) ∈ w.asIdeal →
  ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal

end UpperTheory.Gal.G1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAdFour
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem UpperTheory.Gal.G1.exists_local (hF : LocFour) (hU : LocUnit) (hR : LocRoot) (hS : SplitRep)
    (F : Type) [Field F] [NumberField F] (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm ≠ 0) (c : 𝓞 F) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f : Fin 4 → v.adicCompletion F,
      algebraMap F (v.adicCompletion F) (c : F) * (qf tr nm (f 0) (f 1) + qf tr nm (f 2) (f 3)) = 1 ∧
      (c ∉ v.asIdeal → (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) → ∀ i, f i ∈ v.adicCompletionIntegers F) := by
  have hcF : (c : F) ≠ 0 := by simpa using hc
  have hcv : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    simpa using hcF
  by_cases hg : c ∉ v.asIdeal ∧ (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm)
  · obtain ⟨hcm, hor⟩ := hg
    have hval : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)).trans ?_
      have h0 : v.valuation F (c : F) = v.intValuation c := HeightOneSpectrum.valuation_of_algebraMap v c
      rw [h0]
      first
        | exact (HeightOneSpectrum.intValuation_eq_one_iff v).2 hcm
        | exact le_antisymm (v.intValuation_le_one c)
            (not_lt.1 fun h => hcm ((v.intValuation_lt_one_iff_mem c).1 h))
    have hval' : Valued.v (algebraMap F (v.adicCompletion F) (c : F))⁻¹ = 1 := by
      rw [map_inv₀, hval, inv_one]
    let c1 : v.adicCompletionIntegers F := ⟨_, hval.le⟩
    let c2 : v.adicCompletionIntegers F := ⟨_, hval'.le⟩
    have h12 : c2 * c1 = 1 := Subtype.ext (inv_mul_cancel₀ hcv)
    have hu : IsUnit c2 := isUnit_iff_exists_inv.2 ⟨c1, h12⟩
    obtain ⟨a, b, hab⟩ : ∃ a b : v.adicCompletionIntegers F, qf tr nm a b = c2 := by
      rcases hor with h | ⟨q, hq, hqv, hqd, hr⟩
      · exact hU F v tr nm h c2 hu
      · obtain ⟨ρ, h1, h2⟩ := hR F v tr nm q hq hqv hqd hr
        exact hS _ tr nm ρ h1 h2 c2
    have hab' : qf tr nm (a : v.adicCompletion F) (b : v.adicCompletion F)
        = (algebraMap F (v.adicCompletion F) (c : F))⁻¹ := by
      have := congrArg (Subtype.val) hab
      simpa [qf] using this
    refine ⟨![a, b, 0, 0], ?_, fun _ _ i => ?_⟩
    · simp only [Matrix.cons_val]
      have h0 : qf tr nm (0 : v.adicCompletion F) 0 = 0 := by simp [qf]
      rw [hab', h0, add_zero, mul_inv_cancel₀ hcv]
    · fin_cases i
      · exact a.2
      · exact b.2
      · exact zero_mem _
      · exact zero_mem _
  · obtain ⟨a, b, a', b', h⟩ := hF F v tr nm hd _ (inv_ne_zero hcv)
    refine ⟨![a, b, a', b'], ?_, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
    simp only [Matrix.cons_val]
    rw [h, mul_inv_cancel₀ hcv]

theorem UpperTheory.Gal.G1.pAdFour :
    LocFour → LocUnit → LocRoot → SplitRep → AdFour := by
  intro hF hU hR hS F _ _ tr nm hd c hc
  choose f hf1 hf2 using exists_local hF hU hR hS F tr nm hd c hc
  have hD : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ≠ 0 := by
    have : (2 * (tr ^ 2 - 4 * nm) : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hd
    exact_mod_cast this
  have hI : Ideal.span {((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hD hc
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors hI).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hev : ∀ i, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, f v i ∈ v.adicCompletionIntegers F := by
    intro i
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    have h1 : c ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_left _ _ hm)
    have h2 : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_right _ _ hm)
    exact hv (hf2 v h1 (Or.inl h2) i)
  let A : Fin 4 → FiniteAdeleRing (𝓞 F) F := fun i => ⟨fun v => f v i, hev i⟩
  refine ⟨A, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have := hf1 v
    let φ : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
      { toFun := fun x => x v
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have key : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F) *
        (qf tr nm (A 0) (A 1) + qf tr nm (A 2) (A 3))) = φ 1 := by
      simp only [qf, map_mul, map_add (f := _), map_pow, map_intCast, map_one]
      have hA : ∀ i, φ (A i) = f v i := fun _ => rfl
      have hc' : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F)) =
          algebraMap F (v.adicCompletion F) (c : F) := rfl
      rw [hc']
      simp only [hA]
      simpa only [qf] using this
    exact key
  · intro v q hq hqv hqd hr hcv i
    exact hf2 v hcv (Or.inr ⟨q, hq, hqv, hqd, hr⟩) i
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBlockMat
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pBlockMat :
    BlockMat := by
  intro R _ σ hσ c x y hc h m
  let b : Matrix (Fin 2) (Fin 2) R := !![x, -σ y; y, σ x]
  let b' : Matrix (Fin 2) (Fin 2) R := !![c * σ x, c * σ y; -(c * y), c * x]
  let M : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b)
  let M' : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b')
  let e : Fin 1 ⊕ (Fin 2 × Fin m) ≃ Fin (2 * m + 1) :=
    ((Equiv.refl (Fin 1)).sumCongr finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  have hbd : (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) :
      Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) = 1 := by
    have h1 : (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) = 1 :=
      blockDiagonal_one
    rw [h1, fromBlocks_one]
  have hbb' : b * b' = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hb'b : b' * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hu : (b.map σ)ᵀ * diagonal (fun _ : Fin 2 => c) * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, Matrix.mul_apply, Fin.sum_univ_two, hσ] <;>
      first | linear_combination h | ring
  have hM : M * M' = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hbb', Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hM' : M' * M = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hb'b, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hD : (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e =
      Sum.elim (fun _ => 1) (fun _ => c) := by
    funext p
    rcases p with p | p
    · have hp : p = 0 := Subsingleton.elim _ _
      subst hp
      simp [e]
      intro hne
      exact (hne (Fin.ext (by simp))).elim
    · simp [e]
  have hd2 : (diagonal fun _ : Fin 2 × Fin m => c) =
      blockDiagonal fun _ : Fin m => diagonal fun _ : Fin 2 => c := by
    rw [blockDiagonal_diagonal]
  have hcore : (M.map σ)ᵀ *
      diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e) * M = 1 := by
    rw [hD, ← fromBlocks_diagonal]
    simp only [M, fromBlocks_map, fromBlocks_transpose, blockDiagonal_map _ _ (map_zero σ),
      blockDiagonal_transpose, hd2]
    simp only [fromBlocks_multiply, Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
    rw [← blockDiagonal_mul, ← blockDiagonal_mul]
    simp only [hu]
    simpa using hbd
  have hbS : ∀ (S : Subring R), x ∈ S → y ∈ S → σ x ∈ S → σ y ∈ S → c ∈ S →
      (∀ i j, b i j ∈ S) ∧ ∀ i j, b' i j ∈ S := by
    intro S hx hy hsx hsy hcS
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b] <;>
        first | assumption | exact S.neg_mem hsy
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b'] <;>
        first | exact S.neg_mem (S.mul_mem hcS hy) | exact S.mul_mem hcS hsx | exact S.mul_mem hcS hsy | exact S.mul_mem hcS hx | exact S.mul_mem hcS hy
  have hblk : ∀ (S : Subring R) (N : Matrix (Fin 2) (Fin 2) R), (∀ i j, N i j ∈ S) →
      ∀ p q, (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => N) :
        Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) p q ∈ S := by
    intro S N hN p q
    rcases p with p | ⟨i, k⟩ <;> rcases q with q | ⟨j, l⟩
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₂, blockDiagonal_apply]
      split_ifs
      · exact hN _ _
      · exact S.zero_mem
  refine ⟨⟨reindex e e M, reindex e e M', ?_, ?_⟩, ?_, ?_⟩
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM, submatrix_one_equiv]
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM', submatrix_one_equiv]
  · have hDD : diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) =
        (diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e)).submatrix
          e.symm e.symm := by
      rw [submatrix_diagonal_equiv]
      congr 1
      funext i
      simp
    show ((reindex e e M).map σ)ᵀ *
        diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) * reindex e e M = 1
    rw [hDD, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv, hcore, submatrix_one_equiv]
  · intro S hx hy hsx hsy hcS i j
    obtain ⟨h1, h2⟩ := hbS S hx hy hsx hsy hcS
    exact ⟨hblk S b h1 _ _, hblk S b' h2 _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCongrScale
section
noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem congr_core {n : ℕ} {B : Type*} [CommRing B] (σ : B →+* B)
    (Nb N'b Mb X X' : Matrix (Fin n) (Fin n) B) (τ τ' s z : B)
    (hz : IsUnit z) (hX : IsUnit X.det) (hX' : IsUnit X'.det)
    (hτ : τ' = s * τ * (z * σ z))
    (h : X * Nb * (X.map σ)ᵀ = τ • Mb)
    (h' : X' * N'b * (X'.map σ)ᵀ = τ' • Mb) :
    ∃ P : Matrix (Fin n) (Fin n) B, IsUnit P.det ∧ N'b = Pᵀ * (s • Nb) * P.map σ := by
  have hW : X'⁻¹ * X' = 1 := Matrix.nonsing_inv_mul _ hX'
  have hW' : (X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hW]
    simp
  have hWd : IsUnit (X'⁻¹).det := by
    have : (X'⁻¹).det * X'.det = 1 := by rw [← Matrix.det_mul, hW, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ this
  have hzX : (z • X).map σ = σ z • X.map σ := by
    ext i j
    simp
  refine ⟨(X'⁻¹ * (z • X))ᵀ, ?_, ?_⟩
  · rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_smul]
    exact hWd.mul ((hz.pow _).mul hX)
  · have hP : ((X'⁻¹ * (z • X))ᵀ).map σ = σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
      have e : (X'⁻¹ * (z • X)).map σ = (X'⁻¹).map σ * (σ z • X.map σ) := by
        rw [Matrix.map_mul, hzX]
      rw [Matrix.transpose_map, e, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul]
    rw [Matrix.transpose_transpose, hP]
    calc N'b = X'⁻¹ * X' * N'b * ((X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
          rw [hW, hW', Matrix.one_mul, Matrix.mul_one]
      _ = X'⁻¹ * (X' * N'b * (X'.map σ)ᵀ) * ((X'⁻¹).map σ)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = X'⁻¹ * ((s * (z * σ z)) • (X * Nb * (X.map σ)ᵀ)) * ((X'⁻¹).map σ)ᵀ := by
          rw [h', h, hτ, smul_smul]
          congr 3
          ring
      _ = X'⁻¹ * (z • X) * (s • Nb) * (σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
          congr 1
          ring

theorem pCongrScale : CongrScale := by
  intro E _ _ _ n M N N' K _ _ θ D hθ hD t t' a b s ht' ht X X' hX hX' h h'
  let F := maximalRealSubfield E
  let B := K ⊗[F] E
  let σ := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  let cB : K →+* B := algebraMap K B
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hmul : ∀ x y : E, inE K (x * y) = inE K x * inE K y := fun x y => by
    simp [inE, Algebra.TensorProduct.tmul_mul_tmul]
  have hrat : ∀ q : ℚ, inE K (q : E) = cB (q : K) := fun q => by
    have e : ((Algebra.TensorProduct.includeRight : E →ₐ[F] B) : E →+* B).comp (Rat.castHom E) =
        cB.comp (Rat.castHom K) := RingHom.ext_rat _ _
    exact congrArg (fun f : ℚ →+* B => f q) e
  have hint : inE K (D : E) = cB (D : K) := by
    have := hrat (D : ℚ)
    simpa using this
  set z : B := cB a + cB b * inE K θ with hzdef
  have hσθ : σ (inE K θ) = -inE K θ := by
    show (1 : K) ⊗ₜ[F] (IsCMField.complexConj E θ) = _
    rw [hθ, TensorProduct.tmul_neg]
  have hσc : ∀ x : K, σ (cB x) = cB x := fun x => σ.commutes x
  have hσz : σ z = cB a - cB b * inE K θ := by
    rw [hzdef, map_add (f := _), map_mul, hσc, hσc, hσθ]
    ring
  have hθθ : inE K θ * inE K θ = cB (D : K) := by
    rw [← hmul, ← pow_two, hD, hint]
  have hnorm : z * σ z = cB (a ^ 2 - D * b ^ 2) := by
    rw [hσz, hzdef, map_sub, map_mul, map_pow, map_pow]
    linear_combination (-(cB b) ^ 2) * hθθ
  have hu : (a ^ 2 - D * b ^ 2) ≠ 0 := fun h0 => ht' (by rw [ht, h0, mul_zero])
  have hzu : IsUnit z := by
    have : IsUnit (z * σ z) := by
      rw [hnorm]
      exact (IsUnit.mk0 _ hu).map cB
    exact isUnit_of_mul_isUnit_left this
  have hsm : ∀ (c : K) (A : Matrix (Fin n) (Fin n) B), c • A = cB c • A := fun c A => by
    ext i j
    simp [Algebra.smul_def, cB]
  obtain ⟨P, hP, hE⟩ := congr_core (σ : B →+* B) (N.map (inE K)) (N'.map (inE K)) (M.map (inE K)) X X'
    (cB t) (cB t') (inE K (s : E)) z hzu hX hX' (by
      have hn2 : z * (σ : B →+* B) z = cB (a ^ 2 - D * b ^ 2) := hnorm
      rw [hn2, hrat, ht, map_mul, map_mul])
    (by rw [← hsm]; exact h) (by rw [← hsm]; exact h')
  refine ⟨P, hP, ?_⟩
  have hN : ((s : E) • N).map (fun x => (1 : K) ⊗ₜ[F] x) = inE K (s : E) • N.map (inE K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact hmul _ _
  rw [hN]
  exact hE

end UpperTheory.Gal.G1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDefSign
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem re_dot_swap {n : ℕ} (y x : Fin n → ℂ) : (star y ⬝ᵥ x).re = (star x ⬝ᵥ y).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem def_of_inv {n : ℕ} (M Mi : Matrix (Fin n) (Fin n) ℂ) (h1 : Mi * M = 1) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (Mi *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M *ᵥ x)).re := by
  have hy : M *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    have := congrArg (fun v => Mi *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, h1] using this
  have := h _ hy
  rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, re_dot_swap] at this

private theorem def_conj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (M *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x)).re := by
  have hy : star x ≠ 0 := by
    intro h0
    apply hx
    simpa using congrArg star h0
  have key : star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x) =
      starRingEnd ℂ (star (star x) ⬝ᵥ (M *ᵥ star x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, Matrix.mulVec, map_sum, map_mul]
  rw [key, Complex.conj_re]
  exact h _ hy

private theorem inv_map_ring {n : ℕ} {R R' : Type*} [Field R] [Field R'] (f : R →+* R') (A : Matrix (Fin n) (Fin n) R)
    (hA : A.det ≠ 0) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
    Matrix.map_one _ (map_zero f) (map_one f)]

private theorem herm_N {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (H β : Matrix (Fin n) (Fin n) E)
    (hH : H.map (cj E) = H) (hT : Hᵀ = H) (hd : H.det ≠ 0) (hs : H⁻¹ * (β.map (cj E))ᵀ * H = β) (a b : Fin n) :
    IsCMField.complexConj E ((β * H⁻¹) a b) = (β * H⁻¹) b a := by
  have hHi : (H⁻¹).map (cj E) = H⁻¹ := by rw [inv_map_ring _ _ hd, hH]
  have hHiT : (H⁻¹)ᵀ = H⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
  have key : ((β * H⁻¹).map (cj E))ᵀ = β * H⁻¹ := by
    rw [Matrix.map_mul, hHi, Matrix.transpose_mul, hHiT]
    conv_rhs => rw [← hs]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), Matrix.mul_one]
  have := congrFun (congrFun key b) a
  rw [Matrix.transpose_apply, Matrix.map_apply] at this
  exact this

theorem UpperTheory.Gal.G1.pDefSign :
    DefSign := by
  classical
  intro E _ _ _ A n p _ S B
  have hT : (A.H n)ᵀ = A.H n := Matrix.diagonal_transpose _
  have hH' : (A.H n).map (cj E) = A.H n := by
    have h := congrArg Matrix.transpose (A.herm n)
    rw [Matrix.transpose_transpose] at h
    rw [h]
    exact hT
  have hsym : (A.H n)⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * A.H n = mat S ↑B.β := by
    have h := B.sym
    change MulOpposite.unop (hermStar (A.H n) (A.det_ne n) (mat S ↑B.β)) = mat S ↑B.β at h
    rw [hermStar_apply] at h
    change ((A.H n).map (cj E))⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * (A.H n).map (cj E) = _ at h
    rwa [hH'] at h
  refine ⟨herm_N _ _ hH' hT (A.det_ne n) hsym, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · have hu : IsUnit (mat S ↑B.β) := B.β.isUnit
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero (A.det_ne n)
  · intro τ x hx
    set v := InfinitePlace.mk τ with hvdef
    set ε : ℝ := if v = InfinitePlace.mk A.τ₀ then 1 else -1 with hεdef
    have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < ε *
        (star y ⬝ᵥ ((((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *ᵥ y)).re := by
      intro y hy
      have hp := B.posR v y hy
      have hsig : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding := rfl
      rw [hsig] at hp
      have hme : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
      by_cases hv : v = InfinitePlace.mk A.τ₀
      · have h1 := ((S.sig v.embedding).1 (by rw [hme]; exact hv)).1
        rw [hεdef, if_pos hv, one_mul]
        exact hp.1 h1
      · have h0 := ((S.sig v.embedding).2 (by rw [hme]; exact hv)).1
        rw [hεdef, if_neg hv, neg_one_mul, neg_pos]
        exact hp.2 (by rw [h0]; exact zero_ne_one)
    have h1 : (((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *
        (mat S ↑B.β * (A.H n)⁻¹).map v.embedding = 1 := by
      have hb : mat S ↑(B.β⁻¹) * mat S ↑B.β = 1 := B.β.inv_mul
      have h2 : A.H n * mat S ↑(B.β⁻¹) * (mat S ↑B.β * (A.H n)⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (mat S ↑(B.β⁻¹)), hb, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (A.det_ne n))]
      rw [← Matrix.transpose_map, hT, ← Matrix.map_mul, ← Matrix.map_mul, h2,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hM := def_of_inv _ _ h1 ε hpos
    rcases InfinitePlace.embedding_mk_eq τ with he | he
    · have he' : v.embedding = τ := he
      rw [he'] at hM
      exact hM x hx
    · have he' : v.embedding = ComplexEmbedding.conjugate τ := he
      rw [he'] at hM
      have hc := def_conj _ ε hM x hx
      have hcc : ((mat S ↑B.β * (A.H n)⁻¹).map (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ) =
          (mat S ↑B.β * (A.H n)⁻¹).map τ := by
        ext i j
        simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [hcc] at hc
end

