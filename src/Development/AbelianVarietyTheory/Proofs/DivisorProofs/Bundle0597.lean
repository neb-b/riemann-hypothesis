module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabLeBlockTri
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.LatValRam

section Sz

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (hx : Sz l lam r x) (h : r ≤ r') : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem norm_nat_le (n : ℕ) : ‖(n : ℂ_[l])‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

theorem sz_nat (n : ℕ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨natCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), natCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := rfl
  rw [this, map_natCast, Real.rpow_zero]
  exact norm_nat_le n

theorem sz_one : Sz l lam 0 1 := by simpa using sz_nat (l := l) (lam := lam) 1

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_neg_one_pow_mul {r : ℝ} {x : ℂ} (n : ℕ) (hx : Sz l lam r x) : Sz l lam r ((-1) ^ n * x) := by
  rcases neg_one_pow_eq_or ℂ n with h | h
  · rwa [h, one_mul]
  · rw [h, neg_one_mul]; exact sz_neg hx

theorem sz_pow {r : ℝ} {x : ℂ} (hx : Sz l lam r x) (n : ℕ) : Sz l lam (n * r) (x ^ n) := by
  induction n with
  | zero => simpa using sz_one (l := l) (lam := lam)
  | succ n ih =>
    have := sz_mul ih hx
    rw [pow_succ]
    convert this using 1
    push_cast; ring

theorem sz_prod {ι : Type} (s : Finset ι) (r : ι → ℝ) (x : ι → ℂ) (h : ∀ i ∈ s, Sz l lam (r i) (x i)) :
    Sz l lam (∑ i ∈ s, r i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sz_one (l := l) (lam := lam)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact sz_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Sz

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem per_factor (a b Ω r π : ℂ) (k n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hΩ : Ω ≠ 0) (hr : r ≠ 0) (hpi : π ≠ 0)
    (f : ℂ) (hf : f ≠ 0) :
    (b / a) ^ n / (a ^ k * f) * (f * ((a * b * r / (2 * π))⁻¹) ^ n * (a / Ω) ^ (k + 2 * n)) =
      (2 * π / r) ^ n / Ω ^ (k + 2 * n) := by
  simp only [inv_div, div_pow, pow_add, pow_mul, mul_pow]
  have h1 : a ^ n ≠ 0 := pow_ne_zero _ ha
  have h2 : b ^ n ≠ 0 := pow_ne_zero _ hb
  have h3 : r ^ n ≠ 0 := pow_ne_zero _ hr
  have h4 : Ω ^ k ≠ 0 := pow_ne_zero _ hΩ
  have h5 : (Ω ^ 2) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hΩ)
  have h6 : a ^ k ≠ 0 := pow_ne_zero _ ha
  field_simp
  ring

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl


open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (ValGe_vp betaBound_vp c_vp cE_vp a0 n_vp) in
theorem latIntRam : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  intro hSt hEx E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc κ S hS
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  rw [GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding]
  intro lam
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  have hΩ0 : Ω ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ (by rw [← hΩ]; simp)
  obtain ⟨a, b, hab, hT⟩ := hEx E I d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc lam Ω hΩ
  have hCM : IsCMType φ := hF.2.2.2.2.2.2.1
  have hcard := card_eq_finrank hCM
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := hcard ▸ hF.2.2.2.2.2.1
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  have hTg := hT g κ u hg hu
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hF.1.pos)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hper : ∀ i, (b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ)) *
      (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
        (a i / Ω) ^ (2 * s + 2 * κ i)) =
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) := by
    intro i
    exact per_factor _ _ _ _ _ _ _ (hab i).1 (hab i).2.1 hΩ0 hsd hpi _ (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hX : ((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ =
      (-1) ^ (∑ i, κ i) * ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 *
        ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))))) *
        ∏ i, (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
          (a i / Ω) ^ (2 * s + 2 * κ i)) := by
    have hQF := Finset.prod_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => hper i)
    have hR : ∏ i, (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) =
        (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) / Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i) := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]
    have hM : Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ = Fintype.card I • (2 * s) + 2 * ∑ i, κ i := by
      simp [Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK, mul_comm]
    have hsq : ((-1 : ℂ) ^ (∑ i, κ i)) * (-1) ^ (∑ i, κ i) = 1 := by
      rw [← mul_pow]; norm_num
    rw [hDg, risingFactor_eq, cmPeriodConstant_eq_of_card_cmType hcard d s hs κ, hM]
    calc _ = ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          ((2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) /
            Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i)) := by
            push_cast; ring
      _ = _ := by
        rw [← hR, ← hQF, Finset.prod_mul_distrib]
        linear_combination (-(((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          (∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ)))) *
          (∏ i, (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
              (a i / Ω) ^ (2 * s + 2 * κ i))))) * hsq
  have hSzX : Sz l lam (betaBound_vp d s κ 𝔣 z l / 12)
      (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) := by
    rw [hX, mul_assoc]
    refine sz_neg_one_pow_mul _ (sz_mono (sz_mul hTg (sz_prod Finset.univ
      (fun i => (0 + ((κ i : ℕ) : ℝ) * (c_vp 𝔣 l + if l = d then 1 / 2 else 0)) +
        ((2 * s + 2 * κ i : ℕ) : ℝ) * (a0 𝔣 l : ℝ)) _
      (fun i _ => sz_mul (sz_mul (sz_nat _) (sz_pow (hab i).2.2.2 _)) (sz_pow (hab i).2.2.1 _)))) (le_of_eq ?_))
    simp only [betaBound_vp, n_vp, if_neg hc, Formalism.PairingDivisionLocalBalance.nl, Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK]
    push_cast
    simp only [zero_add, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have hβ : beta E d s κ Λ (S 0) = (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
    rw [beta, div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm 12]
  rw [hβ]
  convert sz_pow hSzX 12 using 1
  push_cast
  ring

end GlobalTheory.LatValRam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTensorBlockExt
section
noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def extMat (b : Fin r → Fin s) (c : Fin s) :
    Matrix {i // b i = c} {i // b i = c} K →* Matrix (Fin r) (Fin r) K where
  toFun g := Matrix.reindex (Equiv.sumCompl fun a => b a = c) (Equiv.sumCompl fun a => b a = c)
    (Matrix.fromBlocks g 0 0 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem extMat_in (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K)
    (i j : {i // b i = c}) : extMat b c g i.1 j.1 = g i j := by
  simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) i.2,
    Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) j.2]

theorem extMat_out (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) : extMat b c g i j = (1 : Matrix (Fin r) (Fin r) K) i j := by
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · exact absurd ⟨hi, hj⟩ h
  · have : i ≠ j := fun e => hj (e ▸ hi)
    simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, this]
  · have : i ≠ j := fun e => hi (e ▸ hj)
    simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hj, this]
  · simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, Matrix.one_apply]

def blockExt (b : Fin r → Fin s) (c : Fin s) :
    GL {i // b i = c} K →* blockTri (κ := K) (natBlocks b) :=
  (Units.map (extMat b c)).codRestrict (blockTri (κ := K) (natBlocks b)) fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show extMat b c _ i j = 0
    have hne : b i ≠ b j := fun e => by
      simp only [natBlocks, e] at hij
      exact lt_irrefl _ hij
    rw [extMat_out b c _ i j (fun e => hne (e.1.trans e.2.symm)),
      Matrix.one_apply_ne (fun e => hne (congrArg b e))]

theorem blockExt_in (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : {i // b i = c}) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i.1 j.1 =
      (g : Matrix _ _ K) i j :=
  extMat_in b c _ i j

theorem blockExt_out (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j =
      (1 : Matrix (Fin r) (Fin r) K) i j :=
  extMat_out b c _ i j h

theorem levi_blockExt_same (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) :
    levi K b c (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = g := by
  apply Units.ext
  ext x y
  exact blockExt_in b c g x y

theorem levi_blockExt_ne (b : Fin r → Fin s) {c c' : Fin s} (h : c' ≠ c) (g : GL {i // b i = c} K) :
    levi K b c' (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = 1 := by
  apply Units.ext
  ext x y
  have := blockExt_out b c g x.1 y.1 (fun e => h (x.2.symm.trans e.1))
  show (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 =
    (1 : Matrix _ _ K) x y
  rw [this]
  simp [Matrix.one_apply, Subtype.ext_iff]

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem leviTensor_blockExt (c : Fin s) (g : GL {i // b i = c} K) :
    leviTensor b lam (blockExt b c g) = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ g)) := by
  rw [leviTensor_apply]
  congr 1
  funext c'
  by_cases h : c' = c
  · subst h
    rw [levi_blockExt_same, Function.update_self]
  · rw [levi_blockExt_ne b h, Function.update_of_ne h, map_one]
    rfl

end GlobalTheory.HcIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransfer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullIsoCongr

theorem lbIso_pull_congr (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X) (h₁ : Q₁.IsLB) (h₂ : Q₂.IsLB)
    (e : LBIso Q₁ Q₂) (f : LBIso (Q₁.pull m) (Q₁.pull m')) : LBIso (Q₂.pull m) (Q₂.pull m') := by
  have a : LBIso (Q₂.pull m) (Q₁.pull m) :=
    LBIso.chartPull (chartPullPull Q₂ m m rfl) (chartPullPull Q₁ m m rfl) (LBIso.symm e)
  have b : LBIso (Q₁.pull m') (Q₂.pull m') :=
    LBIso.chartPull (chartPullPull Q₁ m' m' rfl) (chartPullPull Q₂ m' m' rfl) e
  exact LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m') (pull_isLB h₂ m')
    (LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m) (pull_isLB h₁ m') a f) b

theorem isocongr : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') :=
  fun X Y Q₁ Q₂ m m' h₁ h₂ e f => lbIso_pull_congr X Y Q₁ Q₂ m m' h₁ h₂ e f

end GlobalTheory.PullIsoCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapAlgebraMapPowerSeriesEvalTwoGroups
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem map_algebraMap_powerSeriesEvalTwoGroups : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := by
  intro R S _ _ _ d τ t u v hu hv
  have ha : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun i => by cases i <;> simp [hu, hv])
  rw [at2, at2, map_subst ha]
  congr 1
  funext i
  cases i <;> rfl

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

end GlobalTheory.SmallSecond

namespace GlobalTheory.SmallSecond

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {θ : B →+* O} {Θ : Q →+* C}

theorem map_up {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) :
    (fun i => map Θ (up Q μ' i)) = up C (fun i => map θ (μ' i)) := by
  funext i; ext α; simp [up, coeff_map, hΘ]

theorem map_formalGroupLawCoboundaryOne_square {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ') f) = cob1 (up C (fun i => map θ (μ' i))) (map Θ f) := by
  rw [map_formalGroupLawCoboundaryOne_eq Θ _ (fun i => by simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
    coeff_zero_eq_constantCoeff_apply, hμ]), map_up hΘ]

theorem map_comb {σ ι : Type} [Fintype ι] (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul, hΘ]

theorem ql_map {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL (fun i => map θ (μ' i)) ⊤ (map Θ f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  · obtain ⟨b, -, hb⟩ := h1 i
    exact ⟨θ b, trivial, by simp only [lin, coeff_map] at hb ⊢; rw [hb, hΘ]⟩
  · rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
    intro α
    obtain ⟨b, -, hb⟩ := h2 α
    exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) :
    cob1 (up C (fun i => map θ (μ' i))) (map Θ f) = 0 := by
  rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
  ext α
  obtain ⟨b, hb0, hb⟩ := hf α
  rw [coeff_map, hb, hΘ, RingHom.mem_ker.1 hb0, map_zero, map_zero]

end GlobalTheory.SmallSecond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionOnGroupSchemeIntCombinationEqProdZpow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActSum

theorem act_sum_zsmul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  intro S A _ _ O _ act h r e c
  let f : Multiplicative O →* (A ⟶ A) := MonoidHom.mk' (fun a => act (Multiplicative.toAdd a)) (fun a b => h.2.2.2 _ _)
  have key : ∀ x : O, act x = f (Multiplicative.ofAdd x) := fun x => rfl
  rw [key, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

end GlobalTheory.ActSum
end

