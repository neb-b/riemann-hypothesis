module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraic
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_mul_mem_algebraicClosure {f g : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ)
    (hg : ∀ n, PowerSeries.coeff n g ∈ algebraicClosure ℚ ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) ∈ algebraicClosure ℚ ℂ := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ ↦ mul_mem (hf _) (hg _)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_pow_mem_algebraicClosure {f : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ) (e : ℕ) :
    ∀ n, PowerSeries.coeff n (f ^ e) ∈ algebraicClosure ℚ ℂ := by
  induction e with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ e ih =>
    rw [pow_succ]
    exact coeff_mul_mem_algebraicClosure ih hf

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_exp_two_pi_I_mul_rat (q : ℚ) :
    IsAlgebraic ℚ (Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ))) := by
  refine (IsIntegral.of_pow q.den_pos ?_).isAlgebraic
  have h : Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ)) ^ q.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hq : (q : ℂ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have hmul : (q.den : ℂ) * (2 * ↑Real.pi * Complex.I * (q : ℂ)) =
        (q.num : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      linear_combination (2 * ↑Real.pi * Complex.I) * hq
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  rw [h]
  exact isIntegral_one

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_realEmbedding_apply {F : Type} [Field F] [NumberField F]
    (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F) : IsAlgebraic ℚ ((i y : ℝ) : ℂ) :=
  (Algebra.IsAlgebraic.isAlgebraic y).algHom (Complex.ofRealHom.comp i).toRatAlgHom

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma ecoef_mem_algebraicClosure_of_isCoef {F : Type} [Field F] [NumberField F] {k : ℕ}
    {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a) (ha₀ : IsAlgebraic ℚ a₀) (N : ℕ)
    (x : F) (μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (n : ℕ) :
    _root_.GlobalTheory.HilbFam.ecoef N a x μ n ∈ algebraicClosure ℚ ℂ := by
  unfold _root_.GlobalTheory.HilbFam.ecoef
  refine finsum_mem_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun ξ _ ↦ ?_
  refine mul_mem (mul_mem ?_ ?_) (prod_mem fun i _ ↦ pow_mem ?_ _)
  · rw [mem_algebraicClosure_iff]
    by_cases hξ : ξ = 0
    · rw [hξ, ha.1]
      exact ha₀
    · obtain ⟨m, hm⟩ := ha.2.1 ξ hξ
      rw [hm]
      exact isAlgebraic_int _
  · rw [mem_algebraicClosure_iff]
    unfold _root_.GlobalTheory.HilbFam.eTr
    exact isAlgebraic_exp_two_pi_I_mul_rat _
  · rw [mem_algebraicClosure_iff]
    exact isAlgebraic_realEmbedding_apply i ξ


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hser_coeff_isAlgebraic : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N κ c n hk ha ha₀ hc
  rw [← mem_algebraicClosure_iff]
  unfold _root_.GlobalTheory.HilbFam.hser
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul]
  refine mul_mem ?_ (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _) ?_)
  · rw [hk, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
    exact SubfieldClass.ratCast_mem _ _
  · refine coeff_mul_mem_algebraicClosure
      (coeff_pow_mem_algebraicClosure (fun m ↦ ?_) _) (fun m ↦ ?_) n
    · rw [PowerSeries.coeff_mk, mem_algebraicClosure_iff]
      exact hc m
    · rw [PowerSeries.coeff_mk]
      exact ecoef_mem_algebraicClosure_of_isCoef ha ha₀ N x μ m

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinCoeffSupportTraceFinite
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma le_one_and_mem_latM_of_hasLevel {F : Type} [Field F] [NumberField F] {N : ℕ}
    {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {x : F}
    (h : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) :
    ((B : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) ∧ (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A ∧
      (N : F) * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A := by
  obtain ⟨h1, h2⟩ := h
  have mem : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.split A B x ↔
      v 0 ∈ (B : FractionalIdeal (𝓞 F)⁰ F) ∧ v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A :=
    fun v ↦ Iff.rfl
  have std : ∀ v : Fin 2 → F, v ∈ _root_.GlobalTheory.HilbFam.stdLat F ↔
      ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := by
    intro v; simp [_root_.GlobalTheory.HilbFam.stdLat, Submodule.mem_pi]
  have one_mem : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have zero_mem' : (0 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.zero_mem _
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    have hv : ![b, b * x] ∈ _root_.GlobalTheory.HilbFam.split A B x :=
      (mem _).2 ⟨by simpa using hb, by
        simpa using FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)⟩
    have := ((std _).1 (h2 hv)) 0
    simp only [Matrix.cons_val_zero] at this
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨y, hy⟩
  · have hv := h1 ![0, 1] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := ((mem _).1 hv).2
    simpa [Algebra.smul_def] using this
  · have hv := h1 ![1, 0] ((std _).2 (by intro i; fin_cases i <;> simpa))
    have := FractionalIdeal.mem_coe.1
      (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 ((mem _).1 hv).2))
    simpa [Algebra.smul_def] using this

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma mem_and_totally_pos_of_coeff_ne_zero {F : Type} [Field F] [NumberField F]
    {k N : ℕ} {A B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k A B a₀ a)
    (hN : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split A B x)) {ξ : F}
    (hξ0 : ξ ≠ 0) (hξ : a ξ ≠ 0) :
    ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := by
  obtain ⟨-, -, hsupp, -⟩ := ha
  obtain ⟨hmem, hpos⟩ := hsupp ξ hξ0 hξ
  refine ⟨?_, hpos⟩
  have hB := (le_one_and_mem_latM_of_hasLevel hN).1
  have hle : ((A * B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : FractionalIdeal (𝓞 F)⁰ F) ≤ A := by
    rw [Units.val_mul]
    calc (A : FractionalIdeal (𝓞 F)⁰ F) * B ≤ A * 1 := by gcongr
      _ = A := mul_one _
  exact hle hmem

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma sum_realEmbeddings_eq_trace {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] (y : F) :
    ∑ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i y = ((Algebra.trace ℚ F y : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  exact _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace F y

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma trace_mul_int_of_mem_latM {F : Type} [Field F] [NumberField F]
    {A : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {y ξ : F} (hy : y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM A)
    (hξ : ξ ∈ (A : FractionalIdeal (𝓞 F)⁰ F)) : ∃ c : ℤ, Algebra.trace ℚ F (y * ξ) = c := by
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual A.ne_zero] at hy
  obtain ⟨c, hc⟩ := hy ξ hξ
  exact ⟨c, by simpa [Algebra.traceForm_apply] using hc.symm⟩

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_support_trace_natCast_and_finite {F : Type} [Field F] [NumberField F]
    [IsTotallyReal F] {k : ℕ} {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ} {x : F}
    {N : ℕ} (hN : 0 < N) (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a)
    (hlev : _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x)) :
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite := by
  have hNF : (N : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 := (le_one_and_mem_latM_of_hasLevel hlev).2.1
  have hpos : ∀ ξ, a ξ ≠ 0 → ξ ≠ 0 → ξ ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ := fun ξ hξ hξ0 ↦
    mem_and_totally_pos_of_coeff_ne_zero ha hlev hξ0 hξ

  have hbound : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, i ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
    intro ξ hξ i
    rw [← sum_realEmbeddings_eq_trace]
    exact Finset.single_le_sum (fun j _ ↦ (hξ j).le) (Finset.mem_univ i)
  have htr_nonneg : ∀ ξ : F, (∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, 0 < i ξ) →
      0 ≤ Algebra.trace ℚ F ξ := by
    intro ξ hξ
    have : (0 : ℝ) ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) := by
      rw [← sum_realEmbeddings_eq_trace]
      exact Finset.sum_nonneg fun j _ ↦ (hξ j).le
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    by_cases hξ0 : ξ = 0
    · exact ⟨0, by simp [hξ0]⟩
    obtain ⟨hmem, hξpos⟩ := hpos ξ hξ hξ0
    obtain ⟨c, hc⟩ := trace_mul_int_of_mem_latM hNF hmem
    have hc' : (N : ℚ) * Algebra.trace ℚ F ξ = c := by
      rw [← hc, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
    have hc0 : 0 ≤ c := by
      have : (0 : ℚ) ≤ c := hc' ▸ mul_nonneg (Nat.cast_nonneg _) (htr_nonneg ξ hξpos)
      exact_mod_cast this
    exact ⟨c.toNat, by rw [hc']; exact_mod_cast (Int.toNat_of_nonneg hc0).symm⟩
  · intro n
    obtain ⟨d, hd0, hd⟩ := (𝔞 : FractionalIdeal (𝓞 F)⁰ F).isFractional
    set D : F := algebraMap (𝓞 F) F d with hD
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0
    set M : ℝ := (∑ φ : F →+* ℂ, ‖φ D‖) * ((n : ℝ) / N) with hM
    have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ M
    refine (hfin.image fun z ↦ z / D).subset ?_
    rintro ξ ⟨hξ, htr⟩
    refine ⟨D * ξ, ⟨?_, ?_⟩, by field_simp⟩
    · by_cases hξ0 : ξ = 0
      · simpa [hξ0] using isIntegral_zero
      obtain ⟨r, hr⟩ := hd ξ (hpos ξ hξ hξ0).1
      have hDξ : D * ξ = algebraMap (𝓞 F) F r := by rw [hr, Algebra.smul_def]
      rw [hDξ]
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro φ
      have hMnn : 0 ≤ M := by rw [hM]; positivity
      rw [map_mul, norm_mul]
      by_cases hξ0 : ξ = 0
      · simpa [hξ0] using hMnn
      have hξpos := (hpos ξ hξ hξ0).2
      have hφ := IsTotallyReal.complexEmbedding_isReal φ
      have htrq : Algebra.trace ℚ F ξ = n / N := by
        rw [eq_div_iff (by exact_mod_cast hN.ne')]
        rw [mul_comm]; exact htr
      have hφξ : ‖φ ξ‖ ≤ (n : ℝ) / N := by
        rw [← ComplexEmbedding.IsReal.coe_embedding_apply hφ, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hξpos _)]
        calc ComplexEmbedding.IsReal.embedding hφ ξ ≤ ((Algebra.trace ℚ F ξ : ℚ) : ℝ) :=
              hbound ξ hξpos _
          _ = (n : ℝ) / N := by rw [htrq]; push_cast; ring
      have hφD : ‖φ D‖ ≤ ∑ ψ : F →+* ℂ, ‖ψ D‖ :=
        Finset.single_le_sum (fun ψ _ ↦ norm_nonneg (ψ D)) (Finset.mem_univ φ)
      rw [hM]
      exact mul_le_mul hφD hφξ (norm_nonneg _) (Finset.sum_nonneg fun ψ _ ↦ norm_nonneg _)


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.coef_support_trace : ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F)
    (N : ℕ), 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a →
    _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) →
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite :=
  fun _ _ _ _ _ _ _ _ _ _ _ hN ha hlev ↦ coeff_support_trace_natCast_and_finite hN ha hlev

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierCoeffRingEquivConj
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem ecoef_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (Emb F)) (μ : Emb F → ℕ) (n : ℕ), 0 < N → IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → HasLevel N (split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (ecoef N a x μ n) = ecoef N a (m * x) (fun j ↦ μ (π.symm j)) n := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x N g m π μ n hN hco hg0 hlev hζ hemb
  obtain ⟨h0, hint, hsupp, -⟩ := hco
  have hmap : ∀ {ι : Sort _} (f : ι → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hmapP : ∀ {p : Prop} (f : p → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'

  have hprod : ∀ ξ : F, g (∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) = ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    rw [map_prod]
    simp only [map_pow, hemb]
    exact Equiv.prod_comp π (fun j ↦ ((j ξ : ℝ) : ℂ) ^ μ (π.symm j)) |>.symm ▸ by
      simp only [Equiv.symm_apply_apply]

  have hchar : ∀ ξ : F, ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → g (eTr (ξ * x)) = eTr (ξ * ((m : F) * x)) := by
    intro ξ hξ
    obtain ⟨r, hr⟩ := (_root_.GlobalTheory.HilbFam.trace_denominator_of_hasLevel F N 𝔞 𝔟 x ξ hlev hξ).2
    have ht : Algebra.trace ℚ F (ξ * x) = (r : ℚ) / N := by
      rw [eq_div_iff hNq, mul_comm]; exact hr
    have hsm : ξ * ((m : F) * x) = (m : ℚ) • (ξ * x) := by
      rw [Algebra.smul_def, map_intCast]; ring
    have ht' : Algebra.trace ℚ F (ξ * ((m : F) * x)) = (m : ℚ) * ((r : ℚ) / N) := by
      rw [hsm, LinearMap.map_smul, smul_eq_mul, ht]
    have e1 : eTr (ξ * x) = Complex.exp ((2 * Real.pi * Complex.I) / N) ^ r := by
      rw [eTr, ht, ← Complex.exp_int_mul]; congr 1; push_cast; ring
    rw [e1, map_zpow₀, hζ, ← Complex.exp_int_mul, eTr, ht']
    congr 1; push_cast; ring
  have key : ∀ ξ : F, g (a ξ * eTr (ξ * x) * ∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) =
      a ξ * eTr (ξ * ((m : F) * x)) * ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    by_cases ha : a ξ = 0
    · simp [ha]
    have hga : g (a ξ) = a ξ := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; rw [h0]; exact hg0
      · obtain ⟨z, hz⟩ := hint ξ hξ0; rw [hz, map_intCast]
    have hmem : ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; exact Submodule.zero_mem _
      · exact (hsupp ξ hξ0 ha).1
    rw [map_mul, map_mul, hga, hchar ξ hmem, hprod]
  unfold ecoef
  rw [hmap]
  refine finsum_congr fun ξ ↦ ?_
  rw [hmapP]
  refine finsum_congr fun _ ↦ ?_
  exact key ξ

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueLinearTransfer
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.HilbFam.transf_units_smul (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (ε : (𝓞 F)ˣ) (x : Fin 2 → F) :
    T (ε • x) = ε • T x := by
  change T.toLinearMap ((ε : 𝓞 F) • x) = (ε : 𝓞 F) • T.toLinearMap x
  exact LinearMap.map_smul_of_tower T.toLinearMap _ _

noncomputable def transfQuot (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) :
    Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) ≃ Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F)) :=
  Quotient.congr T.toEquiv (by
    intro x y
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨ε, rfl⟩
      exact ⟨ε, (transf_units_smul T ε y).symm⟩
    · rintro ⟨ε, h⟩
      refine ⟨ε, T.injective ?_⟩
      rw [transf_units_smul]
      exact h)

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfTraceIntegralUnramified
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
open scoped nonZeroDivisors

namespace GlobalTheory.LieDisc

theorem isIntegral_of_trace_integral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E,
      (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  intro E _ _ _ hu w hw
  set F := maximalRealSubfield E
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hu
    infer_instance
  have hd : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [hd, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  have hmem : w ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have ht := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (w * algebraMap (𝓞 E) E b)
    have hi : IsIntegral ℤ (Algebra.trace F E (w * algebraMap (𝓞 E) E b)) := by
      rw [← isIntegral_algebraMap_iff (B := E), ht]
      exact hw _ (RingOfIntegers.isIntegral_coe b)
    exact ⟨⟨_, hi⟩, rfl⟩
  rw [hdual] at hmem
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

end GlobalTheory.LieDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem isAffineOpen_preimage_and_finite_app_of_isFinite_restrict :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) →
      IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  intro X Z φ V hV hf
  haveI : IsAffine (V : Scheme) := hV
  have h1 : IsAffine (φ ⁻¹ᵁ V : Scheme) := isAffine_of_isAffineHom (φ ∣_ V)
  refine ⟨h1, ?_⟩
  have h2 := hf.finite_app ⊤ (isAffineOpen_top _)
  rw [morphismRestrict_app] at h2
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [← e]
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).mp h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.isKum_kumT
  | exact GlobalTheory.EtC.KummerSplit.isKum_kumT
  | (intros; apply GlobalTheory.EtC.KummerSplit.isKum_kumT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBoundStatement
section
open NumberField IsDedekindDomain GlobalTheory.SUVol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  first | exact @GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | exact GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | (intros; apply GlobalTheory.SUVol.prod_le_locFactor_of_isPrime <;> assumption)
end

