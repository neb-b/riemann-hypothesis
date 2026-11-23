module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormDetInnerLeOfDetEqOne
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PlueckerBound

theorem norm_det_inner_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u w : Fin b → E) :
    ‖(Matrix.of fun a a' => ⟪u a, w a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖w a‖ := by
  have h := GlobalTheory.Hadamard.norm_det_apply_le (𝕜 := ℂ) (fun a => innerSL ℂ (u a)) w
  simp only [innerSL_apply_apply, innerSL_apply_norm] at h
  rw [mul_comm]
  exact h

theorem det_inner_sum_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u v : Fin b → E) (t : Matrix (Fin b) (Fin b) ℂ) :
    (Matrix.of fun a a' => ⟪u a, ∑ i, t i a' • v i⟫_ℂ).det
      = (Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det * t.det := by
  rw [← Matrix.det_mul]
  congr 1
  ext a a'
  simp [Matrix.mul_apply, inner_sum, inner_smul_right, mul_comm]

theorem norm_det_inner_le_of_det_eq_one (n b : ℕ) (v u : Fin b → EuclideanSpace ℂ (Fin n))
    (t : Matrix (Fin b) (Fin b) ℂ) (ht : t.det = 1)
    (_h : ∀ a a', a ≠ a' → ⟪∑ i, t i a • v i, ∑ i, t i a' • v i⟫_ℂ = 0) :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖∑ i, t i a • v i‖ := by
  have h := norm_det_inner_le u (fun a => ∑ i, t i a • v i)
  rwa [det_inner_sum_smul, ht, mul_one] at h

end GlobalTheory.PlueckerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormLeadingMinorMonomial
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem partialProd_inv_le (t : ℕ → ℝ) (ht : ∀ a, 0 < t a) (j : ℕ) (De : ℝ)
    (h : ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ De ∨ (0 < b ∧ b < j ∧ t (b - 1) = t b)) :
    ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ De := by
  have hP : ∀ b, 0 < ∏ a ∈ Finset.range b, t a := fun b => Finset.prod_pos fun a _ => ht a
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (j + 1))
    (fun b => (∏ a ∈ Finset.range b, t a)⁻¹) ⟨0, by simp⟩
  have hle : ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ (∏ a ∈ Finset.range m, t a)⁻¹ :=
    fun b hb => hmax b (Finset.mem_range.2 (Nat.lt_succ_of_le hb))

  have key : ∀ b, b ≤ j → (∏ a ∈ Finset.range b, t a)⁻¹ = (∏ a ∈ Finset.range m, t a)⁻¹ →
      (∏ a ∈ Finset.range m, t a)⁻¹ ≤ De := by
    intro b
    induction b with
    | zero =>
      intro hb h0
      rcases h 0 hb with h1 | ⟨h1, -, -⟩
      · rw [← h0]; exact h1
      · exact absurd h1 (lt_irrefl 0)
    | succ n ih =>
      intro hn heq
      rcases h (n + 1) hn with h1 | ⟨-, hlt, hteq⟩
      · rw [← heq]; exact h1
      · rw [Nat.add_sub_cancel] at hteq
        apply ih (Nat.le_of_succ_le hn)
        have hx := hP n
        have hc := ht n
        have h0 := hle n (Nat.le_of_succ_le hn)
        have h2 := hle (n + 1 + 1) (by omega)
        rw [← heq] at h0 h2 ⊢
        rw [Finset.prod_range_succ] at h0 ⊢
        rw [Finset.prod_range_succ, Finset.prod_range_succ, ← hteq] at h2
        rw [inv_le_inv₀ hx (mul_pos hx hc)] at h0
        rw [inv_le_inv₀ (mul_pos (mul_pos hx hc) hc) (mul_pos hx hc)] at h2
        have c1 : t n ≤ 1 := by nlinarith
        have c2 : 1 ≤ t n := by nlinarith [mul_pos hx hc]
        rw [le_antisymm c1 c2, mul_one]
  intro b hb
  exact (hle b hb).trans (key m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) rfl)

theorem norm_leading_minor_monomial {j l : ℕ} (hl : l ≤ j) (Z : Matrix (Fin j) (Fin j) ℂ) (w : Equiv.Perm (Fin j))
    (hw : ∀ a b, Z a b ≠ 0 ↔ b = w a) (hc : ∀ a : Fin j, a.val < l → (w a).val < l) :
    ‖(Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det‖ = ∏ a : Fin l, ‖Z (Fin.castLE hl a) (w (Fin.castLE hl a))‖ := by
  set M := Z.submatrix (Fin.castLE hl) (Fin.castLE hl) with hM

  let f : Fin l → Fin l := fun a => ⟨(w (Fin.castLE hl a)).val, hc _ a.2⟩
  have hcf : ∀ a, Fin.castLE hl (f a) = w (Fin.castLE hl a) := fun a => Fin.ext rfl
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg (Fin.castLE hl) hab
    rw [hcf, hcf] at h1
    exact Fin.castLE_injective hl (w.injective h1)
  let w' : Equiv.Perm (Fin l) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hw' : ∀ a, w' a = f a := fun a => rfl
  have hMne : ∀ a b, M a b ≠ 0 ↔ b = w' a := by
    intro a b
    rw [hM, Matrix.submatrix_apply, hw, hw', ← hcf]
    exact (Fin.castLE_injective hl).eq_iff

  rw [Matrix.det_apply', Finset.sum_eq_single w'.symm]
  · have hs : ‖((Equiv.Perm.sign w'.symm : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign w'.symm) with hsg | hsg <;> simp [hsg]
    rw [norm_mul, hs, one_mul, norm_prod]
    refine Fintype.prod_equiv w'.symm _ _ fun i => ?_
    have hi : Fin.castLE hl i = w (Fin.castLE hl (w'.symm i)) := by
      rw [← hcf, ← hw', Equiv.apply_symm_apply]
    show ‖Z (Fin.castLE hl (w'.symm i)) (Fin.castLE hl i)‖ = _
    rw [hi]
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, w' (σ i) ≠ i := by
      by_contra hne
      push_neg at hne
      exact hσ (Equiv.ext fun i => w'.eq_symm_apply.2 (hne i))
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_contra hz
    exact hi ((hMne (σ i) i).1 hz).symm
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem blockAnti_perm_partialProd : ∀ (j : ℕ) (β : Fin j → ℕ) (Z : Matrix (Fin j) (Fin j) ℂ) (De : ℝ), BlockAnti β Z → 1 ≤ De → (∀ (l : ℕ) (hl : l ≤ j), (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 → ‖(Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det‖⁻¹ ≤ De) → ∃ (w : Equiv.Perm (Fin j)), (∀ a b, Z a b ≠ 0 ↔ b = w a) ∧ (∀ a, β (w a) = β a) ∧ ∀ b : ℕ, (∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b), ‖Z a (w a)‖)⁻¹ ≤ De := by
  intro j β Z De hZ _ hminor
  unfold BlockAnti at hZ
  obtain ⟨hmono, hdet, hblk, hanti⟩ := hZ

  have hrow : ∀ a, ∃ b, Z a b ≠ 0 := by
    intro a
    by_contra hne
    push_neg at hne
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero a hne)
  choose f hf using hrow
  have huniq : ∀ a b, Z a b ≠ 0 → b = f a := fun a b hab =>
    (hanti a b a (f a) hab (hf a) rfl).2.1 rfl

  have hinj : Function.Injective f := by
    intro a a' h
    have h1 := hf a
    have h2 := hf a'
    rw [← h] at h2
    have hb : β a = β a' := (hblk a (f a) h1).trans (hblk a' (f a) h2).symm
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exact absurd ((hanti a (f a) a' (f a) h1 h2 hb).2.2 hlt) (lt_irrefl _)
    · exact heq
    · exact absurd ((hanti a' (f a) a (f a) h2 h1 hb.symm).2.2 hgt) (lt_irrefl _)
  let w : Equiv.Perm (Fin j) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hw : ∀ a b, Z a b ≠ 0 ↔ b = w a := fun a b =>
    ⟨huniq a b, fun h => by rw [h]; exact hf a⟩
  have hβ : ∀ a, β (w a) = β a := fun a => (hblk a (w a) (hf a)).symm
  refine ⟨w, hw, hβ, ?_⟩

  let t : ℕ → ℝ := fun n => if h : n < j then ‖Z ⟨n, h⟩ (w ⟨n, h⟩)‖ else 1
  have ht : ∀ n, 0 < t n := by
    intro n
    simp only [t]
    split_ifs with h
    · exact norm_pos_iff.2 (hf _)
    · exact one_pos
  have htfin : ∀ a : Fin j, t a.val = ‖Z a (w a)‖ := by
    intro a
    simp [t]
  have hconv : ∀ b, ∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b), ‖Z a (w a)‖ =
      ∏ n ∈ Finset.range (min b j), t n := by
    intro b
    rw [Finset.prod_filter]
    simp_rw [← htfin]
    refine (Fin.prod_univ_eq_prod_range (fun n => if n < b then t n else 1) j).trans ?_
    rw [← Finset.prod_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    exact and_comm

  have hh : ∀ l ≤ j, (∏ n ∈ Finset.range l, t n)⁻¹ ≤ De ∨ (0 < l ∧ l < j ∧ t (l - 1) = t l) := by
    intro l hl
    by_cases hbd : ∀ a : Fin j, a.val < l → (w a).val < l
    · left
      have hnorm := norm_leading_minor_monomial hl Z w hw hbd
      have hprod : ∏ a : Fin l, ‖Z (Fin.castLE hl a) (w (Fin.castLE hl a))‖ = ∏ n ∈ Finset.range l, t n := by
        rw [← Fin.prod_univ_eq_prod_range]
        exact Finset.prod_congr rfl fun a _ => (htfin (Fin.castLE hl a)).symm
      have hpos : 0 < ∏ n ∈ Finset.range l, t n := Finset.prod_pos fun n _ => ht n
      have hne : (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
        intro h0
        rw [h0, norm_zero, hprod] at hnorm
        linarith
      have hb := hminor l hl hne
      rw [hnorm, hprod] at hb
      exact hb
    · right
      push_neg at hbd
      obtain ⟨a, hal, hwa⟩ := hbd
      have hlj : l < j := lt_of_le_of_lt hwa (w a).2
      have hl0 : 0 < l := lt_of_le_of_lt (Nat.zero_le _) hal
      refine ⟨hl0, hlj, ?_⟩
      let p : Fin j := ⟨l - 1, by omega⟩
      let q : Fin j := ⟨l, hlj⟩
      have hβeq : β p = β q := by
        have h1 : β a ≤ β p := hmono (Fin.le_def.2 (show a.val ≤ l - 1 by omega))
        have h2 : β p ≤ β q := hmono (Fin.le_def.2 (show l - 1 ≤ l by omega))
        have h3 : β q ≤ β (w a) := hmono (Fin.le_def.2 hwa)
        rw [hβ a] at h3
        omega
      have e1 : t (l - 1) = ‖Z p (w p)‖ := htfin p
      have e2 : t l = ‖Z q (w q)‖ := htfin q
      rw [e1, e2]
      exact (hanti p (w p) q (w q) (hf p) (hf q) hβeq).1
  intro b
  rw [hconv]
  exact partialProd_inv_le t ht j De hh (min b j) (min_le_right _ _)

end GlobalTheory.Amp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.FockTen

theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    have hf : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    rw [hf, zero_mul, zero_mul]

theorem fockF_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (ten f) (ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [fockF_eq_fockL]
  show Formalism.L2.DIV.fockL (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ)) (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) = _
  rw [Formalism.L2.DIV.fk_fock_prod]
  exact Finset.prod_congr rfl fun τ _ => (fockF_eq_fockL _ _).symm

theorem fockF_extremal_ne {n : ℕ} (l : DomWeight n) : Formalism.REAL.fockF (extremal ℂ n l) (extremal ℂ n l) ≠ 0 := by
  intro h0
  have h1 : normFock l (extremal ℂ n l) (extremal ℂ n l) = 1 := bridge_normFock_extremal_holds n l
  rw [normFock, h0, div_zero] at h1
  exact zero_ne_one h1

theorem nfAll_ten : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  intro ι _ n lam
  have hden : ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => fockF_extremal_ne (lam τ)
  refine ⟨fun f g => ?_, fun p hp => ?_, fun G M s f y => ?_⟩
  · rw [nfAll, fockF_ten]
    simp only [normFock]
    rw [Finset.prod_div_distrib]
  · rw [nfAll, div_eq_zero_iff] at hp
    rcases hp with hp | hp
    · by_contra hne
      exact (@LT.lt.ne' ℂ Complex.partialOrder.toPreorder _ _ (Formalism.L2.DIV.ps_fockF_pos p hne)) hp
    · exact absurd hp hden
  · show (∏ τ, (M τ * y.1 τ).det ^ s τ) *
        MvPolynomial.eval _ (∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)) = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_rename]
    rfl

end GlobalTheory.FockTen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
section
open Matrix Finset Formalism.MainNotions.S
open scoped ComplexOrder

namespace GlobalTheory.Dec

private lemma blockTriangular_toDual_of_isLo {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) :
    b.BlockTriangular OrderDual.toDual :=
  fun i j hij => hb i j (OrderDual.toDual_lt_toDual.mp hij)

private lemma isLo_of_blockTriangular_toDual {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.BlockTriangular OrderDual.toDual) : IsLo b :=
  fun _ _ hij => hb (OrderDual.toDual_lt_toDual.mpr hij)

theorem exists_isLo_mul_conjTranspose {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, IsLo b ∧ x = b * bᴴ := by
  classical

  have hLi : (LDL.lowerInv hx).BlockTriangular OrderDual.toDual :=
    LDL.isLowerTriangular_lowerInv hx
  have hL : (LDL.lower hx).BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hLi

  have hD : (LDL.diag hx).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    refine hx.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h := congrArg (fun u => u ᵥ* (LDL.lowerInv hx)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible] using h
  have hd : ∀ i, 0 < LDL.diagEntries hx i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  let s : Fin n → ℂ := fun i => ((Real.sqrt (LDL.diagEntries hx i).re : ℝ) : ℂ)
  have hs : ∀ i, s i * star (s i) = LDL.diagEntries hx i := fun i => by
    obtain ⟨hre, him⟩ := Complex.pos_iff.mp (hd i)
    have hsq := Real.mul_self_sqrt hre.le
    apply Complex.ext
    · simp [s, Complex.mul_re, hsq]
    · simp [s, Complex.mul_im, ← him]
  refine ⟨LDL.lower hx * Matrix.diagonal s,
    isLo_of_blockTriangular_toDual (hL.mul (Matrix.blockTriangular_diagonal s)), ?_⟩
  have hDs : LDL.diag hx = Matrix.diagonal s * (Matrix.diagonal s)ᴴ := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    unfold LDL.diag
    congr 1
    funext i
    exact (hs i).symm
  conv_lhs => rw [← LDL.lower_conj_diag hx, hDs]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem one_mem_Omega_leadMinor (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Omega n := by
  intro i
  simp [leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _)]

theorem diag_ne_zero_of_posDef_mul_conjTranspose {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b)
    (hx : (b * bᴴ).PosDef) (l : Fin n) : b l l ≠ 0 := by
  classical
  have hdet : (b * bᴴ).det ≠ 0 := hx.det_pos.ne'
  have hb' : b.det ≠ 0 := fun h => hdet (by rw [Matrix.det_mul, h, zero_mul])
  rw [Matrix.det_of_isLowerTriangular b (blockTriangular_toDual_of_isLo hb)] at hb'
  exact Finset.prod_ne_zero_iff.mp hb' l (Finset.mem_univ l)

private lemma phi_mul_conjTranspose_of_isLo (hT : PhiTri) {n : ℕ} (lam : Fin n → ℝ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) (hd : ∀ l, b l l ≠ 0) :
    b * bᴴ ∈ Omega n ∧ Phi lam (b * bᴴ) = ((∏ l, ‖b l l‖ ^ (-(2 * muInt lam l)) : ℝ) : ℂ) := by
  have hup : IsUp bᴴ := fun i j hji => by
    simp [Matrix.conjTranspose_apply, hb j i hji]
  have h := hT n lam b 1 bᴴ hb hup
    (fun l => ⟨hd l, by simpa [Matrix.conjTranspose_apply] using hd l⟩) (one_mem_Omega_leadMinor n)
  rw [Matrix.mul_one] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, Phi_at_one, mul_one, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_zpow,
    ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

theorem phiPos_of_phiTri (hT : PhiTri) : PhiPos := by
  intro n lam x hx
  obtain ⟨b, hb, rfl⟩ := exists_isLo_mul_conjTranspose hx
  have hd := fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb hx l
  obtain ⟨hΩ, hΦ⟩ := phi_mul_conjTranspose_of_isLo hT lam hb hd
  refine ⟨hΩ, ?_, ⟨b, hb, rfl⟩, fun b' hb' hx' => ?_⟩
  · rw [hΦ, Complex.zero_lt_real]
    exact Finset.prod_pos fun l _ => zpow_pos (norm_pos_iff.mpr (hd l)) _
  · have hx2 : (b' * b'ᴴ).PosDef := hx' ▸ hx
    rw [hx']
    exact (phi_mul_conjTranspose_of_isLo hT lam hb'
      (fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb' hx2 l)).2

theorem phiPos : PhiPos := phiPos_of_phiTri GlobalTheory.PhiTriangular.phiTri

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjAbsHolds
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.Dec

theorem projAbs_holds : ProjAbs := by
  intro G _ _ _ _ _ _ μ _ _ H _ _ _ σ hσ hσc d hd hS w hw hint
  have hcont : ∀ x y : H, Continuous fun g => ⟪y, σ g x⟫_ℂ := fun x y =>
    continuous_const.inner (hσc x)
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hm1 : ⟪w, σ 1 w⟫_ℂ = 1 := by
    rw [map_one, ContinuousLinearMap.one_apply, hww]
  obtain ⟨hsf, hinv⟩ := GlobalTheory.sigmaFinite_and_isInvInvariant_of_continuous_integrable G μ (fun g => ⟪w, σ g w⟫_ℂ) (hcont w w)
    (by show ⟪w, σ 1 w⟫_ℂ ≠ 0; rw [hm1]; exact one_ne_zero) hint
  have hpol := GlobalTheory.polarised_schur_relations G μ H σ d (fun x y => (hcont x y).aestronglyMeasurable) hS
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.matrixCoeff_idempotent_of_orthogonality G μ H σ d hd hσ (fun v w v' w' => (hpol v w v' w').2) w hw
  have hφ : Integrable (phG d σ w) μ := by
    have : Integrable (fun g => star ⟪w, σ g w⟫_ℂ) μ :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hint
    exact this.const_mul (d : ℂ)
  refine ⟨h1, h2, ?_⟩
  intro Hp _ _ _ π hπ hπc
  refine ⟨?_, ?_⟩
  · obtain ⟨P, -, hP⟩ := GlobalTheory.absOpInt G μ Hp π hπ hπc (phG d σ w) hφ
    exact ⟨P, hφ, hP⟩
  intro P hP
  obtain ⟨hsp, hPxP⟩ := GlobalTheory.integratedOperator_isStarProjection_and_sandwich G μ Hp π hπ hπc (phG d σ w) (fun x => ⟪w, σ x w⟫_ℂ) hφ h1 h2 hm1
    P hP.2
  have hfix : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), P v = v := by
    rintro _ ⟨u, rfl⟩
    have := congrArg (fun T : Hp →L[ℂ] Hp => T u) hsp.isIdempotentElem.eq
    simpa using this
  have hunit : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
      (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
    intro v hv hn
    have hPv := hfix v hv
    have hc : ∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ := by
      intro g
      have hvv : ⟪v, v⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hn]; simp
      have e1 : P (π g v) = ⟪w, σ g w⟫_ℂ • v := by
        have := congrArg (fun T : Hp →L[ℂ] Hp => T v) (hPxP g)
        simpa [hPv] using this
      have hadj : ContinuousLinearMap.adjoint P = P := by
        rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsp.isSelfAdjoint
      calc ⟪v, π g v⟫_ℂ = ⟪ContinuousLinearMap.adjoint P v, π g v⟫_ℂ := by rw [hadj, hPv]
        _ = ⟪v, P (π g v)⟫_ℂ := ContinuousLinearMap.adjoint_inner_left _ _ _
        _ = ⟪w, σ g w⟫_ℂ := by rw [e1, inner_smul_right, hvv, mul_one]
    exact ⟨hc, GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq G H σ Hp π hσ hπ w v h4 hc⟩
  refine ⟨hsp, hPxP, hunit, ?_⟩
  ext v
  constructor
  · intro hv
    by_cases h0 : v = 0
    · exact ⟨0, fun g => by simp, by simp [h0]⟩
    · have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hv' : ((‖v‖ : ℂ)⁻¹ • v) ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp) := Submodule.smul_mem _ _ hv
      obtain ⟨-, io, hio, hint'⟩ := hunit _ hv' (norm_smul_inv_norm h0)
      refine ⟨(‖v‖ : ℂ) • io.toContinuousLinearMap, fun g => ?_, ?_⟩
      · ext u
        simp [hint']
      · show v = (‖v‖ : ℂ) • io w
        rw [hio, smul_smul, mul_inv_cancel₀ hn, one_smul]
  · rintro ⟨io, hio, rfl⟩
    refine ⟨io w, ?_⟩
    show P (io w) = io w
    refine ext_inner_left ℂ fun x => ?_
    have e : ∀ g, ⟪x, π g (io w)⟫_ℂ = ⟪ContinuousLinearMap.adjoint io x, σ g w⟫_ℂ := by
      intro g
      rw [ContinuousLinearMap.adjoint_inner_left]
      have := congrArg (fun T : H →L[ℂ] Hp => T w) (hio g)
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this]
    rw [hP.2]
    simp only [e]
    have := h3 w (ContinuousLinearMap.adjoint io x)
    rw [hww, one_mul, ContinuousLinearMap.adjoint_inner_left] at this
    exact this

end GlobalTheory.Dec
end

