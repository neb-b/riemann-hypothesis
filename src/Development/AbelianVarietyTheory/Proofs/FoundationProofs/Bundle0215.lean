module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.GradedWeylDivisibility.FinalC
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InitMinorNeZeroOfStrictMono
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem initMinor_ne_zero_of_strictMono {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) (hI : StrictMono I) :
    initMinor ℂ I hs ≠ 0 := by
  intro h0
  have := (colLexInitMinor ℂ r n s I hs hI).2
  rw [h0] at this
  simp at this

theorem xiB_ne_zero {n : ℕ} (lam sg : Fin n → ℕ) : Formalism.BranchingDeterminantCap.xiB ℂ lam sg ≠ 0 := by
  unfold Formalism.BranchingDeterminantCap.xiB
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    exact hpq
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    have h1 := p.2
    have h2 := q.2
    have h3 := i.2
    rw [Fin.lt_def] at hpq ⊢
    simp only [Formalism.BranchingDeterminantCap.rowsB]
    split_ifs <;> simp <;> omega

theorem det_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  have e : (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [e, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem transpose_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose =
      Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose := by
  ext a b
  rw [Matrix.transpose_apply, embGL_apply]
  simp only [Formalism.BranchingDeterminantCap.extM, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : a.val < n ∧ b.val < n
  · rw [dite_eq_left h, dite_eq_left h.symm]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h h'.symm)]
    simp only [eq_comm]

theorem exists_intertwining_ne_zero : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu → ∃ φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam), φ ≠ 0 := by
  intro n N h lam mu hI
  subst h
  set c : ℕ := (mu.detShift - lam.detShift).toNat with hcdef
  have hls : lam.detShift = lam.w (Fin.last n) := by
    simp [DomWeight.detShift, Fin.last]
  have hlow : ∀ i, lam.detShift ≤ lam.w i := fun i => hls ▸ lam.anti (Fin.le_last i)
  have hc : 0 < n → (c : ℤ) = mu.detShift - lam.detShift := by
    intro hn
    have h1 := (hI ⟨n - 1, by omega⟩).2
    have h2 := hlow ⟨n - 1 + 1, by omega⟩
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    simp only at h1
    omega
  have hmlow : ∀ i, mu.detShift ≤ mu.w i := fun i => by
    have hn : 0 < n := i.pos
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    rw [h3]
    refine mu.anti ?_
    have := i.2
    rw [Fin.le_def]
    simp only
    omega
  have hsg : ∀ i, ((mu.natW i + c : ℕ) : ℤ) = mu.w i - lam.detShift := fun i => by
    have h1 := hc i.pos
    have h2 := hmlow i
    simp only [DomWeight.natW]
    omega
  have hlz : ∀ a, Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc) a = lam.w a - lam.detShift := fun a => by
    have h2 := hlow a
    unfold Formalism.BranchingDeterminantCap.lamZ
    split_ifs with ha
    · have : (⟨a.val, ha⟩ : Fin n).castSucc = a := rfl
      simp only [DomWeight.natW, this]
      omega
    · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
      rw [hls, this]; simp
  have hI' : Formalism.BranchingDeterminantCap.Interlace (Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc))
      (fun i => ((mu.natW i + c : ℕ) : ℤ)) := by
    intro i
    simp only [hsg, hlz]
    have h1 : mu.w i ≤ lam.w i.castSucc := (hI i).1
    have h2 : lam.w i.succ ≤ mu.w i := (hI i).2
    constructor <;> omega
  obtain ⟨io, hmem, heq, hhw, -⟩ := Formalism.BranchingDeterminantCap.branchMap ℂ n (fun i : Fin n => lam.natW i.castSucc)
    (fun i => mu.natW i + c) hI'
  obtain ⟨dm, de, dh⟩ := GlobalTheory.Branching.genericDet_pow_mul n c mu.natW
  obtain ⟨am, ae⟩ := GlobalTheory.Branching.AddColumn.add_column (n + 1) n lam.natW (by simp [DomWeight.natW, hls])
  have ha : Antitone mu.natW := fun i j hij => by
    have := mu.anti hij
    simp only [DomWeight.natW]
    omega
  let D : nablaSq ℂ n mu →ₗ[ℂ] dualWeyl ℂ n n (fun i => mu.natW i + c) :=
    { toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [mul_add])
      map_smul' := fun a f => Subtype.ext (by simp) }
  let L : nablaSq ℂ n mu →ₗ[ℂ] nablaSq ℂ (n + 1) lam :=
    { toFun := fun f => ⟨rename (Prod.map id Fin.castSucc) (io (D f)), am _ (hmem _)⟩
      map_add' := fun f f' => Subtype.ext (by simp)
      map_smul' := fun a f => Subtype.ext (by simp) }
  have hdet : ∀ g : GL (Fin n) ℂ, detPow ℂ n g mu.detShift =
      detPow ℂ n g lam.detShift * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by
    intro g
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
      simp [detPow, this]
    · have : mu.detShift = lam.detShift + c := by have := hc hn; omega
      rw [this, detPow, detPow, zpow_add, zpow_natCast]
      simp
  have hL : ∀ (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu),
      L (sqRep ℂ n mu g f) = sqRep ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (L f) := by
    intro g f
    apply Subtype.ext
    have hd0 : detPow ℂ n g lam.detShift ≠ 0 := Units.ne_zero _
    have h1 : io ((detPow ℂ n g lam.detShift)⁻¹ • D (sqRep ℂ n mu g f)) =
        rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose) (io (D f)) := by
      apply heq
      change (detPow ℂ n g lam.detShift)⁻¹ • (lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n mu g f) =
        rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose
          (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))
      rw [de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ hd0, one_mul]
    have h2 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = detPow ℂ n g lam.detShift := by
      rw [detPow, detPow, det_embGL]
    change rename (Prod.map id Fin.castSucc) (io (D (sqRep ℂ n mu g f))) =
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (rename (Prod.map id Fin.castSucc) (io (D f)))
    rw [sqAct, transpose_embGL, ae, ← h1, h2, map_smul, map_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  refine ⟨⟨L, fun g => LinearMap.ext fun f => hL g f⟩, fun h0 => ?_⟩
  have h1 : L ⟨_, hwMem ℂ n n le_rfl _ ha⟩ = 0 := by
    have := congrArg (fun φ => φ.toLinearMap ⟨_, hwMem ℂ n n le_rfl _ ha⟩) h0
    exact this
  have h2 : rename (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1))
      (io (D ⟨_, hwMem ℂ n n le_rfl _ ha⟩)) = 0 := congrArg Subtype.val h1
  rw [hhw _ (dh ha)] at h2
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  have h3 := rename_injective _ hinj (h2.trans (map_zero _).symm)
  rcases smul_eq_zero.1 h3 with h4 | h4
  · exact (Formalism.BranchingDeterminantCap.capConst n _ _ hI').1 (by exact_mod_cast h4)
  · exact xiB_ne_zero _ _ h4

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMvPolynomialCoeffAbsSumEqSumOfSupportSubset
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.IntMvPolynomialCoeffAbsSum

noncomputable def l1 {σ : Type*} (f : MvPolynomial σ ℤ) : ℕ :=
  ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs

variable {σ : Type*}

theorem intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset (f : MvPolynomial σ ℤ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    l1 f = ∑ mo ∈ s, (AddMonoidAlgebra.coeff f mo).natAbs := by
  unfold l1
  refine Finset.sum_subset h ?_
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.1 hm]

theorem intMvPolynomialCoeffAbsSum_add_le (f g : MvPolynomial σ ℤ) : l1 (f + g) ≤ l1 f + l1 g := by
  classical
  rw [intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset (f + g) (f.support ∪ g.support) MvPolynomial.support_add,
    intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset f (f.support ∪ g.support) Finset.subset_union_left,
    intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset g (f.support ∪ g.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  exact Int.natAbs_add_le _ _

theorem intMvPolynomialCoeffAbsSum_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem intMvPolynomialCoeffAbsSum_monomial (m : σ →₀ ℕ) (a : ℤ) : l1 (monomial m a) = a.natAbs := by
  classical
  rw [intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset _ {m} MvPolynomial.support_monomial_subset]
  simp

theorem intMvPolynomialCoeffAbsSum_mul_le (f g : MvPolynomial σ ℤ) : l1 (f * g) ≤ l1 f * l1 g := by
  have h : f * g = ∑ m ∈ f.support, ∑ k ∈ g.support,
      monomial (m + k) (AddMonoidAlgebra.coeff f m * AddMonoidAlgebra.coeff g k) := by
    conv_lhs => rw [f.as_sum, g.as_sum, Finset.sum_mul_sum]
    simp only [monomial_mul]
  rw [h]
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  conv_rhs => unfold l1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun m _ => (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [intMvPolynomialCoeffAbsSum_monomial, Int.natAbs_mul]

theorem intMvPolynomialCoeffAbsSum_C (a : ℤ) : l1 (C a : MvPolynomial σ ℤ) = a.natAbs := intMvPolynomialCoeffAbsSum_monomial 0 a

theorem intMvPolynomialCoeffAbsSum_one : l1 (1 : MvPolynomial σ ℤ) = 1 := intMvPolynomialCoeffAbsSum_monomial 0 1

theorem intMvPolynomialCoeffAbsSum_X (v : σ) : l1 (X v : MvPolynomial σ ℤ) = 1 := intMvPolynomialCoeffAbsSum_monomial _ 1

theorem intMvPolynomialCoeffAbsSum_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intMvPolynomialCoeffAbsSum_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (intMvPolynomialCoeffAbsSum_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem intMvPolynomialCoeffAbsSum_pow_le (f : MvPolynomial σ ℤ) (k : ℕ) : l1 (f ^ k) ≤ l1 f ^ k := by
  simpa using intMvPolynomialCoeffAbsSum_prod_le (Finset.range k) (fun _ => f)

theorem intMvPolynomialCoeffAbsSum_det_X_le_factorial {s : ℕ} (v : Fin s → Fin s → σ) :
    l1 (Matrix.of fun p q : Fin s => (X (v p q) : MvPolynomial σ ℤ)).det ≤ s.factorial := by
  rw [Matrix.det_apply']
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  have : ∀ π : Equiv.Perm (Fin s), l1 ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) *
      ∏ i, (Matrix.of fun p q : Fin s => (X (v p q) : MvPolynomial σ ℤ)) (π i) i) ≤ 1 := by
    intro π
    refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ?_
    have h1 : l1 (((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) = 1 := by
      have := intMvPolynomialCoeffAbsSum_C (σ := σ) ((Equiv.Perm.sign π : ℤˣ) : ℤ)
      rw [Int.units_natAbs] at this
      simpa using this
    rw [h1, one_mul]
    refine (intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_
    simp [intMvPolynomialCoeffAbsSum_X]
  refine (Finset.sum_le_sum fun π _ => this π).trans ?_
  simp [Fintype.card_perm]

theorem sum_range_sub_succ_add_eq_of_antitone (e : ℕ → ℕ) (he : Antitone e) (n : ℕ) :
    ∑ i ∈ Finset.range n, (e i - e (i + 1)) + e n = e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := he (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at this
    omega

theorem sum_exponents_le {n : ℕ} (ν : Fin n → ℕ) (R : ℕ) (hν : Antitone ν) (hR : ∀ i, ν i ≤ R) :
    ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) ≤ R := by
  let e : ℕ → ℕ := fun i => if h : i < n then ν ⟨i, h⟩ else 0
  have he : Antitone e := by
    intro i j hij
    simp only [e]
    split_ifs with h1 h2 h3
    · exact hν hij
    · omega
    · omega
    · omega
  have h0 : e 0 ≤ R := by
    simp only [e]
    split_ifs
    · exact hR _
    · omega
  have h1 := sum_range_sub_succ_add_eq_of_antitone e he n
  have h2 : ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) = ∑ i ∈ Finset.range n, (e i - e (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => e i - e (i + 1)) n]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [e, Formalism.GradedWeylDivisibility.nuNext]
  omega

theorem highestWeightVector_coeff_natAbs_sum_le_factorial_pow : ∀ (n : ℕ) (ν : Fin n → ℕ) (R : ℕ), Antitone ν → (∀ i, ν i ≤ R) → ∑ mo ∈ (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν).support, (AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν) mo).natAbs ≤ (n.factorial) ^ R := by
  intro n ν R hν hR
  change l1 (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν) ≤ _
  unfold Formalism.GradedWeylDivisibility.hw
  refine (intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_
  refine le_trans (Finset.prod_le_prod' (g := fun s => n.factorial ^ (ν s - Formalism.GradedWeylDivisibility.nuNext ν s))
    fun s _ => ?_) ?_
  · refine (intMvPolynomialCoeffAbsSum_pow_le _ _).trans (Nat.pow_le_pow_left ?_ _)
    unfold Formalism.GradedWeylDivisibility.lpMinor
    exact (intMvPolynomialCoeffAbsSum_det_X_le_factorial _).trans (Nat.factorial_le s.isLt)
  · rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (Nat.factorial_pos n) (sum_exponents_le ν R hν hR)

end GlobalTheory.IntMvPolynomialCoeffAbsSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_mem_of_unitary_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M)
    (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin k) ℂ) (hf : f ∈ M) : rowAct ℂ g f ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  obtain ⟨P, hP⟩ := exists_poly_rowAct_coef n k f l
  have h0 : P = 0 := eq_zero_of_vanish_unitaryGroup n P fun u hu => by
    rw [← hP]
    exact (Submodule.mem_dualAnnihilator l).1 hl _ (hM u hu f hf)
  rw [hP, h0, map_zero]

theorem rowDivClosed_of_rowAct_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ f ∈ M, rowAct ℂ g f ∈ M) : RowDivClosed M := by
  intro a b j p hp
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  set N := (rowGen ℂ a b p).natDegree + j + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : j ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (l (rowDiv ℂ a b i p)) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := (Submodule.mem_dualAnnihilator l).1 hl _ (hM (lfockq_mat a b c) p hp)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← lfockq_eval_rowGen, lfockq_eval_C _ N h1, map_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

theorem height_rowDiv_le {n k : ℕ} (H : ℤ) (a b : Fin n) (j : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (hf : ∀ d ∈ f.support, Finsupp.weight (lhwinHt n k) d ≤ H) :
    ∀ d ∈ (rowDiv ℂ a b j f).support, Finsupp.weight (lhwinHt n k) d ≤ H + j * ((a.val : ℤ) - b.val) := by
  intro e he
  have hs : rowDiv ℂ a b j f = ∑ d ∈ f.support, (rowGen ℂ a b (monomial d (AddMonoidAlgebra.coeff f d))).coeff j := by
    unfold rowDiv
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Polynomial.finsetSum_coeff]
  rw [mem_support_iff, hs, coeff_sum] at he
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have h1 := lhwinShift_rowGen_monomial ℂ a b d (AddMonoidAlgebra.coeff f d) j hne
  have h2 := hf d hd
  omega

theorem exists_killed_of_rowDivClosed {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin n, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv ℂ a b j v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ ∀ d ∈ v.support, Finsupp.weight (lhwinHt n k) d ≤ (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨f.support.sup fun d => (Finsupp.weight (lhwinHt n k) d).toNat, f, hfM, hf0, fun d hd => ?_⟩
    have := Finset.le_sup (f := fun d => (Finsupp.weight (lhwinHt n k) d).toNat) hd
    have h2 : ((Finsupp.weight (lhwinHt n k) d).toNat : ℤ) ≤ _ := Int.ofNat_le.2 this
    exact (Int.self_le_toNat _).trans h2
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab j hj => ?_⟩
  by_contra hne'
  have hH := height_rowDiv_le _ a b j v hvH
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne'
  have hnn := (lhwin_weight_nonneg d).trans (hH d (mem_support_iff.2 hd))
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hlt : ((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b j v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

theorem dualWeyl_le_of_rowDivClosed {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hle : M ≤ dualWeyl ℂ r n ν) (hM : RowDivClosed M)
    (hne : M ≠ ⊥) : dualWeyl ℂ r n ν ≤ M := by
  obtain ⟨v, hvM, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hM hne
  obtain ⟨c, hc⟩ := hwLine ℂ r n hn ν hν v (hle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℂ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hhw : hw ℂ hn ν ∈ M := e ▸ M.smul_mem _ hvM
  refine (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν).trans ?_
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hhw
  | cons x w ih => exact hM _ _ _ _ ih

theorem isIrreducible_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    (smallRep (unitaryIncl n) mu).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (smallRep (unitaryIncl n) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.ext hS)
  refine Or.inr (Subrepresentation.ext ?_)
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := S.toSubmodule.map (nablaSq ℂ n mu).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, S.apply_mem_toSubmodule t hf, rfl⟩
    have h2 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) =
        detPow ℂ n (unitaryIncl n t) mu.detShift • rowAct ℂ u f := rfl
    rw [h2] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hS (Submodule.map_injective_of_injective (nablaSq ℂ n mu).injective_subtype
    (e.trans (Submodule.map_bot _).symm))
  have hle := dualWeyl_le_of_rowDivClosed le_rfl mu.natW (factNatW n mu).1 M
    (Submodule.map_subtype_le (nablaSq ℂ n mu) _) hcl hne
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨g, hg, e⟩ := hle f.2
  rwa [← Subtype.ext e]

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlaceStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_has_basis_at_every_finite_place : BasisAtEx := by
  first | exact @GlobalTheory.LatBasisAt.basisAtEx | exact GlobalTheory.LatBasisAt.basisAtEx | (intros; apply GlobalTheory.LatBasisAt.basisAtEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpaceStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdWeylLattices_fg_and_span_coeffSpace : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (nabStd K lam).FG ∧ (delStd K lam).FG ∧ Submodule.span K (nabStd K lam : Set (Pol K ι n)) = VV K lam ∧ Submodule.span K (delStd K lam : Set (Pol K ι n)) = VV K lam := by
  first | exact @GlobalTheory.StdLatSpan.std_fg_span | exact GlobalTheory.StdLatSpan.std_fg_span | (intros; apply GlobalTheory.StdLatSpan.std_fg_span <;> assumption)
end

