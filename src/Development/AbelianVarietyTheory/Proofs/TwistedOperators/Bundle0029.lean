module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColEInvMulAffPt
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.ColumnSupport

theorem colE_inv_mul_affPt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    {c p : ℕ} (hp : p < c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (p + 1) rs} → k) (r : n) :
    (((colE c (p + 1) β)⁻¹).val * affPt (p + 1) x₀ e) (Sum.inl r) (Sum.inr ⟨p, by omega⟩) = -β r := by
  have hv : ((colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p + 1 then β r else 0)) 0 1 := rfl
  have h1 : ∀ s : n, affPt (p + 1) x₀ e (Sum.inl s) (Sum.inr ⟨p, by omega⟩) = 0 := by
    intro s
    simp [affPt, basePt, Free]
  have h2 : affPt (p + 1) x₀ e (Sum.inr ⟨p, hp⟩) (Sum.inr ⟨p, by omega⟩) = 1 := by
    simp [affPt, basePt, Free]
  rw [hv, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [h1, mul_zero, Finset.sum_const_zero, zero_add, fromBlocks_apply₁₂]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : Fin c)]
  · simp [h2]
  · intro j _ hj
    have : j.val ≠ p := fun e => hj (Fin.ext e)
    simp [this]
  · simp


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.RootEx.ColumnSupport.opE_colE_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ), ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∃ K : Set (n → k), IsCompact K ∧ ∀ β, β ∉ K → ∀ χ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => χ y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.colE c (p + 1) β) Φ y) = 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp ψ ν μ Φ hΦ
  have hcs : HasCompactSupport Φ := (show IsLocallyConstant Φ ∧ HasCompactSupport Φ from hΦ).2
  let q : Fin (c + 1) := ⟨p, by omega⟩
  refine ⟨(fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => fun r => -z (Sum.inl r) (Sum.inr q)) '' tsupport Φ,
    hcs.isCompact.image (continuous_pi fun r => (continuous_apply_apply _ _).neg), ?_⟩
  intro β hβ χ
  funext x
  unfold _root_.GlobalTheory.RootEx.opE
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
  have hentry : ∀ r, ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e) (Sum.inl r) (Sum.inr q) = -β r := by
    intro r
    rw [_root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp [q, Matrix.mul_apply, Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, _root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.RootEx.ExchangeSupport.colM, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => if_neg (fun h => hb (Fin.ext h))) (by simp)]
    simp
  have hzero : Φ ((((_root_.GlobalTheory.RootEx.colE c (p + 1) β)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x e * ((1 : GL (n' ⊕ Fin (c + 1)) k) : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) = 0 := by
    by_contra h
    apply hβ
    refine ⟨_, subset_tsupport _ h, ?_⟩
    funext r
    simp only [Units.val_one, Matrix.mul_one]
    rw [hentry r, neg_neg]
  unfold _root_.GlobalTheory.SplitWeil.om
  simp only [Pi.zero_apply]
  rw [hzero]
  simp

end GlobalTheory.RootEx.ColumnSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactModStabilizer
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.PairingOne

section Alg
variable {k : Type*} [Field k] {m : Type*} [Fintype m] [DecidableEq m]

end Alg

variable {k : Type*} [Field k] [ValuativeRel k] {m : Type*} [Fintype m] [DecidableEq m]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_bounded (t : ValueGroupWithZero k) :
    IsCompact {w : GL m k | (∀ a b, valuation k (w.val a b) ≤ t) ∧ ∀ a b, valuation k ((w⁻¹).val a b) ≤ t} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} := by
    have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k t
    have e : {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} =
        (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix m m k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.PairingOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasisStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F), (∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) → f = g := by
  first | exact @GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | exact GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | (intros; apply GlobalTheory.continuousMultilinearMap_ext_hilbertBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergSubgroupFourierJacobiCommutator
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSubgroup

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def zM (c p : ℕ) (t : k) : Matrix (Fin c) (Fin c) k :=
  Matrix.of fun l i => if l.val + 1 = p ∧ i.val + 1 = p + 1 then t else 0

def hM (c p : ℕ) (u β : n → k) (t : k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  fromBlocks 1 (ExchangeSupport.colM c (p + 1) β) (ExchangeSupport.rowM c p u) (1 + zM c p t)

theorem zM_add (s t : k) : zM c p (s + t) = zM c p s + zM c p t := by
  ext l i
  simp only [zM, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem zM_zero : zM c p (0 : k) = 0 := by
  ext l i
  simp [zM]

theorem zM_mul (s t : k) : zM c p s * zM c p t = 0 := by
  ext l i
  simp only [Matrix.mul_apply, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem col_mul_zM (β : n → k) (t : k) : ExchangeSupport.colM c (p + 1) β * zM c p t = 0 := by
  ext r i
  simp only [Matrix.mul_apply, ExchangeSupport.colM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem zM_mul_row (u : n → k) (t : k) : zM c p t * ExchangeSupport.rowM c p u = 0 := by
  ext l s
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [DecidableEq n] in
theorem row_mul_col (u β : n → k) :
    ExchangeSupport.rowM c p u * ExchangeSupport.colM c (p + 1) β = zM c p (u ⬝ᵥ β) := by
  ext l i
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, ExchangeSupport.colM, zM, Matrix.of_apply]
  by_cases hl : l.val + 1 = p <;> by_cases hi : i.val + 1 = p + 1 <;> simp [hl, hi, dotProduct]

omit [Fintype n] [DecidableEq n] in
theorem row_add (u w : n → k) : ExchangeSupport.rowM c p (u + w) =
    ExchangeSupport.rowM c p u + ExchangeSupport.rowM c p w := by
  ext l s
  simp only [ExchangeSupport.rowM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem col_add (u w : n → k) : ExchangeSupport.colM c p (u + w) =
    ExchangeSupport.colM c p u + ExchangeSupport.colM c p w := by
  ext r i
  simp only [ExchangeSupport.colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem row_zero : ExchangeSupport.rowM c p (0 : n → k) = 0 := by
  ext l s
  simp [ExchangeSupport.rowM]

omit [Fintype n] [DecidableEq n] in
theorem col_zero : ExchangeSupport.colM c p (0 : n → k) = 0 := by
  ext r i
  simp [ExchangeSupport.colM]

theorem hM_mul (u β u' β' : n → k) (t t' : k) :
    hM c p u β t * hM c p u' β' t' = hM c p (u + u') (β + β') (t + t' + u ⬝ᵥ β') := by
  simp only [hM, Matrix.fromBlocks_multiply]
  congr 1
  · rw [ExchangeSupport.colM_mul_rowM, Matrix.one_mul, add_zero]
  · rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, col_mul_zM, add_zero, col_add]
    abel
  · rw [Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, zM_mul_row, add_zero, row_add]
  · rw [row_mul_col]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, zM_mul, zM_add]
    abel

omit [Fintype n] in
theorem hM_zero : hM c p (0 : n → k) 0 0 = 1 := by
  rw [hM, row_zero, col_zero, zM_zero, add_zero, Matrix.fromBlocks_one]

theorem rowE_eq (u : n → k) : (rowE c p u).val = hM c p u 0 0 := by
  rw [ExchangeSupport.rowE_val, hM, col_zero, zM_zero, add_zero]

theorem colE_eq (β : n → k) : (colE c (p + 1) β).val = hM c p 0 β 0 := by
  rw [ExchangeSupport.colE_val, hM, row_zero, zM_zero, add_zero]

theorem cenM_eq (t : k) : cenM n c p t = hM c p 0 0 t := by
  rw [hM, row_zero, col_zero]
  rfl

theorem prod_eq (u β : n → k) (t : k) :
    (rowE c p u).val * (colE c (p + 1) β).val * cenM n c p t = hM c p u β (u ⬝ᵥ β + t) := by
  rw [rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul]
  simp only [add_zero, zero_add, dotProduct_zero]

def Heisenberg₂ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | ∃ (u β : n → k) (t : k), g.val = hM c p u β t}
  one_mem' := ⟨0, 0, 0, hM_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨u, β, t, hg⟩ ⟨u', β', t', hh⟩
    exact ⟨_, _, _, by rw [Units.val_mul, hg, hh, hM_mul]⟩
  inv_mem' := by
    rintro g ⟨u, β, t, hg⟩
    refine ⟨-u, -β, u ⬝ᵥ β - t, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hg, hM_mul, ← hM_zero (p := p)]
    simp

theorem mem_N_of_val {g : GL (n ⊕ Fin c) k} {β : n → k} {t : k} (hg : g.val = hM c p 0 β t) :
    g ∈ N k n c p := by
  show g ∈ Subgroup.closure {g | InN p g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [hg, hM, row_zero]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₁₂, ExchangeSupport.colM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.add_apply, zM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp [Matrix.one_apply]

private theorem eMat_mem_N_succ (u : n → k) : rowE c p u ∈ N k n c (p + 1) := by
  show rowE c p u ∈ Subgroup.closure {g | InN (p + 1) g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [ExchangeSupport.rowE_val]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₁, ExchangeSupport.rowM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp [Matrix.one_apply]

theorem heis_le : Heisenberg₂ k n c p ≤ NFJ k n c p := by
  rintro g ⟨u, β, t, hg⟩
  have hinv : rowE c p u * rowE c p (-u) = 1 := by
    rw [← ExchangeSupport.rowE_add, add_neg_cancel, ExchangeSupport.rowE_zero]
  have hsplit : g = rowE c p u * (rowE c p (-u) * g) := by
    rw [← mul_assoc, hinv, one_mul]
  have hrest : rowE c p (-u) * g ∈ N k n c p := by
    refine mem_N_of_val (β := β) (t := t - u ⬝ᵥ β) ?_
    rw [Units.val_mul, hg, rowE_eq, hM_mul]
    simp only [neg_add_cancel, zero_add, neg_dotProduct]
    ring_nf
  rw [hsplit]
  exact Subgroup.mul_mem _ (le_sup_right (a := N k n c p) (eMat_mem_N_succ u))
    (le_sup_left (b := N k n c (p + 1)) hrest)

end

theorem heisenberg_subgroup : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∃ H : Subgroup (GL (n ⊕ Fin c) k), H ≤ NFJ k n c ρ ∧ ∀ g, g ∈ H ↔ ∃ (u β : n → k) (t : k), g.val = (rowE c ρ u).val * (colE c (ρ + 1) β).val * cenM n c ρ t) ∧ ∀ u β₀ : n → k, (rowE c ρ u * colE c (ρ + 1) β₀).val = cenM n c ρ (u ⬝ᵥ β₀) * (colE c (ρ + 1) β₀ * rowE c ρ u).val := by
  intro k _ n _ _ c ρ _ _
  refine ⟨⟨Heisenberg₂ k n c ρ, heis_le, fun g => ?_⟩, fun u β₀ => ?_⟩
  · constructor
    · rintro ⟨u, β, t, hg⟩
      refine ⟨u, β, t - u ⬝ᵥ β, ?_⟩
      rw [prod_eq, hg]
      congr 1
      ring
    · rintro ⟨u, β, t, hg⟩
      exact ⟨u, β, u ⬝ᵥ β + t, by rw [hg, prod_eq]⟩
  · rw [Units.val_mul, Units.val_mul, rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul, hM_mul]
    simp only [add_zero, zero_add, dotProduct_zero, zero_dotProduct]

end GlobalTheory.RootEx.HeisenbergSubgroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}

theorem isSelfDual_iff_vol (h : HasConductor ψ c) (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1 := by
  have := t2Space k
  have hcl : IsClosed (𝒪[k] : Set k) := (isCompact_int k).isClosed
  have hclo : IsClopen (𝒪[k] : Set k) := ⟨hcl, isOpen_int k⟩
  set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf
  have hfSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · have hlc := (LocallyConstant.charFn ℂ hclo).isLocallyConstant
      exact hlc
    · exact HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]
  have hf0 : f 0 = 1 := by simp [f]
  have hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal := measureReal_def ν _
  constructor
  · rintro ⟨-, hsd⟩
    have e := (fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)
    rw [hf0, mul_one] at e
    rw [← hvol]
    exact_mod_cast e
  · intro hC
    refine ⟨inferInstance, fun g hg => ?_⟩
    rw [fourier_inversion ν h hg, hvol, hC]
    simp

theorem exists_isSelfDual_of_hasConductor (h : HasConductor ψ c) : ∃ ν : Measure k, IsSelfDual ψ ν := by
  obtain ⟨ν₀, hH, h1⟩ := exists_isUnitVol k
  have hn : 0 < nabs k c := nabs_pos k c
  set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have : (Real.sqrt (nabs k c))⁻¹ = 0 := congrArg Subtype.val h0
    have hs : 0 < Real.sqrt (nabs k c) := Real.sqrt_pos.2 hn
    exact (inv_pos.2 hs).ne' this
  have : (a • ν₀).IsAddHaarMeasure := .nnreal_smul ν₀ ha0
  refine ⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩
  have hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹ := by
    rw [smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
    rfl
  rw [hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']

theorem isUnitVol_iff_isSelfDual (h : HasConductor ψ 1) (ν : Measure k) : IsUnitVol ν ↔ IsSelfDual ψ ν := by
  constructor
  · intro hν
    haveI := hν.1
    exact isSelfDual_of_isUnitVol ν h hν
  · intro hsd
    haveI : ν.IsAddHaarMeasure := hsd.1
    have e := (isSelfDual_iff_vol h ν).1 hsd
    rw [nabs_one, mul_one] at e
    have hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal := ENNReal.toReal_nonneg
    have e1 : (ν (𝒪[k] : Set k)).toReal = 1 := by nlinarith
    exact ⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩

theorem selfDual_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1), (∃ ν : Measure k, IsSelfDual ψ ν) ∧ (HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν ↔ IsSelfDual ψ ν) ∧ ∀ (c : kˣ) (ν : Measure k), HasConductor ψ c → ν.IsAddHaarMeasure → (IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1) := by
  intro k _ _ _ _ _ _ ψ hψ h1
  refine ⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    exact exists_isSelfDual_of_hasConductor hc
  · exact isSelfDual_iff_vol hc ν

end GlobalTheory.SplitWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
section
noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

theorem phase_eq_eChar (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) :
    phase w x = GlobalTheory.Published.Metaplectic.eChar (⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2) := by
  rw [GlobalTheory.Published.Metaplectic.eChar_apply, phase]
  congr 1
  push_cast
  ring

theorem hasTemperateGrowth_phase' (w : l ⊕ l → ℝ) : Function.HasTemperateGrowth (phase w) := by
  have h1 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth
  have h := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (h1.add (Function.HasTemperateGrowth.const
    (⟪pPart w, qPart w⟫ / 2)))
  have e : phase w = (GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘
      ((fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫) + fun _ => ⟪pPart w, qPart w⟫ / 2) := by
    funext x
    simp [phase_eq_eChar]
  rw [e]
  exact h

def rhoSch (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  SchwartzMap.smulLeftCLM ℂ (phase w) ∘L SchwartzMap.compSubConstCLM ℂ (-pPart w)

theorem coe_rhoSch (w : l ⊕ l → ℝ) (f : Sch l) : ⇑(rhoSch w f) = rhoFun w ⇑f := by
  funext x
  rw [rhoSch, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase' w),
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, rhoFun]

theorem exists_schwartz_rhoFun : ∀ (l : Type) [Fintype l] (w : l ⊕ l → ℝ) (f : Sch l), ∃ f₁ : Sch l, ⇑f₁ = rhoFun w ⇑f :=
  fun _ _ w f => ⟨rhoSch w f, coe_rhoSch w f⟩

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumSmulOfLocallyConstantCompactSupport
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.LocConstTensor

theorem exists_sum (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V]
    [Module ℂ V] (T : Z → V) (hT : IsLocallyConstant T) (K : Set Z) (hK : IsCompact K)
    (h0 : ∀ y, y ∉ K → T y = 0) :
    ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  classical
  have hfin : (T '' K).Finite := by
    letI : TopologicalSpace V := ⊥
    haveI : DiscreteTopology V := ⟨rfl⟩
    exact (hK.image hT.continuous).finite_of_discrete
  let S : Finset V := hfin.toFinset.erase 0
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hmem : ∀ w : V, w ≠ 0 → (fun y => if T y = w then (1 : ℂ) else 0) ∈ SB Z := by
    intro w hw
    refine ⟨hT.comp (fun u => if u = w then (1 : ℂ) else 0), ?_⟩
    refine HasCompactSupport.intro hK ?_
    intro y hy
    rw [h0 y hy, if_neg (Ne.symm hw)]
  refine ⟨S.card, fun i => (e i : V),
    fun i => ⟨_, hmem (e i) (Finset.ne_of_mem_erase (e i).2)⟩, fun y => ?_⟩
  have h1 : ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
      = ∑ w ∈ S, (if T y = w then (1 : ℂ) else 0) • w := by
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp e (fun w : S => (if T y = (w : V) then (1 : ℂ) else 0) • (w : V))
  change T y = ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
  rw [h1]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    refine Finset.mem_erase.2 ⟨hne, hfin.mem_toFinset.2 ⟨y, ?_, rfl⟩⟩
    by_contra hy
    exact hne (h0 y hy)

end GlobalTheory.LocConstTensor
end

