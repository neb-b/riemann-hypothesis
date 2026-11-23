module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPart
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConj

open Matrix
open Formalism.UG (bc GLint)

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

section Pure

variable {K : Type} [Field K] {n : ℕ}

theorem inv_val_of_diagonal {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0) :
    (d⁻¹ : GL (Fin n) K).val = Matrix.diagonal fun i => (D i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hd, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with i
  exact mul_inv_cancel₀ (hD i)

theorem conj_diag_apply {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0)
    (g : GL (Fin n) K) (p q : Fin n) : (d * g * d⁻¹).val p q = D p * g.val p q * (D q)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, inv_val_of_diagonal hd hD, hd, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_GLint_of {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) :
    x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable (v : Valuation K (WithZero (Multiplicative ℤ))) {r : ℕ} {ϖ : K}

theorem conj_le_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (h2 : ∀ q p : Fin n, p.val < r → q ≠ p → v (M q p) < 1) (p q : Fin n) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) ≤ 1 := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [map_mul, map_mul, map_inv₀]
  by_cases hp : (p : ℕ) < r <;> by_cases hq : (q : ℕ) < r <;>
    simp only [hp, hq, if_true, if_false, map_one, inv_one, one_mul, mul_one, hϖ]
  · exact h1 q p
  · have hqp : q ≠ p := fun e => hq (e ▸ hp)
    calc v (M q p) * (WithZero.exp (-1))⁻¹ ≤ WithZero.exp (-1) * (WithZero.exp (-1))⁻¹ :=
          mul_le_mul' (le_exp_neg_one_of_lt_one (h2 q p hp hqp)) le_rfl
      _ = 1 := mul_inv_cancel₀ hne
  · calc WithZero.exp (-1) * v (M q p) ≤ 1 * 1 := mul_le_mul' exp_neg_one_lt_one.le (h1 q p)
      _ = 1 := one_mul 1
  · rw [mul_comm (WithZero.exp (-1)), mul_assoc, mul_inv_cancel₀ hne, mul_one]; exact h1 q p

theorem conj_lower_lt_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (p q : Fin n) (hp : r ≤ p.val) (hq : q.val < r) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) < 1 := by
  rw [if_neg (not_lt.2 hp), if_pos hq, inv_one, mul_one, map_mul, hϖ]
  calc WithZero.exp (-1) * v (M q p) ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl (h1 q p)
    _ < 1 := by rw [mul_one]; exact exp_neg_one_lt_one

end Pure

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem valued_lt_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem valued_le_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem facts_of_mem (s : SplitPlace L) (r t : ℕ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (a : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)))
    (ha : Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t) :
    (∀ i j, Valued.v (a.val i j) ≤ 1) ∧
      ∀ q p : Fin (r + t), p.val < r → Valued.v (a.val q p - if q = p then 1 else 0) < 1 := by
  obtain ⟨hK, hcol⟩ := ha
  refine ⟨fun i j => ?_, fun q p hp => ?_⟩
  · have := val_le_one_of_mem_KO hK i j
    rw [valued_le_one_iff_w] at this
    simpa [hc] using this
  · have := hcol q ⟨p, hp⟩
    have e : Fin.castAdd t (⟨p, hp⟩ : Fin r) = p := Fin.ext rfl
    rw [e, valued_lt_one_iff_w] at this
    have e2 : ((Matrix.GeneralLinearGroup.map c.toRingHom a).val - 1) q p =
        c (a.val q p - if q = p then 1 else 0) := by
      by_cases h : q = p <;> simp [Matrix.one_apply, h]
    rw [e2, hc] at this
    exact this

end Place

end GlobalTheory.BlockConj

namespace GlobalTheory.BlockConj

open Formalism.UG (GLint)

theorem conj_transpose_inv_uniRT : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → NG.UniRT s r (d * b * d⁻¹) ∧ Valued.v (NG.supDiag s r (d * b * d⁻¹)) < 1 := by
  intro L _ _ _ s r t c hc a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hD : ∀ i : Fin (r + t), (if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) ≠ 0 := by
    intro i; split_ifs
    · exact one_ne_zero
    · exact hϖ0
  obtain ⟨ha1, ha2⟩ := facts_of_mem s r t c hc a ha
  obtain ⟨hi1, hi2⟩ := facts_of_mem s r t c hc a⁻¹ (by rw [map_inv]; exact (blockGrp _ r t).inv_mem ha)
  have ha2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v (a.val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using ha2 q p hp
  have hi2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v ((a⁻¹).val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using hi2 q p hp
  have hbinv : (b⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val = a.val.transpose := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hb, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hN : ∀ p q, (d * b * d⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * (a⁻¹).val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    intro p q; rw [conj_diag_apply hd hD, hb, Matrix.transpose_apply]
  have hNi : ∀ p q, ((d * b * d⁻¹)⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * a.val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    have e : (d * b * d⁻¹)⁻¹ = d * b⁻¹ * d⁻¹ := by group
    intro p q; rw [e, conj_diag_apply hd hD, hbinv, Matrix.transpose_apply]

  have hUL : ∀ p q : Fin (r + t), p.val < r → q.val < r → (d * b * d⁻¹).val p q = (a⁻¹).val q p := by
    intro p q hp hq; rw [hN, if_pos hp, if_pos hq, inv_one, one_mul, mul_one]
  refine ⟨⟨⟨mem_GLint_of (fun i j => ?_) (fun i j => ?_), fun p q hp hq => ?_⟩, fun p q hp hq => ⟨fun hlt => ?_, fun he => ?_⟩⟩, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hN]
    exact conj_le_one Valued.v hϖ hi1 hi2' i j
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hNi]
    exact conj_le_one Valued.v hϖ ha1 ha2' i j
  · rw [hN]; exact conj_lower_lt_one Valued.v hϖ hi1 p q hp hq
  · rw [hUL p q hp hq]; exact hi2' q p hp (Fin.ne_of_lt hlt)
  · subst he; rw [hUL p p hp hp]; simpa using hi2 p p hp
  · unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · rw [hUL p q (by omega) h.2]
      exact hi2' q p (by omega) (fun e => by rw [e] at h; omega)
    · rw [map_zero]; exact zero_lt_one

end GlobalTheory.BlockConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

open Polynomial Module

namespace GlobalTheory.Pst.TwistLetters

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {L : FinExt l}
  (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

def smulEnd : (Fin 1 → ↥L.1) →ₗ[ℚ_[l]] End ℚ_[l] V where
  toFun v' := ((LinearMap.lsmul ↥L.1 V) (v' 0)).restrictScalars ℚ_[l]
  map_add' x y := by ext v; simp [add_smul]
  map_smul' c x := by ext v; simp [smul_assoc]

def mulB : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) →ₗ[ℚ_[l]] End ℚ_[l] (V ⊗[ℚ_[l]] Bst P) :=
  TensorProduct.lift ((TensorProduct.mapBilinear (RingHom.id ℚ_[l]) V (Bst P) V (Bst P)).compl₁₂ (smulEnd V)
    (LinearMap.mul ℚ_[l] (Bst P)))

@[simp] theorem mulB_tmul (v' : Fin 1 → ↥L.1) (b' : Bst P) (v : V) (b : Bst P) :
    mulB P V (v' ⊗ₜ b') (v ⊗ₜ b) = (v' 0 • v) ⊗ₜ (b' * b) := by
  simp [mulB, smulEnd]

variable {P V}

theorem mulB_smul (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (a • x) = a • mulB P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', smul_smul, smul_smul, mul_comm]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_smul_left (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V (a • y) x = a • mulB P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', Pi.smul_apply, smul_eq_mul, mul_smul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (mulV P ↥L.1 V c x) = mulV P ↥L.1 V c (mulB P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_left_comm]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulV_mulB (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB P V (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) x = mulV P ↥L.1 V c (mulB P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_assoc]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem phiV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    phiV P ↥L.1 V (mulB P V y x) = mulB P V (phiV P ↥L.1 (Fin 1 → ↥L.1) y) (phiV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, phiV_tmul, phiV_tmul, phiV_tmul, mulB_tmul, map_mul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem monV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    monV P ↥L.1 V (mulB P V y x) = mulB P V (monV P ↥L.1 (Fin 1 → ↥L.1) y) x +
      mulB P V y (monV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, monV_tmul, monV_tmul, monV_tmul, mulB_tmul, mulB_tmul, ← TensorProduct.tmul_add]
      congr 1
      simp only [monSt_apply, derivative_mul]
      ring
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

variable {K : FinExt l} (ρs ρt : Representation ↥L.1 ↥(GK K) V)
  (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)

theorem stRep_mulB (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K))
    (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g (mulB P V y x) = mulB P V (stRep P ρm g y) (stRep P ρs g x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, stRep_tmul, stRep_tmul, stRep_tmul, mulB_tmul, map_mul, ht, hm, map_smul, Pi.smul_apply,
        smul_eq_mul, smul_smul, mul_smul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mem_Dpst (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    {x : V ⊗[ℚ_[l]] Bst P} {y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρs) (hy : y ∈ Dpst P ρm) :
    mulB P V y x ∈ Dpst P ρt := by
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρs).mp hx
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρm).mp hy
  refine (mem_Dpst P ρt).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
  rw [stRep_mulB ρs ρt ρm χ hm ht, h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg),
    h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)]

variable (P)

set_option synthInstance.maxHeartbeats 100000 in
def dmul (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) :
    ↥(Dpst P ρs) →ₗ[↥L.1] ↥(Dpst P ρm) →ₗ[↥L.1] ↥(Dpst P ρt) :=
  LinearMap.mk₂ ↥L.1 (fun x y => ⟨mulB P V y.1 x.1, mulB_mem_Dpst ρs ρt ρm χ hm ht x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul]))
    (fun x y y' => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul_left]))

variable (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)

@[simp] theorem coe_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    (dmul P ρs ρt ρm χ hm ht x y : V ⊗[ℚ_[l]] Bst P) = mulB P V y.1 x.1 := rfl

theorem dmul_mulD_left (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht (mulD P ρs c x) y = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulB_mulV])

theorem dmul_mulD_right (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht x (mulD P ρm c y) = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulV_mulB])

theorem phiD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    phiD P ρt (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (phiD P ρs x) (phiD P ρm y) :=
  Subtype.ext (by simp [phiV_mulB])

theorem monD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    monD P ρt (dmul P ρs ρt ρm χ hm ht x y) =
      dmul P ρs ρt ρm χ hm ht (monD P ρs x) y + dmul P ρs ρt ρm χ hm ht x (monD P ρm y) :=
  Subtype.ext ((monV_mulB y.1 x.1).trans (add_comm _ _))

theorem actD_dmul (g : ↥(GK K)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    actD P ρt g (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (actD P ρs g x) (actD P ρm g y) :=
  Subtype.ext (by simp [stRep_mulB ρs ρt ρm χ hm ht])

end GlobalTheory.Pst.TwistLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNat
section
open NumberField

open scoped IntermediateField

namespace GlobalTheory.CMSqrtNeg

theorem finrank_adjoin_sq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (c : E) (t : Ω)
    (ht : t ^ 2 = algebraMap E Ω c) (hn : t ∉ Set.range (algebraMap E Ω)) :
    IsIntegral E t ∧ Module.finrank E E⟮t⟯ = 2 := by
  have hm : (Polynomial.X ^ 2 - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c two_ne_zero
  have h0 : Polynomial.aeval t (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by simp [ht]
  have hi : IsIntegral E t := ⟨_, hm, by simpa [Polynomial.aeval_def] using h0⟩
  refine ⟨hi, ?_⟩
  rw [IntermediateField.adjoin.finrank hi]
  have h1 : (minpoly E t).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd E t h0) hm.ne_zero
    rwa [Polynomial.natDegree_X_pow_sub_C _] at this
  have h2 : 2 ≤ (minpoly E t).natDegree := (minpoly.two_le_natDegree_iff hi).2 (by simpa using hn)
  omega

theorem exists_qcm_adjoin_sqrt_neg : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) →
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  intro E Ω _ _ _ _ _ _ p hp δ hδ hδn
  have hδ' : δ ^ 2 = algebraMap E Ω (-(p : E)) := by simp [hδ]
  obtain ⟨hint, htwo⟩ := finrank_adjoin_sq (-(p : E)) δ hδ' hδn
  haveI : FiniteDimensional E E⟮δ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField E⟮δ⟯ := NumberField.of_module_finite E _
  obtain ⟨d, s, hs, hsn, hneg⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hs0 : s ≠ 0 := fun h => hsn (h ▸ zero_mem _)
  let t : E⟮δ⟯ := ⟨δ * algebraMap E Ω s,
    mul_mem (IntermediateField.subset_adjoin E {δ} rfl) (IntermediateField.algebraMap_mem _ s)⟩
  let d' : maximalRealSubfield E := -(p : maximalRealSubfield E) * (d : maximalRealSubfield E)
  have ht : t ^ 2 = algebraMap E E⟮δ⟯ (algebraMap (maximalRealSubfield E) E d') := by
    apply Subtype.ext
    show (δ * algebraMap E Ω s) ^ 2 = algebraMap E Ω (algebraMap (maximalRealSubfield E) E d')
    rw [mul_pow, hδ, ← map_pow, hs]
    simp [d']
  have htn : t ∉ Set.range (algebraMap E E⟮δ⟯) := by
    rintro ⟨e, he⟩
    apply hδn
    refine ⟨e * s⁻¹, ?_⟩
    have h1 : algebraMap E Ω e = δ * algebraMap E Ω s := congrArg Subtype.val he
    have h2 : algebraMap E Ω s ≠ 0 := (map_ne_zero _).2 hs0
    rw [map_mul, h1, map_inv₀, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have hpos : ∀ φ : maximalRealSubfield E →+* ℝ, 0 < φ d' := fun φ => by
    have := hneg φ
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    simp only [d', map_mul, map_neg, map_natCast]
    nlinarith
  have hcm := (GlobalTheory.isCMField_of_sq_eq_totallyPositive E E⟮δ⟯ htwo d' t ht htn hpos).1
  exact ⟨⟨E⟮δ⟯, nf, hcm, htwo⟩, rfl⟩

end GlobalTheory.CMSqrtNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionEmbedding_inducing_hostEmbedding : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := by
  first | exact @GlobalTheory.EmbExt.main | exact GlobalTheory.EmbExt.main | (intros; apply GlobalTheory.EmbExt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_rational_eigenform_hitting_carried_part : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → ∃ (sy : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), x ∈ BlockGood.goodR (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) ∧ (∀ i, (A3.liftI j A3.A.μ0).opAll i x = sy i • x) ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 ∧ labW j pl cW c = fun i => D.what₂.embLL (sy i) := by
  first | exact @GlobalTheory.CarriedPart.exists_good_eigenform | exact GlobalTheory.CarriedPart.exists_good_eigenform | (intros; apply GlobalTheory.CarriedPart.exists_good_eigenform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEven
section
open NumberField

namespace GlobalTheory.RealGal

theorem QCM.even_finrank_maximalRealSubfield (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  have h1 := (letI : Module.Free (maximalRealSubfield Q.K) Q.K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield Q.K) Q.K)
  have h2 := Module.finrank_mul_finrank ℚ E Q.K
  have h3 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield Q.K) Q.K] at h1
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3
  rw [Q.two] at h2
  exact ⟨Module.finrank ℚ (maximalRealSubfield E), by omega⟩

end GlobalTheory.RealGal
end

