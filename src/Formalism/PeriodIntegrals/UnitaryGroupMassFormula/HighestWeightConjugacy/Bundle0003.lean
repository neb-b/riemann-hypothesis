module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensityFirstBound
section
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem mapMatrix_inv (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) (h : M.det ≠ 0) :
    f.mapMatrix M⁻¹ = (f.mapMatrix M)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), map_one]

theorem det_mapMatrix (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) : (f.mapMatrix M).det = f M.det :=
  (RingHom.map_det f M).symm

variable [IsCMField L]

def skewL (b : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  b - ((IsCMField.complexConj L : L →+* L).mapMatrix b)ᵀ

def zOf (b : Matrix (Fin n) (Fin n) L) : Fin n → Fin n → InfinitePlace L → ℂ :=
  fun i j w => w.embedding (b i j)

theorem map_skewL (b : Matrix (Fin n) (Fin n) L) (w : InfinitePlace L) :
    w.embedding.mapMatrix (skewL b) = skewOf (zOf b) w := by
  ext i j
  simp [skewL, skewOf, zOf, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]

theorem det_one_add_skewL (b : Matrix (Fin n) (Fin n) L) : (1 + skewL b).det ≠ 0 := by
  intro h0
  let w0 : InfinitePlace L := Classical.arbitrary _
  apply det_one_add_ne_zero (skewOf_skew (zOf b) w0)
  rw [← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_add (f := _), det_mapMatrix, h0, map_zero]

theorem det_one_sub_skewL (b : Matrix (Fin n) (Fin n) L) : (1 - skewL b).det ≠ 0 := by
  intro h0
  let w0 : InfinitePlace L := Classical.arbitrary _
  apply (isUnit_det_one_sub (skewOf_skew (zOf b) w0)).ne_zero
  rw [← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_sub, det_mapMatrix, h0, map_zero]

theorem map_cay (b : Matrix (Fin n) (Fin n) L) (w : InfinitePlace L) :
    w.embedding.mapMatrix (cay (skewL b)) = cay (skewOf (zOf b) w) := by
  unfold cay
  rw [map_mul, mapMatrix_inv _ _ (det_one_add_skewL b), map_sub, map_add (f := _), map_one, map_skewL]

theorem map_conjT (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) :
    f.mapMatrix (conjT (IsCMField.complexConj L : L →+* L) M) = (f.mapMatrix M)ᴴ := by
  ext i j
  simp [conjT, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]

theorem cay_skewL_mem (b : Matrix (Fin n) (Fin n) L) :
    cay (skewL b) * conjT (IsCMField.complexConj L : L →+* L) (cay (skewL b)) = 1 := by
  let w0 : InfinitePlace L := Classical.arbitrary _
  have hinj : Function.Injective (w0.embedding.mapMatrix : Matrix (Fin n) (Fin n) L →+* _) := by
    intro M N h
    ext i j
    exact w0.embedding.injective (congrFun (congrFun h i) j)
  apply hinj
  rw [map_mul, map_conjT, map_cay, map_one]
  exact cay_mul_conjTranspose (skewOf_skew (zOf b) w0)

theorem det_cay_skewL (b : Matrix (Fin n) (Fin n) L) : (cay (skewL b)).det ≠ 0 := by
  unfold cay
  rw [det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (det_one_sub_skewL b) (inv_ne_zero (det_one_add_skewL b))

theorem ratPt_cay (b : Matrix (Fin n) (Fin n) L) :
    ratPt (cay (skewL b)) = cpt (fun w => cay (skewOf (zOf b) w)) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  simp only [ratPt, cpt]
  split_ifs with h
  · rw [← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply]
    conv_rhs => rw [← h]
  · have hc : σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding := by
      rcases InfinitePlace.embedding_mk_eq σ with h' | h'
      · exact absurd h'.symm h
      · rw [h']; exact (star_star σ).symm
    rw [← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply]
    conv_lhs => rw [hc]
    rw [ComplexEmbedding.conjugate_coe_eq]
    rfl

theorem rat_zero (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hF : ∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0)
    (b : Matrix (Fin n) (Fin n) L) :
    MvPolynomial.eval (cpt (fun w => cay (skewOf (zOf b) w))) F = 0 := by
  have hu : IsUnit (cay (skewL b)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_cay_skewL b))
  have hmem : hu.unit ∈ GQ0 L n := by
    show ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      conjT (IsCMField.complexConj L : L →+* L) ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1
    rw [IsUnit.unit_spec]
    exact cay_skewL_mem b
  have := hF _ hmem
  rwa [IsUnit.unit_spec, ratPt_cay] at this

theorem density_first_bound : DensA := by
  intro L _ _ _ n F hF Y hYu hY1
  have hH : (fun z : Fin n → Fin n → InfinitePlace L → ℂ => MvPolynomial.eval (cpt (fun w => cay (skewOf z w))) F) =
      fun _ => 0 :=
    (denseRange_matEmb (L := L) (n := n)).equalizer ((MvPolynomial.continuous_eval F).comp continuous_cpt_cay)
      continuous_const (funext fun b => rat_zero F hF b)
  choose X hXs hXc using fun w => exists_cay (hYu w) (hY1 w)
  let z : Fin n → Fin n → InfinitePlace L → ℂ := fun i j w => ((2 : ℂ)⁻¹ • X w) i j
  have hz : ∀ w, cay (skewOf z w) = Y w := by
    intro w
    have hs : skewOf z w = X w := by
      ext i j
      have h1 := congrArg (fun M => M i j) (hXs w)
      simp only [conjTranspose_apply, Matrix.neg_apply] at h1
      have h2 : (starRingEnd ℂ) (X w j i) = -X w i j := h1
      simp only [skewOf, z, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        star_mul']
      simp [h2]
      ring
    rw [hs, hXc]
  rw [repPt_eq_cpt Y hYu]
  have := congrFun hH z
  rwa [show (fun w => cay (skewOf z w)) = Y from funext hz] at this

theorem density_induction : DensStep := densStep_of density_first_bound density_second_bound

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.VmulCommEvPt
section
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev Vars (L : Type) [Field L] (n : ℕ) := (L →+* ℂ) × Fin n × Fin n

def vmul (y z : Vars L n → ℂ) : Vars L n → ℂ := fun p => ∑ k, y (p.1, p.2.1, k) * z (p.1, k, p.2.2)

theorem eval_aeval_eq {σ' : Type} (y : σ' → ℂ) (f : Vars L n → MvPolynomial σ' ℂ) (Q : MvPolynomial (Vars L n) ℂ) :
    MvPolynomial.eval y (MvPolynomial.aeval f Q) = MvPolynomial.eval (fun p => MvPolynomial.eval y (f p)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]

def tInv (g : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨((g⁻¹).val)ᵀ, (g.val)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩

theorem inV_evPt (τ : L →+* ℂ) (g : GL (Fin n) ℂ) : InV (evPt τ g) := by
  intro σ
  by_cases h1 : σ = τ
  · subst h1
    refine ⟨g, fun i j => ⟨?_, ?_⟩⟩
    · simp [evPt]
    · simp [evPt, conj_ne σ]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      refine ⟨tInv g, fun i j => ⟨?_, ?_⟩⟩
      · simp [evPt, conj_ne τ, tInv]
      · simp [evPt, conj_conj, tInv]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun h => h2 (by rw [← h, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun h => h1 (by
        rw [← conj_conj σ, h, conj_conj])
      refine ⟨1, fun i j => ⟨?_, ?_⟩⟩
      · simp [evPt, h1, h2, Matrix.one_apply]
      · simp [evPt, h3, h4, Matrix.one_apply, eq_comm]

theorem unit_conj (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) (i j : Fin n) :
    (IsCMField.complexConj L : L →+* L) (γ₀.val i j) = (γ₀⁻¹).val j i := by
  have hg' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := hg
  rw [Units.inv_eq_of_mul_eq_one_right hg']
  rfl

theorem conj_ratPt (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) (σ : L →+* ℂ) (i j : Fin n) :
    (ComplexEmbedding.conjugate σ) (γ₀.val i j) = σ ((γ₀⁻¹).val j i) := by
  rw [← unit_conj γ₀ hg]
  exact (IsCMField.complexEmbedding_complexConj (K := L) σ _).symm

theorem inV_ratPt (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) : InV (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) := by
  intro σ
  refine ⟨Matrix.GeneralLinearGroup.map σ γ₀, fun i j => ⟨rfl, ?_⟩⟩
  rw [← map_inv]
  exact conj_ratPt γ₀ hg σ i j


open Classical in
def trivAt (τ : L →+* ℂ) (y : Vars L n → ℂ) : Vars L n → ℂ := fun p =>
  if p.1 = τ ∨ p.1 = ComplexEmbedding.conjugate τ then (if p.2.1 = p.2.2 then 1 else 0) else y p

theorem inV_trivAt (τ : L →+* ℂ) (y : Vars L n → ℂ) (hy : InV y) : InV (trivAt τ y) := by
  intro σ
  by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
  · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
      rcases h with h | h <;> subst h <;> simp [conj_conj]
    refine ⟨1, fun i j => ⟨?_, ?_⟩⟩
    · simp only [trivAt, if_pos h]; simp [Matrix.one_apply]
    · simp only [trivAt, if_pos h']; simp [Matrix.one_apply, eq_comm]
  · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
      rintro (h1 | h1)
      · exact h (Or.inr (by rw [← h1, conj_conj]))
      · exact h (Or.inl (by rw [← conj_conj σ, h1, conj_conj]))
    obtain ⟨B, hB⟩ := hy σ
    exact ⟨B, fun i j => by simp only [trivAt, h, h', if_false]; exact hB i j⟩

theorem trivAt_tau (τ : L →+* ℂ) (y : Vars L n → ℂ) (i j : Fin n) :
    trivAt τ y (τ, i, j) = if i = j then 1 else 0 := by simp [trivAt]

theorem trivAt_conj (τ : L →+* ℂ) (y : Vars L n → ℂ) (i j : Fin n) :
    trivAt τ y (ComplexEmbedding.conjugate τ, i, j) = if i = j then 1 else 0 := by simp [trivAt]

theorem ratPt_split (τ : L →+* ℂ) (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) :
    ratPt (γ₀ : Matrix (Fin n) (Fin n) L) =
      vmul (trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) (evPt τ (Matrix.GeneralLinearGroup.map τ γ₀)) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, trivAt, evPt, ratPt]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      have e1 : ∀ k, trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) (ComplexEmbedding.conjugate τ, i, k) =
          if i = k then 1 else 0 := fun k => trivAt_conj τ _ i k
      have e2 : ∀ k, evPt τ (Matrix.GeneralLinearGroup.map τ γ₀) (ComplexEmbedding.conjugate τ, k, j) =
          ((Matrix.GeneralLinearGroup.map τ γ₀)⁻¹).val j k := fun k => by
        simp only [evPt, conj_ne τ, if_false, if_true]
      simp only [vmul, e1, e2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      show (ComplexEmbedding.conjugate τ) (γ₀.val i j) = _
      rw [conj_ratPt γ₀ hg, ← map_inv]
      rfl
    · simp [vmul, trivAt, evPt, ratPt, h1, h2]

theorem vmul_comm_evPt (τ : L →+* ℂ) (y : Vars L n → ℂ)
    (hy : ∀ i j, y (τ, i, j) = (if i = j then 1 else 0) ∧ y (ComplexEmbedding.conjugate τ, i, j) = (if i = j then 1 else 0))
    (g : GL (Fin n) ℂ) : vmul y (evPt τ g) = vmul (evPt τ g) y := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, evPt, (hy _ _).1]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [vmul, evPt, (hy _ _).2, conj_ne τ]
    · simp [vmul, evPt, h1, h2]

theorem evPt_mul (τ : L →+* ℂ) (g h : GL (Fin n) ℂ) : evPt τ (g * h) = vmul (evPt τ g) (evPt τ h) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, evPt, Matrix.mul_apply]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [vmul, evPt, conj_ne τ, Matrix.mul_apply, mul_comm]
    · simp [vmul, evPt, h1, h2]

end

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

