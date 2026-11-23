module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PartialTrace
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0012

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.AestronglyMeasurablePsiInner
section
noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def ob3PsiCoef (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (ξ c) (∑ d, (cond dual ((g⁻¹) d c) (g c d)) • Ψ g (ζ d))

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_weighted_memLp {v₀ : T.V} (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (v w : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) := by
  have hC : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h := datumEmbedding_highest_ne_zero hgap hP hv₀
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have hmem : ∀ u, (⟨uniformisationL2 ε Ψ v₀ u, datumEmbedding_mem_smooth hP v₀ u⟩ : smD ε (rreg ε)) ∈
      genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) := fun u =>
    Submodule.mem_sInf.2 (fun S hS => hS.1 (Submodule.mem_comap.2 (Submodule.subset_span ⟨u, rfl⟩)))
  have h := (hW _ (hmem v) _ (hmem w)).const_mul (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)⁻¹)
  refine h.congr_norm ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun g => by
      simp only
      rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
      field_simp)
  · simp only
    rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
    congr 1
    field_simp

end Psi

theorem norm_unitary_inv_entry {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖(Formalism.MainNotions.S.umat g)⁻¹ d c‖ = ‖Formalism.MainNotions.S.umat g c d‖ := by
  have hg : inUJ ε (Formalism.MainNotions.S.umat g) := g.2
  have h1 : (Jm ε * (Formalism.MainNotions.S.umat g)ᴴ * Jm ε) * Formalism.MainNotions.S.umat g = 1 := by
    calc (Jm ε * (Formalism.MainNotions.S.umat g)ᴴ * Jm ε) * Formalism.MainNotions.S.umat g
        = Jm ε * ((Formalism.MainNotions.S.umat g)ᴴ * Jm ε * Formalism.MainNotions.S.umat g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, S7.Jm_mul_self]
  rw [Matrix.inv_eq_left_inv h1]
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem norm_unitary_entry_le_sqrt_hs {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖Formalism.MainNotions.S.umat g c d‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  rw [← Real.sqrt_sq (norm_nonneg (Formalism.MainNotions.S.umat g c d))]
  apply Real.sqrt_le_sqrt
  unfold S7.hs
  calc ‖Formalism.MainNotions.S.umat g c d‖ ^ 2 ≤ ∑ j, ‖Formalism.MainNotions.S.umat g c j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.umat g c j‖ ^ 2) (fun j _ => sq_nonneg _) (mem_univ d)
    _ ≤ ∑ i, ∑ j, ‖Formalism.MainNotions.S.umat g i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.umat g i j‖ ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (mem_univ c)

theorem norm_dual_entry_le_sqrt_hs (dual : Bool) {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  cases dual
  · exact norm_unitary_entry_le_sqrt_hs g c d
  · simp only [cond]; rw [norm_unitary_inv_entry]; exact norm_unitary_entry_le_sqrt_hs g c d

theorem continuous_dual_entry (dual : Bool) {ε : Fin n → Bool} (c d : Fin n) :
    Continuous (fun g : Formalism.REAL.UJ ε => cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)) := by
  cases dual
  · exact (continuous_apply d).comp ((continuous_apply c).comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val))
  · have e : (fun g : Formalism.REAL.UJ ε => cond true ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)) =
        fun g : Formalism.REAL.UJ ε => ((((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
          Matrix (Fin n) (Fin n) ℂ) d c) := by
      funext g
      simp only [cond, Formalism.MainNotions.S.umat, Matrix.coe_units_inv]
    rw [e]
    exact (continuous_apply c).comp ((continuous_apply d).comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val))

section Psi2

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem aestronglyMeasurable_psi_inner (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) (Formalism.REAL.muG ε) := by
  have hΨm : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) :=
    (hP.2.2.2.2 (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)).aestronglyMeasurable
  exact (continuous_const.inner (continuous_id.clm_apply continuous_const)).comp_aestronglyMeasurable hΨm

theorem psi_inner_memLp (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hΨ : MemLp (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    hP.2.2.2.2 (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)
  refine hΨ.of_le_mul (c := ‖x‖ * ‖y‖) (aestronglyMeasurable_psi_inner hP x y) (Filter.Eventually.of_forall fun g => ?_)
  calc ‖inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)‖ ≤ ‖x‖ * ‖Ψ (Formalism.MainNotions.S.umat g) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖x‖ * ‖y‖ * ‖Ψ (Formalism.MainNotions.S.umat g)‖ := by ring

theorem psi_coef_memLp_of_weighted (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have e : (fun g : Formalism.REAL.UJ ε => ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) = fun g => ∑ c, ∑ d,
      cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d) *
        inner ℂ (ξ c) (Ψ (Formalism.MainNotions.S.umat g) (ζ d)) := by
    funext g
    simp only [ob3PsiCoef, inner_sum, inner_smul_right]
  rw [e]
  refine memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => ?_
  refine (hWT (ζ d) (ξ c)).of_le (((continuous_dual_entry dual c d).aestronglyMeasurable).mul (aestronglyMeasurable_psi_inner hP _ _))
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (norm_dual_entry_le_sqrt_hs dual g c d) (norm_nonneg _)

theorem psi_pairing_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u' v' : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')) (Formalism.REAL.muG ε) :=
  (psi_coef_memLp_of_weighted dual hP hWT ξ ζ).star.integrable_mul (psi_inner_memLp hP' u' v')

end Psi2

theorem clm_mul_apply_eq_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A B : E →L[ℂ] E) (x : E) :
    (A * B) x = A (B x) := rfl

theorem dual_entry_mul_sum (dual : Bool) (K H : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    cond dual ((K * H)⁻¹ d c) ((K * H) c d) =
      ∑ e, cond dual (K⁻¹ e c) (K c e) * cond dual (H⁻¹ d e) (H e d) := by
  cases dual
  · simp only [cond, Matrix.mul_apply]
  · simp only [cond, Matrix.mul_inv_rev, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

section Psi3

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_k_left_equivariant {Λ : Fin n → ℝ} {T : S7.KType ε Λ} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hK : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂) (k : S7.KG ε) (h : Formalism.REAL.UJ ε) :
    Ψ (S7.toMK k * Formalism.MainNotions.S.umat h) = T.op k * Ψ (Formalism.MainNotions.S.umat h) := by
  have e := hK k 1 (Formalism.MainNotions.S.umat h) h.2
  have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
  have h2 : T.op 1 = 1 := by simp [S7.KType.op]
  rwa [h1, mul_one, h2, mul_one] at e

theorem psi_coef_k_left_translate (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (k : S7.KG ε) (h : Formalism.REAL.UJ ε)
    (ξ ζ : Fin n → T.V) :
    ob3PsiCoef dual Ψ ξ ζ (S7.toMK k * Formalism.MainNotions.S.umat h) =
      ob3PsiCoef dual Ψ (fun e => ∑ c, starRingEnd ℂ (cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e)) •
        (ContinuousLinearMap.adjoint (T.op k)) (ξ c)) ζ (Formalism.MainNotions.S.umat h) := by
  have hΨ := psi_k_left_equivariant hP.1 k h
  have hL : ob3PsiCoef dual Ψ ξ ζ (S7.toMK k * Formalism.MainNotions.S.umat h) = ∑ c, ∑ d, ∑ e,
      cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) := by
    simp only [ob3PsiCoef, hΨ, dual_entry_mul_sum, clm_mul_apply_eq_comp, inner_sum, inner_smul_right,
      Finset.sum_mul]
  have hR : ob3PsiCoef dual Ψ (fun e => ∑ c, starRingEnd ℂ (cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e)) •
        (ContinuousLinearMap.adjoint (T.op k)) (ξ c)) ζ (Formalism.MainNotions.S.umat h) = ∑ e, ∑ d, ∑ c,
      cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) := by
    simp only [ob3PsiCoef, inner_sum, inner_smul_right, sum_inner, inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left, RCLike.conj_conj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  rw [hL, hR]
  calc _ = ∑ c, ∑ e, ∑ d, cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun e _ => Finset.sum_comm

theorem psi_pairing_vanishing_spread (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V} (hv₀' : v₀' ≠ 0)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (h0 : ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0) :
    ∀ (ξ ζ : Fin n → T.V) (u' v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0 := by
  let W : Submodule ℂ T'.V :=
    { carrier := {u' | ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
        starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
          ∂(Formalism.REAL.muG ε) = 0}
      add_mem' := fun {a b} ha hb ξ ζ v' => by
        simp only [inner_add_left, mul_add]
        rw [integral_add (psi_pairing_integrable dual hP hP' hWT ξ ζ a v') (psi_pairing_integrable dual hP hP' hWT ξ ζ b v'),
          ha ξ ζ v', hb ξ ζ v', add_zero]
      zero_mem' := fun ξ ζ v' => by simp only [inner_zero_left, mul_zero, integral_zero]
      smul_mem' := fun c x hx ξ ζ v' => by
        have e : (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
            inner ℂ (c • x) (Ψ' (Formalism.MainNotions.S.umat g) v')) = fun g => starRingEnd ℂ c *
              (starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ x (Ψ' (Formalism.MainNotions.S.umat g) v')) := by
          funext g
          rw [inner_smul_left]
          ring
        show ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
            inner ℂ (c • x) (Ψ' (Formalism.MainNotions.S.umat g) v') ∂(Formalism.REAL.muG ε) = 0
        rw [e, integral_const_mul, hx ξ ζ v', mul_zero] }
  have hst : ∀ k : S7.KG ε, ∀ v ∈ W, T'.op k v ∈ W := by
    intro k u hu ξ ζ v'
    let kk : Formalism.REAL.UJ ε := ⟨((k : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ), (k : S7.UJ ε).2⟩
    rw [← integral_mul_left_eq_self (μ := Formalism.REAL.muG ε) _ kk]
    have e : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat (kk * g) =
        S7.toMK k * Formalism.MainNotions.S.umat g := fun g => rfl
    simp only [e, psi_coef_k_left_translate dual hP k, psi_k_left_equivariant hP'.1 k, clm_mul_apply_eq_comp,
      ContinuousLinearMap.inner_map_map_of_mem_unitary (T'.τ k).2]
    exact hu _ ζ v'
  have hv : v₀' ∈ W := h0
  rcases T'.irred W hst with hW | hW
  · exact absurd ((Submodule.mem_bot ℂ).1 (hW ▸ hv)) hv₀'
  · intro ξ ζ u' v'
    have hu : u' ∈ W := hW ▸ Submodule.mem_top
    exact hu ξ ζ v'

end Psi3

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PtrScalar
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Helpers
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tpsc_single_mem {S : Submodule ℂ M} {x : M} (hx : x ∈ S) (c : Fin n) :
    (Pi.single c x : Fin n → M) ∈ tensSub S := by
  refine Submodule.mem_pi.2 fun d _ => ?_
  by_cases h : d = c
  · subst h; simpa using hx
  · simp [h]

theorem tpsc_coord_mem {S : Submodule ℂ M} {f : Fin n → M} (hf : f ∈ tensSub S) (c : Fin n) : f c ∈ S :=
  Submodule.mem_pi.1 hf c (Set.mem_univ _)

theorem tpsc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensV E a b (Pi.single c x) = Pi.single c (E a b x) + if b = c then Pi.single a x else 0 := by
  funext d
  rw [tensV_coord]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp [Pi.single_apply, hdc, hda, hbc] <;> split_ifs <;> simp_all

theorem tpsc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensVd E a b (Pi.single c x) = Pi.single c (E a b x) - if a = c then Pi.single b x else 0 := by
  funext d
  rw [tensVd_coord]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp [Pi.single_apply, hdc, hdb, hac] <;> split_ifs <;> simp_all

end Helpers

def tpscK (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual (star (k c d)) (k c d)

theorem tpscK_rows {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (c c' : Fin n) : ∑ d, tpscK dual k c' d * star (tpscK dual k c d) = if c' = c then 1 else 0 := by
  have hu : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  cases dual
  · have := congrFun (congrFun hu c') c
    simpa [tpscK, Matrix.mul_apply, Matrix.one_apply] using this
  · have := congrFun (congrFun hu c) c'
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [show (∑ d, star (k c' d) * k c d) = ∑ d, k c d * star (k c' d) from
      Finset.sum_congr rfl fun d _ => mul_comm _ _, this]
    by_cases h : c' = c
    · subst h; simp
    · simp [h, Ne.symm h]

theorem tpscK_cols {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (e d : Fin n) : ∑ c, tpscK dual k c d * star (tpscK dual k c e) = if e = d then 1 else 0 := by
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  cases dual
  · have := congrFun (congrFun hu e) d
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_false]
    rw [show (∑ c, k c d * star (k c e)) = ∑ c, star (k c e) * k c d from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
  · have := congrFun (congrFun hu d) e
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [this]
    by_cases h : e = d
    · subst h; simp
    · simp [h, Ne.symm h]

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {A : Module.End ℂ (Fin n → D)}

theorem ptr_mem {dual : Bool} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ x ∈ genSub E V, ptr A x ∈ genSub E V := by
  intro x hx
  rw [ptr_apply]
  exact Submodule.sum_mem _ fun c _ => tpsc_coord_mem (hA.1 _ (tpsc_single_mem hx c)) c

theorem ptr_comm {dual : Bool} (hE : IsGlRep E) (hA : IsGKEndo dual ε σ E (genSub E V) A) (a b : Fin n) :
    ∀ x ∈ genSub E V, ptr A (E a b x) = E a b (ptr A x) := by
  intro x hx
  have hs : ∀ c, (Pi.single c x : Fin n → D) ∈ tensSub (genSub E V) := fun c => tpsc_single_mem hx c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ptr_apply, ptr_apply, map_sum]
  cases dual
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) +
        (if c = a then A (Pi.single c x) b else 0) - (if b = c then A (Pi.single a x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensV E a b (Pi.single c x) - (if b = c then Pi.single a x else 0) := by
        rw [tpsc_tensV_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_false] at h2
      rw [h1, map_sub, h2, Pi.sub_apply, tensV_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, add_sub_cancel_right]
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) -
        (if c = b then A (Pi.single c x) a else 0) + (if a = c then A (Pi.single b x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensVd E a b (Pi.single c x) + (if a = c then Pi.single b x else 0) := by
        rw [tpsc_tensVd_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_true] at h2
      rw [h1, map_add (f := _), h2, Pi.add_apply, tensVd_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_add_cancel]

theorem tpsc_kDiag (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    kDiag dual σ k f c = ∑ d, tpscK dual k c d • σ k (f d) := rfl

theorem ptr_kcomm {dual : Bool} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k (x : H) →
      ((ptr A y : D) : H) = σ k ((ptr A x : D) : H) := by
  intro k hk x hx y hy hxy
  have hku := hk.1
  let g : Fin n → Fin n → D := fun c d => star (tpscK dual k c d) • x
  have hg : ∀ c, g c ∈ tensSub (genSub E V) := fun c =>
    Submodule.mem_pi.2 fun d _ => Submodule.smul_mem _ _ hx
  have hgs : ∀ c, g c = ∑ e, star (tpscK dual k c e) • (Pi.single e x : Fin n → D) := by
    intro c; funext d
    simp [g, Finset.sum_apply, Pi.single_apply]
  have hf' : ∀ c, (fun c' => (((Pi.single c y : Fin n → D) c' : D) : H)) =
      kDiag dual σ k (fun d => ((g c d : D) : H)) := by
    intro c; funext c'
    rw [tpsc_kDiag]
    simp only [g, Submodule.coe_smul, map_smul, smul_smul]
    rw [← Finset.sum_smul, tpscK_rows hku dual c c', ← hxy]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  have hAf : ∀ c c', ((A (Pi.single c y) c' : D) : H) = ∑ d, tpscK dual k c' d •
      σ k (∑ e, star (tpscK dual k c e) • ((A (Pi.single e x) d : D) : H)) := by
    intro c c'
    have := congrFun (hA.2.2 k hk _ (hg c) _ (tpsc_single_mem hy c) (hf' c)) c'
    rw [this, tpsc_kDiag, hgs c]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ptr_apply, ptr_apply, Submodule.coe_sum, Submodule.coe_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hAf, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, tpscK_cols hku dual]
  simp [ite_smul]

end

theorem ptr_scalar (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ptr A x = c • x :=
  data_end_scalar hgap hσ hD hV hc hVK (ptr A) (ptr_mem hA) (fun a b => ptr_comm hD.glRep hA a b)
    (ptr_kcomm hσ hD hA)

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

