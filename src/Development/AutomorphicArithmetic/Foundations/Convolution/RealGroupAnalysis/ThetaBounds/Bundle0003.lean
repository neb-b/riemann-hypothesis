module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.IsRealComp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

open UpperTheory.ConvolutionTheory.R2.Fo (pl cw)

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private def Dm (s : ℂ) (d : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![d 1, (2 : ℂ)⁻¹ * (d 2 + s⁻¹ * d 3); (2 : ℂ)⁻¹ * (d 2 - s⁻¹ * d 3), d 0]

private theorem pair (s : ℂ) (hs : s ≠ 0) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) (d : Fin 4 → ℂ) :
    ∑ a, ∑ b, Hm s w x a b * Dm s d a b = ∑ i, ((x i w : ℝ) : ℂ) * d i := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_four]
  simp [Hm, Dm]
  field_simp
  ring

private theorem Hm_neg (s : ℂ) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) :
    Hm (-s) w x = (Hm s w x)ᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Hm] <;> ring

private theorem Dm_neg (s : ℂ) (d : Fin 4 → ℂ) : Dm (-s) d = (Dm s d)ᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Dm] <;> ring

private theorem swap (Y H D : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a, ∑ b, (Y.map (starRingEnd ℂ) * Hᵀ) a b * Dᵀ a b = ∑ a, ∑ b, (H * Yᴴ) a b * D a b := by
  simp [Fin.sum_univ_two, Matrix.mul_apply]
  ring

private theorem pair_neg (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a, ∑ b, (-(A + B)) a b * D a b = -(∑ a, ∑ b, A a b * D a b) - ∑ a, ∑ b, B a b * D a b := by
  simp [Fin.sum_univ_two]
  ring

private theorem im_of_sq {s : ℂ} {r : ℝ} (h : s ^ 2 = (r : ℂ)) (hr : r < 0) :
    starRingEnd ℂ s = -s ∧ s ≠ 0 := by
  have hre : s.re * s.re - s.im * s.im = r := by
    have := congrArg Complex.re h
    simpa [pow_two, Complex.mul_re] using this
  have him : s.re * s.im + s.im * s.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two, Complex.mul_im] using this
  have h0 : s.re = 0 := by
    have : s.re * s.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg s.re]
  refine ⟨Complex.ext (by simp [h0]) (by simp), fun hs => ?_⟩
  rw [hs] at hre
  simp at hre
  linarith

private theorem isReal_comp (τ : E →+* ℂ) : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
  InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)

private theorem θ_sq (D : Dat F E) (τ : E →+* ℂ) : (τ D.θ) ^ 2 = (τ.comp (algebraMap F E)) D.δ := by
  rw [← map_pow, D.sq]
  rfl

private theorem θ_im (D : Dat F E) (τ : E →+* ℂ) : starRingEnd ℂ (τ D.θ) = -τ D.θ ∧ τ D.θ ≠ 0 := by
  have hr := isReal_comp (F := F) τ
  refine im_of_sq (r := hr.embedding D.δ) ?_ (D.neg hr.embedding)
  rw [θ_sq, hr.coe_embedding_apply]

private theorem emb_ext (D : Dat F E) {τ τ' : E →+* ℂ} (h : τ.comp (algebraMap F E) = τ'.comp (algebraMap F E))
    (hθ : τ D.θ = τ' D.θ) : τ = τ' := by
  have hc : ∀ c : F, τ (algebraMap F E c) = τ' (algebraMap F E c) := fun c => RingHom.congr_fun h c
  refine RingHom.ext fun x => ?_
  rw [← D.b.sum_repr x, Fin.sum_univ_two, D.b0, D.b1]
  simp only [Algebra.smul_def, map_add (f := _), map_mul, map_one, hc, hθ]

private theorem conj_comp (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap F E) = τ.comp (algebraMap F E) := by
  have hr := ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ)
  ext x
  have := RingHom.congr_fun hr x
  simpa [ComplexEmbedding.conjugate_coe_eq] using congrArg id this

private theorem pl_conj (τ : E →+* ℂ) : pl (F := F) (ComplexEmbedding.conjugate τ) = pl (F := F) τ := by
  unfold pl
  rw [conj_comp]

private theorem conj_θ (D : Dat F E) (τ : E →+* ℂ) : (ComplexEmbedding.conjugate τ) D.θ = -τ D.θ := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact (θ_im D τ).1

private theorem conj_ne (D : Dat F E) (τ : E →+* ℂ) : τ ≠ ComplexEmbedding.conjugate τ := fun h => by
  have h1 := conj_θ D τ
  rw [← h] at h1
  have h2 := (θ_im D τ).2
  exact h2 (self_eq_neg.1 h1)

private theorem pl_fiber (D : Dat F E) {τ τ' : E →+* ℂ} (h : pl (F := F) τ' = pl (F := F) τ) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : τ'.comp (algebraMap F E) = τ.comp (algebraMap F E) := by
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact h
    · rw [← h]
      exact (ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ')).symm
  have h2 : (τ' D.θ) ^ 2 = (τ D.θ) ^ 2 := by rw [θ_sq, θ_sq, h1]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ h2 with h3 | h3
  · exact Or.inl (emb_ext D h1 h3)
  · exact Or.inr (emb_ext D (h1.trans (conj_comp τ).symm) (h3.trans (conj_θ D τ).symm))

private theorem pl_surj (D : Dat F E) (w : InfinitePlace F) : ∃ τ : E →+* ℂ, pl (F := F) τ = w := by
  haveI : Module.Finite F E := Module.Finite.of_basis D.b
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
  refine ⟨w'.embedding, ?_⟩
  unfold pl
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw'

private theorem sum_pl (D : Dat F E) (f : (E →+* ℂ) → ℂ) (g : InfinitePlace F → ℂ)
    (h : ∀ τ, f τ + f (ComplexEmbedding.conjugate τ) = g (pl (F := F) τ)) : ∑ τ, f τ = ∑ w, g w := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ => pl (F := F) τ) f]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨τ, rfl⟩ := pl_surj D w
  have hf : (Finset.univ.filter fun τ' : E →+* ℂ => pl (F := F) τ' = pl (F := F) τ) = {τ, ComplexEmbedding.conjugate τ} := by
    ext τ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨pl_fiber D, ?_⟩
    rintro (rfl | rfl)
    · rfl
    · exact pl_conj τ
  rw [← h τ, ← Finset.sum_pair (conj_ne D τ), ← hf]

variable (D : Dat F E) (O : Fo.Ops F) (v : V4 F)

private theorem X_apply (τ : E →+* ℂ) (a b : Fin 2) (ψ' : S4 F) :
    (O.X D τ a b ψ').1 v = Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i)) a b * ψ'.1 v := by
  fin_cases a <;> fin_cases b <;> simp [Fo.Ops.X, Hm, O.x_apply, Fo.cw] <;> ring

private theorem DX_apply (τ : E →+* ℂ) (a b : Fin 2) (ψ' : S4 F) :
    (O.DX D τ a b ψ').1 v = Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) a b := by
  fin_cases a <;> fin_cases b <;> simp [Fo.Ops.DX, Dm] <;> ring

private theorem dE_apply (τ : E →+* ℂ) (i j : Fin 2) (ψ' : S4 F) :
    (O.dE D τ i j ψ').1 v = -(if i = j then ψ'.1 v else 0) -
      ∑ b, Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i)) j b *
        Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) i b := by
  unfold Fo.Ops.dE
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  by_cases h : i = j
  · simp [h, Module.End.mul_apply, X_apply, DX_apply]
  · simp [h, Module.End.mul_apply, X_apply, DX_apply]

private theorem dL_apply (Y : Lie E 2) (ψ' : S4 F) :
    (O.dL D Y ψ').1 v = ∑ τ : E →+* ℂ, ∑ i, ∑ j, coord τ (Y i j) * (O.dE D τ i j ψ').1 v := by
  simp [Fo.Ops.dL, LinearMap.sum_apply, Finset.sum_apply]

private def T (Y : Lie E 2) (ψ' : S4 F) (τ : E →+* ℂ) : ℂ :=
  ∑ a, ∑ b, ((Matrix.of Y).map (coord τ) * Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i))) a b *
    Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) a b

private theorem T_conj (Y : Lie E 2) (ψ' : S4 F) (τ : E →+* ℂ) :
    T D O v Y ψ' (ComplexEmbedding.conjugate τ) =
      ∑ a, ∑ b, (Hm (τ D.θ) (pl (F := F) τ) (fun i => TR.pInf F (v i)) * ((Matrix.of Y).map (coord τ))ᴴ) a b *
        Dm (τ D.θ) (fun i => (O.d (pl (F := F) τ) i ψ').1 v) a b := by
  have hy : (Matrix.of Y).map (coord (ComplexEmbedding.conjugate τ)) =
      ((Matrix.of Y).map (coord τ)).map (starRingEnd ℂ) := by
    ext a b
    simp [GlobalTheory.IsoPull.coord_conj]
  unfold T
  rw [pl_conj, conj_θ, Hm_neg, Dm_neg, hy]
  exact swap _ _ _

private theorem term (Y : Lie E 2) (hY : (Matrix.of Y).trace = 0) (ψ' : S4 F) (τ : E →+* ℂ) :
    ∑ i, ∑ j, coord τ (Y i j) * (O.dE D τ i j ψ').1 v = -T D O v Y ψ' τ := by
  have tr : coord τ (Y 0 0) + coord τ (Y 1 1) = 0 := by
    rw [Matrix.trace_fin_two] at hY
    rw [← map_add (f := _)]
    have : Y 0 0 + Y 1 1 = 0 := hY
    rw [this, map_zero]
  simp only [dE_apply, T, Fin.sum_univ_two, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_true, if_false]
  linear_combination (-(ψ'.1 v)) * tr

end UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators

end

open UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators in
theorem UpperTheory.ConvolutionTheory.R2.Ff.vfOps :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), VfOps D O := by
  intro F E _ _ _ _ _ _ _ D O Y hY v x' hx φ
  rw [Finset.sum_comm, dL_apply]
  simp_rw [term D O v Y hY φ]
  symm
  refine sum_pl D (fun τ => -T D O v Y φ τ) _ fun τ => ?_
  have h1 := pair (τ D.θ) (θ_im D τ).2 (pl (F := F) τ) x' (fun i => (O.d (pl (F := F) τ) i φ).1 v)
  rw [hx τ, pair_neg] at h1
  rw [← h1, T_conj]
  unfold T
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormMatrixMulLeTwo
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem ht_le {E : Type} [Field E] [NumberField E] (y : GL (Fin 2) (Cinf E)) :
    ‖toL y.val‖ ≤ GlobalTheory.CuspRep.height y ∧ ‖toL (y⁻¹).val‖ ≤ GlobalTheory.CuspRep.height y := by
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  refine ⟨?_, ?_⟩ <;> first | (unfold GlobalTheory.CuspRep.height; linarith) | fail "height"

private theorem norm_matrix_mul_le_two {E : Type} [Field E] [NumberField E]
    (x x' : Matrix (Fin 2) (Fin 2) (Cinf E)) : ‖toL (x * x')‖ ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by
  have h0 : 0 ≤ 2 * ‖toL x‖ * ‖toL x'‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  have e1 : ∀ a b, ‖x a b w‖ ≤ ‖toL x‖ := fun a b =>
    (norm_le_pi_norm (x a b) w).trans ((norm_le_pi_norm (toL x a) b).trans (norm_le_pi_norm (toL x) a))
  have e2 : ∀ a b, ‖x' a b w‖ ≤ ‖toL x'‖ := fun a b =>
    (norm_le_pi_norm (x' a b) w).trans ((norm_le_pi_norm (toL x' a) b).trans (norm_le_pi_norm (toL x') a))
  have e : toL (x * x') i j w = x i 0 w * x' 0 j w + x i 1 w * x' 1 j w := by
    show (x * x') i j w = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  have p : ∀ k, ‖x i k w * x' k j w‖ ≤ ‖toL x‖ * ‖toL x'‖ := fun k => by
    rw [norm_mul]
    exact mul_le_mul (e1 _ _) (e2 _ _) (norm_nonneg _) (norm_nonneg _)
  have := norm_add_le (x i 0 w * x' 0 j w) (x i 1 w * x' 1 j w)
  linarith [p 0, p 1]

private theorem cont_toL {E : Type} [Field E] [NumberField E] :
    Continuous fun x : Matrix (Fin 2) (Fin 2) (Cinf E) => toL x :=
  continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j

theorem UpperTheory.ConvolutionTheory.R2.Ff.htLe :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], HtLe E := by
  intro E _ _ _
  refine ⟨?_, fun y => ⟨?_, ?_, fun y' => ?_⟩⟩
  · unfold Ht
    have c1 : Continuous fun y : GL (Fin 2) (Cinf E) => toL y.val := cont_toL.comp Units.continuous_val
    have c2 : Continuous fun y : GL (Fin 2) (Cinf E) => toL (y⁻¹).val :=
      cont_toL.comp (Units.continuous_val.comp continuous_inv)
    exact (continuous_const.add c1.norm).add c2.norm
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    unfold Ht
    linarith
  · have h := ht_le y
    have h1 := GlobalTheory.CuspRep.one_le_height y
    unfold Ht
    linarith [h.1, h.2]
  · have n1 := norm_nonneg (toL y.val)
    have n2 := norm_nonneg (toL (y⁻¹).val)
    have n3 := norm_nonneg (toL y'.val)
    have n4 := norm_nonneg (toL (y'⁻¹).val)
    have m1 := norm_matrix_mul_le_two y.val y'.val
    have m2 := norm_matrix_mul_le_two (y'⁻¹).val (y⁻¹).val
    have e1 : (y * y').val = y.val * y'.val := rfl
    have e2 : ((y * y')⁻¹).val = (y'⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
    unfold Ht
    rw [e1, e2]
    nlinarith [mul_nonneg n1 n3, mul_nonneg n1 n4, mul_nonneg n2 n3, mul_nonneg n2 n4]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OmGrowth
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem abs_le_of_continuous_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →+ ℝ) (hf : Continuous f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |f z| ≤ B * ‖z‖ := by
  refine ⟨‖f.toRealLinearMap hf‖, norm_nonneg _, fun z => ?_⟩
  have h := (f.toRealLinearMap hf).le_opNorm z
  simpa using h

private noncomputable def eU {E : Type} [Field E] [NumberField E] (z : InfinitePlace E → ℂ) : (Cinf E)ˣ where
  val := fun w => Complex.exp (z w)
  inv := fun w => Complex.exp (-z w)
  val_inv := by
    funext w
    change Complex.exp (z w) * Complex.exp (-z w) = 1
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by
    funext w
    change Complex.exp (-z w) * Complex.exp (z w) = 1
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

private theorem continuous_eU {E : Type} [Field E] [NumberField E] :
    Continuous (eU (E := E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w)
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w).neg

private theorem eU_add {E : Type} [Field E] [NumberField E] (z z' : InfinitePlace E → ℂ) :
    eU (z + z') = eU z * eU z' := by
  refine Units.ext ?_
  funext w
  change Complex.exp (z w + z' w) = Complex.exp (z w) * Complex.exp (z' w)
  rw [Complex.exp_add]

private theorem eU_log {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) :
    eU (fun w => Complex.log (s.val w)) = s := by
  refine Units.ext ?_
  funext w
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  change Complex.exp (Complex.log (s.val w)) = s.val w
  exact Complex.exp_log h0

private theorem norm_log_le {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) (w : InfinitePlace E) :
    ‖Complex.log (s.val w)‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) + Real.pi := by
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  have h1 : s⁻¹.val w ≠ 0 := right_ne_zero_of_mul_eq_one h
  have p0 : 0 < ‖s.val w‖ := norm_pos_iff.2 h0
  have p1 : 0 < ‖s⁻¹.val w‖ := norm_pos_iff.2 h1
  have hprod : ‖s.val w‖ * ‖s⁻¹.val w‖ = 1 := by rw [← norm_mul, h, norm_one]
  have b0 : ‖s.val w‖ ≤ ‖s.val‖ := norm_le_pi_norm s.val w
  have b1 : ‖s⁻¹.val w‖ ≤ ‖s⁻¹.val‖ := norm_le_pi_norm s⁻¹.val w
  have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
  have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
  have l0 : Real.log ‖s.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p0 (by linarith)
  have l1 : Real.log ‖s⁻¹.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p1 (by linarith)
  have hs : Real.log ‖s.val w‖ + Real.log ‖s⁻¹.val w‖ = 0 := by
    rw [← Real.log_mul p0.ne' p1.ne', hprod, Real.log_one]
  have hre : |(Complex.log (s.val w)).re| ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) := by
    rw [Complex.log_re, abs_le]
    constructor <;> linarith
  have him : |(Complex.log (s.val w)).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

theorem UpperTheory.ConvolutionTheory.R2.Ff.omGrowth :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), OmGrowth F E := by
  intro F E _ _ _ _ _ _ _ _D
  have hN : Continuous (fun s : (Cinf E)ˣ => ideleNorm F E (infId E s)) :=
    continuous_ideleNorm.comp (continuous_infId E)
  refine ⟨hN, fun ω hω => ?_⟩
  let c : (Cinf E)ˣ → ℝ := fun s => ‖((ω (ideleNorm F E (infId E s)) : ℂˣ) : ℂ)‖
  have hc : Continuous c := (Units.continuous_val.comp (hω.comp hN)).norm
  have hpos : ∀ s, 0 < c s := fun s => norm_pos_iff.2 (Units.ne_zero _)
  have hmul : ∀ s s', c (s * s') = c s * c s' := by
    intro s s'
    simp only [c, map_mul, Units.val_mul, norm_mul]
  let f : (InfinitePlace E → ℂ) →+ ℝ :=
    { toFun := fun z => Real.log (c (eU z))
      map_zero' := by
        have h1 : eU (0 : InfinitePlace E → ℂ) = 1 := by
          have := eU_add (0 : InfinitePlace E → ℂ) 0
          rw [add_zero] at this
          exact left_eq_mul.1 this
        have h2 : c 1 = 1 := by simp [c]
        change Real.log (c (eU 0)) = 0
        rw [h1, h2, Real.log_one]
      map_add' := fun z z' => by
        change Real.log (c (eU (z + z'))) = Real.log (c (eU z)) + Real.log (c (eU z'))
        rw [eU_add, hmul, Real.log_mul (hpos _).ne' (hpos _).ne'] }
  have hf : Continuous f :=
    (hc.comp continuous_eU).log fun z => (hpos _).ne'
  obtain ⟨B, hB0, hB⟩ := abs_le_of_continuous_add f hf
  refine ⟨Real.exp (B * Real.pi), ⌈B⌉₊, fun s => ?_⟩
  change c s ≤ _
  set H : ℝ := 1 + ‖s.val‖ + ‖s⁻¹.val‖ with hH
  have hH1 : 1 ≤ H := by
    have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
    have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
    linarith
  have hH0 : 0 < H := by linarith
  have hL : 0 ≤ Real.log H := Real.log_nonneg hH1
  let z : InfinitePlace E → ℂ := fun w => Complex.log (s.val w)
  have hz : ‖z‖ ≤ Real.log H + Real.pi :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => norm_log_le s w
  have hfz : f z = Real.log (c s) := by
    change Real.log (c (eU z)) = _
    rw [eU_log]
  have h1 : Real.log (c s) ≤ B * (Real.log H + Real.pi) := by
    rw [← hfz]
    exact (le_abs_self _).trans ((hB z).trans (mul_le_mul_of_nonneg_left hz hB0))
  have h2 : B * (Real.log H + Real.pi) ≤ B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H := by
    have : B * Real.log H ≤ (⌈B⌉₊ : ℝ) * Real.log H :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil B) hL
    linarith
  calc c s = Real.exp (Real.log (c s)) := (Real.exp_log (hpos s)).symm
    _ ≤ Real.exp (B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H) := Real.exp_le_exp.2 (h1.trans h2)
    _ = Real.exp (B * Real.pi) * H ^ ⌈B⌉₊ := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hH0]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ParCont
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem parCont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Continuous (TR.infGL F 2) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((TR.continuous_infEq F).prodMk continuous_const :
    Continuous fun x : TR.Rinf F => ((TR.infEq F x, 0) : InfiniteAdeleRing F × Af F))))

private theorem parCont_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {c : ℝ → GL (Fin 2) (TR.Rinf F)} {Y : TR.Lie F 2} (h : Par c Y) :
    Continuous fun t => (c t).val := by
  have h0 : ContinuousAt (fun t => (c t).val) 0 := h.2.continuousAt
  refine continuous_iff_continuousAt.2 fun t => ?_
  have e : (fun s => (c s).val) = fun s => (c t).val * (c (s - t)).val := by
    funext s
    rw [← Units.val_mul, ← h.1, add_sub_cancel]
  rw [e]
  have hs : ContinuousAt (fun s : ℝ => s - t) t := (continuous_id.sub continuous_const).continuousAt
  have h0' : ContinuousAt (fun t => (c t).val) ((fun s : ℝ => s - t) t) := by
    simpa using h0
  exact continuousAt_const.mul (ContinuousAt.comp (f := fun s : ℝ => s - t) h0' hs)

theorem UpperTheory.ConvolutionTheory.R2.Ff.parCont :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ParCont F := by
  intro F _ _ _
  refine ⟨parCont_infGL F, fun c Y h => ?_⟩
  have h1 : c 0 = 1 := by
    have := h.1 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← h.1, add_neg_cancel, h1])
  have hv := parCont_val h
  refine ⟨h1, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, ?_⟩
  · have : (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val) = fun t => (c (-t)).val := by
      funext t; rw [hinv]
    change Continuous (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val)
    rw [this]
    exact hv.comp continuous_neg
  · intro s t
    change c (-(s + t)) = c (-s) * c (-t)
    rw [neg_add, h.1]
  · have h2 : HasDerivAt (fun t => TR.toL (c t).val) Y (-(0 : ℝ)) := by simpa using h.2
    have := HasDerivAt.scomp (0 : ℝ) h2 (hasDerivAt_neg 0)
    simpa [Function.comp_def] using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Transl
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.transl :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F), Transl W M := by
  intro F E _ _ _ _ _ _ _ D W M f φ h h₀
  have hnu : nu F (h * h₀) = nu F h * nu F h₀ := by
    simp only [nu, map_mul]
  unfold lift
  refine congrArg (fun u : G1 F → ℂ => ∫ g in M.D, u g ∂M.μ) (funext fun g => ?_)
  simp only [hnu, dM_mul, map_mul, Module.End.mul_apply, mul_assoc]
end

