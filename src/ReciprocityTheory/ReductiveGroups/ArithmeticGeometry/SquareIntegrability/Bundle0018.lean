module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0016

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitOA
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem so_prod_norm (x : E) : ∏ σ : E →+* ℂ, ‖σ x‖ = |(Algebra.norm ℚ x : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun σ => rfl),
    ← norm_prod, ← h, eq_ratCast, Complex.norm_ratCast]

theorem so_norm_ge (w : E) (hw0 : w ≠ 0)
    (hw : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n) :
    1 ≤ |Algebra.norm ℚ w| * |((discr E : ℤ) : ℚ)| := by
  classical
  set B := RingOfIntegers.basis E
  set b := NumberField.integralBasis E
  have hb : ∀ i, b i = (B i : E) := fun i => NumberField.integralBasis_apply E i
  choose N0 hN using fun i j => hw (B i * B j)
  set N : Matrix _ _ ℤ := Matrix.of N0 with hNdef
  have hTA : Algebra.traceMatrix ℚ b * Algebra.leftMulMatrix b w = (N.map (Int.cast : ℤ → ℚ)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.map_apply, hNdef, Matrix.of_apply, ← hN i j]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have e : w * (b i * b j) = b i * (w * b j) := by ring
    rw [show ((B i * B j : 𝓞 E) : E) = b i * b j by rw [hb, hb]; push_cast; ring, e]
    conv_rhs => rw [← b.sum_repr (w * b j)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet := congrArg Matrix.det hTA
  rw [Matrix.det_mul, ← Algebra.discr_def, ← Algebra.norm_eq_matrix_det, ← NumberField.coe_discr,
    ← Int.cast_det] at hdet
  have hne : N.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdet
    rcases mul_eq_zero.1 hdet with h1 | h1
    · exact NumberField.discr_ne_zero E (by exact_mod_cast h1)
    · exact hw0 ((Algebra.norm_eq_zero_iff).1 h1)
  have h1 : (1 : ℚ) ≤ |(N.det : ℚ)| := by exact_mod_cast Int.one_le_abs hne
  calc (1 : ℚ) ≤ |(N.det : ℚ)| := h1
    _ = |Algebra.norm ℚ w| * |((discr E : ℤ) : ℚ)| := by
      rw [← hdet, abs_mul, mul_comm]

theorem so_sum_sq_ge [IsCMField E] (w : E) (hw0 : w ≠ 0)
    (hw : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n) :
    2 ≤ PT.rd E ^ 2 * ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := by
  haveI := NumberField.IsCMField.isTotallyComplex E
  have hcard : (Finset.univ : Finset (E →+* ℂ)).card = Module.finrank ℚ E := by
    rw [Finset.card_univ, NumberField.Embeddings.card]
  have hn2 : 2 ≤ Module.finrank ℚ E := by
    have h1 := NumberField.IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hnR : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast (by omega : 0 < Module.finrank ℚ E)
  have hwt : ∑ _σ ∈ (Finset.univ : Finset (E →+* ℂ)), (1 / (Module.finrank ℚ E : ℝ)) = 1 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  have amgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Module.finrank ℚ E : ℝ))
    (fun σ : E →+* ℂ => ‖σ w‖ ^ 2) (fun _ _ => by positivity) hwt (fun _ _ => by positivity)
  rw [Real.finsetProd_rpow Finset.univ (fun σ : E →+* ℂ => ‖σ w‖ ^ 2) (fun _ _ => by positivity),
    Finset.prod_pow, so_prod_norm, ← Finset.mul_sum] at amgm
  have hX : 0 ≤ |(Algebra.norm ℚ w : ℝ)| := abs_nonneg _
  have hY : 0 ≤ |(discr E : ℝ)| := abs_nonneg _
  have key : (1 : ℝ) ≤ |(Algebra.norm ℚ w : ℝ)| * |(discr E : ℝ)| := by
    have h := so_norm_ge w hw0 hw
    exact_mod_cast h
  have hrd : PT.rd E ^ 2 = (|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
    unfold PT.rd
    rw [← Real.rpow_natCast, ← Real.rpow_natCast (|(discr E : ℝ)|) 2, ← Real.rpow_mul hY,
      ← Real.rpow_mul hY, mul_comm]
  have hprodge : 1 ≤ (|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) *
      (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.one_le_rpow _ (by positivity)
    nlinarith [key, mul_nonneg hX hY]
  have hS : (Module.finrank ℚ E : ℝ) * (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) ≤
      ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left amgm hnR.le
    rwa [← mul_assoc, mul_one_div_cancel hnR.ne', one_mul] at h
  calc (2 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast hn2
    _ ≤ (Module.finrank ℚ E : ℝ) * ((|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) *
        (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ))) := le_mul_of_one_le_right hnR.le hprodge
    _ = PT.rd E ^ 2 * ((Module.finrank ℚ E : ℝ) *
        (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ))) := by rw [hrd]; ring
    _ ≤ PT.rd E ^ 2 * ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := mul_le_mul_of_nonneg_left hS (sq_nonneg _)

theorem so_emb_inj (v : (E →+* ℂ) → ℂ)
    (h : ∀ i, ∑ σ : E →+* ℂ, v σ * σ (RingOfIntegers.basis E i : E) = 0) : v = 0 := by
  classical
  have hM : (NumberField.basisMatrix E).mulVec v = 0 := by
    ext i
    rw [NumberField.basisMatrix_eq_embeddingsMatrixReindex]
    simp only [Matrix.mulVec, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply,
      NumberField.integralBasis_apply, Pi.zero_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm]
    rw [← h (NumberField.equivReindex E i)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [mul_comm]
    rfl
  have h2 := congrArg (fun u => (⅟(NumberField.basisMatrix E)).mulVec u) hM
  simp only [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact h2

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section SlopeTestRemainingChoices
variable {dim : (E →+* ℂ) → ℕ}

theorem smul_add_scalar (β β' : 𝓞 E) (v : Vsp dim) : act (β + β') v = act β v + act β' v := by
  ext i
  simp [act, add_mul]

theorem Hf_add_rightSquareIntegrability (x w w' : Vsp dim) : Hf x (w + w') = Hf x w + Hf x w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left_conj [IsCMField E] (α : 𝓞 E) (v w : Vsp dim) :
    Hf (act α v) w = Hf v (act (IsCMField.ringOfIntegersComplexConj E α) w) := by
  simp only [Hf, act, PiLp.toLp_apply, IsCMField.coe_ringOfIntegersComplexConj,
    IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

end SlopeTestRemainingChoices

theorem sum_sq_norm_ge_of_span [IsCMField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) {ξ : Vsp X.dim} (hξ : ξ ∈ I) (hξ0 : ξ ≠ 0)
    (k : ℕ) (x u : Fin k → Vsp X.dim) (hxu : ∀ j, x j ∈ X.L ∧ IsU I (x j) (u j))
    (hspan : Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I) :
    2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by
  classical

  have hint : ∀ j (β : 𝓞 E), ∃ n : ℤ, (Hf (x j) (act β ξ)).im = n := fun j β =>
    X.integral _ _ (hxu j).1 (hle (hst β ξ hξ))
  let φ : Fin k → 𝓞 E →+ ℤ := fun j => AddMonoidHom.mk' (fun β => (hint j β).choose) (by
    intro β β'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← (hint j (β + β')).choose_spec, ← (hint j β).choose_spec, ← (hint j β').choose_spec,
      smul_add_scalar, Hf_add_rightSquareIntegrability, Complex.add_im])
  have hφ : ∀ j β, ((φ j β : ℤ) : ℝ) = (Hf (x j) (act β ξ)).im := fun j β =>
    ((hint j β).choose_spec).symm

  choose y hy using fun j => exists_dual (φ j)
  have hyR : ∀ j (β : 𝓞 E), ((Algebra.trace ℚ E ((β : E) * y j) : ℚ) : ℝ) = (Hf (x j) (act β ξ)).im := by
    intro j β
    rw [hy j β, ← hφ j β]
    push_cast
    rfl
  have hcs : ∀ j, 2 * ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖u j‖ ^ 2 := fun j =>
    cs_bound I hst hξ (x j) (u j) (hxu j).2 (y j) (hyR j)

  set l : E := ∑ j, y j * IsCMField.complexConj E (y j) with hldef
  set a : (E →+* ℂ) → ℝ := fun σ => ∑ j, ‖σ (y j)‖ ^ 2 with hadef
  have ha0 : ∀ σ, 0 ≤ a σ := fun σ => Finset.sum_nonneg fun _ _ => by positivity
  have hσl : ∀ σ : E →+* ℂ, σ l = (a σ : ℂ) := by
    intro σ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hldef, hadef, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj']

  have hl : l ≠ 0 := by
    intro hl0
    obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : a σ₀ = 0 := by
      have := hσl σ₀
      rw [hl0, map_zero] at this
      exact_mod_cast this.symm
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
        (Finset.mem_univ j)
      have h3 : σ₀ (y j) = 0 := by simpa using h2
      exact (map_eq_zero_iff σ₀ σ₀.injective).1 h3
    have horth : ∀ w ∈ IR I, inner ℝ w ξ = 0 := by
      intro w hw
      rw [← hspan] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, α, hU⟩ := hw
        rw [hU.2 ξ (Submodule.subset_span hξ), herm_smul_left_conj, ← hyR, hy0 j, mul_zero, map_zero]
        simp
      | zero => simp
      | add w w' _ _ h h' => rw [inner_add_left, h, h', add_zero]
      | smul r w _ h => rw [real_inner_smul_left, h, mul_zero]
    have h4 := horth ξ (Submodule.subset_span hξ)
    rw [real_inner_self_eq_norm_sq] at h4
    have h5 : ‖ξ‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 h4
    exact hξ0 (norm_eq_zero.1 h5)

  have hmemD : ∀ j, y j ∈ Dual1 E := fun j => mem_dual_of (y j) fun β => ⟨φ j β, hy j β⟩
  have htr : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have hmemD' : ∀ j, IsCMField.complexConj E (y j) ∈ Dual1 E := fun j =>
    mem_dual_of _ fun β => by
      refine ⟨φ j (IsCMField.ringOfIntegersComplexConj E β), ?_⟩
      rw [← hy j, IsCMField.coe_ringOfIntegersComplexConj, ← htr, map_mul,
        IsCMField.complexConj_apply_apply]
  have hmem : l ∈ Dual1 E * Dual1 E := by
    rw [hldef, ← FractionalIdeal.mem_coe]
    exact Submodule.sum_mem _ fun j _ =>
      (FractionalIdeal.mem_coe).2 (FractionalIdeal.mul_mem_mul (hmemD j) (hmemD' j))
  have hnorm := one_le_norm_mul l hl hmem

  have hprodC : ((Algebra.norm ℚ l : ℚ) : ℂ) = ((∏ σ, a σ : ℝ) : ℂ) := by
    rw [norm_prod_emb]
    push_cast
    exact Finset.prod_congr rfl fun σ _ => hσl σ
  have hprodR : ((Algebra.norm ℚ l : ℚ) : ℝ) = ∏ σ, a σ := by exact_mod_cast hprodC
  have hP0 : 0 ≤ ∏ σ, a σ := Finset.prod_nonneg fun σ _ => ha0 σ
  set D : ℝ := ((NumberField.discr E).natAbs : ℝ) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact_mod_cast Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  have hprod : (D ^ 2)⁻¹ ≤ ∏ σ, a σ := by
    have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ l : ℚ) : ℝ)| * D ^ 2 := by
      have h1' := (Rat.cast_le (K := ℝ)).2 hnorm
      push_cast at h1'
      rw [hDdef]
      exact h1'
    rw [hprodR, abs_of_nonneg hP0] at h1
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    linarith
  have hcard : Fintype.card (E →+* ℂ) = 2 * PT.f E := by
    rw [NumberField.Embeddings.card, PT.f, IsTotallyComplex.finrank]
    omega
  have hcpos : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos
  have hsum := sum_ge_of_prod_ge a ha0 D hD hprod hcpos
  have hrd : D ^ ((Fintype.card (E →+* ℂ) : ℝ)⁻¹) = PT.rd E := by
    rw [PT.rd, NumberField.Embeddings.card, one_div, hDdef]
    congr 1
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hrd, hcard] at hsum
  push_cast at hsum

  have hξpos : 0 < ‖ξ‖ ^ 2 := by
    have := norm_pos_iff.2 hξ0
    positivity
  have hj : ∀ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 ≤ ‖u j‖ ^ 2 / 2 := by
    intro j
    rw [div_le_iff₀ hξpos]
    linarith [hcs j]
  have hsw : ∑ σ, a σ = ∑ j, ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 := by
    rw [hadef]
    exact Finset.sum_comm
  calc 2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) = (2 * PT.f E / PT.rd E ^ 2) / ‖ξ‖ ^ 2 := by
        rw [div_div]
    _ ≤ (∑ σ, a σ) / ‖ξ‖ ^ 2 := by
        apply div_le_div_of_nonneg_right hsum hξpos.le
    _ = ∑ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 := by
        rw [hsw, Finset.sum_div]
    _ ≤ ∑ j, ‖u j‖ ^ 2 / 2 := Finset.sum_le_sum fun j _ => hj j

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofCovolLb
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_covol_lb [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hG : Ext.GHadamard)
    (ob : OrthonormalBasis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I))
    (a : Fin (Module.finrank ℝ (IR I)) → IR I) (ha : ∀ i, (a i : Vsp X.dim) ∈ I)
    (hdet : ob.toBasis.det a ≠ 0) :
    1 ≤ |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph /
      (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
  unfold Ext.GHadamard at hG
  obtain ⟨x, u, hxu, hli, hnorm⟩ := hI.u1
  let u' : Fin (Module.finrank ℝ (IR I)) → IR I := fun j => ⟨u j, (hxu j).2.1⟩
  have hli' : LinearIndependent ℝ u' := LinearIndependent.of_comp (IR I).subtype (by exact hli)
  have hU : IsUnit (ob.toBasis.det u') := by
    rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ (IR I))) with hE | hN
    · rw [Module.Basis.det_apply, Matrix.det_isEmpty]
      exact isUnit_one
    · have hspan : Submodule.span ℝ (Set.range u') = ⊤ :=
        hli'.span_eq_top_of_card_eq_finrank (by simp)
      have hU' := ob.toBasis.isUnit_det (Module.Basis.mk hli' hspan.ge)
      rwa [Module.Basis.coe_mk] at hU'
  have hint : ∀ j k, ∃ m : ℤ, (Hf (x j) (a k : Vsp X.dim)).im = m := fun j k =>
    X.integral _ _ (hxu j).1 (hI.le (ha k))
  let Gz : Matrix (Fin (Module.finrank ℝ (IR I))) (Fin (Module.finrank ℝ (IR I))) ℤ :=
    fun j k => (hint j k).choose
  have hGjk : ∀ j k, inner ℝ (u' j) (a k) = (Gz j k : ℝ) := fun j k => by
    show _ = (((hint j k).choose : ℤ) : ℝ)
    rw [← (hint j k).choose_spec]
    exact (hxu j).2.2 _ (a k).2
  have hmat : Matrix.transpose (ob.toBasis.toMatrix u') * ob.toBasis.toMatrix a = Gz.map (fun m : ℤ => (m : ℝ)) := by
    ext j k
    rw [Matrix.mul_apply, Matrix.map_apply, ← hGjk j k]
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [← OrthonormalBasis.sum_inner_mul_inner ob]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (u' j) (ob i)]
  have hdetG : ob.toBasis.det u' * ob.toBasis.det a = ((Gz.det : ℤ) : ℝ) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_transpose (ob.toBasis.toMatrix u'),
      ← Matrix.det_mul, hmat]
    first
      | exact (Int.cast_det Gz).symm
      | exact (RingHom.map_det (Int.castRingHom ℝ) Gz).symm
      | simp [Int.cast_det]
  have hGz : Gz.det ≠ 0 := by
    intro h0
    have h00 : ob.toBasis.det u' * ob.toBasis.det a = 0 := by rw [hdetG, h0, Int.cast_zero]
    rcases mul_eq_zero.mp h00 with h | h
    · exact hU.ne_zero h
    · exact hdet h
  have h1 : (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := by
    rw [← abs_mul, hdetG]
    exact_mod_cast Int.one_le_abs hGz
  have hH := hG (Module.finrank ℝ (IR I)) (ob.toBasis.toMatrix u')
  rw [← Module.Basis.det_apply] at hH
  have hcol : ∀ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) := fun j => by
    apply Real.sqrt_le_sqrt
    have hn : ∑ i, ob.toBasis.toMatrix u' i j ^ 2 = ‖u j‖ ^ 2 := by
      have hu : ‖u j‖ = ‖u' j‖ := rfl
      simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
      rw [hu, ← ob.repr.norm_map (u' j), EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hn]
    exact hnorm j
  have hprod : ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤
      Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
    calc ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2)
        ≤ ∏ _j : Fin (Module.finrank ℝ (IR I)), Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) :=
          Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => hcol j)
      _ = Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := h1
    _ ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) * |ob.toBasis.det a| :=
      mul_le_mul_of_nonneg_right (hH.trans hprod) (abs_nonneg _)
    _ = |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := mul_comm _ _

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmGAddI
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

theorem z_add {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (v w : EuclideanSpace ℂ ι) : z K k (v + w) = z K k v + z K k w := by
  simp [z, Hf, add_mul, Finset.sum_add_distrib]

theorem z_rsmul {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (t : ℝ) (v : EuclideanSpace ℂ ι) : z K k (t • v) = t * z K k v := by
  simp [z, Hf, Finset.mul_sum, mul_assoc]

theorem z_sum {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    {κ : Type} (F : Finset κ) (f : κ → EuclideanSpace ℂ ι) :
    z K k (∑ j ∈ F, f j) = ∑ j ∈ F, z K k (f j) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · simp [z, Hf]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, z_add, ih]

theorem conj_eq (ξ : ℂ) : (starRingEnd ℂ) ξ = ξ - 2 * (ξ.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp <;> ring

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def gaugeExp (I : Submodule ℤ (Vsp X.dim)) (γ v : Vsp X.dim) : ℂ :=
  -(2 * Real.pi * Complex.I * ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v) -
    Real.pi * Complex.I * ∑ k, z (IR I) k γ * ((z (IR I) k γ).im : ℂ) +
    Real.pi * Hf (p2 (IR I) v) (p2 (IR I) γ) + Real.pi * Hf (p2 (IR I) γ) (p2 (IR I) γ) / 2

private theorem Hf_add_left_euclidean {ι : Type} [Fintype ι] (x x' y : EuclideanSpace ℂ ι) :
    Hf (x + x') y = Hf x y + Hf x' y := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

private theorem Hf_real_smul_left {ι : Type} [Fintype ι] (t : ℝ) (x y : EuclideanSpace ℂ ι) :
    Hf (t • x) y = t * Hf x y := by
  simp [Hf, Finset.mul_sum, mul_assoc]

private theorem Hf_add_right_euclidean {ι : Type} [Fintype ι] (x y y' : EuclideanSpace ℂ ι) :
    Hf x (y + y') = Hf x y + Hf x y' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

private theorem Hf_real_smul_right' {ι : Type} [Fintype ι] (t : ℝ) (x y : EuclideanSpace ℂ ι) :
    Hf x (t • y) = t * Hf x y := by
  simp [Hf, Finset.mul_sum, mul_left_comm]

private theorem Hf_im_eq_zero_on_IR_of_isSplit (hI : IsSplit P I) :
    ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := by
  intro a ha b hb
  change a ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at ha
  change b ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hb
  induction hb using Submodule.span_induction with
  | mem y hy =>
    induction ha using Submodule.span_induction with
    | mem x hx => exact hI.iso x hx y hy
    | zero => simp [Hf]
    | add x x' _ _ h1 h2 => rw [Hf_add_left_euclidean, Complex.add_im, h1, h2, add_zero]
    | smul t x _ h => rw [Hf_real_smul_left, Complex.im_ofReal_mul, h, mul_zero]
  | zero => simp [Hf]
  | add y y' _ _ h1 h2 => rw [Hf_add_right_euclidean, Complex.add_im, h1, h2, add_zero]
  | smul t y _ h => rw [Hf_real_smul_right', Complex.im_ofReal_mul, h, mul_zero]

theorem zmG_add (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {γ : Vsp X.dim} (hγ : γ ∈ X.L) (v : Vsp X.dim) :
    zmG I s (v + γ) = (X.eps γ : ℂ) * Complex.exp (gaugeExp I γ v) * zmG I s v := by
  have hsec := hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)
  have hfun : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := rfl
  have hkey : ∀ a b c d : ℂ, a + b = c + d →
      (X.eps γ : ℂ) * Complex.exp a * s (fun _ => v) * Complex.exp b =
        (X.eps γ : ℂ) * Complex.exp c * (s (fun _ => v) * Complex.exp d) := by
    intro a b c d h
    have hab : Complex.exp a * Complex.exp b = Complex.exp c * Complex.exp d := by
      rw [← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination ((X.eps γ : ℂ) * s (fun _ => v)) * hab
  have e1 : ∑ k, z (IR I) k v * (starRingEnd ℂ) (z (IR I) k γ) =
      ∑ k, z (IR I) k v * z (IR I) k γ -
        2 * Complex.I * ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_eq]
    ring
  have e2 : ∑ k, z (IR I) k γ * (starRingEnd ℂ) (z (IR I) k γ) =
      ∑ k, z (IR I) k γ ^ 2 -
        2 * Complex.I * ∑ k, z (IR I) k γ * ((z (IR I) k γ).im : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_eq]
    ring
  have e3 : Col.S (IR I) (v + γ) =
      Col.S (IR I) v + 2 * ∑ k, z (IR I) k v * z (IR I) k γ + ∑ k, z (IR I) k γ ^ 2 := by
    simp only [Col.S, z_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold zmG
  rw [hfun, hsec]
  simp only [Fin.prod_univ_one, pow_one]
  apply hkey
  simp only [HC, Fin.sum_univ_one, Nat.cast_one, one_mul]
  rw [e3, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) v γ, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) γ γ, e1, e2]
  unfold gaugeExp
  push_cast
  ring

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

