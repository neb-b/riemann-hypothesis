module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
section
noncomputable section

namespace GlobalTheory.Proof.GenusMassSignature

open NumberField Formalism.BasicNotions Matrix
open scoped ComplexOrder MatrixOrder

theorem denseRange_of_not_isReal {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

theorem hasSignature_of_posDef {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : J.PosDef) :
    Formalism.UG.HasSignature J n 0 := by
  let e : Fin n ≃ Fin n ⊕ Fin 0 := (Equiv.sumEmpty (Fin n) (Fin 0)).symm
  have h1 : (J.reindex e e).PosDef := by
    simpa using h.submatrix (e := e.symm) e.symm.injective
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set A := J.reindex e e with hA
  have hS : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h1.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := by
    have := h1.isUnit
    rw [← hSS] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨U, hU⟩ := hu
  refine ⟨e, U⁻¹, ?_⟩
  have hc : Formalism.UG.cT (starRingEnd ℂ) ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix _ _ ℂ) =
      star ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  have hA2 : A = star (U : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) * U := by
    rw [hU, hS, hSS]
  rw [hJ, hc, ← hA, hA2, ← mul_assoc, ← star_mul, mul_assoc, Units.mul_inv, star_one, one_mul]

section Field

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_form (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) (x : W.V) :
    τ (W.hD x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ
        (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i)) := by
  unfold HSpace.hD
  conv_lhs => rw [← W.frame.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec,
    Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_isHermitian (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) : (W.gram.map τ).IsHermitian := by
  ext i k
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, HSpace.gram, HSpace.gram,
    ← W.herm.eq (W.frame k) (W.frame i), starRingEnd_apply, hst]
  rfl

theorem pos_iff_posDef (htc : IsTotallyComplex E)
    (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) :
    (∀ x : W.V, x ≠ 0 → 0 < (τ (W.hD x x)).re) ↔ (W.gram.map τ).PosDef := by
  constructor
  · intro h
    have hH := gram_isHermitian hst W τ
    have hd : DenseRange τ :=
      denseRange_of_not_isReal τ (IsTotallyComplex.complexEmbedding_not_isReal τ)
    have hdn : DenseRange fun (l : Fin W.rank → E) => (fun i => τ (l i)) :=
      DenseRange.piMap (fun _ : Fin W.rank => hd)
    have hco : ∀ l : Fin W.rank → E, τ (W.hD (W.frame.equivFun.symm l) (W.frame.equivFun.symm l)) =
        star (fun i => τ (l i)) ⬝ᵥ (W.gram.map τ).mulVec (fun i => τ (l i)) := by
      intro l
      rw [emb_form hst]
      have : ∀ i, W.frame.repr (W.frame.equivFun.symm l) i = l i := fun i =>
        congrFun (W.frame.equivFun.apply_symm_apply l) i
      simp only [this]
    have hne : ∀ l : Fin W.rank → E, l ≠ 0 → W.frame.equivFun.symm l ≠ 0 := fun l hl h0 =>
      hl (W.frame.equivFun.symm.injective (by rw [h0, map_zero]))
    have hpsd : (W.gram.map τ).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
      rw [Complex.nonneg_iff]
      refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
      refine hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((W.gram.map τ) *ᵥ y)).re) x ?_ ?_
      · exact isClosed_le continuous_const (by fun_prop)
      · intro l
        by_cases hl : l = 0
        · subst hl
          simp [dotProduct]
        · have := h _ (hne l hl)
          rw [hco] at this
          exact this.le
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have h1 : W.gram.det = 0 := by
      apply τ.injective
      rw [RingHom.map_det, map_zero]
      exact h0
    obtain ⟨l, hl, hl0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
    have h2 : (W.gram.map τ).mulVec (fun i => τ (l i)) = 0 := by
      funext i
      have := congrArg τ (congrFun hl0 i)
      simpa [Matrix.mulVec, dotProduct] using this
    have := h _ (hne l hl)
    rw [hco, h2] at this
    simp at this
  · intro h x hx
    have hv : (fun i => τ (W.frame.repr x i)) ≠ 0 := by
      intro h
      apply hx
      apply W.frame.repr.injective
      ext i
      simpa using congrFun h i
    rw [emb_form hst]
    exact h.re_dotProduct_pos hv

end Field

end GlobalTheory.Proof.GenusMassSignature
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
section
namespace GlobalTheory.EntireTaylor

theorem summable_of_entire {σ : Type*} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0) (w : σ → ℂ) :
    Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := by
  obtain ⟨R, hRdef⟩ : ∃ R : σ → ℝ, R = fun j => 2 * ‖w j‖ + 1 := ⟨_, rfl⟩
  have hR : ∀ j, 0 < R j := fun j => by rw [hRdef]; positivity
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ Set.univ.pi (fun j => Metric.closedBall (0 : ℂ) (R j)), ‖f z‖ ≤ M :=
    (isCompact_univ_pi fun j => isCompact_closedBall (0 : ℂ) (R j)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM 0 (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by simpa using (hR j).le)))
  have hw : ∀ j, ‖w j‖ / R j ≤ 1 / 2 := fun j => by
    rw [div_le_iff₀ (hR j), hRdef]
    linarith [norm_nonneg (w j)]
  have key : ∀ α : σ →₀ ℕ, ‖c α * ∏ j, w j ^ α j‖ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j := by
    intro α
    have hP : (∏ j, ((α j).factorial : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
    have hcα : c α = pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
      rw [← hc α, mul_div_cancel_left₀ _ hP]
    have hnormP : ‖∏ j, ((α j).factorial : ℂ)‖ = ∏ j, ((α j).factorial : ℝ) := by
      rw [norm_prod]
      simp
    have hPpos : 0 < ∏ j, ((α j).factorial : ℝ) :=
      Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos _
    have hC : ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k :=
      GlobalTheory.norm_pderivIter_le_of_differentiable α (fun k => (hR k).le) (fun k _ => hR k) hf
        fun z hz => hM z (Set.mem_univ_pi.mpr fun j => Metric.mem_closedBall.mpr (by
          have h := hz j
          simp only [Pi.zero_apply, sub_zero] at h
          rw [dist_zero_right]
          exact h.le))
    have h1 : ‖c α‖ ≤ M / ∏ j, R j ^ α j := by
      rw [hcα, norm_div, hnormP, div_le_iff₀ hPpos]
      calc ‖pderivIter α f 0‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, R k ^ α k := hC
        _ = (M / ∏ j, R j ^ α j) * ∏ j, ((α j).factorial : ℝ) := by ring
    calc ‖c α * ∏ j, w j ^ α j‖ = ‖c α‖ * ∏ j, ‖w j‖ ^ α j := by
          rw [norm_mul, norm_prod]
          simp [norm_pow]
      _ ≤ (M / ∏ j, R j ^ α j) * ∏ j, ‖w j‖ ^ α j :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun j _ => by positivity)
      _ = M * ∏ j, (‖w j‖ / R j) ^ α j := by
          simp only [div_pow, Finset.prod_div_distrib]
          ring
      _ ≤ M * ∏ j, (1 / 2 : ℝ) ^ α j :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun j _ => by have := (hR j).le; positivity)
              fun j _ => pow_le_pow_left₀ (by have := (hR j).le; positivity) (hw j) _) hM0
  exact Summable.of_norm_bounded
    ((GlobalTheory.ProdThetaConj.summable_prod_half_pow (σ := σ)).mul_left M) key

end GlobalTheory.EntireTaylor

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem GlobalTheory.EntireTaylor.hasSum_taylor_mono : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z) (F z) := by
  intro D N N' F hF z
  have hcd : Differentiable ℂ (fun w => F (GlobalTheory.GaussCauchy.curry D N N' w)) := fun w =>
    (hF _).comp w (LinearMap.toContinuousLinearMap (GlobalTheory.GaussCauchy.curry D N N')).differentiableAt
  have hS := GlobalTheory.EntireTaylor.summable_of_entire hcd (fun α => Formalism.MainNotions.TaylorLogMetric.taylor D F α)
    (fun α => by
      rw [← GlobalTheory.GaussCauchy.factorial_mul_taylor D N N' F hF α, Finsupp.prod_fintype]
      intro i
      simp)
    (fun k => z k.1 k.2.1 k.2.2)
  have hmono : ∀ α : Mono D N N', mono D α z = ∏ k, z k.1 k.2.1 k.2.2 ^ α k := fun α => by
    show (α.prod fun k n => z k.1 k.2.1 k.2.2 ^ n) = _
    rw [Finsupp.prod_fintype]
    intro i
    simp
  have hS' : Summable fun α : Mono D N N' => Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z := by
    simpa only [hmono] using hS
  rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D hF z]
  exact hS'.hasSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpec
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.KerSum

theorem exists_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖ := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => H u v)
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul])
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, LinearMap.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul])
  let B' : V →L[ℝ] V →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ B)
  exact ⟨‖B'‖, norm_nonneg _, fun u v => B'.le_opNorm₂ u v⟩

theorem norm_kerTerm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : Sesq V) {M R : ℝ} (hM : 0 ≤ M) (hB : ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖) (x w z : V)
    (hw : ‖w‖ ≤ R) :
    ‖kerTerm H x w z‖ ≤ Real.exp (π * (M * R * ‖z‖)) *
      Real.exp (-(π / 2) * (H x x).re + (π * (M * ‖z‖ + M * R)) * ‖x‖) := by
  rw [kerTerm, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have h1 : (H w z).re ≤ M * R * ‖z‖ :=
    ((Complex.re_le_norm _).trans (hB w z)).trans (by gcongr)
  have h2 : (H x z).re ≤ M * ‖x‖ * ‖z‖ := (Complex.re_le_norm _).trans (hB x z)
  have h3 : -(H w x).re ≤ M * R * ‖x‖ :=
    (((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hB w x)).trans (by gcongr)
  have e : ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2).re
      = π * ((H w z).re + (H x z).re + -(H w x).re) - π / 2 * (H x x).re := by
    simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) Real.pi_pos.le
  linarith

theorem differentiable_kerTerm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (H : Sesq V) (x z : V) :
    Differentiable ℂ (fun w => kerTerm H x w z) := by
  have h : ∀ v, Differentiable ℂ (fun w => H w v) := fun v =>
    (LinearMap.toContinuousLinearMap (H.flip v)).differentiable
  have e : (fun w => kerTerm H x w z) = fun w =>
      cexp ((π : ℂ) * (H w z + H x z) - (π : ℂ) * H w x - (π : ℂ) * H x x / 2) := by
    funext w; simp [kerTerm]
  rw [e]
  exact (((((h z).add_const _).const_mul _).sub ((h x).const_mul _)).sub_const _).cexp

theorem kerTerm_shift {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ z w, H z w = conj (H w z)) (x y w z : V) :
    kerTerm H x (w + y) z * cexp (-(π : ℂ) * H w y - (π : ℂ) * H y y / 2)
      = cexp (-((π : ℂ) * I) * ((H y x).im : ℂ)) * kerTerm H (y + x) w z := by
  have h : I * ((H y x).im : ℂ) = (H y x - H x y) / 2 := by
    rw [hH x y, Complex.sub_conj]; push_cast; ring
  rw [kerTerm, kerTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add (f := _), LinearMap.add_apply]
  linear_combination (π : ℂ) * h

theorem kerSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  intro V _ _ _ H hH Λ _ α hα
  obtain ⟨M, hM, hB⟩ := exists_bound H
  have hn : ∀ x : Λ, ‖α x‖ = 1 := fun x => by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have key : ∀ (z : V) (R : ℝ), ∃ u : Λ → ℝ, Summable u ∧
      ∀ (x : Λ) (w : V), ‖w‖ ≤ R → ‖α x * kerTerm H x w z‖ ≤ u x := fun z R =>
    ⟨_, (_root_.GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm V H hH Λ (π * (M * ‖z‖ + M * R))).mul_left (Real.exp (π * (M * R * ‖z‖))),
      fun x w hw => by
        rw [norm_mul, hn, one_mul]
        exact norm_kerTerm_le H hM hB x w z hw⟩
  refine ⟨fun w z => ?_, fun z => ?_, fun z y hy w => ?_⟩
  · obtain ⟨u, hu, h⟩ := key z ‖w‖
    exact Summable.of_norm_bounded hu fun x => h x w le_rfl
  · refine differentiableOn_univ.1 (GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal isOpen_univ
      (F := fun (x : Λ) w => α x * kerTerm H x w z)
      (fun x => ((differentiable_kerTerm H x z).const_mul _).differentiableOn) fun w _ => ?_)
    obtain ⟨u, hu, h⟩ := key z (‖w‖ + 1)
    refine ⟨Metric.ball w 1, Metric.ball_mem_nhds w one_pos, u, hu, fun x v hv => h x v ?_⟩
    have := norm_le_norm_add_norm_sub' v w
    rw [mem_ball_iff_norm] at hv
    linarith
  · simp only [Heisenberg₂, kerSum]
    rw [← tsum_mul_right, ← tsum_mul_left,
      ← (Equiv.addLeft (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α x * kerTerm H x w z)]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addLeft, AddSubgroup.coe_add]
    rw [hα.2.2 y hy x x.2, mul_assoc (α x), kerTerm_shift H hH.1]
    ring

end GlobalTheory.UnitaryTheta.KerSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InertParity

variable {D : D7}

def Ev (D : D7) (n : ℕ) : Prop := ∀ q : ℕ, q.Prime → InertQ D q → Even (n.factorization q)

def hlf (D : D7) (n : ℕ) : ℕ := ∑ q ∈ n.primeFactors.filter (InertQ D), n.factorization q / 2

def sgn (D : D7) (n : ℕ) : ℂ := (-1) ^ hlf D n

def idx (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : ℕ :=
  Nat.card (stdL D n ⧸ Submodule.comap (stdL D n).subtype L)

def scal (D : D7) (N N' : ℕ) (b : D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' :=
  GlobalTheory.RatEqui.mulV D (b • (1 : Matrix (Fin N') (Fin N') D.host.E)) 1

theorem scal_apply {N N' : ℕ} (b : D.host.E) (z : VC D N N') (τ i j) :
    scal D N N' b z τ i j = embT D τ b * z τ i j := by
  have e : (b • (1 : Matrix (Fin N') (Fin N') D.host.E)).map (embT D τ) =
      embT D τ b • (1 : Matrix (Fin N') (Fin N') ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [scal, GlobalTheory.RatEqui.mulV_apply, e, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem idx_eq_relIndex {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idx D L = L.toAddSubgroup.relIndex (stdL D n).toAddSubgroup := rfl

theorem idx_std (n : ℕ) : idx D (stdL D n) = 1 := by
  rw [idx_eq_relIndex, AddSubgroup.relIndex_self]

theorem hlf_eq_sum {n : ℕ} {s : Finset ℕ} (hs : n.primeFactors ⊆ s) :
    hlf D n = ∑ q ∈ s.filter (InertQ D), n.factorization q / 2 := by
  refine Finset.sum_subset (Finset.filter_subset_filter _ hs) fun q hq hq' => ?_
  have : q ∉ n.factorization.support := fun h =>
    hq' (Finset.mem_filter.2 ⟨by simpa using h, (Finset.mem_filter.1 hq).2⟩)
  rw [Finsupp.notMem_support_iff.1 this, Nat.zero_div]

theorem Ev.one : Ev D 1 := fun q _ _ => by simp

theorem sgn_one : sgn D 1 = 1 := by simp [sgn, hlf]

theorem sgn_mul_self (n : ℕ) : sgn D n * sgn D n = 1 := by
  rw [sgn, ← mul_pow]; simp

theorem sgn_pow_even (n : ℕ) {k : ℕ} (hk : Even k) : sgn D n ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_add, ← mul_pow, sgn_mul_self, one_pow]

theorem Ev.mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D (a * b) := fun q hq hi => by
  rw [Nat.factorization_mul ha0 hb0]
  exact (ha q hq hi).add (hb q hq hi)

theorem Ev.of_mul {a b : ℕ} (hab : Ev D (a * b)) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D a :=
  fun q hq hi => by
    have := hab q hq hi
    rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, Nat.even_add] at this
    exact this.2 (hb q hq hi)

theorem Ev.pow {a : ℕ} (ha : Ev D a) (k : ℕ) : Ev D (a ^ k) := fun q hq hi => by
  rw [Nat.factorization_pow]
  exact (ha q hq hi).mul_left k

theorem sgn_mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    sgn D (a * b) = sgn D a * sgn D b := by
  have h : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := Nat.primeFactors_mul ha0 hb0
  rw [sgn, sgn, sgn, ← pow_add, hlf_eq_sum (n := a) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_left),
    hlf_eq_sum (n := b) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_right), hlf, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp := Nat.prime_of_mem_primeFactors hq1
  obtain ⟨i, hi'⟩ := ha q hp hi
  obtain ⟨j, hj⟩ := hb q hp hi
  rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply]
  omega

theorem sgn_pow {a : ℕ} (ha : Ev D a) (ha0 : a ≠ 0) (k : ℕ) : sgn D (a ^ k) = sgn D a ^ k := by
  induction k with
  | zero => simp [sgn_one]
  | succ k ih => rw [pow_succ, sgn_mul (ha.pow k) ha (pow_ne_zero _ ha0) ha0, ih, pow_succ]

theorem sgn_congr {a b : ℕ} (h : ∀ q : ℕ, q.Prime → InertQ D q → a.factorization q = b.factorization q) :
    sgn D a = sgn D b := by
  rw [sgn, sgn, hlf_eq_sum (n := a) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_left,
    hlf_eq_sum (n := b) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_right]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp : q.Prime := by
    rcases Finset.mem_union.1 hq1 with h | h <;> exact Nat.prime_of_mem_primeFactors h
  rw [h q hp hi]

theorem sgn_of_eq {n a b c k : ℕ} (h : n * a ^ k = b ^ k * c ^ k) (ha : Ev D a) (hb : Ev D b) (hc : Ev D c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) : sgn D n = sgn D b ^ k * (sgn D c * sgn D a) ^ k := by
  have h0 : b ^ k * c ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)
  have hn0 : n ≠ 0 := left_ne_zero_of_mul (h ▸ h0)
  have hn : Ev D n := Ev.of_mul (h ▸ (hb.pow k).mul (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)) (ha.pow k) hn0
    (pow_ne_zero _ ha0)
  have e := congrArg (sgn D) h
  rw [sgn_mul hn (ha.pow k) hn0 (pow_ne_zero _ ha0),
    sgn_mul (hb.pow k) (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0), sgn_pow ha ha0, sgn_pow hb hb0,
    sgn_pow hc hc0] at e
  rw [mul_pow, ← mul_assoc, ← e, mul_assoc, ← mul_pow, sgn_mul_self, one_pow, mul_one]

end GlobalTheory.InertParity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpaceStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTranslateClassInvariant_of_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N')) (F : VC D N N' → ℂ), (∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) → F ∈ ThSp D T A₁ → RepInd D T A₁ A₂ F := by
  first | exact @GlobalTheory.ThetaConj.repInd_of_thSp | exact GlobalTheory.ThetaConj.repInd_of_thSp | (intros; apply GlobalTheory.ThetaConj.repInd_of_thSp <;> assumption)
end

