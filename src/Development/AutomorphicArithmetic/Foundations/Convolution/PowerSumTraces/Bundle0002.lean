module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0002
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelH
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClass
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

private theorem rop_mem (f : CC K n) (v : L2 μ) (hv : v ∈ cuspidalL2 μ) : Rop μ f v ∈ cuspidalL2 μ :=
  UnitaryRep.IsInvariant.integrated_mem _ μ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ) _ hv

private theorem pc_rop_pc (f : CC K n) : Pc μ ∘L Rop μ f ∘L Pc μ = Rop μ f ∘L Pc μ :=
  ContinuousLinearMap.ext fun v => Submodule.starProjection_eq_self_iff.2
    (rop_mem μ f _ ((cuspidalL2 μ).starProjection_apply_mem v))

private theorem adjoint_pc : ContinuousLinearMap.adjoint (Pc μ) = Pc μ :=
  (isSelfAdjoint_starProjection (cuspidalL2 μ)).adjoint_eq

private theorem adjoint_rop (f : CC K n) :
    ContinuousLinearMap.adjoint (Rop μ f) = Rop μ (CuspidalProjection.ccStar f) := by
  have := isInvInvariant_of_isMulRightInvariant μ
  exact ((rightRegularRep (Gam K n) μ).adjoint_integrated μ (UnitaryRep.ccToL1 μ f)).trans
    (congrArg _ (CuspidalProjection.ccToL1_ccStar (μ := μ) f).symm)

private theorem adjoint_rop_star (f : CC K n) :
    ContinuousLinearMap.adjoint (Rop μ (CuspidalProjection.ccStar f)) = Rop μ f := by
  rw [← adjoint_rop, ContinuousLinearMap.adjoint_adjoint]

private theorem pc_comm (f : CC K n) : Pc μ ∘L Rop μ f = Rop μ f ∘L Pc μ := by
  have h := congrArg ContinuousLinearMap.adjoint (pc_rop_pc μ (CuspidalProjection.ccStar f))
  simp only [ContinuousLinearMap.adjoint_comp, adjoint_pc, adjoint_rop_star] at h
  rw [← pc_rop_pc μ f, ← h, ContinuousLinearMap.comp_assoc]

private theorem hs_of_decay (f : CC K n) (h : PositivityTheory.Rg.Tf.Core.CuspDecay μ f) :
    IsHilbertSchmidt (Rop μ f ∘L Pc μ) := by
  obtain ⟨C, hC⟩ := h 0
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let T := Rop μ f ∘L (cuspidalL2 μ).subtypeL
  let e : RightCosetSpace (Gam K n) → StrongDual ℂ (cuspidalL2 μ) := fun q =>
    (rconvCLM (Gam K n) μ f (Quotient.out q)).comp (cuspidalL2 μ).subtypeL
  have he : ∀ q, ‖e q‖ ≤ max C 0 := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun w => ?_
    change ‖rconv (Gam K n) μ f (w : L2 μ) (Quotient.out q)‖ ≤ _
    have hb : ‖rconv (Gam K n) μ f (w : L2 μ) (Quotient.out q)‖ ≤ C * ‖(w : L2 μ)‖ := by
      simpa using hC w w.2 (Quotient.out q)
    refine hb.trans ?_
    rw [Submodule.coe_norm]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hout : ∀ (φ : L2 μ) (q : RightCosetSpace (Gam K n)),
      rconvQ (Gam K n) μ f φ q = rconv (Gam K n) μ f φ (Quotient.out q) := by
    intro φ q
    obtain ⟨a, rfl⟩ := mk_surjective (Gam K n) q
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K n)).1 (Quotient.out_eq (mk (Gam K n) a))
    rw [rconvQ_mk, ← hγ]
    exact (rconv_mul_left (Gam K n) μ f φ γ.2 a).symm
  have hae : ∀ w, T w =ᵐ[quotientMeasure (Gam K n) μ] fun q => e q w := by
    intro w
    filter_upwards [integrated_ae_eq_rconvQ (Gam K n) μ f (w : L2 μ)] with q hq
    exact hq.trans (hout _ q)
  have hT : IsHilbertSchmidt T := isHilbertSchmidt_of_ae_eq_dual T e (max C 0) he hae
  have hcomp := hT.comp_right (cuspidalL2 μ).orthogonalProjectionOnto
  convert hcomp using 1
  ext v
  rfl

end

theorem UpperTheory.ConvolutionTheory.C.decayTraceClass :
    UpperTheory.ConvolutionTheory.C.DecayTraceClass := by
  intro K _ _ n μ _ a g M ha hg _
  have hA := hs_of_decay μ a ha
  have hB : IsHilbertSchmidt (Rop μ g ∘L Pc μ) := by
    have h := (hs_of_decay μ _ hg).adjoint
    rw [ContinuousLinearMap.adjoint_comp, adjoint_pc, adjoint_rop_star, pc_comm] at h
    exact h
  have e : Pc μ ∘L (Rop μ a ∘L M ∘L Rop μ g) ∘L Pc μ =
      (Rop μ a ∘L Pc μ) ∘L (M ∘L (Rop μ g ∘L Pc μ)) :=
    ContinuousLinearMap.ext fun v =>
      DFunLike.congr_fun (pc_comm μ a) (M (Rop μ g (Pc μ v)))
  rw [e]
  exact isTraceClass_comp hA (hB.comp_left M)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSplit
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.eigSplit :
    UpperTheory.ConvolutionTheory.C.EigSplit := by
  intro H _ _ _ W A hW hA hinv hK η hη
  have hsa : IsSelfAdjoint A := isSelfAdjoint_of_nonneg hA
  obtain ⟨hfin, hfd⟩ := UpperTheory.eigIn_finite_above_of_isCompactOperator H W A hW hsa hinv hK η hη
  obtain ⟨s, b, hb⟩ := UpperTheory.exists_hilbertBasis_prj_eigenvectors_of_isCompactOperator H W A hW hsa hinv hK
  have hS : ∀ x, x ∈ hfin.toFinset ↔ η < x ∧ eigIn W A x ≠ ⊥ := fun x => by simp
  refine ⟨hfin.toFinset, hS, fun x hx => hfd x ((hS x).1 hx).1, fun φ c T hφ hc hφc hT => ?_⟩
  rw [UpperTheory.trOn_sub_sum_eq_trace_comp_compression H W (eigIn W A) hfin.toFinset (fun x => (φ x : ℂ)) (cfc φ A) T (fun x => inf_le_left) hT]
  have hmem : ∀ v, prj W v ∈ W := fun v => by
    have h : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hW.submodule_topologicalClosure_eq] at h
  have hPP : ∀ v, prj W (prj W v) = prj W v := fun v =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)
  refine UpperTheory.norm_trace_comp_le_mul_traceNorm H s b _ _ c hc hT fun i => ?_
  obtain ⟨μ, hμ⟩ := hb i
  have hF := UpperTheory.cfc_apply_of_eigenvector H A hsa φ hφ μ _ hμ
  have hD : (prj W ∘L cfc φ A ∘L prj W - ∑ x ∈ hfin.toFinset, (φ x : ℂ) • prj (eigIn W A x)) (b i) =
      (if μ ∈ hfin.toFinset then 0 else (φ μ : ℂ)) • prj W (b i) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, hF, map_smul, hPP, UpperTheory.prj_eigIn_of_eigenvector_prj H W A hW hsa (b i) μ _ hμ, smul_ite, smul_zero,
      Finset.sum_ite_eq']
    split_ifs <;> simp
  rw [hD]
  by_cases h0 : prj W (b i) = 0
  · exact ⟨0, by simpa using hc, by simp [h0]⟩
  refine ⟨if μ ∈ hfin.toFinset then 0 else (φ μ : ℂ), ?_, by simp only [map_smul, ContinuousLinearMap.comp_apply, hPP]⟩
  split_ifs with hm
  · simpa using hc
  have hne : eigIn W A μ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨_, ⟨hmem _, Module.End.mem_eigenspace_iff.2 hμ⟩, h0⟩
  have hle : μ ≤ η := not_lt.1 fun h => hm ((hS μ).2 ⟨h, hne⟩)
  have hge : 0 ≤ μ := by
    have h1 := (ContinuousLinearMap.nonneg_iff_isPositive.1 hA).re_inner_nonneg_right (prj W (b i))
    rw [hμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
    have h2 : 0 < ‖prj W (b i)‖ ^ 2 := by positivity
    have h3 : 0 ≤ μ * ‖prj W (b i)‖ ^ 2 := by
      have : RCLike.re ((μ : ℂ) * ((‖prj W (b i)‖ : ℝ) : ℂ) ^ 2) = μ * ‖prj W (b i)‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; rfl
      rw [← this]; exact h1
    exact nonneg_of_mul_nonneg_left h3 h2
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hφc μ ⟨hge, hle⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSummands
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

section SlopeTestRemainingChoices

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem isHS_prj (E : Submodule ℂ H) [FiniteDimensional ℂ E] : IsHilbertSchmidt (prj E) := by
  have hcl : E.topologicalClosure = E :=
    (Submodule.closed_of_finiteDimensional E).submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance
  have h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL) := by
    rw [isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top enorm_lt_top
  exact h1.comp_right E.topologicalClosure.orthogonalProjection

private theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem _ v
  rwa [hV.submodule_topologicalClosure_eq] at h

private theorem prj_eq_zero {V : Submodule ℂ H} {v : H} (hv : v ∈ Vᗮ) : prj V v = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).2 (by rwa [Submodule.orthogonal_closure])

private theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem sub_prj_mem (V : Submodule ℂ H) (v : H) : v - prj V v ∈ Vᗮ := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := V.topologicalClosure) v
  rwa [Submodule.orthogonal_closure] at h

private theorem prj_comm {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (hinv : ∀ v ∈ V, A v ∈ V) (v : H) : prj V (A v) = A (prj V v) := by
  have hu := sub_prj_mem V v
  have hadj : ContinuousLinearMap.adjoint A = A := (ContinuousLinearMap.isSelfAdjoint_iff').1 hA
  have hAu : A (v - prj V v) ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
    exact hu _ (hinv w hw)
  have h : A v = A (prj V v) + A (v - prj V v) := by
    rw [← map_add (f := _)]; congr 1; abel
  rw [h, map_add (f := _), prj_eq_zero hAu, add_zero, prj_self (hinv _ (prj_mem hV v))]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.C.eigSummands :
    UpperTheory.ConvolutionTheory.C.EigSummands := by
  intro H ι _ _ _ V W A x hc ho hW hA hinv hfd
  classical
  let E : ι → Submodule ℂ H := fun i => eigIn (V i) A x
  have hVW : ∀ i, V i ≤ W := fun i => hW ▸ (le_iSup V i).trans (Submodule.le_topologicalClosure _)
  have hEW : ∀ i, E i ≤ eigIn W A x := fun i => inf_le_inf_right _ (hVW i)
  have hEV : ∀ i, E i ≤ V i := fun i => inf_le_left
  have hEo : Pairwise fun i j => E i ⟂ E j := fun i j hij => (ho hij).mono (hEV i) (hEV j)
  have hfin : {i | E i ≠ ⊥}.Finite := by
    have hex : ∀ i : {i | E i ≠ ⊥}, ∃ v ∈ E i, v ≠ 0 := fun i => (Submodule.ne_bot_iff _).1 i.2
    choose v hvE hv0 using hex
    have hli : LinearIndependent ℂ v := linearIndependent_of_ne_zero_of_inner_eq_zero hv0 fun i j hij =>
      (hEo fun e => hij (Subtype.ext e)).inner_eq (hvE i) (hvE j)
    let v' : {i | E i ≠ ⊥} → eigIn W A x := fun i => ⟨v i, hEW i (hvE i)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp (eigIn W A x).subtype hli
    exact Set.finite_coe_iff.1 hli'.finite_of_isNoetherian
  let s := hfin.toFinset
  have hs : ∀ i, i ∈ s ↔ E i ≠ ⊥ := fun i => by simp [s]
  have hPE : ∀ i, ∀ v ∈ eigIn W A x, prj (V i) v ∈ E i := by
    intro i v hv
    refine mem_eigIn.2 ⟨prj_mem (hc i) v, ?_⟩
    rw [← prj_comm (hc i) hA (hinv i), (mem_eigIn.1 hv).2, map_smul]
  have hPP : ∀ i j, i ≠ j → ∀ v, prj (V j) (prj (V i) v) = 0 := fun i j hij v =>
    prj_eq_zero ((ho hij) (prj_mem (hc i) v))
  have hsup : eigIn W A x = ⨆ i ∈ s, E i := by
    refine le_antisymm (fun v hv => ?_) (iSup₂_le fun i _ => hEW i)
    have hu : ∑ i ∈ s, prj (V i) v ∈ ⨆ i ∈ s, E i :=
      Submodule.sum_mem _ fun i hi => (le_iSup₂_of_le i hi le_rfl : E i ≤ ⨆ i ∈ s, E i) (hPE i v hv)
    have huE : ∑ i ∈ s, prj (V i) v ∈ eigIn W A x :=
      (iSup₂_le fun i _ => hEW i : (⨆ i ∈ s, E i) ≤ eigIn W A x) hu
    have hw : v - ∑ i ∈ s, prj (V i) v ∈ W := sub_mem (mem_eigIn.1 hv).1 (mem_eigIn.1 huE).1
    have hPw : ∀ j, prj (V j) (v - ∑ i ∈ s, prj (V i) v) = 0 := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      by_cases hj : j ∈ s
      · rw [Finset.sum_eq_single_of_mem j hj (fun i _ hij => hPP i j hij v), prj_self (prj_mem (hc j) v), sub_self]
      · have h0 : prj (V j) v = 0 := by
          have hb : E j = ⊥ := by_contra fun h => hj ((hs j).2 h)
          have h1 := hPE j v hv
          rw [hb] at h1
          exact (Submodule.mem_bot ℂ).1 h1
        rw [h0, Finset.sum_eq_zero (fun i hi => hPP i j (ne_of_mem_of_not_mem hi hj) v), sub_zero]
    have hperp : v - ∑ i ∈ s, prj (V i) v ∈ Wᗮ := by
      rw [← hW, Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro j
      have h := sub_prj_mem (V j) (v - ∑ i ∈ s, prj (V i) v)
      rwa [hPw j, sub_zero] at h
    have hz : v - ∑ i ∈ s, prj (V i) v = 0 :=
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hperp _ hw)
    rw [sub_eq_zero.1 hz]
    exact hu
  refine ⟨s, hs, hsup, fun T => ?_⟩
  have hS : (⨆ i : s, E i) = eigIn W A x := by
    rw [hsup, iSup_subtype']
  have htc : IsTraceClass (prj (⨆ i : s, E i) ∘L T ∘L prj (⨆ i : s, E i)) := by
    rw [hS]
    exact isTraceClass_comp (isHS_prj _) ((isHS_prj _).comp_left T)
  have h := UpperTheory.ConvolutionTheory.C.traceSum H s (fun i => E i) T (fun i j hij => hEo fun e => hij (Subtype.ext e)) htc
  rw [hS] at h
  rw [h.unique (hasSum_fintype _)]
  exact Finset.sum_coe_sort s fun i => trOn (E i) T
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

private theorem rho_le_height {K : Type} [Field K] [NumberField K] {n : ℕ} {ρ : Fin n → ℝ}
    (hρ : ∀ i, 0 < ρ i) (i : Fin n) :
    ρ i ≤ AutomorphicForm.height (diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i)) ∧
      (ρ i)⁻¹ ≤ AutomorphicForm.height (diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i)) := by
  classical
  set a := diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i) with ha
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hw : locHeight (infAt w a) ≤ AutomorphicForm.height a := by
    have h1 : locHeight (infAt w a) ≤ locHeight (infAt w a) ^ w.mult :=
      le_self_pow₀ (one_le_locHeight _) InfinitePlace.mult_ne_zero
    have h2 : locHeight (infAt w a) ^ w.mult ≤ ∏ v : InfinitePlace K, locHeight (infAt v a) ^ v.mult := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      refine le_mul_of_one_le_right (pow_nonneg (locHeight_pos _).le _) ?_
      exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
        (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl
        fun _ _ => one_le_pow₀ (one_le_locHeight _)
    refine (h1.trans h2).trans ?_
    unfold AutomorphicForm.height
    exact le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight a)) (one_le_finprod_locHeight a)
  constructor
  · refine le_trans ?_ hw
    have e1 := norm_apply_le_locHeight (infAt w a) i i
    rw [infAt_diagUnits_posIdele, coe_diagUnits, Matrix.diagonal_apply_eq, norm_posRealToUnits w (hρ i)] at e1
    rwa [infAt_diagUnits_posIdele]
  · refine le_trans ?_ hw
    have e2 := norm_inv_apply_le_locHeight (infAt w a) i i
    rw [infAt_diagUnits_posIdele, ← map_inv, coe_diagUnits, Matrix.diagonal_apply_eq, Pi.inv_apply,
      Units.val_inv_eq_inv_val, norm_inv, norm_posRealToUnits w (hρ i)] at e2
    rwa [infAt_diagUnits_posIdele]

theorem UpperTheory.ConvolutionTheory.C.polyBdAll :
    UpperTheory.ConvolutionTheory.C.PolyBdAll := by
  intro K _ _ n μ _ a
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  have hbasic : ∃ (C : ℝ) (N : ℕ), ∀ φ : Lp ℂ 2 (quotientMeasure (Gam K n) μ), ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ)
      (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL (K := K) (n := n),
      (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      ‖rconv (Gam K n) μ a φ x‖ ≤ C * √(R ^ N) * ‖φ‖ := by
    obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht a.hasCompactSupport
    have hf2 : ∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
      have := (a.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) a.hasCompactSupport)
      rw [← L2Kernel.eLpNorm_two_sq]
      have hnorm := this.eLpNorm_lt_top
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) this.aestronglyMeasurable,
        ENNReal.toReal_ofNat] at hnorm
      exact (ENNReal.pow_lt_top hnorm).ne
    set A := (∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ).toReal
    have hA : 0 ≤ A := ENNReal.toReal_nonneg
    refine ⟨√(A * max Cc 0), N, ?_⟩
    intro φ b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    obtain ⟨m, hmC, hm⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    have hS : MeasurableSet ((fun y => x * y) '' tsupport (a : normOneGL (K := K) (n := n) → ℂ)) :=
      (a.hasCompactSupport.image (continuous_const_mul x)).measurableSet
    set_option synthInstance.maxHeartbeats 200000 in
    have h1 := enorm_rconv_sq_le (Gam K n) μ a φ x hS (fun y hy => image_eq_zero_of_notMem_tsupport
      fun h' => hy ⟨x⁻¹ * y, h', by simp⟩) hm
    rw [← mul_assoc] at h1
    have h2 := norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) h1
    refine h2.trans ?_
    gcongr
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← Real.sqrt_mul (mul_nonneg hA
      (le_max_right _ _))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (hmC.trans ?_) hA
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
  obtain ⟨C₀, N₀, hC₀⟩ := hbasic
  obtain ⟨C₁, N₁, hC₁⟩ := UpperTheory.V.Fb.siegelHeight K n ω hω hωB t ht
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact hω
  obtain ⟨c, hcdef⟩ : ∃ c, c = heightConst K n := ⟨_, rfl⟩
  have hc : 1 ≤ c := hcdef ▸ one_le_heightConst
  obtain ⟨M', hM'def⟩ : ∃ M', M' = max M 1 := ⟨_, rfl⟩
  have hM'1 : 1 ≤ M' := hM'def ▸ le_max_right _ _
  obtain ⟨E, hEdef⟩ : ∃ E, E = max C₁ 1 * 2 ^ N₁ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = c * (c * M') := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    exact one_le_mul_of_one_le_of_one_le hc (one_le_mul_of_one_le_of_one_le hc hM'1)
  refine ⟨max C₀ 0 * (D * E) ^ N₀, N₁ * N₀, fun φ x => ?_⟩
  have hq1 : 1 ≤ qht x := le_ciInf fun γ => one_le_height _
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K n)
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL (K := K) (n := n) := rationalGL_le_normOneGL ⟨γ, rfl⟩
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : normOneGL (K := K) (n := n), γ₁ = ⟨AdelicGLn.diagonal K n γ, hγ1⟩ := ⟨_, rfl⟩
  have hγΓ : γ₁ ∈ Gam K n := ⟨γ, by rw [hγ₁]; rfl⟩
  have hhq : AutomorphicForm.height (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) ≤
      E * qht x ^ N₁ := by
    obtain ⟨γ', hγ'⟩ : ∃ γ' : Gam K n,
        AutomorphicForm.height (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) < 2 * qht x :=
      exists_lt_of_ciInf_lt (show qht x < 2 * qht x by linarith)
    obtain ⟨δ, hδ⟩ := γ'.2
    have hδ' : AdelicGLn.diagonal K n δ = (((γ' : G1 K n)) : AdelicGLn.AdelicGL K n) := hδ
    have e : AdelicGLn.diagonal K n (γ * δ⁻¹) * (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) =
        AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n) := by
      rw [Subgroup.coe_mul, ← hδ', map_mul, map_inv]
      group
    have h1 := hC₁ (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n) (γ * δ⁻¹) (e ▸ hγ)
    rw [e] at h1
    refine h1.trans ?_
    have hy := height_pos (((γ' : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)
    calc C₁ * _ ≤ max C₁ 1 * (2 * qht x) ^ N₁ :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hy.le hγ'.le _) (pow_nonneg hy.le _)
            (zero_le_one.trans (le_max_right _ _))
      _ = E * qht x ^ N₁ := by rw [hEdef, mul_pow]; ring
  rw [← rconv_mul_left (Gam K n) μ a φ hγΓ x]
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hx⟩ := hγ
  have hx' : ((γ₁ * x : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) =
      b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk := by
    rw [hγ₁]; exact hx
  obtain ⟨h, hhdef⟩ : ∃ h, h = AutomorphicForm.height (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) :=
    ⟨_, rfl⟩
  rw [← hhdef] at hhq
  have hh1 : 1 ≤ h := hhdef ▸ one_le_height _
  have hdiag : AutomorphicForm.height (diagUnits n fun i => posIdele (K := K) (ρ i) (hρ i)) ≤ D * h := by
    have e : diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) =
        b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n)) * kk⁻¹ := by
      rw [hx]; group
    rw [e]
    have hbM : AutomorphicForm.height b⁻¹ ≤ M' := by
      rw [height_inv, hM'def]; exact (hM b hb).trans (le_max_left _ _)
    have hk : AutomorphicForm.height kk⁻¹ = 1 :=
      height_eq_one_of_mem_maxCompact (inv_mem hkk)
    have h1 := height_mul_le (b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))) kk⁻¹
    have h2 := height_mul_le b⁻¹ (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))
    rw [hk, mul_one, ← hcdef] at h1
    rw [← hcdef, ← hhdef] at h2
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have h3 : c * AutomorphicForm.height b⁻¹ * h ≤ c * M' * h := by gcongr
    calc _ ≤ c * AutomorphicForm.height (b⁻¹ * (AdelicGLn.diagonal K n γ * (x : AdelicGLn.AdelicGL K n))) := h1
      _ ≤ c * (c * M' * h) := mul_le_mul_of_nonneg_left (h2.trans h3) hc0
      _ = D * h := by rw [hDdef]; ring
  have hDh1 : 1 ≤ D * h := one_le_mul_of_one_le_of_one_le hD1 hh1
  have hR1 : 1 ≤ (D * h) ^ 2 := one_le_pow₀ hDh1
  have hratio : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ (D * h) ^ 2 := by
    intro i j _
    have h1 := ((rho_le_height (K := K) hρ i).1).trans hdiag
    have h2 := ((rho_le_height (K := K) hρ j).2).trans hdiag
    rw [div_eq_mul_inv, sq]
    exact mul_le_mul h1 h2 (inv_pos.2 (hρ j)).le (zero_le_one.trans hDh1)
  have hmain := hC₀ φ b hb ρ hρ hs kk hkk (γ₁ * x) hx' _ hR1 hratio
  have hsq : √(((D * h) ^ 2) ^ N₀) = (D * h) ^ N₀ := by
    rw [pow_right_comm, Real.sqrt_sq (pow_nonneg (zero_le_one.trans hDh1) _)]
  rw [hsq] at hmain
  have hfin : (D * h) ^ N₀ ≤ (D * E) ^ N₀ * qht x ^ (N₁ * N₀) := by
    rw [pow_mul, ← mul_pow, mul_assoc]
    exact pow_le_pow_left₀ (zero_le_one.trans hDh1) (mul_le_mul_of_nonneg_left hhq (zero_le_one.trans hD1)) _
  have hnn : 0 ≤ (D * h) ^ N₀ := pow_nonneg (zero_le_one.trans hDh1) _
  calc _ ≤ C₀ * (D * h) ^ N₀ * ‖φ‖ := hmain
    _ ≤ max C₀ 0 * (D * h) ^ N₀ * ‖φ‖ := by gcongr; exact le_max_left _ _
    _ ≤ max C₀ 0 * ((D * E) ^ N₀ * qht x ^ (N₁ * N₀)) * ‖φ‖ := by
        have : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
        gcongr
    _ = max C₀ 0 * (D * E) ^ N₀ * qht x ^ (N₁ * N₀) * ‖φ‖ := by ring
end

