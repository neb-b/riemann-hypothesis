module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

private theorem haar {n : ℕ} {U : Type} [Group U] [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (e : archCompact K n ≃ₜ* (ι → U)) (ν : Measure U) [IsProbabilityMeasure ν] (hl : ∀ k, MeasurePreserving (k * ·) ν ν)
    (hr : ∀ k, MeasurePreserving (· * k) ν ν) : IsHaarK (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := by
  have hm : Measurable e.symm := e.symm.continuous.measurable
  have hE : MeasurePreserving e.symm (Measure.pi fun _ : ι => ν) (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := ⟨hm, rfl⟩
  refine ⟨inferInstance, fun k => ?_, fun k => ?_⟩
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hl (e k i)) (fun x => ?_) (continuous_const_mul k).measurable
    change e.symm (e k * x) = _
    rw [map_mul, e.symm_apply_apply]
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hr (e k i)) (fun x => ?_) (continuous_mul_const k).measurable
    change e.symm (x * e k) = _
    rw [map_mul, e.symm_apply_apply]

private theorem coe_arc {n : ℕ} (k : archCompact K n) :
    ((arc1 k : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (k : archGroup K n) := by
  rw [arc1, ← retract_infEmb]
  exact congrArg Subtype.val (retractOne_coe (⟨_, maxCompact_le_normOneGL k.2⟩ : normOneGL (K := K) (n := n)))

private theorem zt0 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem inf_fst {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n x a b).1 =
      (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from (x.1 : ArchMatrix K n)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_infEmb]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

private theorem inf_snd {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    (infEmb K n x a b).2 = (1 : Matrix (Fin n) (Fin n) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_snd, prodEquiv_infEmb]
  rfl

omit [Fintype ι] in
private theorem ent (C : Co K ι) {n : ℕ} (x : ι → unitaryGroup (Fin n) ℂ) (i : ι) (a b : Fin n) :
    C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n ((C.Φ n).symm x : archCompact K n) a b).1) i =
      (x i : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [inf_fst, ← C.Ψ_val, ← C.Φ_val, ContinuousMulEquiv.apply_symm_apply]

omit [Fintype ι] in
private theorem blkA (C : Co K ι) (a b : ι → U2) :
    lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i)) := by
  apply Subtype.ext
  rw [(blkLaws (K := K)).1, neg_zero, zt0, mul_one, mul_one, coe_arc, coe_arc, coe_arc]
  ext r s
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective r
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective s
  refine Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace K).injective (C.c.injective (funext fun i => ?_))) ?_
  · rw [ent, u4.1]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact ent C a i r s
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · exact ent C b i r s
  · rw [inf_snd, ← Matrix.submatrix_apply (1 : Matrix _ _ _) finSumFinEquiv finSumFinEquiv, Matrix.submatrix_one_equiv,
      ← Matrix.fromBlocks_one]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact inf_snd _ r s
    · rfl
    · rfl
    · exact inf_snd _ r s

private theorem cmm {n : ℕ} (g : archGroup K n) (h : FA K n) : Commute (archP K n g) (fin1 h) :=
  (MultiplicityOne.finProj_mul_archProj_comm h g).symm

private theorem dec (n : ℕ) (k : G1 K n) (hk : k ∈ KG K n) :
    ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  have hk' : (k : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact := hk
  have e := infEmb_infPart_mul_finEmb_finPart (k : AdelicGLn.AdelicGL K n)
  have hf : finEmb K n (finPart K n k) ∈ Reduction.maxCompact := by
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have : infAt w (finEmb K n (finPart K n k)) = 1 := by
        refine Units.ext (Matrix.ext fun a b => ?_)
        change (finEmb K n (finPart K n k) a b).1 w = _
        rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_finEmb]
        by_cases h : a = b
        · subst h; simp; rfl
        · simp [h]; rfl
      rw [this]; exact one_mem _
    · have : finAt v (finEmb K n (finPart K n k)) = finAt v (k : AdelicGLn.AdelicGL K n) := by
        exact Units.ext (Matrix.ext fun a b => rfl)
      rw [this]; exact hk'.2 v
  refine ⟨⟨infPart K n k, ?_⟩, finPart K n k, (AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, Subtype.ext ?_⟩
  · change infEmb K n (infPart K n k) ∈ Reduction.maxCompact
    rw [eq_mul_inv_of_mul_eq e]
    exact mul_mem hk' (inv_mem hf)
  · have : (AdelicGLn.finiteRestrictedEquiv K n (finPart K n k) v : GL (Fin n) (v.adicCompletion K)) =
        finAt v (k : AdelicGLn.AdelicGL K n) := by
      exact Units.ext (Matrix.ext fun a b => rfl)
    rw [this]; exact hk'.2 v
  · rw [Subgroup.coe_mul, coe_arc, fin1, MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL hf)]
    exact e.symm

private noncomputable def GG (C : Co K ι) : (ι → GL (Fin 2) ℂ) →* G1 K 2 := (archP K 2).comp (C.Ψ 2).symm.toMonoidHom

omit [Fintype ι] in
private theorem gl_eq (C : Co K ι) (i : ι) (a : GL (Fin 2) ℂ) : C.gl i a = GG C (Pi.mulSingle i a) := rfl

omit [Fintype ι] in
private theorem GG_eq (C : Co K ι) (g : archGroup K 2) : archP K 2 g = GG C (C.Ψ 2 g) :=
  congrArg (archP K 2) ((C.Ψ 2).symm_apply_apply g).symm

omit [Fintype ι] in
private theorem GG_cmm (C : Co K ι) (x : ι → GL (Fin 2) ℂ) (h : FA K 2) : Commute (GG C x) (fin1 h) := cmm _ h

omit [Fintype ι] in
private theorem ms_cont (i : ι) : Continuous fun m : GL (Fin 2) ℂ => (Pi.mulSingle i m : ι → GL (Fin 2) ℂ) :=
  continuous_pi fun j => by
    by_cases h : j = i
    · subst h; simpa using continuous_id'
    · simpa [h] using continuous_const

omit [Fintype ι] in
private theorem spl (C : Co K ι) (i : ι) (g : G1 K 2) : ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b) := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj g
  obtain ⟨x, hx⟩ : ∃ x, archProj K 2 A = GG C x := ⟨_, GG_eq C ⟨A, Subgroup.mem_top _⟩⟩
  refine ⟨x i, GG C (Function.update x i 1) * fin1 u, ?_, fun b => Commute.mul_left ?_ ?_⟩
  · have : Pi.mulSingle i (x i) * Function.update x i 1 = x := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [gl_eq, ← mul_assoc, ← map_mul, this, hx]
  · rw [gl_eq]
    refine Commute.map ?_ (GG C)
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [gl_eq]
    exact (GG_cmm C _ u).symm

omit [Fintype ι] in
private theorem lst (C : Co K ι) (g : archGroup K 2) :
    ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod := by
  refine ⟨C.Ψ 2 g, fun l hl hm => ?_⟩
  rw [GG_eq C]
  generalize C.Ψ 2 g = x
  have : (l.map fun i => (Pi.mulSingle i (x i) : ι → GL (Fin 2) ℂ)).prod = x := by
    funext j
    rw [Pi.list_prod_apply, List.map_map, List.prod_map_eq_pow_single j, List.count_eq_one_of_mem hl (hm j)]
    · simp
    · intro i hi _
      simp [hi.symm]
  conv_lhs => rw [← this, map_list_prod, List.map_map]
  rfl

omit [Fintype ι] in
private theorem un_eq (C : Co K ι) (i : ι) (m : U2) : C.un i m = C.gl i (kC m) := by
  refine congrArg (archP K 2) ((C.Ψ 2).injective (funext fun j => Units.ext ?_))
  rw [← C.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι), IsHaarK C.κ₂ ∧ (∀ μ, Haar4 μ → IsHaarK (C.κ₄ μ)) ∧ (∀ i m, C.un i m = C.gl i (kC m)) ∧ (∀ i, Continuous (C.gl i)) ∧
      (∀ i a b, C.gl i (a * b) = C.gl i a * C.gl i b) ∧ (∀ i j, i ≠ j → ∀ a b, Commute (C.gl i a) (C.gl j b)) ∧
      (∀ i a (h : FA K 2), Commute (C.gl i a) (fin1 h)) ∧ (∀ i (g : G1 K 2), ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b)) ∧
      (∀ g : archGroup K 2, ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod) ∧
      (∀ a b : ι → U2, lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i))) ∧
      (∀ n (k : archCompact K n) (h : FA K n), Commute (arc1 k) (fin1 h)) ∧
      ∀ n, ∀ k ∈ KG K n, ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  intro K _ _ _ ι _ C
  refine ⟨haar _ _ (measurePreserving_mul_left μK) (measurePreserving_mul_right μK), fun μ hμ => ?_, un_eq C, fun i => ?_,
    fun i a b => ?_, fun i j hij a b => ?_, fun i a h => cmm _ h, spl C, lst C, blkA C, fun n k h => cmm _ h, dec⟩
  · haveI := hμ.prob
    exact haar _ μ hμ.left hμ.right
  · exact continuous_archP.comp ((C.Ψ 2).symm.continuous.comp (ms_cont i))
  · rw [gl_eq, gl_eq, gl_eq, Pi.mulSingle_mul, map_mul]
  · rw [gl_eq, gl_eq]
    exact (Pi.mulSingle_commute (f := fun _ => GL (Fin 2) ℂ) hij a b).map (GG C)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefIdem
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem chi_mul_neg (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi ν θ * chi ν (-θ) = 1 := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  simp

private theorem chi_mul_conj (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi ν θ * conj (chi ν θ) = 1 := by
  have h : conj (chi ν θ) = chi ν (-θ) := by
    unfold chi
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Complex.exp_conj, map_mul, map_sum, Complex.conj_I]
    congr 1
    simp only [map_mul, map_intCast, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
  rw [h, chi_mul_neg]

private theorem int_zero {μ : Measure U4} (hH : Haar4 μ) {ν ν' : Fin (2 + 2) → ℤ} (hne : ν ≠ ν') (F : U4 → ℂ)
    (hF : ∀ θ h, chi ν' θ * F (dg θ * h) = chi ν θ * F h) : ∫ h, F h ∂μ = 0 := by
  obtain ⟨θ, hθ⟩ : ∃ θ, chi ν θ ≠ chi ν' θ := by
    by_contra hc
    push_neg at hc
    exact hne (u4.2.2.2.2.2.2.2.2.2.2.1 ν ν' hc)
  have hT : ∫ h, F (dg θ * h) ∂μ = ∫ h, F h ∂μ :=
    (hH.left (dg θ)).integral_comp (Homeomorph.mulLeft (dg θ)).measurableEmbedding F
  have h1 : chi ν' θ * ∫ h, F h ∂μ = chi ν θ * ∫ h, F h ∂μ :=
    calc chi ν' θ * ∫ h, F h ∂μ = chi ν' θ * ∫ h, F (dg θ * h) ∂μ := by rw [hT]
      _ = ∫ h, chi ν' θ * F (dg θ * h) ∂μ := (integral_const_mul _ _).symm
      _ = ∫ h, chi ν θ * F h ∂μ := integral_congr_ae (Eventually.of_forall fun h => hF θ h)
      _ = chi ν θ * ∫ h, F h ∂μ := integral_const_mul _ _
  have h2 : (chi ν θ - chi ν' θ) * ∫ h, F h ∂μ = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hθ)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefIdem :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → Continuous ψ ∧ ψ 1 = 1 ∧ Idem μ (eOf μ ψ) ∧ RFix μ (eOf μ ψ) ψ := by
  intro μ ψ n q n' q' hH hO hC
  haveI : CompactSpace U4 := u4.2.2.2.2.2.2.2.2.2.2.2.1
  haveI : IsProbabilityMeasure μ := hH.prob
  obtain ⟨J, _, j₀, a, b, ν, hcont, hexp, ha0, hb0, hν0, hw, -, hne⟩ := hC.exp
  have hψc : Continuous ψ := ha0 ▸ (hcont j₀).1
  have hψ1 : ψ 1 = 1 := by
    have h := hC.res 1 1
    rw [u4.2.2.1, KT.psi_one, KT.psi_one, mul_one] at h
    exact h
  have hint : ∀ f : U4 → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinv : Continuous fun h : U4 => h⁻¹ := continuous_inv
  have hψdg : ∀ θ h, ψ (dg θ * h) = chi (wt n q n' q') θ * ψ h := fun θ h => by
    have := (hw j₀ θ h).2.1
    rwa [ha0] at this
  set c : ℝ := ∫ h, ‖ψ h‖ ^ 2 ∂μ with hc
  have hcpos : 0 < c := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : U4)) (by fun_prop)
      (HasCompactSupport.of_compactSpace _) (fun _ => by positivity) ?_
    simp [hψ1]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hmc : ∀ h, ψ h * conj (ψ h) = ((‖ψ h‖ ^ 2 : ℝ) : ℂ) := fun h => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcC : ∫ h, ψ h * conj (ψ h) ∂μ = (c : ℂ) := by
    simp_rw [hmc]
    exact integral_complex_ofReal
  have key1 : ∀ k, ∫ h, ψ h * ψ (h⁻¹ * k) ∂μ = c * ψ k := fun k => by
    have e1 : ∀ h, ψ h * ψ (h⁻¹ * k) = ∑ j, (ψ h * a j h⁻¹) * b j k := fun h => by
      rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
    simp_rw [e1]
    rw [integral_finsetSum (μ := μ) Finset.univ (f := fun j h => ψ h * a j h⁻¹ * b j k) fun j _ =>
      hint _ ((hψc.mul ((hcont j).1.comp hinv)).mul continuous_const)]
    simp_rw [integral_mul_const]
    rw [Finset.sum_eq_single j₀]
    · rw [ha0, hb0]
      congr 1
      rw [← hcC]
      exact integral_congr_ae (Eventually.of_forall fun h => by
        show ψ h * ψ h⁻¹ = ψ h * conj (ψ h)
        rw [hC.star])
    · intro j _ hj
      rw [int_zero hH (ν := wt n q n' q') (ν' := ν j) (Ne.symm (hν0 ▸ hne j hj)) _ ?_, zero_mul]
      intro θ h
      rw [_root_.mul_inv_rev, u4.2.2.2.2.2.2.2.2.2.1, hψdg, (hw j (-θ) h⁻¹).1]
      have := chi_mul_neg (ν j) θ
      linear_combination (chi (wt n q n' q') θ * ψ h * a j h⁻¹) * this
    · intro h
      exact absurd (Finset.mem_univ _) h
  have key2 : ∀ g, ∫ k, conj (ψ k) * ψ (g * k) ∂μ = c * ψ g := fun g => by
    have e1 : ∀ k, conj (ψ k) * ψ (g * k) = ∑ j, a j g * (conj (ψ k) * b j k) := fun k => by
      rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e1]
    rw [integral_finsetSum (μ := μ) Finset.univ (f := fun j k => a j g * (conj (ψ k) * b j k)) fun j _ =>
      hint _ (continuous_const.mul ((Complex.continuous_conj.comp hψc).mul (hcont j).2))]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single j₀]
    · rw [ha0, hb0, mul_comm]
      congr 1
      rw [← hcC]
      exact integral_congr_ae (Eventually.of_forall fun h => mul_comm _ _)
    · intro j _ hj
      rw [int_zero hH (ν := ν j) (ν' := wt n q n' q') (hν0 ▸ hne j hj) _ ?_, mul_zero]
      intro θ k
      rw [hψdg, (hw j θ k).2.2, map_mul]
      have := chi_mul_conj (wt n q n' q') θ
      linear_combination (conj (ψ k) * chi (ν j) θ * b j k) * this
    · intro h
      exact absurd (Finset.mem_univ _) h
  have heOf : ∀ k, eOf μ ψ k = (c : ℂ)⁻¹ * conj (ψ k) := fun k => rfl
  refine ⟨hψc, hψ1, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact continuous_const.mul (Complex.continuous_conj.comp hψc)
  · intro k
    rw [heOf, heOf, hC.star, map_mul, map_inv₀, Complex.conj_ofReal]
  · intro k
    have e1 : ∀ h, eOf μ ψ h * eOf μ ψ (h⁻¹ * k) = ((c : ℂ)⁻¹ * (c : ℂ)⁻¹) * conj (ψ h * ψ (h⁻¹ * k)) := fun h => by
      rw [heOf, heOf, map_mul]
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_conj, key1, heOf, map_mul, Complex.conj_ofReal]
    field_simp
  · intro g
    have e1 : ∀ k, eOf μ ψ k * ψ (g * k) = (c : ℂ)⁻¹ * (conj (ψ k) * ψ (g * k)) := fun k => by
      rw [heOf, mul_assoc]
    simp_rw [e1]
    rw [integral_const_mul, key2]
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.SingleShift
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section

open PositivityTheory.Rg.Tf.Geo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem gal_infEmb (σ : E ≃ₐ[F] E) (n : ℕ) (a : archGroup E n) :
    Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a) =
      infEmb E n (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) := by
  apply (AdelicGLn.prodEquiv E n).injective
  rw [prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · have h1 : UpperTheory.ConvolutionTheory.T4.pI E n (infEmb E n a) = (archEquiv E n).symm a := congrArg Prod.fst (prodEquiv_infEmb a)
    rw [← UpperTheory.ConvolutionTheory.K.galAdEq F E σ, ← h1]
    exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).1 _
  · have h2 : (AdelicGLn.prodEquiv E n (infEmb E n a)).2 = 1 := congrArg Prod.snd (prodEquiv_infEmb a)
    have h3 : (AdelicGLn.prodEquiv E n
        (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a))).2 =
        mapGL n (Formalism.L2.Host.CT.finMap σ.toRingEquiv) (AdelicGLn.prodEquiv E n (infEmb E n a)).2 :=
      Units.ext (Matrix.ext fun _ _ => rfl)
    rw [h3, h2, map_one]

private theorem compA_shift {σ : E ≃ₐ[F] E} {m : ℕ} (D : InfD σ m) (n : ℕ) (a : archGroup E n) (i : Fin (m + 1)) :
    compA D n i (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) = compA D n (i + 1) a := by
  have e : ∀ j x, compA D n j x = archEquiv F n (D.comp n j ((archEquiv E n).symm x)) := fun _ _ => rfl
  rw [e, e, ContinuousMulEquiv.symm_apply_apply]
  congr 1
  exact Units.ext (Matrix.ext fun p q => D.map_shift _ i)

private theorem single_shift {ι G : Type} [One G] (s i : Fin 2) (u v : ι) (m : G) :
    (Pi.mulSingle (s, u) m : Fin 2 × ι → G) (i + 1, v) = (Pi.mulSingle (s + 1, u) m : Fin 2 × ι → G) (i, v) := by
  have h : i + 1 = s ↔ i = s + 1 := by revert i s; decide
  simp only [Pi.mulSingle_apply, Prod.mk.injEq, h]

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ s u m, θ.e (CE.un (s, u) m) = CE.un (s + 1, u) m := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ s u m
  apply Subtype.ext
  rw [hθ]
  simp only [Co.un, arc1, archimedeanProjection_maximalCompact]
  rw [gal_infEmb]
  congr 1
  apply (CE.Ψ 2).injective
  funext ⟨i, v⟩
  rw [hC, compA_shift, ← hC]
  apply Units.ext
  rw [← CE.Φ_val, ← CE.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  congr 1
  convert single_shift s i u v m
end

