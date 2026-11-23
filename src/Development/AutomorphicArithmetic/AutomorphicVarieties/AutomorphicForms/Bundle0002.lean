module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightGeArchOpNorm
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem loc_le_height {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) (w : InfinitePlace E) :
    locHeight (Reduction.infAt w g) ≤ AutomorphicForm.height g := by
  classical
  have h1 : locHeight (Reduction.infAt w g) ≤ locHeight (Reduction.infAt w g) ^ w.mult :=
    le_self_pow₀ (one_le_locHeight _) InfinitePlace.mult_pos.ne'
  have h2 : locHeight (Reduction.infAt w g) ^ w.mult ≤
      ∏ w : InfinitePlace E, locHeight (Reduction.infAt w g) ^ w.mult := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
    refine le_mul_of_one_le_right (pow_nonneg (locHeight_pos _).le _) ?_
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
      (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun _ _ => one_le_pow₀ (one_le_locHeight _)
  exact h1.trans (h2.trans (le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight g))
    (one_le_finprod_locHeight g)))

private theorem norm_le_height {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ} (g : GA E a) :
    ‖TR.toL (GeneralLinearGroup.map (TR.pInf E) g).val‖ ≤ AutomorphicForm.height g := by
  have h0 : 0 ≤ AutomorphicForm.height g := (height_pos g).le
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  refine le_trans (le_of_eq ?_) ((norm_apply_le_locHeight _ i j).trans (loc_le_height g w))
  have hi := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).isometry
  exact hi.norm_map_of_map_zero
    (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))) ((g.val i j).1 w)

theorem UpperTheory.adelicHeight_ge_archOpNorm :
    UpperTheory.V.Fb.HeightGe := by
  intro E _ _ _ a g
  have h1 := norm_le_height g
  have h2 := norm_le_height g⁻¹
  rw [height_inv, map_inv] at h2
  have h3 := one_le_height g
  unfold TR.height
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightInfGLLeOpNorm
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem ent (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (y : GL (Fin a) (TR.Rinf E))
    (w : InfinitePlace E) (i j : Fin a) :
    ‖(Reduction.infAt w (TR.infGL E a y) : Matrix (Fin a) (Fin a) w.Completion) i j‖ ≤ ‖TR.toL y.val‖ := by
  have h := congrArg (fun g : GL (Fin a) (InfiniteAdeleRing E) => g.val i j w)
    (map_cornerGL_of_hom (TR.sInf E) (RingHom.fst (InfiniteAdeleRing E) (Af E))
      (TR.infEq E).toRingHom (fun _ => rfl) y)
  have e : (Reduction.infAt w (TR.infGL E a y) : Matrix (Fin a) (Fin a) w.Completion) i j =
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y.val i j w) := h
  have e0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
  rw [e, (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.isometry.norm_map_of_map_zero e0]
  exact (norm_le_pi_norm (y.val i j) w).trans
    ((norm_le_pi_norm (TR.toL y.val i) j).trans (norm_le_pi_norm (TR.toL y.val) i))

private theorem finOne (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (y : GL (Fin a) (TR.Rinf E))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) : Reduction.finAt v (TR.infGL E a y) = 1 := by
  have h1 : Reduction.finAt v (TR.infGL E a y) = Reduction.finAt v (1 : AdelicGLn.AdelicGL E a) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h := congrArg (fun g : GL (Fin a) (Af E) => g.val i j v)
      ((TR.pFin_infGL y).trans (map_one (GeneralLinearGroup.map (n := Fin a) (pFin E))).symm)
    exact h
  rw [h1, Reduction.finAt_one]

theorem UpperTheory.adelicHeight_infGL_le_opNorm :
    UpperTheory.V.Fb.HeightLe := by
  intro E _ _ _ a
  refine ⟨∑ w : InfinitePlace E, w.mult, fun y => ?_⟩
  have n1 := norm_nonneg (TR.toL y.val)
  have n2 := norm_nonneg (TR.toL (y⁻¹).val)
  unfold AutomorphicForm.height
  rw [finprod_eq_one_of_forall_eq_one fun v => by rw [finOne, locHeight_one], mul_one,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun w _ => (pow_pos (locHeight_pos _) _).le) fun w _ =>
    pow_le_pow_left₀ (locHeight_pos _).le ?_ _
  unfold TR.height
  refine locHeight_le (by linarith) (fun i j => ?_) fun i j => ?_
  · have := ent E a y w i j
    linarith
  · have := ent E a y⁻¹ w i j
    rw [map_inv, Reduction.infAt_inv] at this
    linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormDetLeHeightPow
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem UpperTheory.V.Fb.norm_term_le {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E)
    (σ : Equiv.Perm (Fin n)) :
    ‖Equiv.Perm.sign σ • ∏ i, (g : Matrix (Fin n) (Fin n) E) (σ i) i‖ ≤ locHeight g ^ n := by
  have h : ‖∏ i, (g : Matrix (Fin n) (Fin n) E) (σ i) i‖ ≤ locHeight g ^ n := by
    rw [norm_prod]
    calc ∏ i, ‖(g : Matrix (Fin n) (Fin n) E) (σ i) i‖ ≤ ∏ _i : Fin n, locHeight g :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => norm_apply_le_locHeight g _ _
      _ = locHeight g ^ n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

private theorem UpperTheory.V.Fb.norm_det_le_arch {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) :
    ‖(g : Matrix (Fin n) (Fin n) E).det‖ ≤ n.factorial * locHeight g ^ n := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun σ _ => norm_term_le g σ).trans ?_)
  simp [Fintype.card_perm]

private theorem UpperTheory.V.Fb.norm_det_le_ultra {E : Type*} [NormedField E] [IsUltrametricDist E] {n : ℕ}
    (g : GL (Fin n) E) : ‖(g : Matrix (Fin n) (Fin n) E).det‖ ≤ locHeight g ^ n := by
  rw [Matrix.det_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_pos (locHeight_pos g) n).le
    fun σ _ => norm_term_le g σ

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction IsDedekindDomain in
theorem UpperTheory.adelicNorm_det_le_height_pow :
    UpperTheory.V.Fb.DetBound := by
  classical
  intro K _ _ n
  refine ⟨∏ w : InfinitePlace K, (n.factorial : ℝ) ^ w.mult, n,
    Finset.prod_pos fun w _ => pow_pos (by exact_mod_cast n.factorial_pos) _, fun g => ?_⟩
  have hi : ∀ w : InfinitePlace K, ((AdelicGLn.det K n g : AdeleRing (𝓞 K) K)).1 w =
      (infAt w g : Matrix (Fin n) (Fin n) w.Completion).det := fun w => by
    rw [AdelicGLn.coe_det, ← infEval_apply, RingHom.map_det]; rfl
  have hf : ∀ v : HeightOneSpectrum (𝓞 K), ((AdelicGLn.det K n g : AdeleRing (𝓞 K) K)).2 v =
      (finAt v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)).det := fun v => by
    rw [AdelicGLn.coe_det, ← finEval_apply, RingHom.map_det]; rfl
  have h1 := finite_mulSupport_norm (AdelicGLn.det K n g)
  have h2 := finite_mulSupport_locHeight_finAt g
  have e1 := finprod_eq_prod_of_mulSupport_subset _ (s := (h1.union h2).toFinset)
    (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl hv)
  have e2 := finprod_eq_prod_of_mulSupport_subset _ (s := (h1.union h2).toFinset)
    (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inr hv)
  rw [ideleModule_eq, AutomorphicForm.height, e1, e2, mul_pow, ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => ?_)
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => by have := locHeight_pos (infAt w g); positivity)
  · rw [hi, ← pow_mul, mul_comm w.mult n, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_arch _) _
  · rw [hf]; exact norm_det_le_ultra _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormVecMulGeOfHeight
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem back_eq {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) (z : Fin n → E) :
    z = (z ᵥ* (g : Matrix (Fin n) (Fin n) E)) ᵥ* ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]

private theorem fin_bound {E : Type*} [NormedField E] [IsUltrametricDist E] {n : ℕ}
    (g : GL (Fin n) E) (z : Fin n → E) :
    ‖z‖ ≤ locHeight g * ‖z ᵥ* (g : Matrix (Fin n) (Fin n) E)‖ := by
  have hp := locHeight_pos g
  set y := z ᵥ* (g : Matrix (Fin n) (Fin n) E) with hy
  have h0 : 0 ≤ locHeight g * ‖y‖ := by positivity
  have hz := back_eq g z
  rw [← hy] at hz
  rw [hz]
  refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  simp only [vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun i _ => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul (norm_inv_apply_le_locHeight g i j) (norm_le_pi_norm y i) (norm_nonneg _) hp.le

private theorem inf_bound {E : Type*} [NormedField E] {n : ℕ}
    (g : GL (Fin n) E) (z : Fin n → E) :
    Reduction.euclidNorm z ≤ (√n * n + 1) * locHeight g *
      Reduction.euclidNorm (z ᵥ* (g : Matrix (Fin n) (Fin n) E)) := by
  have hp := locHeight_pos g
  set y := z ᵥ* (g : Matrix (Fin n) (Fin n) E) with hy
  have he := Reduction.euclidNorm_nonneg y
  have h0 : 0 ≤ (n : ℝ) * (locHeight g * Reduction.euclidNorm y) := by positivity
  have hz := back_eq g z
  rw [← hy] at hz
  have h1 : ‖z‖ ≤ (n : ℝ) * (locHeight g * Reduction.euclidNorm y) := by
    rw [hz]
    refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    simp only [vecMul, dotProduct]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => locHeight g * Reduction.euclidNorm y)
      fun i _ => ?_).trans (by simp)
    rw [norm_mul, mul_comm]
    exact mul_le_mul (norm_inv_apply_le_locHeight g i j) (Reduction.norm_le_euclidNorm y i)
      (norm_nonneg _) hp.le
  calc Reduction.euclidNorm z ≤ √n * ‖z‖ := Reduction.euclidNorm_le_sqrt_mul z
    _ ≤ √n * ((n : ℝ) * (locHeight g * Reduction.euclidNorm y)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = (√n * n) * (locHeight g * Reduction.euclidNorm y) := by ring
    _ ≤ (√n * n + 1) * (locHeight g * Reduction.euclidNorm y) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

private theorem finprod_bound {ι : Type*} {a b c : ι → ℝ} (ha : (Function.mulSupport a).Finite)
    (hb : (Function.mulSupport b).Finite) (hc : (Function.mulSupport c).Finite)
    (h0 : ∀ i, 0 ≤ a i) (h : ∀ i, a i ≤ b i * c i) :
    ∏ᶠ i, a i ≤ (∏ᶠ i, b i) * ∏ᶠ i, c i := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset a (s := ((ha.union hb).union hc).toFinset)
      (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl (Or.inl hv)),
    finprod_eq_prod_of_mulSupport_subset b (s := ((ha.union hb).union hc).toFinset)
      (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl (Or.inr hv)),
    finprod_eq_prod_of_mulSupport_subset c (s := ((ha.union hb).union hc).toFinset)
      (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inr hv),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i _ => h0 i) fun i _ => h i

private theorem combine {A B C P Q R S : ℝ} (hi : A ≤ C * P * Q) (hf : B ≤ R * S) (hA : 0 ≤ A)
    (hB : 0 ≤ B) : A * B ≤ C * (P * R) * (Q * S) :=
  (mul_le_mul hi hf hB (hA.trans hi)).trans (le_of_eq (by ring))

private theorem adelic_bound {K : Type} [Field K] [NumberField K] {n : ℕ}
    (g : AdelicGLn.AdelicGL K n) {y : Fin n → AdeleRing (𝓞 K) K}
    (hy : Reduction.HasFiniteContent y) :
    Reduction.adelicNorm y ≤ (∏ w : InfinitePlace K, (√n * n + 1 : ℝ) ^ w.mult) *
      AutomorphicForm.height g * Reduction.adelicNorm (y ᵥ* g.val) := by
  refine combine ?_ ?_
    (Finset.prod_nonneg fun _ _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _)
    (finprod_nonneg fun _ => norm_nonneg _)
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _)
      fun w _ => ?_
    rw [← mul_pow, ← mul_pow, Reduction.infComp_vecMul_GL]
    exact pow_le_pow_left₀ (Reduction.euclidNorm_nonneg _) (inf_bound _ _) _
  · refine finprod_bound hy.finite_mulSupport (finite_mulSupport_locHeight_finAt g)
      (hy.vecMul g).finite_mulSupport (fun _ => norm_nonneg _) fun v => ?_
    rw [Reduction.finComp_vecMul_GL]
    exact fin_bound _ _

theorem UpperTheory.adelicNorm_vecMul_ge_of_height :
    UpperTheory.V.Fb.VecLower := by
  intro K _ _ n
  refine ⟨∏ w : InfinitePlace K, (√n * n + 1 : ℝ) ^ w.mult, 1,
    Finset.prod_pos fun w _ => by positivity, fun g x hx => ?_⟩
  rw [pow_one]
  exact (Reduction.one_le_adelicNorm_ratVec hx).trans
    (adelic_bound g (Reduction.hasFiniteContent_ratVec hx))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

open MeasureTheory in
theorem UpperTheory.constantTerm_eq_zero_of_isCuspidal :
    UpperTheory.V.Fb.CuspTo := by
  intro E _ _ a φ _ _ h r h0 h1 g
  have hμ : (unipMeasure E a r).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos a r → AdeleRing (𝓞 E) E) := inferInstance
  have hL : ratN E a r = unipLattice E a r := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hu : ∀ x : UPos a r → AdeleRing (𝓞 E) E, unip x = unipGL x := fun x => Units.ext rfl
  have hF : IsAddFundamentalDomain (ratN E a r) (unipFundamentalDomain E a r) (unipMeasure E a r) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have key := h r h0 h1 (unipMeasure E a r) (unipFundamentalDomain E a r) hμ hF g
  simp only [hu] at key
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ContDiffChartOfIsArchSmooth
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb
open scoped ContDiff Topology

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private noncomputable def toArch (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) :
    TR.Lie E a →L[ℝ] ArchMatrix E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => matEq E a (Matrix.of X)
      map_add' := fun X Y => map_add (matEq E a) (Matrix.of X) (Matrix.of Y)
      map_smul' := fun c X => map_smul (matEq E a) c (Matrix.of X) }

private theorem contDiffAt_one {φ : GA E a → ℂ} (hφ : IsArchSmooth φ) (g : GA E a) :
    ContDiffAt ℝ ∞ (TR.chart φ g) (TR.oneL E a) := by
  have h := ((isExpLieAlgebra E a).isSmoothFun_iff).1 (hφ g) 1
  set e := expPartialHomeomorph ℝ (ArchMatrix E a)
  have h1 : toArch E a (TR.oneL E a) = 1 := map_one (matEq E a)
  have hn : e.target ∈ 𝓝 (toArch E a (TR.oneL E a)) := by
    rw [h1]; exact e.open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
  have hl : ContDiffAt ℝ ∞ (fun x => subspaceProj (archLie E a) (e.symm (toArch E a x))) (TR.oneL E a) :=
    (subspaceProj (archLie E a)).contDiff.contDiffAt.comp _
      (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hn).comp _ (toArch E a).contDiff.contDiffAt)
  refine (h.contDiffAt.comp _ hl).congr_of_eventuallyEq ?_
  filter_upwards [(toArch E a).continuous.continuousAt.preimage_mem_nhds hn,
    TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet (1 : GL (Fin a) (TR.Rinf E)))] with x hx hu
  obtain ⟨u, hu⟩ := hu
  have hxu : x = TR.toL u.val := hu.symm
  subst hxu
  rw [TR.chart_val, ← infEmb_grpEq]
  simp only [Function.comp_apply, archSlice_apply, one_mul]
  congr 3
  refine Subtype.ext (Units.ext ?_)
  rw [IsExpLieAlgebra.coe_expG, subspaceProj_of_mem Submodule.mem_top]
  exact (e.right_inv hx).symm

end

theorem UpperTheory.contDiff_chart_of_isArchSmooth :
    UpperTheory.V.Fb.SmOf := by
  intro E _ _ _ a φ hφ g x hx
  obtain ⟨u, hu⟩ := hx
  have hxu : x = TR.toL u.val := hu.symm
  subst hxu
  have e : TR.chart φ g = TR.chart φ (g * TR.infGL E a u) ∘ TR.lmul (TR.toL (u⁻¹).val) := by
    rw [← TR.chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : TR.lmul (TR.toL (u⁻¹).val) (TR.toL u.val) = TR.oneL E a := u.inv_mul
  rw [e]
  refine (ContDiffAt.comp _ ?_ (TR.lmul (TR.toL (u⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt
  rw [e1]
  exact contDiffAt_one hφ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsArchSmoothOfContDiffChart
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb
open scoped ContDiff

theorem UpperTheory.isArchSmooth_of_contDiff_chart :
    UpperTheory.V.Fb.SmTo := by
  intro E _ _ _ a φ hφ g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro x
  let L0 : ArchMatrix E a →ₗ[ℝ] TR.Lie E a := (matEq E a).symm.toLinearMap
  let L : ArchMatrix E a →L[ℝ] TR.Lie E a := LinearMap.toContinuousLinearMap L0
  have hL : ∀ z : archGroup E a, L ((z : (ArchMatrix E a)ˣ) : ArchMatrix E a) = TR.toL ((grpEq E a).symm z).val := by
    intro z
    obtain ⟨y, rfl⟩ := (grpEq E a).surjective z
    rw [MulEquiv.symm_apply_apply, coe_grpEq]
    exact (matEq E a).symm_apply_apply y.val
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix E a → ArchMatrix E a) :=
    contDiff_iff_contDiffAt.2 fun X => (NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt
  have hc : ContDiff ℝ ∞ fun Y : archLie E a =>
      L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) :=
    L.contDiff.comp (contDiff_const.mul (hexp.comp (archLie E a).subtypeL.contDiff))
  have e : (fun Y : archLie E a => archSlice φ g (x * (isExpLieAlgebra E a).expG Y)) = fun Y : archLie E a =>
      TR.chart φ g (L (((x * (isExpLieAlgebra E a).expG Y : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
    funext Y
    rw [hL, TR.chart_val, ← infEmb_grpEq, MulEquiv.apply_symm_apply]
    rfl
  rw [e]
  refine contDiff_iff_contDiffAt.2 fun Y => (TR.contDiffAt_chart hφ g ?_).comp Y hc.contDiffAt
  rw [hL]
  exact TR.val_mem_invSet _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

open MeasureTheory in
private theorem setIntegral_haar {E : Type} [Field E] [NumberField E] {a r : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (g : GA E a) (h : constantTerm r φ g = 0) (ν : Measure (UPos a r → Ad E))
    [ν.IsAddHaarMeasure] {D : Set (UPos a r → Ad E)} (hD : IsAddFundamentalDomain (unipLattice E a r) D ν) :
    ∫ x in D, φ (unipGL x * g) ∂ν = 0 := by
  have hD' : IsAddFundamentalDomain (unipLattice E a r) D (unipMeasure E a r) :=
    hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [constantTerm_eq_setIntegral hl hD'] at h
  rw [Measure.isAddLeftInvariant_eq_smul ν (unipMeasure E a r), Measure.restrict_smul, integral_smul_nnreal_measure, h,
    smul_zero]

private def ixEq (a r : ℕ) : UPos a r ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem unipGL_ixEq {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) :
    unipGL (fun p => x (ixEq a r p)) = unip x := by
  refine Units.ext ?_
  change 1 + blockEntry (fun p => x (ixEq a r p)) = 1 + nilM x
  congr 1

open MeasureTheory in
theorem UpperTheory.isCuspidal_of_constantTerm_eq_zero :
    UpperTheory.V.Fb.CuspOf := by
  intro E _ _ a φ hl _ hφ r h0 h1 i1 i2 μ 𝓕 hμ hF g
  obtain rfl : i1 = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ _ Pi.borelSpace).symm
  let β : (BlockIx a r → Ad E) ≃ₜ+ (UPos a r → Ad E) :=
    { toFun := fun x p => x (ixEq a r p)
      invFun := fun x p => x ((ixEq a r).symm p)
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply _
      continuous_invFun := continuous_pi fun p => continuous_apply _ }
  let e : unipLattice E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => y ((ixEq a r).symm p), rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨_, y, rfl⟩ := x
        exact ⟨fun p => y (ixEq a r p), rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := β.isAddHaarMeasure_map μ
  have h2 := setIntegral_haar hl g (hφ r h0 h1 g) (μ.map m) (D := m '' 𝓕)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply])
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  exact congrArg (fun u => φ (u * g)) (unipGL_ixEq x).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelSetInterTranslateFinite
section
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem posIdele_finite_part_eq {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) :
    ((Reduction.posIdele (K := K) ρ hρ : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).2 = 1 := by
  unfold Reduction.posIdele
  refine Finset.prod_induction _ (fun x : GroundTheory.Global.IdeleGroup K => ((x : AdeleRing (𝓞 K) K)).2 = 1) ?_ ?_ ?_
  · intro a b ha hb
    calc ((a * b : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).2
        = ((a : AdeleRing (𝓞 K) K)).2 * ((b : AdeleRing (𝓞 K) K)).2 := rfl
      _ = 1 := by rw [ha, hb, one_mul]
  · rfl
  · intro w _
    rfl

private theorem finPart_diag_of_infinite_part_eq_one {K : Type} [Field K] [NumberField K] (n : ℕ)
    (d : Fin n → GroundTheory.Global.IdeleGroup K) (hd : ∀ i, ((d i : AdeleRing (𝓞 K) K)).2 = 1) :
    finPart (K := K) (Reduction.diagUnits n d) = 1 := by
  apply Units.ext
  funext i j
  change (((Reduction.diagUnits n d : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 = (1 : Matrix (Fin n) (Fin n) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
  simp only [Reduction.diagUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    exact hd i
  · rfl

private theorem finPart_mul' {K : Type} [Field K] [NumberField K] {n : ℕ} (x y : AdelicGLn.AdelicGL K n) :
    finPart (x * y) = finPart x * finPart y := by
  show ((AdelicGLn.prodEquiv K n) (x * y)).2 = _
  rw [map_mul]
  rfl

theorem UpperTheory.siegelSet_inter_translate_finite :
    UpperTheory.V.Fb.SiegelFin := by
  intro K _ _ n ω hω t
  have hc : Continuous (fun g : AdelicGLn.AdelicGL K n => finPart g) :=
    continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  refine ⟨(fun p : AdelicGLn.FiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n => p.1 * p.2) ''
      ((finPart '' ω) ×ˢ (finPart '' ((Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))),
    ((hω.image hc).prod (Reduction.isCompact_maxCompact.image hc)).image continuous_mul, ?_⟩
  rintro g ⟨b, hb, a, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩
  have ha := finPart_diag_of_infinite_part_eq_one n _ (fun i => posIdele_finite_part_eq (K := K) (r i) (hr i))
  refine ⟨(finPart b, finPart k), ⟨⟨b, hb, rfl⟩, ⟨k, hk, rfl⟩⟩, ?_⟩
  show finPart b * finPart k = _
  rw [finPart_mul', finPart_mul', ha, mul_one]
end

