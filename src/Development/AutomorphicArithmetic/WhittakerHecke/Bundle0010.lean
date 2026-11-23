module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FunctionalQdetEqAevalShiftedPolynomial
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.functional_qdet_eq_aeval_shifted_polynomial :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (j : A) (l : A →ₗ[ℂ] ℂ) (p : Polynomial ℂ),
          (∀ i k, Commute (X i k) j) → (∀ (c : ℂ) (a : A), l (Formalism.REAL.qdet (fun i k => X i k - if i = k then j else 0) c * a) = p.eval c * l a) →
          ∀ v : ℂ, l (Formalism.REAL.qdet X v) = l (Polynomial.aeval j (p.comp (Polynomial.X + Polynomial.C v))) := by
  intro A _ _ n X j l p hc h v
  classical
  let B : Subalgebra ℂ A := Subalgebra.centralizer ℂ {j}
  have hB : ∀ i k, (X i k - if i = k then j else 0) ∈ B := fun i k => by
    rintro _ rfl
    refine (Commute.sub_left (hc i k) ?_).symm
    split_ifs
    · exact Commute.refl _
    · exact Commute.zero_left _
  let X' : Fin n → Fin n → B := fun i k => ⟨_, hB i k⟩
  let Q : Polynomial B := Formalism.REAL.qdet (fun i k => Polynomial.C (X' i k) + if i = k then Polynomial.X else 0) v
  have hev : ∀ (b : A) (hb : ∀ a : B, Commute (B.val a) b), Q.eval₂ (B.val : B →+* A) b =
      Formalism.REAL.qdet (fun i k => (X i k - if i = k then j else 0) + if i = k then b else 0) v := fun b hb => by
    have := UpperTheory.V.Fb.map_qdet (Polynomial.eval₂AlgHom B.val b hb)
      (fun i k => Polynomial.C (X' i k) + if i = k then Polynomial.X else 0) v
    refine Eq.trans ?_ (this.trans ?_)
    · rfl
    · congr 1
      funext i k
      rw [map_add (f := _), apply_ite (Polynomial.eval₂AlgHom B.val b hb), map_zero]
      congr 1
      · exact Polynomial.eval₂_C _ _
      · congr 1
        exact Polynomial.eval₂_X _ _
  have h1 : Q.eval₂ (B.val : B →+* A) j = Formalism.REAL.qdet X v := by
    rw [hev j (fun a => (a.2 j rfl).symm)]
    simp
  set q := p.comp (Polynomial.X + Polynomial.C v) with hq
  have h2 : ∀ (a : A) (k : ℕ), l ((Q.coeff k : A) * a) = q.coeff k * l a := fun a k => by
    have e : (∑ m ∈ Q.support, Polynomial.monomial m (l ((Q.coeff m : A) * a))) = q * Polynomial.C (l a) := by
      refine Polynomial.funext fun c => ?_
      have := h (v + c) a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← GlobalTheory.CuspRep.qdet_shift, ← hev _ (fun a => (Algebra.commutes c _).symm), Polynomial.eval₂_eq_sum, Polynomial.sum,
        Finset.sum_mul, map_sum] at this
      rw [Polynomial.eval_mul, Polynomial.eval_C, hq, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, add_comm c v, ← this, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Polynomial.eval_monomial, ← map_pow, mul_assoc, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul,
        mul_comm]
      rfl
    have e2 := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r k) e
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Polynomial.coeff_mul_C, Finset.sum_ite_eq'] at e2
    rw [← e2]
    split_ifs with hk
    · rfl
    · rw [Polynomial.notMem_support_iff.1 hk]
      simp
  let N := max Q.natDegree q.natDegree + 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h1, Polynomial.eval₂_eq_sum_range' _ (show Q.natDegree < N from Nat.lt_succ_of_le (le_max_left _ _)),
    Polynomial.aeval_eq_sum_range' (show q.natDegree < N from Nat.lt_succ_of_le (le_max_right _ _)), map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul]
  exact h2 _ m
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FunctionalVanishesInvariant
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem zt_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : ℕ) (t : ℝ) :
    zt E r t = GlobalTheory.UnitaryBC.splitCentre E r (t * ((r * Module.finrank ℚ E : ℝ))⁻¹) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) r
    (Real.rpow_pos_of_pos (Real.exp_pos t) ((r * Module.finrank ℚ E : ℝ))⁻¹)
  rw [Real.log_rpow (Real.exp_pos t), Real.log_exp, mul_comm _ t] at h
  exact h

theorem UpperTheory.functional_vanishes_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : ℕ) (f : Sm E r), (∀ t g, f.1 (zt E r t * g) = f.1 g) → j0 E r f = 0 := by
  intro E _ _ _ r f hf
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [j0]
  have hd : ((r * Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hr.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  have h : ∀ t g, f.1 (GlobalTheory.UnitaryBC.splitCentre E r t * g) = f.1 g := fun t g => by
    have := hf (t * (r * Module.finrank ℚ E : ℝ)) g
    rwa [zt_eq, mul_inv_cancel_right₀ hd] at this
  have h0 : lie E r (oneL E r) f = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    have h1 := GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre E r f g 0
    have h2 : (fun t : ℝ => f.1 (g * GlobalTheory.UnitaryBC.splitCentre E r t)) = fun _ => f.1 g := by
      funext t
      rw [← CuspidalL2GL.splitCentre_comm, h]
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (f.1 g))
    rw [CuspidalL2GL.splitCentre_zero, mul_one] at h3
    exact h3
  have h4 : lie E r (oneL E r) = ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ i i := by
    rw [UpperTheory.V.Cm.lie_eq_sum]
    have hc : ∀ (τ : E →+* ℂ) (i k : Fin r), coord τ (oneL E r i k) = if i = k then 1 else 0 := fun τ i k => by
      have : oneL E r i k = (1 : Matrix (Fin r) (Fin r) (Cinf E)) i k := rfl
      rw [this, Matrix.one_apply]
      split_ifs <;> simp
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [j0, LinearMap.smul_apply, ← h4, h0, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralQuotientDerivativeOneParameterEqZero
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem flow_abs {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    (ν : Measure Y) [SFinite ν] (T : ℝ → Y → Y) (hT : Continuous fun p : Y × ℝ => T p.2 p.1)
    (hm : ∀ u, MeasurePreserving (T u) ν ν) (he : ∀ u, MeasurableEmbedding (T u)) (H D : Y → ℂ) (hD : Continuous D)
    (iH : Integrable H ν) (iD : Integrable D ν) (hd : ∀ y u, HasDerivAt (fun s => H (T s y)) (D (T u y)) u) :
    ∫ y, D y ∂ν = 0 := by
  have hc : Continuous fun p : Y × ℝ => D (T p.2 p.1) := hD.comp hT
  have h1 : ∀ y, ∫ u in Set.Ioc (0 : ℝ) 1, D (T u y) = H (T 1 y) - H (T 0 y) := fun y => by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd y u)
      ((hc.comp (Continuous.prodMk_right y)).intervalIntegrable _ _)
  have hi : Integrable (Function.uncurry fun y u => D (T u y)) (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine (integrable_prod_iff' hc.aestronglyMeasurable).2 ⟨.of_forall fun u => ((hm u).integrable_comp_emb (he u)).2 iD, ?_⟩
    have : (fun u => ∫ y, ‖D (T u y)‖ ∂ν) = fun _ => ∫ y, ‖D y‖ ∂ν := funext fun u => (hm u).integral_comp (he u) fun y => ‖D y‖
    exact this ▸ integrable_const _
  have h2 := integral_integral_swap hi
  simp only [h1, fun u => (hm u).integral_comp (he u) D] at h2
  have i : ∀ u, Integrable (fun x => H (T u x)) ν := fun u => ((hm u).integrable_comp_emb (he u)).2 iH
  rw [integral_sub (i 1) (i 0),
    (hm 1).integral_comp (he 1) H, (hm 0).integral_comp (he 0) H] at h2
  simpa using h2.symm

private theorem flow_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) (c : ℝ → G)
    (hc : Continuous c) : Continuous fun p : RightCosetSpace Γ × ℝ => rightMul Γ (c p.2) p.1 :=
  (continuous_rightMul_prod Γ).comp (f := fun p : RightCosetSpace Γ × ℝ => (p.1, c p.2))
    (continuous_fst.prodMk (hc.comp continuous_snd))

theorem UpperTheory.integral_quotient_derivative_oneParameter_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (h D : GA E r → ℂ) (c : ℝ → GA E r),
          AutomorphicForm.IsLeftInvariant h → AutomorphicForm.IsLeftInvariant D → Continuous D → Continuous c → c 0 = 1 →
          (∀ s t, c (s + t) = c s * c t) → (∀ s, c s ∈ normOneGL (K := E) (n := r)) → (∀ g, HasDerivAt (fun s => h (g * c s)) (D g) 0) →
          Integrable (onQ h) (muQ E r) → Integrable (onQ D) (muQ E r) → ∫ y, onQ D y ∂muQ E r = 0 := by
  intro E _ _ r h D c hh hD cD cc _ cadd c1 hd ih iD
  have e : ∀ {f : GA E r → ℂ} (hf : AutomorphicForm.IsLeftInvariant f), onQ f = CuspidalSpectrum.cuspQuot hf := fun hf => by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  rw [e hh] at ih
  rw [e hD] at iD ⊢
  haveI : IsFiniteMeasure (muQ E r) := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  haveI : SigmaFinite (muQ E r) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (muQ E r) := instSFiniteOfSigmaFinite
  set_option synthInstance.maxHeartbeats 200000 in
    refine flow_abs (muQ E r) (fun u => rightMul (rationalGLOne (K := E) (n := r)) ⟨c u, c1 u⟩) ?_
      (fun u => measurePreserving_rightMul (Γ := rationalGLOne (K := E) (n := r)) (mu1 E r) _)
      (fun u => (rightMulHomeomorph (rationalGLOne (K := E) (n := r)) _).measurableEmbedding) _ _ ?_ ih iD fun y u => ?_
    · exact flow_cont (rationalGLOne (K := E) (n := r)) (fun u => ⟨c u, c1 u⟩) (cc.subtype_mk c1)
    · exact (isOpenQuotientMap_mk (rationalGLOne (K := E) (n := r))).isQuotientMap.continuous_iff.2 (cD.comp continuous_subtype_val)
    · obtain ⟨g, rfl⟩ := mk_surjective (rationalGLOne (K := E) (n := r)) y
      have h1 := (hd (g * c u)).scomp_of_eq u ((hasDerivAt_id u).sub_const u) (by simp)
      rw [one_smul] at h1
      refine h1.congr_of_eventuallyEq (.of_forall fun s => ?_)
      change h (g * c s) = h (g * c u * c (s - u))
      rw [mul_assoc, ← cadd, add_sub_cancel]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.LocGLEqLocalEmbeddingAndKGLEqIntegralGL
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

theorem UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)),
          (∀ g, GlobalTheory.CuspRep.locGL E n w g = AdelicGLn.localEmbedding w g) ∧
          GlobalTheory.LFun.KGL w (n := n) = GLnLocal.integralGL (w.adicCompletion E) n := by
  intro E _ _ n w
  refine ⟨fun g => ?_, ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
    have key : ∀ v, Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (GlobalTheory.CuspRep.locGL E n w g) =
        Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (AdelicGLn.localEmbedding w g) := fun v => by
      by_cases h : v = w
      · subst h
        rw [GlobalTheory.CuspRep.pLoc_locGL]
        exact (h1 g).symm
      · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne h]
        exact (h2 v h g).symm
    refine Units.ext (Matrix.ext fun i j => ?_)
    refine DFunLike.ext _ _ fun v => ?_
    exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (key v)
  · have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
        Formalism.UG.GLint (Fin n) O = GLnLocal.integralGL (w.adicCompletion E) n := by
      rintro _ rfl
      rfl
    exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.OneParameterSubgroupNormOne
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
open GroundTheory.Global
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem cv_mod (h : GL (Fin a) (Cinf E)) :
    (Reduction.detModule E a (infGL E a h) : ℝ) = ∏ w : InfinitePlace E, ‖h.val.det w‖ ^ 2 := by
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w => by
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
  have e1 : pInf E (infGL E a h).val.det = h.val.det := by
    rw [RingHom.map_det]
    exact congrArg (fun y : GL (Fin a) (Cinf E) => y.val.det) (pInf_infGL h)
  have e2 : pFin E (infGL E a h).val.det = 1 := by
    rw [RingHom.map_det]
    exact (congrArg (fun y : GL (Fin a) (Af E) => y.val.det) (pFin_infGL h)).trans Matrix.det_one
  have h1 : ∀ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ = ‖h.val.det v‖ := fun v => by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    exact congrArg norm (congrFun e1 v)
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (infGL E a h).val.det v‖ = 1
    rw [e2]
    exact norm_one
  change (IdeleGroup.ideleModule E (AdelicGLn.det E a (infGL E a h)) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one, hm]

private theorem cv_sum (x : Cinf E) : ∑ τ : E →+* ℂ, coord τ x = ∑ w : InfinitePlace E, (x w + starRingEnd ℂ (x w)) := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun τ : E →+* ℂ => InfinitePlace.mk τ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 h)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (ComplexEmbedding.involutive_conjugate E τ).symm
    · rintro (rfl | rfl) <;> simp
  rw [hf, Finset.sum_pair hne.symm]
  unfold coord
  simp [hne.symm]

private theorem cv_det {m : ℝ → Matrix (Fin a) (Fin a) ℂ} {Y : Matrix (Fin a) (Fin a) ℂ} (h0 : m 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun s => m s i j) (Y i j) 0) : HasDerivAt (fun s => (m s).det) (∑ i, Y i i) 0 :=
  _root_.UpperTheory.Reformulated.B.MovedPointDeterminant.cv_det h0 hd

end

theorem UpperTheory.one_parameter_subgroup_norm_one :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : ℕ) (X : Lie E r), ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) = 0 →
          ∃ c : ℝ → GL (Fin r) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ Continuous (fun s => infGL E r (c s)) ∧
            HasDerivAt (fun s => toL (c s).val) X 0 ∧ ∀ s, infGL E r (c s) ∈ normOneGL (K := E) (n := r) := by
  intro E _ _ _ r X hX
  classical
  obtain ⟨c, h0, hadd, hc, hd, -⟩ := UpperTheory.V.Lit.Bor.oneParam E r X
  refine ⟨c, h0, hadd, hc, hd, fun s => ?_⟩
  have hD : ∀ w : InfinitePlace E, HasDerivAt (fun s => (c s).val.det w) (∑ i, X i i w) 0 := fun w => by
    have h1 := cv_det (m := fun s => (c s).val.map fun x => x w) (Y := fun i j => X i j w)
      (by rw [h0]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h])
      fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hd i) j) w
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    exact RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (c s).val
  let Q : ℝ → ℂ := fun s => ∏ w : InfinitePlace E, ((c s).val.det w * starRingEnd ℂ ((c s).val.det w))
  have hQ0 : Q 0 = 1 := by simp [Q, h0]
  have hQm : ∀ s t, Q (s + t) = Q s * Q t := fun s t => by
    simp only [Q, hadd, Units.val_mul, Matrix.det_mul, Pi.mul_apply, map_mul, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => by ring
  have hQd : HasDerivAt Q 0 0 := by
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ) fun (w : InfinitePlace E) _ => (hD w).fun_mul (hD w).star
    refine h.congr_deriv (Eq.symm ?_)
    rw [Finset.sum_comm] at hX
    simp only [cv_sum] at hX
    rw [Finset.sum_comm] at hX
    refine hX.symm.trans ?_
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [h0, Finset.sum_add_distrib]
  have hall : ∀ t, HasDerivAt Q 0 t := fun t => by
    have h1 : HasDerivAt (fun u => Q (u - t)) 0 t := by
      have := HasDerivAt.scomp t (g₁ := Q) (h := fun u => u - t) (by simpa using hQd) ((hasDerivAt_id t).sub_const t)
      simpa [Function.comp_def] using this
    have h2 := h1.const_mul (Q t)
    rw [mul_zero] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    change Q u = Q t * Q (u - t)
    rw [← hQm, add_sub_cancel]
  have hQ : Q s = 1 := (is_const_of_deriv_eq_zero (fun t => (hall t).differentiableAt) (fun t => (hall t).deriv) s 0).trans hQ0
  refine mem_normOneGL_iff_detModule.2 (Subtype.ext ?_)
  refine (cv_mod (c s)).trans ?_
  simp only [Q, Complex.mul_conj'] at hQ
  exact_mod_cast hQ
end

