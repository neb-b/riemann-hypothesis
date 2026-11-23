module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0008
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.ExistsTracePowNe
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem exists_trace_pow_ne {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (R : Module.End ℂ W) (hR : Function.Injective R) : ∃ j : ℕ, LinearMap.trace ℂ W (R ^ (j + 1)) ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : R.charpoly.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff R).1 h0
    exact hm (hR (by rw [hm0, map_zero]))
  have h1 := congrArg (LinearMap.trace ℂ W) (LinearMap.aeval_self_charpoly R)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ', map_add (f := _), map_sum] at h1
  simp only [map_smul, (LinearMap.trace ℂ W).map_zero, h, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, LinearMap.trace_one, smul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact h0 h2
  · exact (Module.finrank_pos (R := ℂ) (M := W)).ne' (by exact_mod_cast h2)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.finTw :
    FinTw := by
  intro W X _ _ _ _ T hc hirr U hU i x hinj
  obtain ⟨c, hc0, H⟩ := UpperTheory.ConvolutionTheory.L1.algTrace W X 1 T
    (by
      intro a b hab y z
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · exact hc y z
      · exact (hc z y).symm
      · exact absurd rfl hab) hirr U hU
  have hcom : ∀ (k : ℕ) (j : Fin 2), j ≠ i → ∀ y, Commute (T i x ^ k) (T j y) := by
    intro k j hj y
    apply Commute.pow_left
    fin_cases i <;> fin_cases j
    · exact absurd rfl hj
    · exact hc x y
    · exact (hc y x).symm
    · exact absurd rfl hj
  rw [Filter.frequently_atTop]
  intro N
  have hN : Function.Injective (T i x ^ N : Module.End ℂ W) := by
    rw [Module.End.coe_pow]
    exact hinj.iterate N
  obtain ⟨j, hj⟩ := exists_trace_pow_ne _ hN
  refine ⟨N * (j + 1), Nat.le_mul_of_pos_right N j.succ_pos, ?_⟩
  rw [H i _ (hcom _), pow_mul]
  exact mul_ne_zero hc0 hj
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem ad_ext (F : Type) [Field F] [NumberField F] [Algebra F E] {g g' : AdelicGLn.AdelicGL E n}
    (h1 : T4.pI E n g = T4.pI E n g') (h2 : ∀ v : Pl F, T4.pE E n v g = T4.pE E n v g') : g = g' := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun w => ?_))
  · exact congrArg (fun x : GL (Fin n) (InfiniteAdeleRing E) => x.val a b) h1
  · exact congrArg (fun x : GL (Fin n) (CompletionsOver E (AdeleBaseChange.below F w)) =>
      x.val a b ⟨w, AdeleBaseChange.liesOver_below w⟩) (h2 _)

private theorem pI_eq (g : AdelicGLn.AdelicGL E n) : T4.pI E n g = (AdelicGLn.prodEquiv E n g).1 :=
  Units.ext (Matrix.ext fun a b => (AdelicGLn.prodEquiv_apply_fst E n g a b).symm)

private theorem pE_ext {v : Pl F} {g : AdelicGLn.AdelicGL E n} (h : ∀ w : PlacesOver E v, finAt w.1 g = 1) :
    T4.pE E n v g = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h1 : (g.val a b).2 w.1 = (1 : GL (Fin n) (w.1.adicCompletion E)).val a b := by
    rw [← h w, finAt_apply]
  refine h1.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

private theorem gal_cent (σ : E ≃ₐ[F] E) (s : {r : ℝ // 0 < r}) :
    mapGL n (galAd σ) (centralSection E n s) = centralSection E n s := by
  have hl : Module.finrank F E ≠ 0 := Module.finrank_pos.ne'
  have e : (⟨(s : ℝ) ^ ((Module.finrank F E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩ : {r : ℝ // 0 < r}) ^
      Module.finrank F E = s := by
    apply Subtype.ext
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hl
  rw [← e, ← UpperTheory.centralSection_baseChange F E n]
  exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _

private theorem gal_retract (σ : E ≃ₐ[F] E) (hn : 0 < n) {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ}
    (hθ : IsGalTwist σ θ) (x : AdelicGLn.AdelicGL E n) :
    θ.e (retractOne x) = retractOne (mapGL n (galAd σ) x) := by
  have h1 : ((θ.e (retractOne x) : G1 E n) : AdelicGLn.AdelicGL E n) * centralSection E n (detModule E n x) =
      mapGL n (galAd σ) x := by
    rw [hθ, coe_retractOne, map_mul, map_inv, gal_cent, inv_mul_cancel_right]
  rw [← h1, retractOne_mul, retractOne_coe, retractOne_centralSection, mul_one]

private theorem gal_infEmb (σ : E ≃ₐ[F] E) (a : archGroup E n) :
    mapGL n (galAd σ) (infEmb E n a) =
      infEmb E n (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) := by
  obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  refine ad_ext F ?_ fun v => ?_
  · rw [c1, pI_eq, pI_eq, prodEquiv_infEmb, prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
  · rw [c2, pE_ext fun w => finAt_infEmb w.1 _, pE_ext fun w => finAt_infEmb w.1 _, map_one]

private theorem arch_shift {σ : E ≃ₐ[F] E} {m : ℕ} (D : InfD σ m) (k : archGroup E n) :
    ∃ k' : archGroup E n, (∀ i, compA D n i k' = compA D n (i + 1) k) ∧
      mapGL n (galAd σ) (infEmb E n k) = infEmb E n k' := by
  refine ⟨_, fun i => ?_, gal_infEmb σ k⟩
  have hsh := (UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ m D n).2.2.2.2.2.2.1
  have h : ∀ i x, compA D n i x = archEquiv F n (D.comp n i ((archEquiv E n).symm x)) := fun _ _ => rfl
  rw [h, h, ContinuousMulEquiv.symm_apply_apply, hsh]

private theorem comp_loc {σ : E ≃ₐ[F] E} {v : Pl F} (D : Split (incFin E v) (galFin σ v) 1)
    (w : Fin 2 ≃ PlacesOver E v)
    (hD : ∀ (b : CompletionsOver E v) i, completionMap v (w i).1 (D.e b i) = b (w i))
    (i j : Fin 2) (g : Gw n v) :
    D.comp n j (T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g)))) =
      if j = i then g else 1 := by
  refine Units.ext (Matrix.ext fun a b => (completionMap v (w j).1).injective ?_)
  refine (hD _ j).trans ?_
  change (finAt (w j).1 (finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g)))).val a b = _
  split_ifs with h
  · subst h
    rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w j).1).2.1]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w i).1).2.2.1 (w j).1 (fun h' => h (w.injective (Subtype.ext h')))]
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp

private theorem pE_loc {v v' : Pl F} (h : v' ≠ v) (w : PlacesOver E v) (x : Gw n w.1) :
    T4.pE E n v' (finEmb E n (AdelicGLn.localEmbedding w.1 x)) = 1 := by
  refine pE_ext fun u => (UpperTheory.ConvolutionTheory.Tf.locEmb E n w.1).2.2.1 u.1 (fun h' => h ?_) x
  apply HeightOneSpectrum.ext
  rw [u.2.over, w.2.over, h']

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc :
    GalLoc := by
  intro F E _ _ _ _ _ _ _ _ σ h2 hσ n hn μ _ θ
  refine ⟨?_, fun hθ => ⟨fun g => ?_, fun D eF e he k => ?_, fun v hv => ?_⟩⟩
  · unfold IsGalTwist UpperTheory.ConvolutionTheory.K.IsGal
    rw [UpperTheory.ConvolutionTheory.K.galAdEq]
  · have hs : σ.toRingEquiv.trans σ.toRingEquiv = RingEquiv.refl E := by
      have h : σ ^ 2 = 1 := by
        rw [← h2, ← IsGalois.card_aut_eq_finrank F E]
        exact pow_card_eq_one'
      ext x
      exact congrArg (fun τ : E ≃ₐ[F] E => τ x) ((sq σ).symm.trans h)
    apply Subtype.ext
    rw [hθ, hθ, UpperTheory.ConvolutionTheory.K.galAdEq]
    refine Units.ext (Matrix.ext fun a b => ?_)
    obtain ⟨-, b1, b2⟩ := UpperTheory.ConvolutionTheory.K.adBasic E
    refine (b2 _ _ _).symm.trans ?_
    rw [hs, b1]
  · have hc := (UpperTheory.ConvolutionTheory.L1.positionOf F E σ 1 D).2 n
    have hk := (hc k).1 k.2
    obtain ⟨k', key, hk'⟩ := arch_shift D (k : archGroup E n)
    have hm : k' ∈ archCompact E n := (hc k').2 fun i => by rw [key i]; exact hk (i + 1)
    refine ⟨⟨k', hm⟩, ?_, ?_⟩
    · change θ.e (archP E n k) = archP E n k'
      rw [← retract_infEmb, ← retract_infEmb, gal_retract σ hn hθ, hk']
    · rw [he k (fun i => ⟨_, hk i⟩) fun _ => rfl, he ⟨k', hm⟩ (fun i => ⟨_, hk (i + 1)⟩) fun i => (key i).symm,
        Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
      rfl
  · obtain ⟨w₀⟩ : Nonempty (PlacesOver E v) := by
      obtain ⟨⟨P, hP, hl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
      exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl⟩⟩
    obtain ⟨D, w, -, hD⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ 1 h2 v w₀ hv
    refine ⟨w, fun i g => ?_⟩
    obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
    obtain ⟨-, g2, -, -, -, -, hsh, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ 1 D n
    change θ.e (retractOne (finEmb E n _)) = retractOne (finEmb E n _)
    rw [gal_retract σ hn hθ]
    congr 1
    refine ad_ext F ?_ fun v' => ?_
    · rw [c1, pI_eq, pI_eq, prodEquiv_finEmb, prodEquiv_finEmb, map_one]
    · rw [c2]
      by_cases h : v' = v
      · subst h
        rw [← g2 (mapGL n (galFin σ v') _), ← g2 (T4.pE E n v' (finEmb E n (AdelicGLn.localEmbedding (w (i + 1)).1 _)))]
        congr 1
        funext j
        rw [hsh, comp_loc D w hD, comp_loc D w hD]
        have : j + 1 = i ↔ j = i + 1 := by revert i j; decide
        simp only [this]
      · rw [pE_loc h, pE_loc h, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SignMs
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem neg_ne_self_unit (a : ℂˣ) : -a ≠ a := by
  intro h
  have h1 : -(a : ℂ) = a := by simpa using congrArg Units.val h
  have h2 : (a : ℂ) = 0 := by linear_combination (-1 / 2 : ℂ) * h1
  exact a.ne_zero h2

private theorem half_of_neg_stable (n : ℕ) : ∀ A : Multiset ℂˣ, A.card ≤ n → A.map (fun x => -x) = A →
    ∃ B' : Multiset ℂˣ, A = B' + B'.map fun b => -b := by
  induction n with
  | zero =>
    intro A hA _
    have : A = 0 := Multiset.card_eq_zero.1 (Nat.le_zero.1 hA)
    exact ⟨0, by simp [this]⟩
  | succ n ih =>
    intro A hA hs
    by_cases h0 : A = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h0
    have hna : -a ∈ A := by
      rw [← hs]
      exact Multiset.mem_map_of_mem _ ha
    obtain ⟨A₁, rfl⟩ := Multiset.exists_cons_of_mem ha
    have hna₁ : -a ∈ A₁ := (Multiset.mem_cons.1 hna).resolve_left (neg_ne_self_unit a)
    obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hna₁
    have hC : C.map (fun x => -x) = C := by
      rw [Multiset.map_cons, Multiset.map_cons, neg_neg, Multiset.cons_swap] at hs
      exact (Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 hs)
    have hc : C.card ≤ n := by
      simp only [Multiset.card_cons] at hA
      omega
    obtain ⟨B', hB'⟩ := ih C hc hC
    refine ⟨a ::ₘ B', ?_⟩
    rw [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons, ← hB']

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.signMs :
    SignMs := by
  intro A B _ _ hs hq
  obtain ⟨B', hB'⟩ := half_of_neg_stable _ A le_rfl hs
  refine ⟨B', ?_, hB'⟩
  have h : B'.map (· ^ 2) + B'.map (· ^ 2) = B + B := by
    rw [← hq, hB', Multiset.map_add (f := _), Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun x _ => by simp
  ext x
  have := congrArg (Multiset.count x) h
  simp only [Multiset.count_add] at this
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TensAmp
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.tensAmp :
    TensAmp := by
  intro K _ _ _ n hn μ _ 𝔞 φ hφ
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  have hUo := 𝔞.isOpen
  have hUc : IsCompact (𝔞.U : Set (FA K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hUo) 𝔞.le
  have hpos : 0 < m.real (𝔞.U : Set (FA K n)) :=
    ENNReal.toReal_pos (hUo.measure_pos m ⟨1, 𝔞.U.one_mem⟩).ne' hUc.measure_lt_top.ne
  have hne : ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  refine ⟨⟨m.real (𝔞.U : Set (FA K n)), hpos, fun Θ hΘ hfix x => ?_, ?_⟩, fun c => ?_⟩
  · rw [hC 𝔞.a₀ φ (fun g => Θ (x * g)) (hΘ.comp (continuous_const.mul continuous_id)), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    have h1 : ∀ h : FA K n, 𝔞.a₀ a * φ h * Θ (x * (archP K n a * MultiplicityOne.finProj K n h)) =
        (𝔞.U : Set (FA K n)).indicator (fun _ => 𝔞.a₀ a * Θ (x * archP K n a)) h := by
      intro h
      by_cases hh : h ∈ (𝔞.U : Set (FA K n))
      · rw [hφ, Set.indicator_of_mem hh, Set.indicator_of_mem hh, ← mul_assoc x, hfix h hh]
        simp
      · rw [hφ, Set.indicator_of_notMem hh, Set.indicator_of_notMem hh]
        simp
    simp only [h1]
    rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul]
  · obtain ⟨e, he, hO⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m 𝔞.U hUo hUc
    have h2 : φ = ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) • e := by
      ext h
      rw [CompactlySupportedContinuousMap.smul_apply, he, hφ]
      by_cases hh : h ∈ (𝔞.U : Set (FA K n))
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, smul_eq_mul, mul_inv_cancel₀ hne]
        rfl
      · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, smul_zero]
    have h3 := UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ 𝔞.ν m hC 𝔞.a₀ φ
    have h4 := ((UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m).2.2.1 ((m.real (𝔞.U : Set (FA K n)) : ℝ) : ℂ) 𝔞.a₀ e).2
    rw [← h2, hO] at h4
    rw [h4, ContinuousLinearMap.comp_smul] at h3
    exact h3
  · rw [← ((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn 𝔞.a₀ φ).2.2.2.2 c).2]
    refine (UpperTheory.ConvolutionTheory.Tf.leftSm K n hn 𝔞.a₀ (c • φ)).1 𝔞.smooth ⟨𝔞.U, hUo, fun u hu h => ?_⟩
    rw [CompactlySupportedContinuousMap.smul_apply, CompactlySupportedContinuousMap.smul_apply, hφ, hφ]
    by_cases hh : h ∈ (𝔞.U : Set (FA K n))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (show u * h ∈ (𝔞.U : Set (FA K n)) from 𝔞.U.mul_mem hu hh)]
      rfl
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (show u * h ∉ (𝔞.U : Set (FA K n)) from fun h' => hh ((𝔞.U.mul_mem_cancel_left hu).1 h'))]
end

