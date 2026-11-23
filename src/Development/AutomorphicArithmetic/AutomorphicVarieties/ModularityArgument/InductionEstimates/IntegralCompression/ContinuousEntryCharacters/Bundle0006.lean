module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0003
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.PeterWeyl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefInj
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem pw2 {f : U2 → ℂ} (hf : Continuous f)
    (h : ∀ (n : ℕ) (q : ℤ) (l r : U2), ∫ m, conj (KT.psi n q n m) * f (l * m * r) ∂μK = 0) : f = 0 := by
  have key : (fun k => conj (f k)) = 0 := by
    refine PW.eq_zero_of_forall_integral_coeff (Complex.continuous_conj.comp hf) fun n q l₁ l₂ => ?_
    have h1 := h n q l₁⁻¹ l₂⁻¹
    rw [← integral_mul_left_K _ l₁, ← integral_mul_right_K _ l₂] at h1
    have h2 := congrArg conj h1
    rw [← integral_conj, map_zero] at h2
    have hne : ((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q * (l₂ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q) ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_U2 _)) (zpow_ne_zero _ (det_ne_zero_of_U2 _))
    apply mul_left_cancel₀ hne
    rw [mul_zero, ← integral_const_mul, ← h2]
    congr 1; funext k
    have e : l₁⁻¹ * (l₁ * (k * l₂)) * l₂⁻¹ = k := by group
    rw [e, map_mul, starRingEnd_self_apply, ← mul_assoc l₁, KT.psi_mul_mul]
    ring
  funext k
  simpa using congrFun key k

private theorem int2 {f : U2 × U2 → ℂ} (hf : Continuous f) : Integrable f (μK.prod μK) :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

private theorem tor2 (n₁ : ℕ) (q₁ : ℤ) (n₂ : ℕ) (q₂ : ℤ) (ν : Fin (2 + 2) → ℤ) (b : U4 → ℂ)
    (hb : ∀ θ h, b (dg θ * h) = chi ν θ * b h) (hν : ν ≠ wt n₁ q₁ n₂ q₂) (g : U4) :
    ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g) ∂(μK.prod μK) = 0 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, hdg, -, hchi, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  by_contra hI
  refine hν (hchi _ _ fun θ => ?_)
  apply mul_right_cancel₀ hI
  conv_rhs => rw [← integral_mul_left_eq_self _ ((tC (θ 0) (θ 1), tC (θ 2) (θ 3)) : U2 × U2)]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext p
  have hθ : θ = ![θ 0, θ 1, θ 2, θ 3] := by
    funext i; fin_cases i <;> rfl
  have e : bd (tC (θ 0) (θ 1) * p.1) (tC (θ 2) (θ 3) * p.2) * g = dg θ * (bd p.1 p.2 * g) := by
    rw [← hmul, ← hdg, ← hθ, mul_assoc]
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [e, hb, KT.psi_tC_mul n₁ q₁ le_rfl, KT.psi_tC_mul n₂ q₂ le_rfl, map_mul, map_mul]
  have hc : chi (wt n₁ q₁ n₂ q₂) θ * (conj (Complex.exp (Complex.I * ((((n₁ : ℝ) + q₁) * θ 0 + ((n₁ : ℝ) - n₁ + q₁) * θ 1 : ℝ) : ℂ))) *
      conj (Complex.exp (Complex.I * ((((n₂ : ℝ) + q₂) * θ 2 + ((n₂ : ℝ) - n₂ + q₂) * θ 3 : ℝ) : ℂ)))) = 1 := by
    rw [chi, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    have hs : ∑ i, ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ) =
        ((n₁ : ℂ) + q₁) * θ 0 + q₁ * θ 1 + ((n₂ : ℂ) + q₂) * θ 2 + q₂ * θ 3 := by
      have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ))
      refine this.trans ?_
      simp [wt]
    rw [hs]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  linear_combination (-(chi ν θ * conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g))) * hc

private theorem wt_eq {n : ℕ} {q : ℤ} {n' : ℕ} {q' : ℤ} {n₁ : ℕ} {q₁ : ℤ} {n₂ : ℕ} {q₂ : ℤ} (h₁ : Above n q n₁ q₁)
    (h₂ : Above n' q' n₂ q₂) (h : ∑ i, wt n₁ q₁ n₂ q₂ i ^ 2 ≤ ∑ i, wt n q n' q' i ^ 2) : wt n₁ q₁ n₂ q₂ = wt n q n' q' := by
  have hs : ∀ (a : ℕ) (b : ℤ) (c : ℕ) (d : ℤ), ∑ i, wt a b c d i ^ 2 = (a + b) ^ 2 + b ^ 2 + (c + d) ^ 2 + d ^ 2 := by
    intro a b c d
    refine (Fin.sum_univ_four (fun i : Fin 4 => wt a b c d i ^ 2)).trans ?_
    simp [wt]
  rw [hs, hs] at h
  obtain ⟨a1, a2⟩ := h₁
  obtain ⟨b1, b2⟩ := h₂
  have a1' : (n : ℤ) ≤ n₁ := by exact_mod_cast a1
  have b1' : (n' : ℤ) ≤ n₂ := by exact_mod_cast b1
  have hn : (0 : ℤ) ≤ n := by positivity
  have hn' : (0 : ℤ) ≤ n' := by positivity
  have e : ∀ a b : ℤ, 2 * ((a + b) ^ 2 + b ^ 2) = (a + 2 * b) ^ 2 + a ^ 2 := by intros; ring
  have e1 := e n₁ q₁
  have e2 := e n₂ q₂
  have e3 := e n q
  have e4 := e n' q'
  rw [a2] at e1
  rw [b2] at e2
  have s1 : (n : ℤ) ^ 2 ≤ (n₁ : ℤ) ^ 2 := by gcongr
  have s2 : (n' : ℤ) ^ 2 ≤ (n₂ : ℤ) ^ 2 := by gcongr
  have t1 : (n₁ : ℤ) = n := (pow_left_inj₀ (by omega) hn two_ne_zero).1 (by linarith)
  have t2 : (n₂ : ℤ) = n' := (pow_left_inj₀ (by omega) hn' two_ne_zero).1 (by linarith)
  have u1 : q₁ = q := by omega
  have u2 : q₂ = q' := by omega
  simp only [wt, t1, t2, u1, u2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefInj :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ (eOf μ ψ) Φ →
      LAbove (fun m => bd m 1) n q Φ → LAbove (fun m => bd 1 m) n' q' Φ → (∀ a b, Φ (bd a b) = 0) → Φ = 0 := by
  intro μ ψ n q n' q' hμ _ hψ Φ hΦ hfix hL hR h0
  obtain ⟨-, hmul, hone, -, hcont, -, -, -, -, -, -, hcpt, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  obtain ⟨J, _, j₀, a, b, ν, hc, hexp, ha0, hb0, hν0, htor, hgood, hgood'⟩ := hψ.exp
  haveI := hμ.prob
  haveI : μ.IsMulLeftInvariant := ⟨fun k => (hμ.left k).map_eq⟩
  have int4 : ∀ f : U4 → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  set c : ℂ := ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹ with hcdef
  have hrep : ∀ g, Φ g = ∫ k, c * ψ (k⁻¹ * g) * Φ k ∂μ := by
    intro g
    rw [← integral_mul_left_eq_self _ g, ← hfix g]
    congr 1; funext k
    have e : (g * k)⁻¹ * g = k⁻¹ := by group
    rw [e, hψ.star, eOf]
  have hsum : ∀ h x, Φ (h * x) = ∑ j, (∫ k, c * a j (k⁻¹ * h) * Φ k ∂μ) * b j x := by
    intro h x
    rw [hrep]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum]
    · congr 1; funext k
      rw [← mul_assoc, hexp, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro j _
      have := (hc j).1
      exact int4 _ (by fun_prop)
  have hp := fun m r => KT.continuous_conj_psi m r m
  have hbd : ∀ l l' : U2, Continuous fun p : U2 × U2 => bd (l * p.1) (l' * p.2) := fun l l' =>
    hcont.comp (f := fun p : U2 × U2 => (l * p.1, l' * p.2)) (by fun_prop)
  have hint : ∀ n₁ q₁ n₂ q₂ l l' g, Integrable (fun p : U2 × U2 => conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g)) (μK.prod μK) := fun n₁ q₁ n₂ q₂ l l' g =>
    int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
      (hΦ.comp ((hbd l l').mul continuous_const)))
  have main : ∀ n₁ q₁ n₂ q₂ l l' g, ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g) ∂(μK.prod μK) = 0 := by
    intro n₁ q₁ n₂ q₂ l l' g
    by_cases h₁ : Above n q n₁ q₁
    · by_cases h₂ : Above n' q' n₂ q₂
      · simp_rw [← hmul l l', mul_assoc (bd l l'), hsum (bd l l'), Finset.mul_sum]
        rw [integral_finsetSum]
        · refine Finset.sum_eq_zero fun j _ => ?_
          simp_rw [mul_left_comm _ (∫ k, c * a j (k⁻¹ * bd l l') * Φ k ∂μ)]
          rw [integral_const_mul]
          by_cases hj : j = j₀
          · rw [hj, ha0, ← hrep, h0, zero_mul]
          · rw [tor2 n₁ q₁ n₂ q₂ (ν j) (b j) (fun θ h => (htor j θ h).2.2), mul_zero]
            intro hν
            have h3 := hgood j
            simp only [hν] at h3
            exact hgood' j hj (hν.trans (wt_eq h₁ h₂ h3))
        · intro j _
          exact int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
            (continuous_const.mul ((hc j).2.comp (hcont.mul continuous_const))))
      · rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' g)]
        refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
        have h3 := hR n₂ q₂ h₂ l' (bd (l * x) 1 * g)
        simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
        simp only [mul_assoc (conj (KT.psi n₁ q₁ n₁ x))]
        rw [integral_const_mul, h3, mul_zero]
    · rw [integral_prod_symm _ (hint n₁ q₁ n₂ q₂ l l' g)]
      refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
      have h3 := hL n₁ q₁ h₁ l (bd 1 (l' * x) * g)
      simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
      simp only [mul_comm _ (conj (KT.psi n₂ q₂ n₂ x)), mul_assoc (conj (KT.psi n₂ q₂ n₂ x))]
      rw [integral_const_mul, h3, mul_zero]
  have step : ∀ n₂ q₂ l' g, (fun x => ∫ y, conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g) ∂μK) = 0 := by
    intro n₂ q₂ l' g
    refine pw2 ?_ fun n₁ q₁ l r => ?_
    · have h3 := continuous_parametric_integral_of_continuous (μ := μK)
        (f := fun x y : U2 => conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g))
        (((hp _ _).comp continuous_snd).mul (hΦ.comp ((by simpa using hbd 1 l' : Continuous fun p : U2 × U2 => bd p.1 (l' * p.2)).mul
          continuous_const))) isCompact_univ
      simpa only [Measure.restrict_univ] using h3
    · have h3 := main n₁ q₁ n₂ q₂ l l' (bd r 1 * g)
      rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' _)] at h3
      rw [← h3]
      congr 1; funext x
      rw [← integral_const_mul]
      congr 1; funext y
      simp only [← mul_assoc, hmul, mul_one]
  funext g
  have fin : (fun y => Φ (bd 1 y * g)) = 0 := by
    refine pw2 (hΦ.comp ((hcont.comp (f := fun y : U2 => ((1 : U2), y)) (by fun_prop)).mul continuous_const)) fun n₂ q₂ l r => ?_
    have h3 := congrFun (step n₂ q₂ l (bd 1 r * g)) 1
    simpa only [← mul_assoc, hmul, mul_one, Pi.zero_apply] using h3
  simpa [hone] using congrFun fin 1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineInj
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem int_map {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (C : Co K ι) (n : ℕ)
    [MeasurableSpace (unitaryGroup (Fin n) ℂ)] [BorelSpace (unitaryGroup (Fin n) ℂ)]
    (ν : Measure (ι → unitaryGroup (Fin n) ℂ)) (F : archCompact K n → ℂ) :
    ∫ k, F k ∂(Measure.map (C.Φ n).symm ν) = ∫ y, F ((C.Φ n).symm y) ∂ν :=
  ((C.Φ n).symm.toHomeomorph.measurableEmbedding).integral_map F

private theorem sw {G : Type} [Group G] (L u v w : G) (h1 : u * w = w * u) (h2 : v * w = w * v) :
    L * w * (u * v) = L * u * v * w := by
  rw [mul_assoc L w, ← mul_assoc w, ← h1, mul_assoc u, ← h2]
  simp only [mul_assoc]

private theorem zt_zero' {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  unfold zt
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
  rw [this, map_one]

private theorem lv_zero {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) :
    ((lv m₁ m₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (m₁ : AdelicGLn.AdelicGL K 2) (m₂ : AdelicGLn.AdelicGL K 2) := by
  rw [(blkLaws (K := K)).1, neg_zero, zt_zero', mul_one, mul_one]

private theorem un_cont {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (C : Co K ι) (i : ι) :
    Continuous (C.un i) := by
  have h : Continuous (fun m : U2 => (Pi.mulSingle i m : ι → U2)) := by
    refine continuous_pi fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id
    · simpa [Pi.mulSingle_eq_of_ne hj] using continuous_const
  exact continuous_archP.comp (continuous_subtype_val.comp ((C.Φ 2).symm.continuous.comp h))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.lineInj :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ →
      ∀ (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ → ExtP μ e n q n' q' x →
      (∀ i, C.MinAt μ₂ τ₁ i (n i) (q i)) → (∀ i, C.MinAt μ₂ τ₂ i (n' i) (q' i)) → ∀ f, IsSec τ₁ τ₂ f → FixA (C.κ₄ μ) (C.e e) f →
        (∀ (h : FA K (2 + 2)) m₁ m₂, f (lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) = 0) → f = 0 := by
  intro K _ _ _ ι _ C μ₂ _ τ₁ τ₂ _ μ e n q n' q' x h4 hE hmin hmin' f hf hfix hz
  obtain ⟨-, -, -, -, -, -, -, -, -, hlv, hcomm, hKG⟩ := coLaws K ι C
  have hb := blkLaws (K := K)
  have hmul := hb.2.1
  obtain ⟨-, -, hbd1, -⟩ := u4
  have he : ∀ k, C.e e ((C.Φ (2 + 2)).symm k) = ∏ i, e i (k i) := by
    intro k; simp only [Co.e, ContinuousMulEquiv.apply_symm_apply]
  have ha : ∀ a b : ι → U4, arc1 ((C.Φ (2 + 2)).symm (a * b)) =
      arc1 ((C.Φ (2 + 2)).symm a) * arc1 ((C.Φ (2 + 2)).symm b) := by
    intro a b
    set_option synthInstance.maxHeartbeats 200000 in
      simp [arc1, map_mul]
  have h1 : (arc1 ((C.Φ 2).symm (1 : ι → U2)) : G1 K 2) = 1 := by simp [arc1, map_one]
  have hun : ∀ i (a b : U2), C.un i (a * b) = C.un i a * C.un i b := by
    intro i a b; simp [Co.un, arc1, Pi.mulSingle_mul, map_mul]
  have hs₁ : ∀ i (m : U2), arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd m 1))) = lv (C.un i m) 1 0 := by
    intro i m
    have hl := hlv (Pi.mulSingle i m) 1
    rw [h1] at hl
    have e1 : (fun j => bd ((Pi.mulSingle i m : ι → U2) j) ((1 : ι → U2) j)) = Pi.mulSingle i (bd m 1) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj, hbd1]
    rw [e1] at hl
    exact hl.symm
  have hs₂ : ∀ i (m : U2), arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd 1 m))) = lv 1 (C.un i m) 0 := by
    intro i m
    have hl := hlv 1 (Pi.mulSingle i m)
    rw [h1] at hl
    have e1 : (fun j => bd ((1 : ι → U2) j) ((Pi.mulSingle i m : ι → U2) j)) = Pi.mulSingle i (bd 1 m) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj, hbd1]
    rw [e1] at hl
    exact hl.symm
  have key₁ : ∀ (y : G1 K (2 + 2)) (M m₂ : G1 K 2) i n₀ q₀, ¬ Above (n i) (q i) n₀ q₀ →
      ∫ m, conj (KT.psi n₀ q₀ n₀ m) * f (lv (M * C.un i m) m₂ 0 * y) ∂μK = 0 := by
    intro y M m₂ i n₀ q₀ hA
    obtain ⟨d, φ, ψ, p₁, p₂, p₃⟩ := hf.levi y
    have hs : ∀ a b : G1 K 2, f (lv a b 0 * y) = ∑ j, φ j a * ψ j b := fun a b =>
      p₃ a b _ (by rw [Subgroup.coe_mul, lv_zero])
    simp only [hs, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨v, hv, hr⟩ := (p₁ j).2
      have h0 := (ptPi K ι C μ₂ v (φ j) (p₁ j).1 hr).1 i n₀ q₀ ((hmin i).2 n₀ q₀ hA v hv) M
      have e1 : ∀ m, conj (KT.psi n₀ q₀ n₀ m) * (φ j (M * C.un i m) * ψ j m₂) =
          (conj (KT.psi n₀ q₀ n₀ m) * φ j (M * C.un i m)) * ψ j m₂ := fun m => by ring
      simp only [e1]
      rw [integral_mul_const, h0, zero_mul]
    · intro j _
      exact KT.integrable_of_continuous ((KT.continuous_conj_psi n₀ q₀ n₀).mul
        (((p₁ j).1.comp (continuous_const.mul (un_cont C i))).mul continuous_const))
  have key₂ : ∀ (y : G1 K (2 + 2)) (M m₁ : G1 K 2) i n₀ q₀, ¬ Above (n' i) (q' i) n₀ q₀ →
      ∫ m, conj (KT.psi n₀ q₀ n₀ m) * f (lv m₁ (M * C.un i m) 0 * y) ∂μK = 0 := by
    intro y M m₁ i n₀ q₀ hA
    obtain ⟨d, φ, ψ, p₁, p₂, p₃⟩ := hf.levi y
    have hs : ∀ a b : G1 K 2, f (lv a b 0 * y) = ∑ j, φ j a * ψ j b := fun a b =>
      p₃ a b _ (by rw [Subgroup.coe_mul, lv_zero])
    simp only [hs, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨v, hv, hr⟩ := (p₂ j).2
      have h0 := (ptPi K ι C μ₂ v (ψ j) (p₂ j).1 hr).1 i n₀ q₀ ((hmin' i).2 n₀ q₀ hA v hv) M
      have e1 : ∀ m, conj (KT.psi n₀ q₀ n₀ m) * (φ j m₁ * ψ j (M * C.un i m)) =
          (conj (KT.psi n₀ q₀ n₀ m) * ψ j (M * C.un i m)) * φ j m₁ := fun m => by ring
      simp only [e1]
      rw [integral_mul_const, h0, zero_mul]
    · intro j _
      exact KT.integrable_of_continuous ((KT.continuous_conj_psi n₀ q₀ n₀).mul
        (continuous_const.mul ((p₂ j).1.comp (continuous_const.mul (un_cont C i)))))
  have hall : ∀ (m₁ m₂ : G1 K 2) (h : FA K (2 + 2)) (a : archCompact K (2 + 2)),
      f (lv m₁ m₂ 0 * fin1 h * arc1 a) = 0 := by
    intro m₁ m₂ h a
    have hc : Continuous fun k : ι → U4 => f (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      refine hf.cont.comp (continuous_const.mul ?_)
      exact continuous_archP.comp (continuous_subtype_val.comp (C.Φ (2 + 2)).symm.continuous)
    have hr : RFix (Measure.pi fun _ : ι => μ) (fun k => ∏ i, e i (k i))
        fun k : ι → U4 => f (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      intro g
      have := hfix (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm g))
      rw [Co.κ₄, int_map] at this
      simp only [he] at this
      simp only [ha, ← mul_assoc]
      exact this
    have hzero := hE.inj _ hc hr (fun i n₀ q₀ hA l k => ?_) (fun i n₀ q₀ hA l k => ?_) (fun a b => ?_)
    · have := congrFun hzero (C.Φ (2 + 2) a)
      simpa only [ContinuousMulEquiv.symm_apply_apply, Pi.zero_apply] using this
    · have e1 : ∀ m : U2, lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd (l * m) 1) * k)) =
          lv (m₁ * C.un i l * C.un i m) m₂ 0 * (fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
        intro m
        have h2 : lv (m₁ * C.un i l * C.un i m) m₂ 0 =
            lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd (l * m) 1))) := by
          have := hmul m₁ m₂ (C.un i (l * m)) 1 0 0
          rw [mul_one, add_zero, hun, ← mul_assoc] at this
          rw [hs₁, hun]
          rw [this]
        rw [h2, ha, mul_assoc, mul_assoc, ← mul_assoc (fin1 h), ← mul_assoc (arc1 _), (hcomm _ _ h).eq]
      simp only [e1]
      exact key₁ _ _ _ i n₀ q₀ hA
    · have e1 : ∀ m : U2, lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd 1 (l * m)) * k)) =
          lv m₁ (m₂ * C.un i l * C.un i m) 0 * (fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
        intro m
        have h2 : lv m₁ (m₂ * C.un i l * C.un i m) 0 =
            lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm (Pi.mulSingle i (bd 1 (l * m)))) := by
          have := hmul m₁ m₂ 1 (C.un i (l * m)) 0 0
          rw [mul_one, add_zero, hun, ← mul_assoc] at this
          rw [hs₂, hun]
          rw [this]
        rw [h2, ha, mul_assoc, mul_assoc, ← mul_assoc (fin1 h), ← mul_assoc (arc1 _), (hcomm _ _ h).eq]
      simp only [e1]
      exact key₂ _ _ _ i n₀ q₀ hA
    · have h2 : lv (m₁ * arc1 ((C.Φ 2).symm a)) (m₂ * arc1 ((C.Φ 2).symm b)) 0 =
          lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i)) := by
        rw [← hlv, hmul, add_zero]
      show f (lv m₁ m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm ((fun i => bd (a i) (b i)) * x))) = 0
      rw [ha, sw _ _ _ _ (hcomm _ _ h).eq (hcomm _ _ h).eq, ← h2]
      exact hz h _ _
  have hray : ∀ (t : ℝ) (y : G1 K (2 + 2)), f (lv 1 1 t * y) = f y := by
    intro t y
    refine hf.ray ⟨Real.exp t, Real.exp_pos t⟩ _ y ?_
    rw [Subgroup.coe_mul, hb.1, Subgroup.coe_one, one_mul, one_mul]
    have e2 : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ :=
      Subtype.ext (Real.exp_neg t)
    simp only [zt, e2]
  funext g
  obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
  obtain ⟨a, h, -, rfl⟩ := hKG (2 + 2) k hk
  have e3 : lv m₁ m₂ t = lv 1 1 t * lv m₁ m₂ 0 := by
    rw [hmul, one_mul, one_mul, add_zero]
  rw [mul_assoc, hf.unip X, e3, mul_assoc, hray, (hcomm _ _ h).eq, ← mul_assoc]
  exact hall m₁ m₂ h a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.MinSwap
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.minSwap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ τ₁ τ₂ : Submodule ℂ (LL μ),
        τ₁.map (θ.U : LL μ →ₗ[ℂ] LL μ) = τ₂ → ∀ s u n q, CE.MinAt μ τ₁ (s, u) n q → CE.MinAt μ τ₂ (s + 1, u) n q := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ τ₁ τ₂ hτ s u n q hmin
  obtain ⟨hnorm, -, hint⟩ := UpperTheory.ConvolutionTheory.Dp.twUnitary E 2 μ θ
  have htw := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw F E σ D CF CE hC μ θ hθ
  let L : LL μ →ₗᵢ[ℂ] LL μ := ⟨(θ.U : LL μ →ₗ[ℂ] LL μ), hnorm⟩
  have hL : ∀ v, L v = θ.U v := fun _ => rfl
  have key : ∀ n' q' v, θ.U (CE.Pi μ (s, u) n' q' v) = CE.Pi μ (s + 1, u) n' q' (θ.U v) := by
    intro n' q' v
    unfold Co.Pi
    rw [← hL, ← L.integral_comp_comm]
    congr 1
    funext m
    rw [map_smul, hL, hint, htw]
  subst hτ
  obtain ⟨⟨v, hv, hne⟩, hz⟩ := hmin
  refine ⟨⟨θ.U v, Submodule.mem_map_of_mem hv, fun h => hne ?_⟩, ?_⟩
  · rw [← key] at h
    rw [← norm_eq_zero, ← hnorm, h, norm_zero]
  · rintro n' q' hn _ ⟨w, hw, rfl⟩
    have := key n' q' w
    rw [hz n' q' hn w hw, map_zero] at this
    exact this.symm
end

