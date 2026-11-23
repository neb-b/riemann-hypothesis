module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Master
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem cont_pt {K : Type} [Field K] [NumberField K] : Continuous (pt (K := K)) := by
  obtain ⟨-, -, -, hc, -⟩ := blkLaws (K := K)
  have hL : Continuous fun p : Par K => lv p.1 p.2.1 p.2.2.1 := by
    have : Continuous fun p : Par K => (p.1, p.2.1, p.2.2.1) := by fun_prop
    simpa only [Function.comp_def] using hc.comp this
  have hN : Continuous fun p : Par K => (nn p.2.2.2.2 : G1 K (2 + 2)) := (continuous_unipOne 2).comp (by fun_prop)
  exact (hN.mul hL).mul (continuous_subtype_val.comp (by fun_prop))

set_option synthInstance.maxHeartbeats 200000 in
private theorem meas_pt {K : Type} [Field K] [NumberField K] : Measurable (pt (K := K)) := by
  haveI : BorelSpace (KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K])) := Prod.borelSpace
  haveI : BorelSpace (ℝ × KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K])) := Prod.borelSpace
  haveI : SecondCountableTopology (G1 K 2) := inferInstance
  haveI : BorelSpace (G1 K 2 × ℝ × KG K (2 + 2) × (UPos (2 + 2) 2 → 𝔸[K])) := Prod.borelSpace
  haveI : BorelSpace (Par K) := Prod.borelSpace
  exact cont_pt.measurable

private theorem core {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (c : ℝ) (hU : Unf μ μ₂ κ c)
    (F : G1 K (2 + 2) → ℂ) (hF : Continuous F) (hP : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (hB : InBand F) (hD : Decays F)
    (v w : L2 μ) (hv : Reps μ v (th F)) (W : G1 K (2 + 2) → ℂ) (hW : Measurable W)
    (hWi : ∀ γ ∈ Gam K (2 + 2), ∀ g, W (γ * g) = W g) (hw : Reps μ w W) :
    Integrable (fun p => conj (F (pt p)) * W (pt p)) (parM μ₂ κ) ∧
      ⟪v, w⟫_ℂ = c * ∫ p, conj (F (pt p)) * W (pt p) ∂parM μ₂ κ := by
  obtain ⟨hfin, -, -, h4⟩ := thBasic μ F hF hP hB
  obtain ⟨⟨C, hC, hCb⟩, -, -⟩ := h4 hD
  have hm : Measurable fun g => conj (F g) * W g := (Complex.continuous_conj.comp hF).measurable.mul hW
  have hinv : ∀ γ ∈ PK K, ∀ g, conj (F (γ * g)) * W (γ * g) = conj (F g) * W g := fun γ hγ g => by
    obtain ⟨δ, -, rfl⟩ := id hγ
    rw [hP _ hγ]
    exact congrArg _ (hWi _ δ.2 g)
  have hwae : ∀ᵐ y ∂fd μ, (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = W y := ae_restrict_of_ae hw
  have hvae : ∀ᵐ y ∂fd μ, (v : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = th F y := ae_restrict_of_ae hv
  have hW1 : ∫⁻ y, ‖W y‖ₑ ∂fd μ < ⊤ := by
    haveI := isFiniteMeasure_quotientMeasure μ
    have h1 := ((Lp.memLp w).integrable one_le_two).2
    rw [hasFiniteIntegral_iff_enorm, lintegral_quotientMeasure] at h1
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) h1
    filter_upwards [hwae] with y hy
    rw [hy]
  have hint : Integrable (fun p => conj (F (pt p)) * W (pt p)) (parM μ₂ κ) := by
    refine ⟨(hm.comp meas_pt).aestronglyMeasurable, ?_⟩
    have h1 := hU.2.1 (fun g => ‖conj (F g) * W g‖ₑ) hm.enorm fun γ hγ g => by rw [hinv γ hγ]
    have h2 : ∫⁻ y, ∑' q : Cos K, ‖conj (F ((q.out : G1 K (2 + 2)) * y)) * W ((q.out : G1 K (2 + 2)) * y)‖ₑ ∂fd μ ≤
        ∫⁻ y, C * ‖W y‖ₑ ∂fd μ := by
      refine lintegral_mono fun y => ?_
      simp only [enorm_mul, hWi _ (Quotient.out _ : Gam K (2 + 2)).2, RCLike.enorm_conj]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul_left (hCb y) _
    rw [lintegral_const_mul' _ _ hC, h1] at h2
    have h3 := h2.trans_lt (ENNReal.mul_lt_top hC.lt_top hW1)
    rw [hasFiniteIntegral_iff_enorm]
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top (by simpa using hU.1)] at h3
    exact lt_irrefl _ h3
  refine ⟨hint, ?_⟩
  rw [← hU.2.2 _ hm hinv hint, L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae ?_
  filter_upwards [hwae, hvae] with y h1 h2
  have hf : (Function.support fun q : Cos K => F ((q.out : G1 K (2 + 2)) * y)).Finite :=
    (hfin {y} isCompact_singleton).subset fun q hq => ⟨y, rfl, hq⟩
  simp only [hWi _ (Quotient.out _ : Gam K (2 + 2)).2]
  rw [tsum_mul_right, ← Complex.conj_tsum, tsum_eq_finsum hf, h1, h2, RCLike.inner_apply, mul_comm]
  rfl

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.master :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (c : ℝ), Unf μ μ₂ κ c → ∀ (F : G1 K (2 + 2) → ℂ), Continuous F → (∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) → InBand F → Decays F → ∀ v w : L2 μ, Reps μ v (th F) →
      Integrable (fun p => conj (F (pt p)) * (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) (pt p))) (parM μ₂ κ) ∧
      ⟪v, w⟫_ℂ = c * ∫ p, conj (F (pt p)) * (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) (pt p)) ∂parM μ₂ κ ∧
      ∀ Φ : G1 K (2 + 2) → ℂ, Continuous Φ → (∀ γ ∈ Gam K (2 + 2), ∀ g, Φ (γ * g) = Φ g) → Reps μ w Φ →
        Integrable (fun p => conj (F (pt p)) * Φ (pt p)) (parM μ₂ κ) ∧ ⟪v, w⟫_ℂ = c * ∫ p, conj (F (pt p)) * Φ (pt p) ∂parM μ₂ κ := by
  intro K _ _ μ _ μ₂ _ κ _ c hU F hF hP hB hD v w hv
  have h := core μ μ₂ κ c hU F hF hP hB hD v w hv
    (fun g => (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) g))
    ((Lp.stronglyMeasurable w).measurable.comp (measurable_mk _)) (fun γ hγ g => by rw [mk_mul_of_mem hγ])
    (Eventually.of_forall fun _ => rfl)
  exact ⟨h.1, h.2, fun Φ hΦ hi hw => core μ μ₂ κ c hU F hF hP hB hD v w hv Φ hΦ.measurable hi hw⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SwapInt
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem w_mul {R : Type} [CommRing R] (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i : Fin 2) (k : Fin (2 + 2)) :
    ((wGL R).val * M) (Fin.natAdd 2 i) k = M (Fin.castAdd 2 i) k := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp only [wGL, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem mul_w {R : Type} [CommRing R] (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (j : Fin 2) (k : Fin (2 + 2)) :
    (M * ((wGL R)⁻¹).val) k (Fin.castAdd 2 j) = M k (Fin.natAdd 2 j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  change (∑ i, _ * (wGL R).inv _ _) + (∑ i, _ * (wGL R).inv _ _) = _
  simp only [wGL, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem swap_int {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ) (hF : Continuous F)
    (hfin : ∀ C : Set (G1 K (2 + 2)), IsCompact C → {q : Cos K | ∃ g ∈ C, F ((q.out : G1 K (2 + 2)) * g) ≠ 0}.Finite)
    (g : G1 K (2 + 2)) :
    (Function.support fun q : Cos K => ∫ X in unipFundamentalDomain K (2 + 2) 2,
      F ((q.out : G1 K (2 + 2)) * (unipOne 2 X * g)) ∂unipMeasure K (2 + 2) 2).Finite ∧ ∀ S : Set (Cos K),
    ∫ X in unipFundamentalDomain K (2 + 2) 2, ∑ᶠ q ∈ S, F ((q.out : G1 K (2 + 2)) * (unipOne 2 X * g)) ∂unipMeasure K (2 + 2) 2 =
      ∑ᶠ q ∈ S, ∫ X in unipFundamentalDomain K (2 + 2) 2,
        F ((q.out : G1 K (2 + 2)) * (unipOne 2 X * g)) ∂unipMeasure K (2 + 2) 2 := by
  classical
  obtain ⟨C, hC, hD⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := 2 + 2) (r := 2)
  have hc : Continuous fun X : UPos (2 + 2) 2 → 𝔸[K] => unipOne 2 X * g := (continuous_unipOne 2).mul continuous_const
  have hQ := hfin _ (hC.image hc)
  have hz : ∀ q : Cos K, q ∉ hQ.toFinset → ∀ X ∈ unipFundamentalDomain K (2 + 2) 2,
      F ((q.out : G1 K (2 + 2)) * (unipOne 2 X * g)) = 0 := fun q hq X hX => by
    by_contra h
    exact hq (hQ.mem_toFinset.2 ⟨_, ⟨X, hD hX, rfl⟩, h⟩)
  have hz' : ∀ q : Cos K, q ∉ hQ.toFinset → ∫ X in unipFundamentalDomain K (2 + 2) 2,
      F ((q.out : G1 K (2 + 2)) * (unipOne 2 X * g)) ∂unipMeasure K (2 + 2) 2 = 0 := fun q hq =>
    setIntegral_eq_zero_of_forall_eq_zero (hz q hq)
  refine ⟨hQ.toFinset.finite_toSet.subset fun q hq => by_contra fun h => hq (hz' q h), fun S => ?_⟩
  have e : ∀ f : Cos K → ℂ, (∀ q, q ∉ hQ.toFinset → f q = 0) → ∑ᶠ q ∈ S, f q = ∑ q ∈ hQ.toFinset.filter (· ∈ S), f q := by
    intro f hf
    refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
    ext q
    simp only [mem_inter_iff, Function.mem_support, Finset.coe_filter, mem_setOf_eq]
    exact ⟨fun h => ⟨⟨by_contra fun h' => h.2 (hf q h'), h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  have hI : ∀ q : Cos K, Integrable (fun X => F ((q.out : G1 K (2 + 2)) * (unipOne 2 X * g)))
      ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := fun q =>
    ((hF.comp (continuous_const.mul hc)).continuousOn.integrableOn_compact hC).mono_set hD
  rw [e _ hz', ← integral_finsetSum _ fun q _ => hI q]
  exact setIntegral_congr_fun measurableSet_unipFundamentalDomain fun X hX => e _ fun q hq => hz q hq X hX

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.thCt :
    ∀ {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ),
      UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.PFun F → InBand F → ∀ g,
      ∫ X in unipFundamentalDomain K (2 + 2) 1, th F (unipOne (K := K) (n := 2 + 2) 1 X * g) ∂unipMeasure K (2 + 2) 1 = 0 ∧
      ∫ X in unipFundamentalDomain K (2 + 2) 3, th F (unipOne (K := K) (n := 2 + 2) 3 X * g) ∂unipMeasure K (2 + 2) 3 = 0 ∧
      HasCompactSupport (fun X : UPos (2 + 2) 2 → 𝔸[K] => F (w0 K * nn X * g)) ∧
      ∫ X in unipFundamentalDomain K (2 + 2) 2, th F (unipOne (K := K) (n := 2 + 2) 2 X * g) ∂unipMeasure K (2 + 2) 2 = volN K * F g + ∫ X, F (w0 K * nn X * g) ∂unipMeasure K (2 + 2) 2 := by
  intro K _ _ F hF hB g
  obtain ⟨hfin, -⟩ := thBasic (Measure.haar : Measure (G1 K (2 + 2))) F hF.cont hF.rat hB
  obtain ⟨-, -, -, -, -, -, hw, hwΓ, -⟩ := blkLaws (K := K)
  obtain ⟨hpar, hPK, -, hout⟩ := pkLaws (K := K)
  have hodd : ∀ r, r = 1 ∨ r = 3 → ∫ X in unipFundamentalDomain K (2 + 2) r, th F (unipOne (K := K) (n := 2 + 2) r X * g)
      ∂unipMeasure K (2 + 2) r = 0 := fun r hr => by
    have := killAvg F hF.cont hF.rat hB r univ (fun _ _ _ _ _ => mem_univ _)
      (fun q _ => dies F hF q.out r (hr.imp_right Or.inl)) g
    simp only [finsum_mem_univ] at this
    exact this
  have hcs : HasCompactSupport fun X : UPos (2 + 2) 2 → 𝔸[K] => F (w0 K * nn X * g) := by
    obtain ⟨R, hR⟩ := hB
    obtain ⟨R', hR'⟩ := (hpSpec (K := K)).2.2.2.2 {g} isCompact_singleton
    obtain ⟨C, hC, hX⟩ := (longCell (K := K)).2 (R + R')
    refine HasCompactSupport.intro hC fun X hX' => by_contra fun h => hX' (hX X 1 (one_mem _) ?_)
    have h1 := abs_le.1 (hR _ h)
    have h2 := abs_le.1 (hR' (w0 K * nn X) g rfl)
    rw [mul_one]
    linarith [h1.1, h2.2]
  refine ⟨hodd 1 (Or.inl rfl), hodd 3 (Or.inr rfl), hcs, ?_⟩
  let n : unipLattice K (2 + 2) 2 → Gam K (2 + 2) := fun ξ => ⟨nn ξ.1, unipOne_mem_rationalGLOne 2 ξ⟩
  let w : Gam K (2 + 2) := ⟨w0 K, hwΓ⟩
  let c : unipLattice K (2 + 2) 2 → Cos K := fun ξ => Quotient.mk _ (w * n ξ)
  have hmk : ∀ a b : Gam K (2 + 2), (Quotient.mk _ a : Cos K) = Quotient.mk _ b ↔ b * a⁻¹ ∈ ParΓ K 2 2 := fun a b =>
    Quotient.eq.trans QuotientGroup.rightRel_apply
  have hadd : ∀ ξ η, n (ξ + η) = n ξ * n η := fun ξ η => Subtype.ext (unipOne_add 2 ξ.1 η.1)
  have hn0 : n 0 = 1 := Subtype.ext (unipOne_zero 2)
  have hneg : ∀ ξ, n (-ξ) = (n ξ)⁻¹ := fun ξ => eq_inv_of_mul_eq_one_left (by rw [← hadd, neg_add_cancel, hn0])
  have hnP : ∀ ξ, n ξ ∈ ParΓ K 2 2 := fun ξ => (hpar _).2 fun i j hi hj => by
    change unipMatrix ξ.1 i j = 0
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_right (by omega), Matrix.one_apply_ne (by
      rintro rfl; omega), add_zero]
  have hinj : Function.Injective c := fun ξ η h => by
    have h1 := (hmk _ _).1 h
    have e : w * n η * (w * n ξ)⁻¹ = w * n (η - ξ) * w⁻¹ := by
      rw [sub_eq_add_neg, hadd, hneg]; group
    rw [e, hpar] at h1
    refine (sub_eq_zero.1 (Subtype.ext (funext fun p => ?_))).symm
    obtain ⟨⟨i, j⟩, hi, hj⟩ := p
    have h2 := h1 (Fin.natAdd 2 ⟨i, hi⟩) (Fin.castAdd 2 ⟨j - 2, by have := j.2; omega⟩) (Nat.le_add_right _ _)
      (by have := j.2; show (j : ℕ) - 2 < 2; omega)
    simp only [w, n, Subgroup.coe_mul, Subgroup.coe_inv, hw, Units.val_mul, coe_unipOne, coe_unipGL] at h2
    rw [mul_w, w_mul] at h2
    have e1 : Fin.castAdd 2 (⟨i, hi⟩ : Fin 2) = i := Fin.ext rfl
    have e2 : Fin.natAdd 2 (⟨j - 2, by have := j.2; omega⟩ : Fin 2) = j := Fin.ext (by
      show 2 + ((j : ℕ) - 2) = j
      have : 2 ≤ (j : ℕ) := hj
      omega)
    rw [e1, e2, unipMatrix, Matrix.add_apply, blockEntry_apply, dite_eq_left ⟨hi, hj⟩, Matrix.one_apply_ne (by
      rintro rfl
      exact absurd hi (not_lt.2 hj)), zero_add] at h2
    exact h2
  have hne : (Quotient.mk _ 1 : Cos K) ∉ range c := by
    rintro ⟨ξ, h⟩
    have h1 := (hmk _ _).1 h.symm
    rw [inv_one, mul_one] at h1
    have h2 := (hpar _).1 (mul_mem h1 (inv_mem (hnP ξ))) (Fin.natAdd 2 0) (Fin.castAdd 2 0) (Nat.le_add_right _ _) two_pos
    rw [mul_inv_cancel_right] at h2
    simp only [w, hw] at h2
    rw [← mul_one (wGL 𝔸[K]).val, w_mul, Matrix.one_apply_eq] at h2
    exact one_ne_zero (α := K) (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (by rw [map_one, map_zero, h2]))
  have hval : ∀ (γ : Gam K (2 + 2)) x, F ((((Quotient.mk _ γ : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) * x) =
      F (γ * x) := fun γ x => by
    obtain ⟨δ, hδ, e⟩ := hout γ
    rw [e, mul_assoc, hF.rat δ hδ]
  obtain ⟨hs, hsw⟩ := swap_int F hF.cont hfin g
  have hk := killAvg F hF.cont hF.rat hB 2 (insert (Quotient.mk _ 1 : Cos K) (range c))ᶜ (fun γ γ' ξ e h h' => h (by
    have e' : γ' = γ * n ξ := Subtype.ext e
    subst e'
    rcases h' with h' | ⟨η, h'⟩
    · refine Or.inl ((hmk _ _).2 ?_)
      have := mul_mem (hnP ξ) ((hmk _ _).1 h')
      simpa using this
    · refine Or.inr ⟨η - ξ, (hmk _ _).2 ?_⟩
      have := (hmk _ _).1 h'
      rw [sub_eq_add_neg, hadd, hneg]
      convert this using 1
      group)) (fun q hq => dies F hF q.out 2 (Or.inr (Or.inr ⟨rfl, fun h => hq (Or.inl (by
        rw [← Quotient.out_eq q]
        exact (hmk _ _).2 (by simpa using h))), fun ⟨δ, ⟨δ', hδ', e'⟩, ξ, e⟩ => hq (Or.inr ⟨ξ, by
        rw [← Quotient.out_eq q]
        refine (hmk _ _).2 ?_
        have : q.out = δ' * (w * n ξ) := Subtype.ext (by rw [e, ← e', mul_assoc]; rfl)
        rw [this, mul_inv_cancel_right]
        exact hδ'⟩)⟩))) g
  rw [hsw] at hk
  have h1 := hsw univ
  simp only [finsum_mem_univ] at h1
  unfold th
  rw [h1, ← finsum_mem_univ, ← union_compl_self (insert (Quotient.mk _ 1 : Cos K) (range c)),
    finsum_mem_union' disjoint_compl_right (hs.inter_of_right _) (hs.inter_of_right _), hk, add_zero,
    finsum_mem_insert' _ hne (hs.inter_of_right _), finsum_mem_range hinj]
  congr 1
  · simp only [hval, OneMemClass.coe_one, one_mul, hF.unip, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      univ_inter, Complex.real_smul, volN]
  · have hi : Integrable (fun X => F (w0 K * nn X * g)) (unipMeasure K (2 + 2) 2) :=
      (hF.cont.comp ((continuous_const.mul (continuous_unipOne 2)).mul continuous_const)).integrable_of_hasCompactSupport hcs
    rw [isAddFundamentalDomain_unipFundamentalDomain.integral_eq_tsum'' _ hi]
    refine (tsum_eq_finsum (L := SummationFilter.unconditional _) (hs.preimage hinj.injOn)).symm.trans ?_
    refine tsum_congr fun ξ => integral_congr_ae (Eventually.of_forall fun X => ?_)
    refine Eq.trans (hval (w * n ξ) (nn X * g)) (congrArg F ?_)
    have e : (nn (ξ.1 + X) : G1 K (2 + 2)) = nn ξ.1 * nn X := unipOne_add 2 _ _
    have e' : ((w * n ξ : Gam K (2 + 2)) : G1 K (2 + 2)) = w0 K * nn ξ.1 := rfl
    have e'' : ξ +ᵥ X = ξ.1 + X := rfl
    rw [e', e'', e]
    simp only [mul_assoc]
end

