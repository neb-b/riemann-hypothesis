module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PKerSwap
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem kerSwap : KerUnif → KerSwap := by
  intro hU H _ _ _ _ _ _ _ _ n ι hι μ _ Ω I _ _ m _ c q hk P _ _ _ W p K C hW hp hK hC hWC
  obtain ⟨B, hB⟩ := hU H n ι hι Ω I m c q hk P W p K C hW hp hK hC hWC
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hmc : Continuous (matCoord ι) := hι.continuous
  set G : H × H → ℂ := fun z => W (matCoord ι z.1, p z.2) with hG
  have hGc : Continuous G := hW.continuous.comp ((hmc.comp continuous_fst).prodMk (hp.comp continuous_snd))
  set F : H → Ω → ℂ := fun k x => ker c q (fun y => W (matCoord ι y, p k)) x with hF

  have hvan : ∀ x, ∀ k ∈ K, ∀ i, i ∉ (hk.fin x C hC).toFinset → c i x * W (matCoord ι (q i x), p k) = 0 := by
    intro x k hkK i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
    rcases hi with h | h
    · simp [h]
    · simp [hWC k hkK _ h]

  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict K).prod m) := by
    obtain ⟨u, hu⟩ := (atTop : Filter (Finset I)).exists_seq_tendsto
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N (z : H × Ω) => ∑ i ∈ u N, c i z.2 * W (matCoord ι (q i z.2), p z.1)) ?_ ?_
    · intro N
      refine (Finset.measurable_sum _ fun i _ => ?_).aestronglyMeasurable
      refine ((hk.mc i).comp measurable_snd).mul ?_
      have : Measurable fun z : H × Ω => ((q i z.2, z.1) : H × H) :=
        ((hk.mq i).comp measurable_snd).prodMk measurable_fst
      exact hGc.measurable.comp this
    · have hae : ∀ᵐ z ∂((μ.restrict K).prod m), z.1 ∈ K :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_restrict_mem hKm)
      filter_upwards [hae] with z hz
      have hs : HasSum (fun i => c i z.2 * W (matCoord ι (q i z.2), p z.1))
          (∑' i, c i z.2 * W (matCoord ι (q i z.2), p z.1)) :=
        (summable_of_ne_finset_zero (s := (hk.fin z.2 C hC).toFinset) (hvan z.2 z.1 hz)).hasSum
      exact hs.comp hu
  have hint : Integrable (Function.uncurry F) ((μ.restrict K).prod m) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hKm] with k hkK
      exact (hB k hkK).1
    · refine Integrable.mono' (integrable_const B) hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hKm] with k hkK
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hB k hkK).2
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF, ker]
  have hT := hvan x
  set T := (hk.fin x C hC).toFinset
  rw [setIntegral_congr_fun hKm (fun k hkK => tsum_eq_sum (s := T) (hT k hkK))]
  rw [integral_finsetSum]
  · rw [tsum_eq_sum (s := T)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_const_mul _ _
    · intro i hi
      simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
      rcases hi with h | h
      · simp [h]
      · rw [setIntegral_eq_zero_of_forall_eq_zero (fun k hkK => hWC k hkK _ h), mul_zero]
  · intro i _
    exact (ContinuousOn.integrableOn_compact hK
      (continuous_const.mul (hW.continuous.comp (continuous_const.prodMk hp))).continuousOn)

end MainStatements.WeightKernel
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PKerUnif
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PKerUnif

theorem ker_eq_sum {H Ω I : Type} (c : I → Ω → ℂ) (q : I → Ω → H) (φ : H → ℂ) (C : Set H) (x : Ω)
    (hf : {i | c i x ≠ 0 ∧ q i x ∈ C}.Finite) (hφ : ∀ y ∉ C, φ y = 0) :
    MainStatements.WeightKernel.ker c q φ x = ∑ i ∈ hf.toFinset, c i x * φ (q i x) := by
  unfold MainStatements.WeightKernel.ker
  apply tsum_eq_sum
  intro i hi
  rw [Set.Finite.mem_toFinset] at hi
  by_cases h1 : c i x = 0
  · simp [h1]
  · have h2 : q i x ∉ C := fun h => hi ⟨h1, h⟩
    simp [hφ _ h2]

end MainStatements.WeightKernel.PKerUnif

open MainStatements.WeightKernel.PKerUnif in
theorem MainStatements.WeightKernel.kerUnif : SmoothSum → ClosedGraph → KerUnif := by
  intro hS hCG H _ _ _ _ _ _ _ _ n ι hι Ω I _ _ m _ c q hker P _ _ _ W p K C hW hp hK hC hvan
  obtain ⟨M, hM⟩ := ((hC.image hι.continuous).prod (hK.image hp)).exists_bound_of_continuousOn
    hW.continuous.continuousOn
  have hMb : ∀ y ∈ C, ∀ k ∈ K, ‖W (matCoord ι y, p k)‖ ≤ M := fun y hy k hk =>
    hM _ (Set.mk_mem_prod ⟨y, hy, rfl⟩ ⟨k, hk, rfl⟩)
  obtain ⟨R, hR⟩ := (hC.image hι.continuous).isBounded.subset_closedBall (0 : Mx n)
  obtain ⟨Bd, hBd⟩ := hCG Ω K m (fun (k : K) x => ker c q (fun y => W (matCoord ι y, p k)) x) (by
    intro x
    refine ⟨∑ i ∈ (hker.fin x C hC).toFinset, ‖c i x‖ * M, fun k => ?_⟩
    rw [ker_eq_sum c q _ C x (hker.fin x C hC) (fun y hy => hvan k k.2 y hy)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMb _ ((Set.Finite.mem_toFinset _).1 hi).2 _ k.2) (norm_nonneg _)) (by
    intro a ha
    have hz : ∀ y ∉ C, ∑' k : K, a k * W (matCoord ι y, p k) = 0 := by
      intro y hy
      have : ∀ k : K, a k * W (matCoord ι y, p k) = 0 := fun k => by rw [hvan k.1 k.2 y hy, mul_zero]
      simp [this]
    let bump : ContDiffBump (0 : Mx n) :=
      ⟨max R 0 + 1, max R 0 + 2, add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos, by linarith⟩
    obtain ⟨Φ, hΦs, hΦ⟩ := hS (Mx n) P W hW (p '' K) (Metric.closedBall 0 (max R 0 + 2)) (hK.image hp)
      (isCompact_closedBall _ _) K (fun k => p k.1) (fun k => ⟨k.1, k.2, rfl⟩) a ha
    have hψ : (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨HasCompactSupport.intro hC fun y hy => hz y hy, fun z => Complex.ofRealCLM (bump z) * Φ z,
        (Complex.ofRealCLM.contDiff.comp bump.contDiff).mul hΦs, fun y => ?_⟩
      simp only [Complex.ofRealCLM_apply]
      by_cases hy : y ∈ C
      · have hin : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 1) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have hin2 : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have h1 : bump (matCoord ι y) = 1 := bump.one_of_mem_closedBall hin
        rw [h1, hΦ _ hin2]
        simp
      · by_cases hb : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2)
        · rw [hΦ _ hb]
          simp [hz y hy]
        · have h0 : bump (matCoord ι y) = 0 :=
            image_eq_zero_of_notMem_tsupport (by rw [bump.tsupport_eq]; exact hb)
          simp [h0, hz y hy]
    refine (hker.int _ hψ).congr (ae_of_all m fun x => ?_)
    have hf := hker.fin x C hC
    have hs : ∀ i ∈ hf.toFinset, Summable (fun k : K => a k * W (matCoord ι (q i x), p k)) := by
      intro i hi
      have hq := ((Set.Finite.mem_toFinset _).1 hi).2
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (ha.mul_right M))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMb _ hq _ k.2) (norm_nonneg _)
    have hu : ∀ k : K, ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑ i ∈ hf.toFinset, c i x * W (matCoord ι (q i x), p k) :=
      fun k => ker_eq_sum c q _ C x hf (fun y hy => hvan k k.2 y hy)
    symm
    calc ∑' k : K, a k * ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑' k : K, ∑ i ∈ hf.toFinset, c i x * (a k * W (matCoord ι (q i x), p k)) := by
          congr 1; ext k; rw [hu k, Finset.mul_sum]; congr 1; ext i; ring
      _ = ∑ i ∈ hf.toFinset, ∑' k : K, c i x * (a k * W (matCoord ι (q i x), p k)) :=
          Summable.tsum_finsetSum fun i hi => (hs i hi).mul_left _
      _ = ∑ i ∈ hf.toFinset, c i x * ∑' k : K, a k * W (matCoord ι (q i x), p k) := by
          congr 1; ext i; rw [tsum_mul_left]
      _ = ker c q (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) x :=
          (ker_eq_sum c q _ C x hf hz).symm)
  exact ⟨Bd, fun k hk => hBd ⟨k, hk⟩⟩

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PShiftT
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PShiftT

def rho (S : ℂ → ℝ) (z : ℂ) : ℂ :=
  if 1 < ‖z‖ then ((Real.sqrt (S z) : ℝ) : ℂ)
  else if ‖z‖ < 1 then (((Real.sqrt (S (star z)⁻¹) : ℝ) : ℂ))⁻¹ else 1

lemma key (S : ℂ → ℝ) (hS : ∀ z, 0 < S z) (z w : ℂ) (h : star z * w = 1) :
    star (rho S z) * rho S w = 1 := by
  have hz : z ≠ 0 := by rintro rfl; simp at h
  have hw : w = (star z)⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hw
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ‖(star z)⁻¹‖ = ‖z‖⁻¹ := by rw [norm_inv, norm_star]
  have hcc : (star (star z)⁻¹)⁻¹ = z := by rw [star_inv₀, star_star, inv_inv]
  have e : ‖z‖ * ‖z‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hipos : 0 < ‖z‖⁻¹ := inv_pos.mpr hpos
  rcases lt_trichotomy 1 ‖z‖ with h1 | h1 | h1
  · have h2 : ‖z‖⁻¹ < 1 := by nlinarith
    have hs : (((Real.sqrt (S z)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS z)).ne'
    simp only [rho, hn, hcc]
    rw [if_pos h1, if_neg (by linarith), if_pos h2, Complex.star_def, Complex.conj_ofReal]
    exact mul_inv_cancel₀ hs
  · have h2 : ‖z‖⁻¹ = 1 := by rw [← h1, inv_one]
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    simp
  · have h2 : 1 < ‖z‖⁻¹ := by nlinarith
    have hs : (((Real.sqrt (S (star z)⁻¹)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS _)).ne'
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_pos h1, if_pos h2, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    exact inv_mul_cancel₀ hs

end MainStatements.WeightKernel.PShiftT

namespace MainStatements.WeightKernel

open MainStatements.WeightKernel.PShiftT in
theorem shiftT : ShiftT := by
  intro n J l hl hJ σ hσ
  classical
  let S : ℂ → ℝ := fun z => if h : ∃ i, l i = z then σ (Classical.choose h) else 1
  have hSpos : ∀ z, 0 < S z := by
    intro z
    simp only [S]
    split_ifs
    · exact hσ _
    · exact zero_lt_one
  have hSl : ∀ i, S (l i) = σ i := by
    intro i
    have h : ∃ j, l j = l i := ⟨i, rfl⟩
    simp only [S, dif_pos h]
    rw [hl (Classical.choose_spec h)]
  refine ⟨fun i => rho S (l i), ?_, ?_⟩
  · ext i j
    have hij := congrFun (congrFun hJ i) j
    simp only [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply] at hij ⊢
    by_cases h0 : J i j = 0
    · simp [h0]
    have e1 : star (l i) * l j = 1 := by
      have : (star (l i) * l j) * J i j = 1 * J i j := by rw [one_mul]; calc _ = star (l i) * J i j * l j := by ring
          _ = J i j := hij
      exact mul_right_cancel₀ h0 this
    have e2 : star (rho S (l i)) * rho S (l j) = 1 := key S hSpos _ _ e1
    calc _ = (star (rho S (l i)) * rho S (l j)) * J i j := by ring
      _ = J i j := by rw [e2, one_mul]
  · intro i hi
    show ‖rho S (l i)‖ ^ 2 = σ i
    rw [rho, if_pos hi, hSl, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hσ i).le]

end MainStatements.WeightKernel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PSmoothSum
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PSmoothSum

lemma le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

end MainStatements.WeightKernel.PSmoothSum

namespace MainStatements.WeightKernel

open PSmoothSum in
theorem smoothSum : SmoothSum := by
  intro X P _ _ _ _ _ _ W hW K B hK hB I p hp a ha
  obtain ⟨R, hR⟩ := hB.isBounded.subset_closedBall (0 : X)
  let φ : ContDiffBump (0 : X) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let G : X × P → ℂ := fun q => ((φ q.1 : ℝ) : ℂ) * W q
  have hG : ContDiff ℝ ∞ G :=
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp contDiff_fst)).mul hW
  have hsupp : tsupport G ⊆ tsupport φ ×ˢ univ := by
    refine closure_minimal ?_ ((isClosed_tsupport _).prod isClosed_univ)
    intro q hq
    refine ⟨subset_tsupport _ ?_, mem_univ _⟩
    intro h0
    apply hq
    simp [G, h0]
  have hcpt : IsCompact (tsupport φ ×ˢ K) := φ.hasCompactSupport.isCompact.prod hK
  have hbound : ∀ k : ℕ, ∃ M : ℝ, ∀ x : X, ∀ y ∈ K, ‖iteratedFDeriv ℝ k G (x, y)‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn
      (hG.continuous_iteratedFDeriv (le_infty k)).continuousOn
    refine ⟨max M 0, fun x y hy => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (by simpa using hM (x, y) ⟨hx, hy⟩ : _ ≤ M).trans (le_max_left _ _)
    · have : (x, y) ∉ tsupport G := fun h => hx (hsupp h).1
      have h0 : iteratedFDeriv ℝ k G (x, y) = 0 := by
        by_contra hne
        exact this (support_iteratedFDeriv_subset k hne)
      simp [h0]
  choose M hM using hbound
  let L : X →L[ℝ] X × P := ContinuousLinearMap.inl ℝ X P
  have hpart : ∀ (y : P) (k : ℕ) (x : X), y ∈ K →
      ‖iteratedFDeriv ℝ k (fun z => G (z, y)) x‖ ≤ M k * ‖L‖ ^ k := by
    intro y k x hy
    have heq : (fun z => G (z, y)) = (fun q => G (q + (0, y))) ∘ L := by
      funext z
      simp [L]
    have hGt : ContDiff ℝ ∞ (fun q => G (q + (0, y))) := hG.comp (contDiff_id.add contDiff_const)
    rw [heq, L.iteratedFDeriv_comp_right hGt x (le_infty k)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hxy : L x + (0, y) = (x, y) := by simp [L]
    rw [hxy]
    exact mul_le_mul_of_nonneg_right (hM k x y hy) (pow_nonneg (norm_nonneg _) _)
  refine ⟨fun x => ∑' i, a i * G (x, p i), ?_, ?_⟩
  · refine contDiff_tsum (N := (⊤ : ℕ∞)) (v := fun k i => ‖a i‖ * (M k * ‖L‖ ^ k)) ?_ ?_ ?_
    · intro i
      exact contDiff_const.mul (hG.comp (contDiff_id.prodMk contDiff_const))
    · intro k _
      exact ha.mul_right _
    · intro k i x _
      have hci : ContDiffAt ℝ k (fun z => G (z, p i)) x :=
        ((hG.comp (contDiff_id.prodMk contDiff_const)).of_le (le_infty k)).contDiffAt
      have := iteratedFDeriv_const_smul_apply' (a := a i) hci
      simp only [smul_eq_mul] at this
      rw [this]
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hpart (p i) k x (hp i)) (norm_nonneg _))
  · intro x hx
    have hx' : dist x 0 ≤ R := hR hx
    have h1 : φ x = 1 := φ.one_of_mem_closedBall (by
      show dist x 0 ≤ max R 0 + 1
      linarith [le_max_left R 0])
    simp [G, h1]

end MainStatements.WeightKernel
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PWeight
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PWeight

variable {n : ℕ}

theorem cancel_l {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

def conjHom {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) : H →* Matrix (Fin n) (Fin n) ℂ where
  toFun h := Q * ι h * P
  map_one' := by simp [hQP]
  map_mul' a b := by simp only [map_mul, Matrix.mul_assoc, cancel_l hPQ]

theorem conjHom_apply {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (g : H) : conjHom ι Q P hPQ hQP g = Q * ι g * P := rfl

def conjHomeo (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ where
  toFun Y := Q * Y * P
  invFun Y := P * Y * Q
  left_inv Y := by simp only [Matrix.mul_assoc, cancel_l hPQ, hPQ, Matrix.mul_one]
  right_inv Y := by simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem isUGroup_conj {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hU : IsUGroup ι J) :
    IsUGroup (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) := by
  have hPQh : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
  have hQPh : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩
  have hPh : IsUnit Pᴴ.det := isUnit_iff_exists_inv.2 ⟨Qᴴ.det, by rw [← det_mul, hQPh, det_one]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact (hPh.mul hU.1).mul hP
  · exact (conjHomeo Q P hPQ hQP).isClosedEmbedding.comp hU.2.1
  · have key1 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (Q * X * P)ᴴ * (Pᴴ * J * P) * (Q * X * P) = Pᴴ * (Xᴴ * J * X) * P := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc, cancel_l hPQh, cancel_l hPQ]
    have key2 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (P * X * Q)ᴴ * J * (P * X * Q) = Qᴴ * (Xᴴ * (Pᴴ * J * P) * X) * Q := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have key3 : Qᴴ * (Pᴴ * J * P) * Q = J := by
      simp only [Matrix.mul_assoc, cancel_l hPQh, hPQ, Matrix.mul_one]
    intro M
    constructor
    · rintro ⟨h, rfl⟩
      have hA := (hU.2.2 (ι h)).1 ⟨h, rfl⟩
      rw [conjHom_apply, key1, hA]
    · intro hM
      have hN : (P * M * Q)ᴴ * J * (P * M * Q) = J := by rw [key2, hM, key3]
      obtain ⟨h, hh⟩ := (hU.2.2 _).2 hN
      refine ⟨h, ?_⟩
      rw [conjHom_apply, hh]
      simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]

def conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) (Y : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n :=
  fun i j => (Q * Matrix.of Y * P) i j

theorem contDiff_conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (conjMx Q P) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [conjMx, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun x _ => ContDiff.mul (ContDiff.sum fun y _ =>
    contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) x).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) y))) contDiff_const

end MainStatements.WeightKernel.PWeight

namespace MainStatements.WeightKernel

open PWeight in
theorem weight : WeightDiag → Weight := by
  intro hWD H _ _ _ _ _ _ _ _ n ι J hU s hreg hprop
  obtain ⟨P, Q, l, hl, hPQ, hQP, hd⟩ := GlobalTheory.CompanionTheory.WeylNear.exists_diag n (ι s) hreg
  obtain ⟨B', hB'⟩ := hWD H n (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) (isUGroup_conj ι J Q P hPQ hQP hU) s l hl
    hd hprop
  refine ⟨fun z => B' (conjMx Q P z.1, conjMx Q P z.2), ?_, fun z => hB'.nonneg _, hB'.pos, hB'.shift, hB'.proper⟩
  exact hB'.smooth.comp (((contDiff_conjMx Q P).comp contDiff_fst).prodMk ((contDiff_conjMx Q P).comp contDiff_snd))

end MainStatements.WeightKernel

end
end

