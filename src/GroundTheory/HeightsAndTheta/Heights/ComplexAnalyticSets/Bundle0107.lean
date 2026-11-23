module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0100
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSliceSheetParam
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set ComplexSets

noncomputable section

namespace ConeSliceSheetParam

theorem eval_sup_span {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {f : MvPolynomial (Fin n) ℂ}
    {x : Fin n → ℂ} (hJ : ∀ q ∈ J, eval x q = 0) (hf : eval x f = 0) :
    ∀ q ∈ J ⊔ Ideal.span {f}, eval x q = 0 := by
  intro q hq
  have hle : J ⊔ Ideal.span {f} ≤ RingHom.ker (eval x) :=
    sup_le (fun q hq => RingHom.mem_ker.2 (hJ q hq))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hf)))
  exact RingHom.mem_ker.1 (hle hq)

theorem eval_smul_of_isHomogIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsHomogIdeal J)
    {x : Fin n → ℂ} (hx : ∀ q ∈ J, eval x q = 0) (t : ℂ) : ∀ q ∈ J, eval (t • x) q = 0 := by
  intro q hq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i q), hx _ (hJ q hq i), mul_zero]

theorem eval_linForm_smul {n : ℕ} (ℓ : Fin n → ℂ) (t : ℂ) (x : Fin n → ℂ) :
    eval (t • x) (linForm ℓ) = t * eval x (linForm ℓ) := by
  rw [eval_smul_of_isHomogeneous (SliceIdeal.isHomogeneous_linForm ℓ), pow_one]

theorem slice_isPrime {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ} (hJ : IsProjPrime J)
    (hℓ : linForm ℓ ∉ J) : (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime := by
  have hP := hJ.isPrime
  have hdeh : ∀ (G : MvPolynomial (Fin n) ℂ) (d : ℕ), G.IsHomogeneous d →
      G ∈ J ⊔ Ideal.span {linForm ℓ - 1} → G ∈ J :=
    fun G d hG hm => ChartDehomog.proof ℂ n J ℓ G d hP hJ.isHomog hℓ hG hm
  have hspan : Ideal.span {linForm ℓ - 1} ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_right
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {a b} hab => ?_⟩
  · exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr
      (hdeh 1 0 (isHomogeneous_one _ _) (htop ▸ Submodule.mem_top)))
  obtain ⟨da, A, hA', hAa⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ a
  obtain ⟨db, B, hB', hBb⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ b
  have hAB : A * B ∈ J ⊔ Ideal.span {linForm ℓ - 1} := by
    have h : A * B = (A - a) * B + a * (B - b) + a * b := by ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hspan (Ideal.mul_mem_right _ _ hAa))
      (hspan (Ideal.mul_mem_left _ _ hBb))) hab
  rcases hP.mem_or_mem (hdeh _ _ (hA'.mul hB') hAB) with h | h
  · left
    have e : a = A - (A - a) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hAa)
  · right
    have e : b = B - (B - b) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hBb)

end ConeSliceSheetParam


open ConeSliceSheetParam in
theorem ConeSliceSheetParam.proof (hCov : DiscriminantSheetCover.Statement) :
    ConeSliceSheetParam.Statement := by
  classical
  intro n e h J ℓ A hJ hdim hℓ hA
  have hP := hJ.isPrime
  obtain ⟨P, U, D, N, s, hP0, hUD, hdisj, hbad, hnull, hfib⟩ :=
    hCov n e _ A (slice_isPrime hJ hℓ) (SliceDim.proof n e J ℓ hJ hdim hℓ) hA
  set J' := J ⊔ Ideal.span {linForm ℓ - 1} with hJ'
  set M := (h.matᵀ)⁻¹ with hM
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det

  have hslice : ∀ x ∈ zeroSet J', (∀ q ∈ J, eval x q = 0) ∧ eval x (linForm ℓ) = 1 := by
    intro x hx
    refine ⟨fun q hq => hx q (Ideal.mem_sup_left hq), ?_⟩
    have h1 := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [map_sub, map_one, sub_eq_zero] at h1
  have hval : ∀ k j y, y ∈ U k → s k j y ∈ zeroSet J' ∧ A *ᵥ s k j y = y := by
    intro k j y hy
    have hm : s k j y ∈ fibre J' A y := by rw [(hfib k y hy).1]; exact ⟨j, rfl⟩
    exact hm

  have hpt : ∀ (t : ℂ) (v : Fin n → ℂ), h.pointOf (t • WithLp.toLp 2 (M *ᵥ v)) = t • v := by
    intro t v
    simp only [HermNorm.pointOf]
    change h.matᵀ *ᵥ (t • (M *ᵥ v)) = t • v
    rw [mulVec_smul, mulVec_mulVec, hM, mul_nonsing_inv _ hdet, one_mulVec]
  refine ⟨U, D, N, s, hUD, hdisj, hnull, hfib, ?_, ?_, ?_⟩
  ·
    rintro ⟨⟨k, j⟩, y, t⟩ ⟨hy, ht⟩ ⟨⟨k', j'⟩, y', t'⟩ ⟨hy', ht'⟩ heq
    simp only at hy ht hy' ht' heq
    have hv := congrArg h.pointOf heq
    rw [hpt, hpt] at hv
    obtain ⟨hZ, hA1⟩ := hval k j y ((hUD k).2.2.1 hy)
    obtain ⟨hZ', hA1'⟩ := hval k' j' y' ((hUD k').2.2.1 hy')
    have hl := congrArg (fun x => eval x (linForm ℓ)) hv
    simp only [eval_linForm_smul, (hslice _ hZ).2, (hslice _ hZ').2, mul_one] at hl
    subst hl
    have hss : s k j y = s k' j' y' := smul_right_injective _ ht hv
    have hyy : y = y' := by rw [← hA1, ← hA1', hss]
    subst hyy
    have hkk : k = k' := by
      by_contra hk
      exact Set.disjoint_left.1 (hdisj hk) hy hy'
    subst hkk
    have hjj : j = j' := (hfib k y ((hUD k).2.2.1 hy)).2.1 hss
    subst hjj
    rfl
  ·
    rintro z ⟨⟨⟨k, j⟩, y, t⟩, ⟨hy, ht⟩, rfl⟩
    simp only at hy ht
    intro q hq
    rw [hpt]
    exact eval_smul_of_isHomogIdeal hJ.isHomog (hslice _ (hval k j y ((hUD k).2.2.1 hy)).1).1 t q hq
  ·
    obtain ⟨δ, G, hG, hGf⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ (pullback A P)
    have hGJ : G ∉ J := by
      intro hGm
      apply hP0
      have hm : pullback A P ∈ J' := by
        have e1 : pullback A P = G - (G - pullback A P) := by ring
        rw [e1]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left hGm) (Ideal.mem_sup_right hGf)
      apply hA.injective
      rw [map_zero]
      change (Ideal.Quotient.mkₐ ℂ J') (pullback A P) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    have hZ1 := NullSmaller.proof n (e + 1) (J ⊔ Ideal.span {linForm ℓ})
      (MassFinite.dim_sup_lt J hP hdim _ hℓ)
    have hZ2 := NullSmaller.proof n (e + 1) (J ⊔ Ideal.span {G})
      (MassFinite.dim_sup_lt J hP hdim _ hGJ)
    set F := fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
      q.2.2 • WithLp.toLp 2 (M *ᵥ s q.1.1 q.1.2 q.2.1) with hF
    let L := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
    have hsub : {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} \
        F '' {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
        L '' (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})) := by
      rintro z ⟨hzC, hzF⟩
      set p := h.pointOf z with hp
      have hzp : L (WithLp.toLp 2 p) = z := by
        change WithLp.toLp 2 (M *ᵥ (h.matᵀ *ᵥ WithLp.ofLp z)) = z
        rw [mulVec_mulVec, hM, nonsing_inv_mul _ hdet, one_mulVec]
      have hpJ : ∀ q ∈ J, eval p q = 0 := hzC
      refine ⟨WithLp.toLp 2 p, ?_, hzp⟩
      by_cases h0 : eval p (linForm ℓ) = 0
      · exact Or.inl (eval_sup_span hpJ h0)
      set c := eval p (linForm ℓ) with hc
      have hpx : p = c • (c⁻¹ • p) := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
      have hx : c⁻¹ • p ∈ zeroSet J' :=
        eval_sup_span (eval_smul_of_isHomogIdeal hJ.isHomog hpJ c⁻¹)
          (by rw [map_sub, map_one, eval_linForm_smul, ← hc, inv_mul_cancel₀ h0, sub_self])
      by_cases hyD : A *ᵥ (c⁻¹ • p) ∈ ⋃ k, D k
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.1 hyD
        have hxf : c⁻¹ • p ∈ fibre J' A (A *ᵥ (c⁻¹ • p)) := ⟨hx, rfl⟩
        rw [(hfib k _ ((hUD k).2.2.1 hk)).1] at hxf
        obtain ⟨j, hj⟩ := hxf
        apply hzF
        refine ⟨⟨⟨k, j⟩, A *ᵥ (c⁻¹ • p), c⟩, ⟨hk, h0⟩, ?_⟩
        rw [← hzp]
        simp only [hF, hj]
        change c • WithLp.toLp 2 (M *ᵥ (c⁻¹ • p)) = WithLp.toLp 2 (M *ᵥ p)
        rw [mulVec_smul, WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h0, one_smul]
      · have hPy : eval (A *ᵥ (c⁻¹ • p)) P = 0 := hbad hyD
        refine Or.inr (eval_sup_span hpJ ?_)
        have hGx : eval (c⁻¹ • p) G = eval (c⁻¹ • p) (pullback A P) := by
          have h2 := hx _ (Ideal.mem_sup_right hGf)
          rwa [map_sub, sub_eq_zero] at h2
        rw [hpx, eval_smul_of_isHomogeneous hG, hGx, MassFinite.eval_pullback, hPy, mul_zero]
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ zero_le
    calc Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          (L '' (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})))
        ≤ (‖L‖₊ : ENNReal) ^ (((2 * (e + 1) : ℕ) : ℝ)) *
            Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
              (zeroSetEuc (J ⊔ Ideal.span {linForm ℓ}) ∪ zeroSetEuc (J ⊔ Ideal.span {G})) :=
          L.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg _) _
      _ = 0 := by rw [measure_union_null hZ1 hZ2, mul_zero]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveGermComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace CurveGermComponents

variable {n : ℕ}

theorem mem_zeroSet_iff_le_ker (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    x ∈ zeroSet J ↔ J ≤ RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  simp only [zeroSet, Set.mem_ofPred_eq, SetLike.le_def, RingHom.mem_ker]

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ f ∈ J, {x : Fin n → ℂ | eval x f = 0} := by
    ext x
    simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem exists_minimalPrime_mem_zeroSet {I : Ideal (MvPolynomial (Fin n) ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ zeroSet I) : ∃ W ∈ I.minimalPrimes, x ∈ zeroSet W := by
  rw [mem_zeroSet_iff_le_ker] at hx
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hx
  exact ⟨W, hW, (mem_zeroSet_iff_le_ker W x).2 hle⟩

theorem ringKrullDim_curveLocalRing_le_zero {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hm : RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) ∈ I.minimalPrimes) :
    ringKrullDim (curveLocalRing I q) ≤ 0 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  let L := Localization.AtPrime m
  let J : Ideal L := I.map (algebraMap (MvPolynomial (Fin n) ℂ) L)
  change ringKrullDim (L ⧸ J) ≤ 0
  have hK : Ring.KrullDimLE 0 (L ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    set Q := p.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hP : (Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime := Ideal.comap_isPrime _ _
    have hIP : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
      rw [← Ideal.map_le_iff_le_comap]
      intro y hy
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
      exact p.zero_mem
    have hPm : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ m := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans
        (Localization.AtPrime.under_maximalIdeal (I := m)).le
    have hPeq : Q.under (MvPolynomial (Fin n) ℂ) = m := le_antisymm hPm (hm.2 ⟨hP, hIP⟩ hPm)
    have hQmax : Q = IsLocalRing.maximalIdeal L := Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1 hPeq
    have hQm : Q.IsMaximal := hQmax ▸ IsLocalRing.maximalIdeal.isMaximal L
    have h := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hQm
    rw [hQdef, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact h.resolve_left hp.ne_top
  exact_mod_cast Ring.krullDimLE_iff.1 hK

theorem ringKrullDim_localRingAt_eq_one {I W : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hW : W ∈ I.minimalPrimes) (hq : q ∈ zeroSet W) (hdim : ringKrullDim (curveLocalRing I q) = 1) :
    ringKrullDim (localRingAt W q) = 1 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  have hWm : W ≤ m := (mem_zeroSet_iff_le_ker W q).1 hq
  have hWp : W.IsPrime := hW.1.1
  let L := Localization.AtPrime m
  have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ W.map (algebraMap (MvPolynomial (Fin n) ℂ) L) :=
    Ideal.map_mono hW.1.2
  have hup : ringKrullDim (localRingAt W q) ≤ 1 := by
    rw [← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have disj : Disjoint (m.primeCompl : Set (MvPolynomial (Fin n) ℂ)) W := by
    rw [Set.disjoint_left]
    intro a ha haW
    exact ha (hWm haW)
  have hWL : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl L W hWp disj
  have hne : ¬ ringKrullDim (localRingAt W q) ≤ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (localRingAt W q) := Ring.krullDimLE_iff.2 (by exact_mod_cast h0)
    have : IsDomain (localRingAt W q) := Ideal.Quotient.isDomain _
    have hf : IsField (localRingAt W q) := Ring.KrullDimLE.isField_of_isDomain (R := localRingAt W q)
    have hmax : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hf
    have hWeq : W = m := by
      have h1 := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl L hWp disj
      rw [IsLocalRing.eq_maximalIdeal hmax, Localization.AtPrime.under_maximalIdeal] at h1
      exact h1.symm
    rw [hWeq] at hW
    have h2 := ringKrullDim_curveLocalRing_le_zero hW
    rw [hdim] at h2
    exact absurd h2 (by decide)
  exact le_antisymm hup (Order.succ_le_of_lt (lt_of_not_ge hne))

theorem exists_ringKrullDim_quotient_eq_nat (W : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime] :
    ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (e : ℕ) := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) :=
    (ringKrullDim_quotient_le W).trans (by simp)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d at h0 h1 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h0
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, WithBot.coe_le_coe] at h1
      exact absurd h1 (not_le.2 (ENat.natCast_lt_top n))
    | coe e => exact ⟨e, rfl⟩

theorem proof : CurveGermComponents.Statement := by
  intro n I q hdim
  classical
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  refine ⟨⋂ W ∈ {W ∈ I.minimalPrimes | q ∉ zeroSet W}, (zeroSet W)ᶜ, ?_, ?_⟩
  · exact (Filter.biInter_mem (hfin.subset (Set.sep_subset _ _))).2 fun W hW =>
      (isClosed_zeroSet W).isOpen_compl.mem_nhds hW.2
  · rintro x ⟨hxI, hxN⟩
    obtain ⟨W, hW, hxW⟩ := exists_minimalPrime_mem_zeroSet hxI
    have hqW : q ∈ zeroSet W := by
      by_contra hq
      exact Set.mem_iInter₂.1 hxN W ⟨hW, hq⟩ hxW
    refine ⟨W, hW, ?_, hqW, hxW⟩
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_nat W
    have h1 := LocalDimDomain.proof n e W hWp he q hqW
    rw [ringKrullDim_localRingAt_eq_one hW hqW hdim] at h1
    rw [he]
    exact_mod_cast h1.symm

end CurveGermComponents

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthLocalizedQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

theorem isNilpotent_of_minimalPrimes_eq_singleton {B : Type*} [CommRing B] [IsNoetherianRing B] {P : Ideal B}
    (hmin : minimalPrimes B = {P}) : IsNilpotent P := by
  have h : sInf (minimalPrimes B) = nilradical B := Ideal.sInf_minimalPrimes
  rw [hmin, sInf_singleton] at h
  rw [h]
  exact IsNoetherianRing.isNilpotent_nilradical B

theorem length_localizedModule_self {B : Type*} [CommRing B] (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) :=
  ((IsLocalizedModule.iso P.primeCompl (Algebra.linearMap B (Localization.AtPrime P))).extendScalarsOfIsLocalization
    P.primeCompl (Localization.AtPrime P)).length_eq

theorem LengthLocalizedQuotient.proof (hCut : LengthCutLocalizedModule.Statement.{u, u}) :
    LengthLocalizedQuotient.Statement.{u} := by
  intro B _ _ P _ y hmin hnzd hy Q _ hQ
  have h1 := hCut B P y (Q.comap (Ideal.Quotient.mk (Ideal.span {y}))) B
    (isNilpotent_of_minimalPrimes_eq_singleton hmin) hy hQ (fun s hs m h => by
      rw [smul_eq_mul] at h
      exact (mem_nonZeroDivisors_iff.1 (hnzd s hs)).1 m h)
  have h2 := NumbersDVR.LocalizedQuotLength.proof B (Ideal.span {y}) Q 0
  have hE : (Ideal.span {y} • ⊤ : Submodule B B) = Ideal.span {y} ⊔ Ideal.span {(0 : B)} := by
    rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq, smul_eq_mul, Ideal.mul_top]
  rw [hE, h2, length_localizedModule_self] at h1
  rw [← h1]
  have hb : Ideal.span {algebraMap (B ⧸ Ideal.span {y}) (Localization.AtPrime Q) (Ideal.Quotient.mk _ 0)} = ⊥ := by
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot]
  exact ((Submodule.quotEquivOfEqBot _ hb).length_eq).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PModelLocalizationMaximalPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem ModelLocalizationMaximalPoint.proof : ModelLocalizationMaximalPoint.Statement := by
  intro n J q M P hP
  let A := MvPolynomial (Fin n) ℂ
  let R' := MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal
  let L := Localization (normalModelSubmonoid M q)
  let ι : A →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
  let φ : A →+* R' := (Ideal.Quotient.mk M.ideal).comp ι
  let _ : Algebra A R' := φ.toAlgebra
  have hφ : ∀ f : A, algebraMap A R' f = Ideal.Quotient.mk M.ideal (rename Sum.inl f) := fun _ ↦ rfl

  have hint : Algebra.IsIntegral A R' := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h : algebraMap A R' (C c) = Ideal.Quotient.mk M.ideal (C c) := by rw [hφ, rename_C]
      exact h ▸ isIntegral_algebraMap
    | add p r hp hr => rw [map_add (f := _)]; exact hp.add hr
    | mul_X p s hp =>
      rw [map_mul]
      refine hp.mul ?_
      cases s with
      | inl i =>
        have h : algebraMap A R' (X i) = Ideal.Quotient.mk M.ideal (X (Sum.inl i)) := by rw [hφ, rename_X]
        exact h ▸ isIntegral_algebraMap
      | inr i =>
        obtain ⟨F, hmon, hF⟩ := M.integral i
        refine ⟨F, hmon, ?_⟩
        rw [RingHom.algebraMap_toAlgebra, show φ = (Ideal.Quotient.mk M.ideal).comp ι from rfl,
          ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hF

  let m : Ideal A := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, eval_C c⟩
  let Q : Ideal R' := P.comap (algebraMap R' L)
  have hQm : Q.comap (algebraMap A R') ≤ m := by
    intro f hf
    by_contra hfm
    have hS : algebraMap A R' f ∈ normalModelSubmonoid M q := Submonoid.mem_map_of_mem _ hfm
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (IsLocalization.map_units L ⟨_, hS⟩))

  obtain ⟨Q', hQQ', hQ'prime, hQ'm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m Q hQm
  have hdisj : Disjoint (normalModelSubmonoid M q : Set R') Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨f, hf, rfl⟩ hfQ
    apply hf
    have h : f ∈ Q'.comap (algebraMap A R') := hfQ
    change f ∈ Ideal.under A Q' at h
    rw [hQ'm] at h
    exact h
  have hPQ' : P = Q'.map (algebraMap R' L) := by
    have hne : Q'.map (algebraMap R' L) ≠ ⊤ :=
      (IsLocalization.isPrime_of_isPrime_disjoint (normalModelSubmonoid M q) L Q' hQ'prime hdisj).ne_top
    refine hP.eq_of_le hne ?_
    rw [← IsLocalization.map_under (normalModelSubmonoid M q) L P]
    exact Ideal.map_mono hQQ'
  have hQeq : P.comap (algebraMap R' L) = Q' := by
    rw [hPQ']
    exact IsLocalization.under_map_of_isPrime_disjoint (normalModelSubmonoid M q) L hQ'prime hdisj
  have hQ'max : Q'.IsMaximal := by
    letI : Q'.IsPrime := hQ'prime
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under Q' (hQ'm ▸ hm)

  let N := P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))
  have hNmax : N.IsMaximal := by
    show (P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))).IsMaximal
    rw [← Ideal.comap_comap, hQeq]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hNmax
  have key : ∀ p, p ∈ N ↔ eval w p = 0 := fun p ↦ by
    rw [hw, mem_vanishingIdeal_singleton_iff]
    exact Iff.rfl
  refine ⟨w, fun p hp ↦ (key p).1 ?_, ?_, ?_⟩
  · show algebraMap R' L (Ideal.Quotient.mk M.ideal p) ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    exact P.zero_mem
  · funext i
    have h1 : X i - C (q i) ∈ m := by
      show eval q (X i - C (q i)) = 0
      rw [map_sub, eval_X, eval_C, sub_self]
    rw [← hQ'm, ← hQeq] at h1
    have h2 := (key (rename Sum.inl (X i - C (q i)))).1 h1
    simp only [map_sub, rename_X, rename_C, eval_X, eval_C] at h2
    exact sub_eq_zero.1 h2
  · ext p
    rw [RingHom.mem_ker]
    exact key p

end

end GroundTheory.Heights₂.Heights
end

