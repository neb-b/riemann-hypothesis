module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionHorizontal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isHorizontal_imageZ {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (h : IsHorizontal W') :
    IsHorizontal (imageZ v W') := by
  have h' : W'.comap (C : ℤ →+* MRing ι') = ⊥ := h
  show (imageZ v W').comap (C : ℤ →+* MRing ι) = ⊥
  rw [← h']
  ext c
  simp [imageZ, Ideal.mem_comap]

theorem dim_eq {P : Ideal (MRing ι)} {d d' : ℕ} (h : IsArithVar P d) (h' : IsArithVar P d') : d = d' := by
  have e := h.2.2.2.symm.trans h'.2.2.2
  have e2 : d + Fintype.card K = d' + Fintype.card K := by exact_mod_cast e
  omega

theorem dim_add_one_le {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isRelevant_of_le {Y Z : Ideal (MRing ι)} (hZ : IsRelevant Z) (hY : Y ≤ Z) : IsRelevant Y :=
  fun k => let ⟨i, hi⟩ := hZ k; ⟨i, fun h => hi (hY h)⟩

theorem mem_minimalPrimes {J Q : Ideal (MRing ι)} {n : ℕ} (hQ : IsArithVar Q n) (hJQ : J ≤ Q)
    (hdim : ∀ M ∈ J.minimalPrimes, IsRelevant M → IsHorizontal M → IsArithVar M n) :
    Q ∈ J.minimalPrimes := by
  have hQp : Q.IsPrime := hQ.2.1.1
  refine ⟨⟨hQp, hJQ⟩, fun q hq hqQ => ?_⟩
  have : q.IsPrime := hq.1
  obtain ⟨M, hM, hMq⟩ := Ideal.exists_minimalPrimes_le hq.2
  have hMQ : M ≤ Q := hMq.trans hqQ
  have hQh : Q.comap (C : ℤ →+* MRing ι) = ⊥ := hQ.2.2.1
  have hMh : IsHorizontal M := by
    show M.comap (C : ℤ →+* MRing ι) = ⊥
    rw [eq_bot_iff, ← hQh]
    exact Ideal.comap_mono hMQ
  have hMn := hdim M hM (isRelevant_of_le hQ.2.1.2.2 hMQ) hMh
  have : M.IsPrime := hM.1.1
  refine le_trans ?_ hMq
  by_contra hQM
  obtain ⟨x, hxQ, hxM⟩ := Set.not_subset.1 hQM
  have h := dim_add_one_le hMQ hxQ hxM
  rw [hQ.2.2.2, hMn.2.2.2] at h
  have h2 : n + Fintype.card K + 1 ≤ n + Fintype.card K := by exact_mod_cast h
  omega


open Classical in
theorem sum_block (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {s : MRing ι} {α : K → ℕ} (hs : IsMultiHomog s α) :
    IsMultiHomog (rename v s) (Function.extend κ α 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  rw [sum_block]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then α k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hs m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

end ArithmeticIntersectionHorizontal


open ArithmeticIntersectionHorizontal in
theorem ArithmeticIntersectionHorizontal.proof (hDiv : DivSuppArithStatement) (hIm : ImageArithStatement)
    (hP0 : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement) : ArithmeticIntersectionHorizontal.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh
  classical

  let A : HermLine ι := HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) (fun k => (α k : ℤ))
  let A' : HermLine ι' :=
    HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι' k)) (fun k => ((Function.extend κ α 0 : K' → ℕ) k : ℤ))
  have hsec : IsSectionOn (imageZ v P') A s := ⟨α, fun _ => rfl, hs, hsP⟩
  have hsec' : IsSectionOn P' A' (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, fun h => hsP (Ideal.mem_comap.mpr h)⟩
  have hW'n : IsArithVar W' n := (hDiv K' ι' P' n A' (rename v s) W' hP' hsec' hW').1 hh
  have hhQ : IsHorizontal (imageZ v W') := isHorizontal_imageZ hh
  obtain ⟨d, hdn, hQd⟩ := hIm K ι K' ι' κ v W' n hP.1 hv hW'n
  rcases hdn.lt_or_eq with hlt | heq
  ·
    right
    refine ⟨fun hm => ?_, hP0 I hI K ι K' ι' κ v W' d n L L' hv hW'n hQd hlt hL hLL'⟩
    have := dim_eq hQd ((hDiv K ι (imageZ v P') n A s _ hP hsec hm).1 hhQ)
    omega
  ·
    left
    rw [heq] at hQd
    have hle := hW'.1.1.2
    have hm : imageZ v W' ∈ divSupp (imageZ v P') s := by
      refine ⟨mem_minimalPrimes hQd ?_ fun M hM hMr hMh => (hDiv K ι (imageZ v P') n A s M hP hsec ⟨hM, hMr⟩).1 hMh,
        hQd.2.1.2.2⟩
      refine sup_le (Ideal.comap_mono (le_sup_left.trans hle)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨hm, fun G' J' hJ' => hn K ι K' ι' κ v W' G' J' L L' hv hW'n hQd hJ' hL hLL'⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_congr_pts (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact hg _ hγ.choose_spec.2.self_of_nhds.2.1
    · rfl
  · rfl

theorem cycR_sub_vertR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) [DecidablePred (IsHorizontal (ι := ι))] :
    cycR I P L s - vertR P L s = ∑ W ∈ (divSupp_finite P s).toFinset.filter IsHorizontal,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L := by
  unfold cycR vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  split_ifs <;> ring

theorem tensor_sqMetric_a {A : HermLine ι} {α β : K → ℕ} (h : ∀ k, (α k : ℤ) - β k = A.a k) (k : K) :
    (A.tensor (HermLine.sqMetric β)).a k = α k := by
  show A.a k + (β k : ℤ) = α k
  rw [← h k]
  ring

theorem Conservation.proof : Conservation.Statement := Conservation.statement_holds

theorem InductiveIntersectionFormula.proof : InductiveIntersectionFormula.Statement := by
  classical
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ hhor hmult hnorm
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hRf := hR P n L _ f α hP hL (isSmoothHerm_tensor hA hB) (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L = arInt P g (HermLine.sqMetric β) L := by
    unfold arInt
    refine ptsIntegral_congr_pts P _ fun z hz ↦ ?_
    have hApos := A.pos z hz.1
    show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z)
    rw [hnorm z hz, mul_comm (A.h z), mul_div_mul_right _ _ hApos.ne']
  have hS : (divSupp_finite P f).toFinset.filter IsHorizontal =
      (divSupp_finite P g).toFinset.filter IsHorizontal := by
    ext W
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h ↦ ⟨(hhor W h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hhor W h.2).2 h.1, h.2⟩⟩
  have hcyc : cycR I P L f - vertR P L f = cycR I P L g - vertR P L g := by
    rw [cycR_sub_vertR, cycR_sub_vertR, hS]
    refine Finset.sum_congr rfl fun W hW ↦ ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    rw [hmult W hW.2 ((hhor W hW.2).2 hW.1)]
  rw [recR_eq] at hRf hRg
  linarith

theorem ae_eval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {h} : Ideal (MRing ι)) :=
    ⟨{h}, fun f hf ↦ by rw [Set.mem_singleton_iff.mp hf]; exact hh, rfl⟩
  have hJP : ¬ (Ideal.span {h} : Ideal (MRing ι)) ≤ P := by
    rwa [Ideal.span_singleton_le_iff_mem]
  have hnull := projB_null Ψ hP hΨ hJ hJP
  refine ae_iff.mpr (measure_mono_null (fun y hy ↦ ?_) hnull)
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hy
  obtain ⟨z, hz, hzy, hz0⟩ := hy
  refine ⟨z, hz, ⟨hz.1, fun q hq ↦ ?_⟩, hzy⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  simp [hz0]

theorem RatR.proof (hInt : PtsIntegrableStatement) : RatR.Statement := by
  intro K _ ι _ I hI P n L A f g hP hL hA ⟨α, β, hf, hg, hfP, hgP, hαβ⟩
  obtain ⟨-, hAdd, hR⟩ := hI
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := isSmoothHerm_tensor hA hB
  have hRf := hR P n L _ f α hP hL hAB (tensor_sqMetric_a hαβ) hf hfP
  have hRg := hR P n L _ g β hP hL hB (fun k ↦ rfl) hg hgP
  have hsum := hAdd P n L A _ hP hL hA hB
  have hint : arInt P f (A.tensor (HermLine.sqMetric β)) L - arInt P g (HermLine.sqMetric β) L =
      ptsIntegral P (pot L) (logNormRat A f g) := by
    show ptsIntegral P (pot L) _ - ptsIntegral P (pot L) _ = _
    unfold ptsIntegral
    split_ifs with hΨ
    · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
      unfold ptsIntegralAt
      rw [← integral_sub (hInt K ι P n _ L _ f hP hΨg hL hAB ⟨α, tensor_sqMetric_a hαβ, hf, hfP⟩)
        (hInt K ι P n _ L _ g hP hΨg hL hB ⟨β, fun k ↦ rfl, hg, hgP⟩)]
      refine integral_congr_ae ?_
      filter_upwards [ae_eval_ne_zero hP hΨg ⟨α, hf⟩ hfP, ae_eval_ne_zero hP hΨg ⟨β, hg⟩ hgP]
        with y hyf hyg
      rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P n _ hP hΨg y)]
      refine finsum_mem_congr rfl fun w _ ↦ ?_
      unfold sheetDensity
      split_ifs with hγ
      · have hs := hγ.choose_spec.2.self_of_nhds
        set z := hγ.choose y
        have hz : z ∈ mcPts P := hs.2.1
        have hf0 := norm_pos_iff.mpr (hyf z hz hs.2.2)
        have hg0 := norm_pos_iff.mpr (hyg z hz hs.2.2)
        have hA0 := A.pos z hz.1
        have hB0 := (HermLine.sqMetric (ι := ι) β).pos z hz.1
        rw [← sub_mul]
        congr 1
        show Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * (HermLine.sqMetric β).h z)) -
          Real.log (‖eval z (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h z) =
          Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
        rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
          Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
          Real.log_div hf0.ne' hg0.ne']
        ring
      · simp
    · simp
  unfold recRRat
  rw [recR_eq] at hRf hRg
  show I P (n + 1) (Fin.snoc L A) = cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)
  rw [← hint]
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ProjectionFormulaVertical

open PointVertical

theorem geoNum_mixed_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d r : ℕ}
    (hP : IsArithVar (imageZ v P') d) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((d + r + Fintype.card K' : ℕ) : WithBot ℕ∞))
    (L : Fin d → K → ℤ) (N : Fin r → K' → ℤ) :
    geoNum (d + r) W (Fin.append (fun j => pullDeg κ (L j)) N) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) (d + r) :=
    ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  obtain ⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩ := hP
  have := hQp
  have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
  have hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P' := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact h
    rw [hQh, Ideal.mem_bot] at h2
    exact hpr.ne_zero (by exact_mod_cast h2)
  have hdim := krullDim_quot_add_one_le hle hpI hpQ
  rw [← ringKrullDim_red p hpI, hD, hQd] at hdim
  have hD' : D + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K' ι'
  rw [hGeo K' ι' p I hI W (d + r) _ hWm hpW hWp]
  unfold ContractMixedFieldStatement at hCMF
  exact hCMF (ZMod p) K ι K' ι' I hI κ v _ (D - Fintype.card K) d r L N hv hWp hVi (by omega)

end ProjectionFormulaVertical


open ProjectionFormulaVertical in
theorem PFVert.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCMF : ContractMixedFieldStatement) :
    PFVert.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N s a W hv hP' hP hL hs hsP hW hh
  classical
  have hsec : IsSectionOn P' (HermLine.sqMetric (ι := ι') a) s := ⟨a, fun _ => rfl, hs, hsP⟩
  obtain ⟨hWm, hpr, hWd⟩ :=
    (divSuppArith K' ι' P' (d + r) (HermLine.sqMetric (ι := ι') a) s W hP' hsec hW).2 hh
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  have e : (fun j => (Fin.append L' N j).a) =
      Fin.append (fun j => pullDeg κ (L j).a) (fun j => (N j).a) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [(hL i).1]
    · simp
  rw [e]
  exact geoNum_mixed_eq_zero hGeo hR4 hCMF hv hP hPW hWm hpr hWd _ _

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsMonoSemiPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsMonoSemiPos.proof (hInt : PtsIntegrableStatement) (hHess : SheetHessPSD.Statement) :
    PtsMonoSemiPos.Statement := by
  intro K _ ι _ Q e M E D t hQ hMs hMp hE ht hD hDa hle
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · rw [dite_eq_right hΨ, dite_eq_right hΨ]
  rw [dite_eq_left hΨ, dite_eq_left hΨ]
  set Ψ := hΨ.choose with hΨdef
  have hΨg : IsGoodProj Q Ψ := hΨ.choose_spec
  unfold ptsIntegralAt
  have hD1 : IsSectionOn Q D 1 := by
    refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
      fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have key : ∀ y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm D 1) y w := by
    intro y w
    unfold sheetDensity
    split_ifs <;> simp [logNorm, Real.log_inv]
  have h1 := hInt K ι Q e Ψ M E t hQ hΨg hMs hE ht
  have h2 : Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w) := by
    simp only [key, finsum_neg_distrib]
    exact (hInt K ι Q e Ψ M D 1 hQ hΨg hMs hD hD1).neg
  obtain ⟨a, -, hta, htQ⟩ := ht
  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJQ : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ hQ hΨg hJ hJQ
  refine integral_mono_ae h1 h2 ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι Q e Ψ hQ hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · rw [dite_eq_left hγ, dite_eq_left hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have ht0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) ≠ 0 := by
      intro h0
      refine hyB ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [map_mul, map_mul, h0, mul_zero]
    have hma : 0 ≤ maDensity (fun j y' => pot M j (hγ.choose y')) y :=
      ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j =>
        hHess K ι Q e Ψ (M j) y w hγ.choose (hMs j) (hMp j) hγ.choose_spec
    exact mul_le_mul_of_nonneg_right (hle _ hmem ht0) hma
  · rw [dite_eq_right hγ, dite_eq_right hγ]

end GroundTheory.Heights₂.Heights.Inter
end
end

