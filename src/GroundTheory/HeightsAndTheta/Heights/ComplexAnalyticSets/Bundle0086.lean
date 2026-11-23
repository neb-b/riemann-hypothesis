module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSheetGramLintegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set ComplexSets

open scoped ENNReal

noncomputable section

theorem IsSheetAt.eventuallyEq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {γ s : (Fin d → ℂ) → Fin n → ℂ}
    (hγ : IsSheetAt J A x γ) (hs : IsSheetAt J A x s) : γ =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, hγd, hγx, hγZ, -⟩ := hγ
  obtain ⟨U', hU', hxU', -, -, -, V, hV, hsV⟩ := hs
  have hc : ContinuousAt γ (A *ᵥ x) := (hγd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (A *ᵥ x), γ y ∈ V := hc.preimage_mem_nhds (by rwa [hγx])
  filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU', hV'] with y hy hy' hyV
  obtain ⟨hAy, hZy⟩ := hγZ y hy
  have h := hsV (γ y) ⟨hZy, hyV⟩ (by rwa [hAy])
  rwa [hAy] at h

theorem ConeSheetGramLintegral.proof (hPar : ConeSliceSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetGramLintegral.Statement := by
  classical
  intro n e h J ℓ A F hJ hdim hℓ hA hF
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hinj, hsub, hcov⟩ := hPar n e h J ℓ A hJ hdim hℓ hA

  set v : (Σ k, Fin (N k)) → (Fin e → ℂ) → (Fin n → ℂ) :=
    fun i y => (h.matᵀ)⁻¹ *ᵥ s i.1 i.2 y with hv_def
  have hvd : ∀ i : Σ k, Fin (N k), DifferentiableOn ℂ (v i) (U i.1) := fun i =>
    (Matrix.mulVecLin (h.matᵀ)⁻¹).toContinuousLinearMap.differentiable.comp_differentiableOn
      ((hUD i.1).2.2.2 i.2)

  set H : (Σ k, Fin (N k)) → (Fin e → ℂ) → ℝ≥0∞ := fun i y =>
    ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i y)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) y)
    with hH_def
  have hHm : ∀ i : Σ k, Fin (N k), AEMeasurable (H i) (volume.restrict (D i.1)) := fun i =>
    aemeasurable_coneTerm (hUD i.1).1 (hUD i.1).2.2.1 (hvd i) hF

  set G : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
          (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y) with hG_def

  have hGD : ∀ k, ∀ y ∈ D k, G y = ∑ j : Fin (N k), H ⟨k, j⟩ y := by
    intro k y hy
    obtain ⟨hfe, hinjy, hsh⟩ := hfib k y ((hUD k).2.2.1 hy)
    simp only [hG_def, hfe]
    rw [finsum_mem_range hinjy, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hAy : A *ᵥ s k j y = y := by
      have hmem : s k j y ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y := hfe ▸ ⟨j, rfl⟩
      exact hmem.2
    have hex : ∃ γ, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) γ := ⟨s k j, hsh j⟩
    have hch : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) =ᶠ[𝓝 y] s k j := by
      have h1 : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) = hex.choose := by
        simp only [sheetThrough, dif_pos hex]
      have h2 := hex.choose_spec.eventuallyEq (hsh j)
      rw [hAy] at h2
      rw [h1]
      exact h2
    have hval : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y = s k j y :=
      hch.eq_of_nhds
    have hgram : gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y') y =
        gramVol (v ⟨k, j⟩) y :=
      gramVol_congr (hch.fun_comp fun f => (h.matᵀ)⁻¹ *ᵥ f)
    simp only [hH_def, hv_def, hval, hgram]

  set G' : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑' k, (D k).indicator (fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) y with hG'_def
  have hGG' : G =ᵐ[volume] G' := by
    have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ ⋃ k, D k := by
      rw [ae_iff]
      simpa [compl_def] using hnull
    filter_upwards [hae] with y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    simp only [hG'_def]
    rw [tsum_eq_single k, indicator_of_mem hk, hGD k y hk]
    intro k' hk'
    exact indicator_of_notMem (fun h' => (hdisj hk').le_bot ⟨h', hk⟩) _
  have hG'm : ∀ k, AEMeasurable ((D k).indicator fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) volume :=
    fun k => (aemeasurable_indicator_iff (hUD k).2.1).2
      (Finset.aemeasurable_fun_sum _ fun j _ => hHm ⟨k, j⟩)
  refine ⟨(AEMeasurable.tsum hG'm).congr hGG'.symm, ?_⟩

  have hRHS : ∫⁻ y, G y = ∑' i : Σ k, Fin (N k), ∫⁻ y in D i.1, H i y := by
    rw [lintegral_congr_ae hGG', lintegral_tsum hG'm, ENNReal.tsum_sigma']
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator (hUD k).2.1, lintegral_finsetSum' _ fun j _ => hHm ⟨k, j⟩,
      tsum_fintype]

  have hLHS : ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫⁻ z in (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    refine setLIntegral_congr (ae_eq_set.2 ⟨hcov, ?_⟩)
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  have hMap := hArea n e (Σ k, Fin (N k)) (fun i => U i.1) (fun i => D i.1) v F
    (fun i => ⟨(hUD i.1).1, (hUD i.1).2.1, (hUD i.1).2.2.1, hvd i⟩) hinj hF
  rw [hLHS, hMap]
  exact congrArg _ hRHS.symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveBranchLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem localMult_ker_eval_eq_zero {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∈ J) (hgq : eval q g ≠ 0) :
    localMult J (RingHom.ker (eval q)) = 0 := by
  have htop : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))
  have hs := Ideal.Quotient.subsingleton_iff.2 htop
  rw [localMult, dite_eq_left (isPrime_ker_eval q), Module.length_eq_zero_iff.2 hs]
  rfl

theorem CurveBranchLength.proof (hN : CurveNormalisationLength.Statement)
    (hB : BranchNormalisation.Statement) : CurveBranchLength.Statement := by
  intro n I u q m c ord hrad hcov hdisj hord
  have hlin : ∀ x, eval x (linForm u) = linEval u x := fun x ↦ by simp [linForm, linEval]
  have hq0 : ∀ b, linEval u q = 0 ↔ 0 < ord b := by
    intro b
    obtain ⟨H, -, hH, hF⟩ := hord b
    have h0 := hF 0 (Metric.mem_ball_self (c b).radius_pos)
    simp only [(c b).map_zero] at h0
    rw [h0]
    simp [hH 0 (Metric.mem_ball_self (c b).radius_pos), Nat.pos_iff_ne_zero]
  by_cases hmain : linEval u q = 0 ∧ 0 < m
  swap
  · have hsum : ∑ b, ord b = 0 := Finset.sum_eq_zero fun b _ ↦ by
      by_contra hb
      exact hmain ⟨(hq0 b).2 (Nat.pos_of_ne_zero hb), Fin.pos_iff_nonempty.2 ⟨b⟩⟩
    rw [hsum]
    by_cases hu : linEval u q = 0
    · have hm : m = 0 := by by_contra hm; exact hmain ⟨hu, Nat.pos_of_ne_zero hm⟩
      subst hm
      obtain ⟨N, hNq, hsub⟩ := hcov
      have hq : q ∉ zeroSet I := fun hq ↦ by simpa using hsub ⟨hq, mem_of_mem_nhds hNq⟩
      obtain ⟨g, hg, hgq⟩ : ∃ g ∈ I, eval q g ≠ 0 := by
        by_contra h
        push Not at h
        exact hq h
      exact localMult_ker_eval_eq_zero (Ideal.mem_sup_left hg) hgq
    · exact localMult_ker_eval_eq_zero (Ideal.mem_sup_right (Ideal.subset_span rfl)) (by rwa [hlin])
  obtain ⟨hu0, hm⟩ := hmain
  have hpt : ∀ b, ∀ x ∈ (c b).image, linEval u x = 0 → x = q := by
    rintro b _ ⟨t, ht, rfl⟩ hx
    obtain ⟨H, -, hH, hF⟩ := hord b
    rw [show linEval u ((c b).toFun t) = t 0 ^ ord b * H t from hF t ht, mul_eq_zero] at hx
    have ht0 : t 0 = 0 := hx.elim eq_zero_of_pow_eq_zero fun h ↦ absurd h (hH t ht)
    have ht' : t = 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]; exact ht0
    rw [ht', (c b).map_zero]
  obtain ⟨hdim, hnzd, e, he⟩ := hB n I q m c hrad hm hcov
    fun b b' hbb x hx ↦ hpt b x hx.1 (hdisj b b' hbb hx)
  have hordb : ∀ b, branchOrder (c b) (linForm u) = ord b := fun b ↦
    branchOrder_eq_of_vanishesToOrder (c b) _ _ (by simpa only [hlin] using hord b)
  have hL := hN n I q (linForm u) hrad hdim (hnzd _ fun b ↦ by rw [hordb b]; exact ENat.natCast_ne_top _)
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype] at hL
  simp only [(he _).1, mul_one, (he _).2, hordb] at hL
  exact_mod_cast hL

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveMinimalPrimeQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveMinimalPrimeQuotient.proof : CurveMinimalPrimeQuotient.Statement := by
  intro n I q p hp
  have hpP : p.IsPrime := hp.1.1

  let ext : Ideal (MvPolynomial (Fin n) ℂ) → Ideal (Localization.AtPrime (RingHom.ker (eval q))) :=
    fun K ↦ K.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  let mk := Ideal.Quotient.mk (ext I)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomp : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) =
      mk.comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) := rfl

  let P : Ideal (Localization.AtPrime (RingHom.ker (eval q))) := p.comap mk
  have hPP : P.IsPrime := Ideal.comap_isPrime mk p
  have hIP : ext I ≤ P := fun x hx ↦ by
    change mk x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact p.zero_mem
  have hpmap : P.map mk = p := Ideal.map_comap_of_surjective mk hmk p
  let J : Ideal (MvPolynomial (Fin n) ℂ) :=
    P.comap (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  have hJP : J.IsPrime := Ideal.comap_isPrime _ P
  have hJmem : ∀ f, f ∈ J ↔ algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ p := fun f ↦ by
    rw [hcomp]; rfl
  have hextJ : ext J = P := IsLocalization.map_under (RingHom.ker (eval q)).primeCompl _ P
  have hIJ : I ≤ J := fun f hf ↦ hIP (Ideal.mem_map_of_mem _ hf)
  have hJm : J ≤ RingHom.ker (eval q) := by
    intro f hf
    by_contra h
    exact hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ ((hJmem f).1 hf)
      (isUnit_algebraMap_curveLocalRing I q f fun h' ↦ h (RingHom.mem_ker.2 h')))

  have hJmin : J ∈ I.minimalPrimes := by
    refine ⟨⟨hJP, hIJ⟩, fun J' hJ' hJ'J ↦ ?_⟩
    obtain ⟨hJ'P, hIJ'⟩ := hJ'
    have hdisj : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J' :=
      Set.disjoint_left.2 fun x hx hx' ↦ hx (hJm (hJ'J hx'))
    have hP'P : (ext J').IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J' hJ'P hdisj
    have hIP' : ext I ≤ ext J' := Ideal.map_mono hIJ'
    have hker : RingHom.ker mk ≤ ext J' := by
      rw [Ideal.mk_ker]; exact hIP'
    have hp'P : ((ext J').map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk hker
    have hp'le : (ext J').map mk ≤ p := by
      rw [← hpmap, ← hextJ]
      exact Ideal.map_mono (Ideal.map_mono hJ'J)
    have hpp' : p ≤ (ext J').map mk := hp.2 ⟨hp'P, bot_le⟩ hp'le
    intro f hf
    have h1 : mk (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) ∈ (ext J').map mk :=
      hpp' ((hJmem f).1 hf)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective mk hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIP'] at h1
    have h2 := (IsLocalization.under_map_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl
      (Localization.AtPrime (RingHom.ker (eval q))) hJ'P hdisj)
    rw [← h2]
    exact h1

  have hle : ext I ≤ ext J := Ideal.map_mono hIJ
  refine ⟨J, hJmin, hJm, (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q),
    Ideal.Quotient.factor_surjective hle, ?_, fun f ↦ Ideal.Quotient.factor_mk hle _⟩
  change RingHom.ker (Ideal.Quotient.factor hle) = p
  rw [Ideal.Quotient.factor_ker, hextJ]
  exact hpmap

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveNormalisationLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem length_quotient_sup_span {L : Type} [CommRing L] (J : Ideal L) (g : L) :
    Module.length L (L ⧸ (J ⊔ Ideal.span {g})) =
      Module.length (L ⧸ J) ((L ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J g}) := by
  have hK : (Ideal.span {g}).map (Ideal.Quotient.mkₐ L J) = Ideal.span {Ideal.Quotient.mk J g} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← (DoubleQuot.quotQuotEquivQuotSupₐ L J (Ideal.span {g})).toLinearEquiv.length_eq, hK]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem length_localization_eq_length_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    Module.length (Localization.AtPrime (RingHom.ker (eval q)))
        (Localization.AtPrime (RingHom.ker (eval q)) ⧸ (I ⊔ Ideal.span {f}).map
          (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))) =
      Module.length (curveLocalRing I q)
        (curveLocalRing I q ⧸ Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f}) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact length_quotient_sup_span _ _

theorem length_quotient_ne_top {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hdim : ringKrullDim O = 1) {x : O} (hx : x ∈ nonZeroDivisors O) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  by_cases hm : x ∈ IsLocalRing.maximalIdeal O
  · have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hx hm
    rw [hdim] at h
    have h0 : ringKrullDim (O ⧸ Ideal.span {x}) ≤ (0 : ℕ) := by
      generalize ringKrullDim (O ⧸ Ideal.span {x}) = d at h ⊢
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe k =>
        have h' : k + 1 = 1 := by exact_mod_cast h
        induction k using ENat.recTopCoe with
        | top => simp at h'
        | coe m =>
          have hm : m + 1 = 1 := by exact_mod_cast h'
          have : m = 0 := by omega
          subst this
          simp
    have : Ring.KrullDimLE 0 (O ⧸ Ideal.span {x}) := Ring.krullDimLE_iff.2 h0
    have := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := O ⧸ Ideal.span {x})
    rw [Module.length_eq_of_surjective (R := O ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective]
    exact Module.length_ne_top
  · have hu : IsUnit x := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hm
    rw [Ideal.span_singleton_eq_top.2 hu,
      Module.length_eq_zero_iff.2 (Ideal.Quotient.subsingleton_iff.2 rfl)]
    exact ENat.zero_ne_top

theorem CurveNormalisationLength.proof (hFin : CurveNormalisationFinite.Statement)
    (hQ : CurveNormalisationQuotientLength.Statement) (hE : ExtensionQuotientLength.Statement) :
    CurveNormalisationLength.Statement := by
  intro n I q f hrad hdim hf
  set O := curveLocalRing I q
  set f' := algebraMap (MvPolynomial (Fin n) ℂ) O f
  have : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing O := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Module.Finite O (curveNormalisation I q) := hFin n I q hrad
  have hfin := length_quotient_ne_top hdim hf

  have hnzd : algebraMap O (curveNormalisation I q) f' ∈ nonZeroDivisors (curveNormalisation I q) := by
    let ι : curveNormalisation I q →+* FractionRing O :=
      (integralClosure O (FractionRing O)).val.toRingHom
    refine mem_nonZeroDivisors_of_injective (f := ι) Subtype.val_injective ?_
    exact (IsLocalization.map_units (FractionRing O) (⟨f', hf⟩ : nonZeroDivisors O)).mem_nonZeroDivisors
  have hEq := hE O (curveNormalisation I q) f' (algebraMap_curveNormalisation_injective I q) hnzd
    (hQ n I q hrad hdim)
  rw [localMult, dite_eq_left (isPrime_ker_eval q), length_localization_eq_length_curveLocalRing,
    ENat.natCast_toNat hfin, hEq]
  exact GroundTheory.Heights₂.Heights.Vertical.LengthDecomp.proof O (curveNormalisation I q) _ (hEq ▸ hfin)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveNormalisationQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem withBot_enat_le_zero_of_add_one_le_one {x : WithBot ℕ∞} (h : x + 1 ≤ 1) : x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    have : e ≤ 0 := by
      induction e using ENat.recTopCoe with
      | top => simp at h'
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h'
        exact_mod_cast (show k ≤ 0 by omega)
    exact_mod_cast this

theorem CurveNormalisationQuotientLength.proof (hF : CurveNormalisationFinite.Statement) :
    CurveNormalisationQuotientLength.Statement := by
  intro n I q hrad hdim
  set O := curveLocalRing I q
  set N := curveNormalisation I q
  set M := N ⧸ LinearMap.range (Algebra.linearMap O N)
  have hfin : Module.Finite O N := hF n I q hrad

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := N)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s
    (fun x : N ↦ ((show ↥(integralClosure O (FractionRing O)) from x) : FractionRing O))
  have hmul : ∀ y : N, (b : O) • y ∈ LinearMap.range (Algebra.linearMap O N) := by
    intro y
    have hle : Submodule.span O (s : Set N) ≤
        (LinearMap.range (Algebra.linearMap O N)).comap ((b : O) • LinearMap.id) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨a, ha⟩ := hb x hx
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
    exact hle (hs ▸ Submodule.mem_top : y ∈ Submodule.span O (s : Set N))
  have hann : (b : O) ∈ Module.annihilator O M := by
    rw [Module.mem_annihilator]
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H y => rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hmul y

  have hd := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (Module.annihilator O M))
    Ideal.Quotient.mk_surjective b.2 (Ideal.Quotient.eq_zero_iff_mem.2 hann)
  rw [hdim] at hd
  have : Ring.KrullDimLE 0 (O ⧸ Module.annihilator O M) :=
    Ring.krullDimLE_iff.2 (by exact_mod_cast withBot_enat_le_zero_of_add_one_le_one hd)
  have : IsArtinianRing (O ⧸ Module.annihilator O M) := isArtinianRing_iff_krullDimLE_zero.2 inferInstance
  let := Module.quotientAnnihilator (R := O) (M := M)
  have := (Module.isTorsionBySet_annihilator O M).isScalarTower (S := O)
  have : Module.Finite (O ⧸ Module.annihilator O M) M := Module.Finite.of_restrictScalars_finite O _ _
  have : IsArtinian O M := isArtinian_of_surjective_algebraMap (S := O) (R := O ⧸ Module.annihilator O M)
    (show Function.Surjective (algebraMap O (O ⧸ Module.annihilator O M)) from Ideal.Quotient.mk_surjective)
  exact Module.length_ne_top

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffTube
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem measurable_tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) : Measurable (tubeWeight Q) := by
  have hl : Measurable (logAbsSq Q) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval Q).norm.pow 2).measurable
  exact Measurable.ite (measurableSet_le hl measurable_const) ((hl.pow_const 2).inv) measurable_const

theorem measurable_tubeDens {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (tubeDens J A P R φ) := by
  have hAm : Measurable fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous.measurable
  have hw : Measurable ((Metric.closedBall (0 : Fin n → ℂ) R).indicator
      fun x => tubeWeight P (A *ᵥ x)) :=
    ((measurable_tubeWeight P).comp hAm).indicator measurableSet_closedBall
  exact SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
    (continuous_abs.comp continuous_mul).measurable hw _

theorem tubeDens_nonneg {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin (d + 1) → ℂ) : 0 ≤ tubeDens J A P R φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOffTube.proof (hC : TubeFormCompare.Statement) (hE : TubeEuclMass.Statement) :
    CutOffTube.Statement := by
  intro n d J A P R φ hJ hdim hA hP hφ
  obtain ⟨C, hCle⟩ := hC n d J A P R φ hJ hdim hA hφ
  refine Integrable.mono' ((hE n d J A P R hJ hdim hA hP).const_mul C)
    (measurable_tubeDens hA P R φ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (tubeDens_nonneg J A P R φ y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
end

