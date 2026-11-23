module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0113
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0111
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GoodPointBranchExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

namespace GoodPointBranch

theorem exists_branch {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    {u q : Fin n → ℂ} (hqu : linEval u q = 0)
    {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)} {V : Set (Fin n → ℂ)}
    {g : (Fin d → ℂ) → Fin n → ℂ} (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hS : zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O)
    {N₀ : Set (Fin n → ℂ)} (hN₀ : N₀ ∈ 𝓝 q)
    (hdouble : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N₀ → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0)
    {w : Fin n ⊕ Fin M.m → ℂ} (hwq : IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q)
    {r : ℝ} {φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ} {k : ℕ} (hr : 0 < r)
    (hφd : DifferentiableOn ℂ φ (ball 0 r)) (hφi : InjOn φ (ball 0 r)) (hφ0 : φ 0 = w)
    (hφZ : MapsTo φ (ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal))
    (hφU : ∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' ball 0 s)
    (hvan : VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k)
    (hinjD : ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0)
    {G : Set (Fin n ⊕ Fin M.m → ℂ)} (hG : G ∈ 𝓝 w) :
    ∃ γ : VarBranch J (d + 1) q,
      (∃ U ∈ 𝓝 w, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius k ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
  set ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ := fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t) with hψdef
  have hψd : DifferentiableOn ℂ ψ (ball 0 r) :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.1 hφd (Sum.inl i)
  have h0r : (0 : Fin (d + 1) → ℂ) ∈ ball 0 r := mem_ball_self hr
  have hψ : HasStrictFDerivAt ψ (fderiv ℂ ψ 0) 0 :=
    (analyticOnNhd_of_differentiableOn isOpen_ball hψd 0 h0r).hasStrictFDerivAt
  have hψ0 : ψ 0 = q := by simp only [hψdef, hφ0, hwq]
  obtain ⟨H, hHd, hH0, hF⟩ := hvan
  have hk : k ≠ 0 := by
    intro hk0
    have h : linEval u (ψ 0) = (0 : Fin (d + 1) → ℂ) 0 ^ k * H 0 := hF 0 h0r
    rw [hψ0, hqu, hk0, pow_zero, one_mul] at h
    exact hH0 0 h0r h.symm
  have hzero : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, linEval u (ψ t) = 0 ↔ t 0 = 0 := by
    intro t ht
    have h : linEval u (ψ t) = t 0 ^ k * H t := hF t ht
    rw [h, mul_eq_zero, pow_eq_zero_iff hk]
    exact or_iff_left (hH0 t ht)
  have hψZ : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, ψ t ∈ zeroSet J := fun t ht =>
    NormalModelFibre.firstCoords_mem_zeroSet M (hφZ ht)
  have hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ zeroSet J ∩ {x | linEval u x = 0} := by
    filter_upwards [ball_mem_nhds (0 : Fin d → ℂ) hr] with v hv
    have hv' := consZero_mem_ball hv
    exact ⟨hψZ _ hv', (hzero _ hv').2 (consZero_apply_zero v)⟩
  obtain ⟨ha, W, hW, hWinj, hcov⟩ := slice_chart hψ hψ0 hinjD hV hqV hg hAg hS hslice
  have hE : ball (0 : Fin (d + 1) → ℂ) r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ ∈ 𝓝 (0 : Fin (d + 1) → ℂ) := by
    have hφc : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    have hψc : ContinuousAt ψ 0 := hψd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    exact inter_mem (inter_mem (ball_mem_nhds 0 hr) (hφc.preimage_mem_nhds (by rw [hφ0]; exact hG)))
      (hψc.preimage_mem_nhds (by rw [hψ0]; exact hN₀))
  obtain ⟨ε₁, hε₁, hε₁E⟩ := Metric.mem_nhds_iff.1 hE
  obtain ⟨ε₂, hε₂, hε₂W⟩ := Metric.mem_nhds_iff.1 hW
  have hs : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hs1 : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ :=
    (ball_subset_ball (min_le_left _ _)).trans hε₁E
  have hsr : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r := fun t ht => (hs1 ht).1.1
  have hs2 : ball (0 : Fin d → ℂ) (min ε₁ ε₂) ⊆ W := (ball_subset_ball (min_le_right _ _)).trans hε₂W
  have hinj : InjOn ψ (ball 0 (min ε₁ ε₂)) := by
    intro t ht t' ht' htt
    by_cases hφe : φ t = φ t'
    · exact hφi (hsr ht) (hsr ht') hφe
    · have hu : linEval u (ψ t) = 0 :=
        hdouble _ (hφZ (hsr ht)) _ (hφZ (hsr ht')) htt (hs1 ht).2 hφe
      have ht0 : t 0 = 0 := (hzero t (hsr ht)).1 hu
      have ht'0 : t' 0 = 0 := (hzero t' (hsr ht')).1 (by rw [← htt]; exact hu)
      have htail : Fin.tail t = Fin.tail t' := hWinj (hs2 (tail_mem_ball ht)) (hs2 (tail_mem_ball ht'))
        (by show ψ (consZero d (Fin.tail t)) = ψ (consZero d (Fin.tail t'))
            rw [consZero_tail t ht0, consZero_tail t' ht'0]
            exact htt)
      calc t = consZero d (Fin.tail t) := (consZero_tail t ht0).symm
        _ = t' := by rw [htail, consZero_tail t' ht'0]
  let γ : VarBranch J (d + 1) q :=
    { radius := min ε₁ ε₂, radius_pos := hs, toFun := ψ, differentiableOn := hψd.mono hsr, injOn := hinj,
      map_zero := hψ0, mapsTo := fun t ht => hψZ t (hsr ht) }
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUs⟩ := hφU (min ε₁ ε₂) hs
    refine ⟨U, hU, fun w' hw' => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hUs hw'
    exact ⟨t, ht, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨(hs1 ht).2, φ t, ⟨hφZ (hsr ht), (hs1 ht).1.2⟩, rfl⟩
  · obtain ⟨N, hN, hNS⟩ := hcov (ball 0 (min ε₁ ε₂)) (ball_mem_nhds 0 hs) hs2
    refine ⟨N, hN, fun x hx hxu => ?_⟩
    obtain ⟨v, hv, hvx⟩ := hNS ⟨⟨hx.1, hxu⟩, hx.2⟩
    exact ⟨consZero d v, ⟨consZero_mem_ball hv, consZero_apply_zero v⟩, hvx⟩
  · exact ⟨H, hHd.mono hsr, fun t ht => hH0 t (hsr ht), fun t ht => hF t (hsr ht)⟩
  · have hπ : ∀ x : Fin n → ℂ, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ x = A x :=
      fun x => LinearMap.toMatrix'_mulVec _ x
    have h1 : HasFDerivAt (fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)))
        ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) 0 :=
      (hasFDerivAt_apply 0 0).prodMk (A.hasFDerivAt.comp 0 hψ.hasFDerivAt)
    have h2 : HasFDerivAt (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ))
        ((consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0)))) 0 := by
      have h3 := (consCLM d).hasFDerivAt.comp 0 h1
      have hfun : (fun τ => vecCons (τ 0)
          (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) =
          ⇑(consCLM d) ∘ fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)) := by
        funext τ
        rw [Function.comp_apply, consCLM_apply, hπ]
      rw [hfun]
      exact h3
    rw [h2.fderiv]
    set L := (consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) with hL
    have hLinj : Function.Injective L := by
      refine (injective_iff_map_eq_zero L).2 fun v hv => ?_
      have hLv : L v = vecCons (v 0) (A (fderiv ℂ ψ 0 v)) := by
        rw [hL, ContinuousLinearMap.comp_apply, consCLM_apply]
        rfl
      have hv' : vecCons (v 0) (A (fderiv ℂ ψ 0 v)) = 0 := by rw [← hLv]; exact hv
      have h0 : v 0 = 0 := by simpa using congrFun hv' 0
      have hA : A (fderiv ℂ ψ 0 v) = 0 := by
        funext j
        simpa using congrFun hv' j.succ
      exact ha v h0 hA
    exact ⟨hLinj, LinearMap.injective_iff_surjective
      (f := (L : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))).1 hLinj⟩

end GoodPointBranch

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveNormalisationFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveNormalisationFinite.proof (hN : FieldNumbers.NoetherIntegralClosureFinite.Statement.{0}) :
    CurveNormalisationFinite.Statement := by
  intro n I q hI
  have := isReduced_curveLocalRing I q hI
  exact finite_integralClosure_of_isReduced hN (algebraMap _ (curveLocalRing I q)) (curveLocalRing_eq_div I q)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.POrdFiniteNonZeroDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

variable {n : ℕ}

theorem isLocalRing_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    [Nontrivial (curveLocalRing I q)] : IsLocalRing (curveLocalRing I q) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective

theorem OrdFiniteNonZeroDivisor.proof : OrdFiniteNonZeroDivisor.Statement := by
  intro n I q f hrad hdim hord
  have : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing (curveLocalRing I q) := isLocalRing_curveLocalRing I q
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  rw [mem_nonZeroDivisors_iff_right]
  intro y hyx
  by_contra hy

  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes (curveLocalRing I q), y ∉ p := by
    have : y ∉ (⊥ : Ideal (curveLocalRing I q)).radical := by
      rintro ⟨k, hk⟩
      exact hy (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
    simpa [← Ideal.sInf_minimalPrimes, minimalPrimes] using this
  have hpP : p.IsPrime := hp.1.1
  have hxp := (hpP.mem_or_mem (hyx ▸ p.zero_mem)).resolve_left hyp

  have hpmax : ¬ p.IsMaximal := by
    intro hm
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := curveLocalRing I q)
    rw [← IsLocalRing.eq_maximalIdeal hm, Ideal.height_eq_zero_iff.mpr hp, hdim] at h1
    exact absurd h1 (by decide)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      (integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (curveNormalisation I q))
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (algebraMap_curveNormalisation_injective I q)]; exact bot_le)
  obtain ⟨P, hPm, hQP⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  apply hord ⟨P, hPm⟩
  have : P.IsPrime := hPm.isPrime
  have hd : Disjoint (P.primeCompl : Set (curveNormalisation I q)) Q :=
    Set.disjoint_left.2 fun a ha haQ ↦ ha (hQP haQ)
  set Q' := Q.map (algebraMap (curveNormalisation I q) (Localization.AtPrime P)) with hQ'def
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd
  have hQ'u : Q'.under _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd
  have hle : Ideal.span {(algebraMap (curveNormalisation I q) (Localization.AtPrime P)
      (algebraMap (curveLocalRing I q) (curveNormalisation I q)
        (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)))} ≤ Q' := by
    rw [Ideal.span_singleton_le_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hQp] at hxp
    exact hxp

  change Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {_}) = ⊤
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨-, hart⟩ := hne
  have : IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Q') :=
    isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)
  have : IsArtinianRing (Localization.AtPrime P ⧸ Q') := isArtinian_of_tower (Localization.AtPrime P) this
  have hQ'max : Q'.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hQeq : Q = P := by
    rw [← hQ'u, IsLocalRing.eq_maximalIdeal hQ'max, Localization.AtPrime.under_maximalIdeal]
  apply hpmax
  rw [← hQp]
  have : Q.IsMaximal := hQeq ▸ hPm
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolynomialChartInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

theorem PolynomialChartInjective.full : PolynomialChartInjective.Statement := by
  classical
  intro σ _ k t f w hk hlin
  set g : Fin (k + 1) → MvPolynomial σ ℂ := Fin.cons t f with hg
  set F : (σ → ℂ) → Fin (k + 1) → ℂ := fun z j ↦ eval z (g j) with hF
  set L : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w with hL
  have hFL : HasStrictFDerivAt F L w := hasStrictFDerivAt_pi.2 fun j ↦
    (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g j) w trivial).hasStrictFDerivAt
  set r : Fin (k + 1) → σ → ℂ :=
    Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) with hr
  have hrow : ∀ j i, fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w (Pi.single i 1) = r j i := by
    intro j i
    rw [NormalCurveRegularPoint.fderiv_eval_single]
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [g, r]
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_fintype_fun_eq_card, hk])
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    let ψ : (σ → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun u ↦ ∑ i, u i * v i
        map_add' := fun a b ↦ by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c a ↦ by simp [Finset.mul_sum, mul_assoc] }
    have hker : Submodule.span ℂ (Set.range r) ≤ LinearMap.ker ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h0 := congrFun hv j
      simp only [hL, ContinuousLinearMap.pi_apply, Pi.zero_apply] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pi_eq_sum_univ' v, map_sum] at h0
      simp only [map_smul, smul_eq_mul, hrow] at h0
      simpa [ψ, mul_comm] using h0
    rw [hspan] at hker
    funext i
    have := hker (Submodule.mem_top (x := Pi.single i 1))
    simpa [ψ, Pi.single_apply] using this
  let e : (σ → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ) :=
    (LinearMap.linearEquivOfInjective L.toLinearMap hinj
      (by simp [Module.finrank_fintype_fun_eq_card, hk])).toContinuousLinearEquiv
  have hFe : HasStrictFDerivAt F (e : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ)) w := by
    convert hFL using 1
    ext v : 1
    rfl
  refine ⟨_, hFe.eventually_left_inverse, fun x hx y hy hxy ↦ ?_⟩
  have hFxy : F x = F y := by
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa [F, g] using hxy
    · simp only [F, g, Fin.cons_succ, hx.2 j, hy.2 j]
  rw [← hx.1, ← hy.1, hFxy]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLogDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedLogDensityNonneg

theorem hessC_logDistSq_comp_posSemidef {n e : ℕ} (x : Fin n → ℂ) (s : (Fin e → ℂ) → Fin n → ℂ)
    (y : Fin e → ℂ) (han : AnalyticAt ℂ s y) (hne : s y ≠ x) :
    (ReciprocityTheory.AnForm.hessC (logDistSq x ∘ s) y).PosSemidef := by
  let τ : (Fin e → ℂ) → Fin n → ℂ := fun w => s w - x
  have hτ : AnalyticAt ℂ τ y := han.sub analyticAt_const
  have hS : sqSum (τ y) ≠ 0 := by
    intro h0
    apply hne
    have hj : ∀ j ∈ Finset.univ, ‖(s y - x) j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0
    funext j
    have := hj j (Finset.mem_univ j)
    simpa [sub_eq_zero] using this
  have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
  have hfun : logDistSq x ∘ s = fun w => 2 * (phi ∘ τ) w := by
    funext w
    simp only [Function.comp_apply, logDistSq, phi, τ, euclPot, sqSum]
    ring
  have hP : (ReciprocityTheory.AnForm.hessC (phi ∘ τ) y).PosSemidef := by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  rw [hfun, ReciprocityTheory.AnForm.M.hessC_const_mul']
  exact hP.smul (by norm_num)

end RegularizedLogDensityNonneg

theorem RegLogDensNonneg.proof : RegLogDensNonneg.Statement := by
  intro n d J A u ε x z s hε hzx hs
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ z
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    exact RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StReducedNormalisationPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def ReducedNormalisationPlace.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : MaximalSpectrum (integralClosure R (FractionRing R))),
    ∃ p ∈ minimalPrimes R, ∀ (S : Type) [CommRing S] (φ : R →+* S),
      Function.Surjective φ → RingHom.ker φ = p →
        ∃ P' : MaximalSpectrum (integralClosure S (FractionRing S)), ∀ x : R,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (integralClosure R (FractionRing R)) (Localization.AtPrime P.asIdeal)
                (algebraMap R (integralClosure R (FractionRing R)) x)) =
            Ring.ord (Localization.AtPrime P'.asIdeal)
              (algebraMap (integralClosure S (FractionRing S)) (Localization.AtPrime P'.asIdeal)
                (algebraMap S (integralClosure S (FractionRing S)) (φ x)))

end

end GroundTheory.Heights₂.Heights
end

