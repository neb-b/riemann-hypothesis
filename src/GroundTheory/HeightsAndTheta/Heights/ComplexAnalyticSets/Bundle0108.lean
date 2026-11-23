module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthTransverseSlice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

theorem length_slice_of_isCohenMacaulay (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) {R : Type} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    [IsCohenMacaulayLocalRing (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))]
    (hW : W ∈ I.minimalPrimes) (hWm : W ≤ m) (huniq : ∀ W' ∈ I.minimalPrimes, W' ≤ m → W' = W)
    (d : ℕ) (lin : Fin d → R) (hlin : ∀ i, lin i ∈ m)
    (hdim : ringKrullDim (Localization.AtPrime m ⧸ W.map (algebraMap R (Localization.AtPrime m))) = (d : ℕ))
    (hT : ∀ g ∈ m, ∃ s ∉ m, s * g ∈ W ⊔ Ideal.span (Set.range lin)) :
    Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))) =
      Module.length (Localization.AtPrime m)
        (Localization.AtPrime m ⧸ (I ⊔ Ideal.span (Set.range lin)).map (algebraMap R (Localization.AtPrime m))) := by
  classical
  have hIW : I ≤ W := hW.1.2
  have hP := isPrime_map_quotient_localization m W I hWm hIW

  have hunit : ∀ s ∉ m, IsUnit (((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) s) := fun s hs =>
    ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m) m s).2 hs).map
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m))))

  have hall : ∀ Q : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))), Q.IsPrime →
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ Q := by
    intro Q hQ
    have hIQ : I ≤ Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := fun f hf => by
      rw [Ideal.mem_comap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hf)]
      exact Q.zero_mem
    have hQm : Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ m := fun f hf => by
      by_contra h
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (hunit f h))
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le hIQ
    have : W' = W := huniq W' hW' (hW'Q.trans hQm)
    subst this
    exact Ideal.map_le_iff_le_comap.2 hW'Q
  have hmin : minimalPrimes (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) =
      {W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))} := by
    ext Q
    rw [Set.mem_singleton_iff]
    constructor
    · intro hQ
      exact le_antisymm (hQ.2 ⟨hP, bot_le⟩ (hall Q hQ.1.1)) (hall Q hQ.1.1)
    · rintro rfl
      exact ⟨⟨hP, bot_le⟩, fun Q hQ _ => hall Q hQ.1⟩

  have hPdef : W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      (W.map (algebraMap R (Localization.AtPrime m))).map (Ideal.Quotient.mk _) := by
    rw [Ideal.map_map]
  have hdimP : ringKrullDim ((Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) ⧸
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))) = (d : ℕ) := by
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hPdef).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hIW)))]
    exact hdim

  have hmB : m.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) =
      (Ideal.span (Set.range lin)).map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hmax : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) ⊔
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [hspan, ← Ideal.map_sup, sup_comm, ← hmB]
    apply le_antisymm
    · refine Ideal.map_mono (sup_le hWm ?_)
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hlin i
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨s, hs, hsg⟩ := hT g hg
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hunit s hs), ← map_mul]
      exact Ideal.mem_map_of_mem _ hsg
  have key := hCM _ _ d _ hmin hdimP hmax
  rw [hLS R m W I hWm hIW _ rfl] at key
  rw [← key, ← Module.length_eq_of_surjective (S := Localization.AtPrime m)
    (R := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) Ideal.Quotient.mk_surjective,
    hspan, ← Ideal.map_map, Ideal.map_sup]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ (Localization.AtPrime m) _ _).toLinearEquiv.length_eq

theorem LengthTransverseSlice.proof (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) : LengthTransverseSlice.Statement := by
  intro n d I W q L hW hdim hq huniq hCMq hT
  have hWp : W.IsPrime := hW.1.1
  have hWm : W ≤ RingHom.ker (eval q) := fun f hf => RingHom.mem_ker.2 (hq f hf)
  have : IsCohenMacaulayLocalRing (localRingAt I q) := hCMq
  have h := length_slice_of_isCohenMacaulay hCM hLS (RingHom.ker (eval q)) W I hW hWm
    (fun W' hW' hle => huniq W' hW' fun f hf => RingHom.mem_ker.1 (hle hf)) d
    (fun i => linPoly L i - C ((L *ᵥ q) i))
    (fun i => by rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self])
    (LocalDimDomain.proof n d W hWp hdim q hq)
    (fun g hg => by
      obtain ⟨s, hs, hsg⟩ := hT g (RingHom.mem_ker.1 hg)
      exact ⟨s, fun h => hs (RingHom.mem_ker.1 h), hsg⟩)
  unfold localMult
  rw [dite_eq_left hWp, dite_eq_left (inferInstance : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime), h]
  rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveBranchOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem NormalCurveBranchOrder.proof (hdvr : NormalCurvePointDVR.Statement)
    (hsz : UniformiserBranchSimpleZero.Statement) : NormalCurveBranchOrder.Statement := by
  intro n J M w r φ hJ hdim hr hdiff hinj hmaps hw0 g
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  obtain ⟨hdom, hD⟩ := hdvr _ M.ideal w M.isPrime M.isIntegrallyClosed hdim' hwZ
  have hnear : ∀ q ∈ M.ideal, ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q = 0 := by
    refine fun q hq ↦ Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun τ hτ ↦ hmaps ?_ q hq
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hat0 : ∀ q, eval (φ fun _ ↦ (0 : ℂ)) q = eval w q := fun q ↦ by rw [← hw0]; rfl
  have han := fun q ↦ analyticAt_eval_disc hr hdiff q
  have hne0 : ∀ q, eval w q ≠ 0 → ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q ≠ 0 :=
    fun q hq ↦ (han q).continuousAt.eventually_ne (by simpa [hat0] using hq)
  have hord0 : ∀ q, eval w q ≠ 0 → analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) q) 0 = 0 :=
    fun q hq ↦ analyticOrderAt_eq_zero.2 (Or.inr (by simpa [hat0] using hq))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (pointLocalRing M.ideal w)
  obtain ⟨t, s₀, hs₀, hts⟩ := pointLocalRing_exists_mul_eq M.ideal w ϖ
  have hassoc : Associated ϖ (algebraMap _ (pointLocalRing M.ideal w) t) :=
    ⟨(isUnit_algebraMap_pointLocalRing _ w s₀ hs₀).unit, hts⟩
  have ht := hassoc.irreducible hϖ
  have ht1 := hsz _ M.ideal w t r φ M.isPrime M.isIntegrallyClosed hdim' ht hr hdiff hinj hmaps hw0
  by_cases hg : algebraMap _ (pointLocalRing M.ideal w) g = 0
  · rw [hg, ord_zero_eq_top_of_dvr, eq_comm, analyticOrderAt_eq_top]
    obtain ⟨s, hs, hsg⟩ := pointLocalRing_exists_mul_mem M.ideal w g hg
    filter_upwards [hnear _ hsg, hne0 s hs] with τ h1 h2
    rw [map_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hg ht
  obtain ⟨a, s, hs, has⟩ := pointLocalRing_exists_mul_eq M.ideal w (v : pointLocalRing M.ideal w)
  have ha : eval w a ≠ 0 := pointLocalRing_eval_ne_zero_of_isUnit M.ideal w hwZ a
    (by rw [← has]; exact v.isUnit.mul (isUnit_algebraMap_pointLocalRing _ w s hs))
  have hrel : algebraMap _ (pointLocalRing M.ideal w) (g * a - t ^ e * s) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, ← has, ← hv]
    ring
  obtain ⟨s', hs', hmem⟩ := pointLocalRing_exists_mul_mem M.ideal w _ hrel
  have heq : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) =ᶠ[𝓝 0]
      (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) := by
    filter_upwards [hnear _ hmem, hne0 s' hs'] with τ h1 h2
    simp only [map_mul, map_sub, map_pow] at h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h2)
  have hL : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) 0 =
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) a) 0 :=
    analyticOrderAt_mul (han g) (han a)
  have hR : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) 0 =
      e • analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) s) 0 := by
    rw [← analyticOrderAt_pow (han t)]
    exact analyticOrderAt_mul ((han t).pow e) (han s)
  have hc := analyticOrderAt_congr heq
  rw [hL, hR, ht1, hord0 a ha, hord0 s hs, add_zero, add_zero] at hc
  rw [hc, ← Ring.ord_mul_of_isUnit_right v.isUnit, hv, ord_pow_irreducible_of_dvr ht]
  simp

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ringKrullDim_quotient_minimalPrime_add_one_of_fintype {σ : Type} [Fintype σ]
    {V W : Ideal (MvPolynomial σ ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial σ ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial σ ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℂ ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MvPolynomial σ ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial σ ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial σ ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h ↦ by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial σ ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial σ ℂ ⧸ V)
    (fun M N hM hN ↦ (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

theorem NormalModelGoodPointGeneric.proof (h₁ : NormalCodimOneCompleteIntersection.Statement)
    (h₂ : NormalCodimOneUniformiser.Statement) (h₃ : JacobianRankOffHypersurface.Statement)
    (h₄ : ProjectionUnramifiedGeneric.Statement) : NormalModelGoodPointGeneric.Statement := by
  classical
  intro n d J u M hJ hdim hu
  have hP : M.ideal.IsPrime := M.isPrime
  set ut : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl (linForm u) with hut
  have hutP : ut ∉ M.ideal := by
    intro h
    apply hu
    rw [← M.comap_eq]
    exact h
  have hdimP : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (d + 1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hev : ∀ x : Fin n ⊕ Fin M.m → ℂ, eval x ut = linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) := fun x ↦ by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hut, linForm, linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords, map_sum]
  set L : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := M.ideal ⊔ Ideal.span {ut} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W ↦ hfinM.mem_toFinset

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one_of_fintype hutP hW (fun h ↦ by
      rw [hdimP] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdimP] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key

  have hgood : ∀ W ∈ L.minimalPrimes, ∃ β : MvPolynomial (Fin n ⊕ Fin M.m) ℂ, β ∉ W ∧
      ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W, eval w β ≠ 0 → NormalModelDivisorGoodPoint M u d w := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    have hPW : M.ideal ≤ W := le_sup_left.trans hW.1.2
    have hutW : ut ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnm : ∀ x y, x ∉ W → y ∉ W → x * y ∉ W := fun x y hx hy hm ↦ (hWp.mem_or_mem hm).elim hx hy
    obtain ⟨c, f, h, hc, hfP, hhW, hgen⟩ :=
      h₁ _ M.ideal W d hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW)
    obtain ⟨g, a, b, t, k, hgW, hk, haW, hbW, htW, hrel, hgenW⟩ :=
      h₂ _ M.ideal W d ut hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW) hutW hutP
    set q : Fin (c + 1) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ := Fin.cons g f with hq
    have hqW : ∀ j, q j ∈ W := fun j ↦ Fin.cases (by simpa [hq] using hgW)
      (fun j ↦ by simpa [hq] using hPW (hfP j)) j
    have hspan : Ideal.span (Set.range f) ≤ Ideal.span (Set.range q) :=
      Ideal.span_mono (Set.range_subset_iff.2 fun j ↦ ⟨j.succ, by simp [hq]⟩)
    have hgq : g ∈ Ideal.span (Set.range q) := Ideal.subset_span ⟨0, by simp [hq]⟩
    have hgenq : ∀ p ∈ W, ∃ i : ℕ, (h * t) ^ i * p ∈ Ideal.span (Set.range q) := by
      intro p hp
      obtain ⟨i₁, hi₁⟩ := hgenW p hp
      obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.1 hi₁
      obtain ⟨i₂, hi₂⟩ := hgen r hr
      refine ⟨i₁ + i₂, ?_⟩
      have e : (h * t) ^ (i₁ + i₂) * p = h ^ i₁ * t ^ i₂ * (h ^ i₂ * r) + h ^ (i₁ + i₂) * t ^ i₂ * s := by
        linear_combination (-(h ^ (i₁ + i₂) * t ^ i₂)) * hrs
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hspan hi₂))
        (Ideal.mul_mem_left _ _ ((Ideal.span_singleton_le_iff_mem _).2 hgq hs))
    have hint : ∀ i : Fin M.m, ∃ F : Polynomial (MvPolynomial (Fin n) ℂ), F.Monic ∧
        F.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
          (X (Sum.inr i)) ∈ W := fun i ↦ by
      obtain ⟨F, hF, hmem⟩ := M.integral i
      exact ⟨F, hF, hPW hmem⟩
    obtain ⟨μ₁, hμ₁W, hμ₁⟩ := h₃ _ W d (c + 1) q (h * t) hWp (hdimW W hW) hqW (hnm _ _ hhW htW) hgenq
    obtain ⟨μ₂, hμ₂W, hμ₂⟩ := h₄ (Fin n) (Fin M.m) W (c + 1) q (h * t) hWp hint hqW (hnm _ _ hhW htW) hgenq
    refine ⟨h * t * a * b * μ₁ * μ₂,
      hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ hhW htW) haW) hbW) hμ₁W) hμ₂W, fun w hw hβ ↦ ?_⟩
    have hwP : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := fun p hp ↦ hw p (hPW hp)
    simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hβ
    obtain ⟨⟨⟨⟨⟨hwh, hwt⟩, hwa⟩, hwb⟩, hwμ₁⟩, hwμ₂⟩ := hβ
    have hc' : c + (d + 1) = n + M.m := by simpa using hc
    have hfam : (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
        Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) = fun j s ↦ eval w (pderiv s (q j)) := by
      funext j s
      refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [hq]
    refine ⟨hwP, c, f, h, g, a, b, k, hc', hfP, hwh, hgen, hw g hgW, ?_, hk, hwa, hwb, hrel, ?_⟩
    · rw [hfam, linearIndependent_iff_card_eq_finrank_span]
      have := hμ₁ w hw hwμ₁
      simp only [Fintype.card_sum, Fintype.card_fin] at this ⊢
      show c + 1 = Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j))))
      omega
    · intro v hv hgv hfv
      refine hμ₂ w hw hwμ₂ v hv fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j
      · simpa [hq] using hgv
      · simpa [hq] using hfv j
  choose! β hβW hβ using hgood

  have hcomp : ∀ x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) = 0 →
      ∃ W ∈ L.minimalPrimes, x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hev] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp ↦ RingHom.mem_ker.mp (hWx hp)⟩

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    fun W ↦ ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set F : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := ∑ W ∈ T, β W * e W with hF
  have hsplit : ∀ W ∈ T, F = β W * e W + ∑ V ∈ T.erase W, β V * e V := fun W hW ↦
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, β V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV ↦ Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hFW : ∀ W ∈ L.minimalPrimes, F ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hβW W hW h
    · exact heW W hW h
  refine ⟨L ⊔ Ideal.span {F}, le_sup_left, ringKrullDim_quotient_sup_span_lt hFW hdimW, ?_⟩
  intro w hwJ hwu hwB
  obtain ⟨W, hW, hwW⟩ := hcomp w hwJ hwu
  have hFw : eval w F ≠ 0 := by
    intro h0
    refine hwB fun p hp ↦ ?_
    have hle : L ⊔ Ideal.span {F} ≤ RingHom.ker (eval w) := by
      refine sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hwW p (hW.1.2 hp))) (Ideal.span_le.mpr (by simpa using h0))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add (f := _), hwW _ (hrest W hW), add_zero, map_mul] at hFw
  exact hβ W hW w hwW (left_ne_zero_of_mul hFw)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProjectionLocallyInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology IndefiniteRowSideFullHecke.ComplexSets

theorem NormalModelProjectionLocallyInjective.proof : NormalModelProjectionLocallyInjective.Statement := by
  intro n J M w hJ hdim hw
  choose a b hbJ hab using M.birational
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  have hBJ : B ∉ J := fun h => by
    have := hJ
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hbJ i hi

  set S : Set (Fin n → ℂ) := ComplexSets.zeroSet J ∩ ComplexSets.zeroSet (Ideal.span {B}) with hS
  have hSfin : S.Finite := CurveProperClosedFinite.proof n J _ hJ hdim
    (fun h => hBJ (h (Ideal.subset_span rfl)))

  choose P hPm hP using M.integral
  set F : Set (Fin n ⊕ Fin M.m → ℂ) := {z | z ∈ zeroSetIn M.ideal ∧ firstCoords z ∈ S} with hF
  have hFfin : F.Finite := by
    have hT : (⋃ x ∈ S, ({x} : Set (Fin n → ℂ)) ×ˢ
        Set.pi Set.univ (fun i => {y : ℂ | ((P i).map (eval x)).IsRoot y})).Finite :=
      hSfin.biUnion fun x _ => (Set.finite_singleton x).prod
        (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map (eval x)).ne_zero)
    refine (hT.image fun p => Sum.elim p.1 p.2).subset ?_
    intro z hz
    refine ⟨(firstCoords z, fun i => z (Sum.inr i)), ?_, ?_⟩
    · refine Set.mem_biUnion hz.2 ⟨rfl, fun i _ => ?_⟩
      exact isRoot_map_eval_of_mem_zeroSetIn hz.1 i (P i) (hP i)
    · funext s
      rcases s with j | i <;> rfl
  refine ⟨(F \ {w})ᶜ, (hFfin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds
    (fun h => h.2 rfl), ?_⟩

  have hnear : ∀ z ∈ zeroSetIn M.ideal ∩ (F \ {w})ᶜ, (∃ i, eval (firstCoords z) (b i) = 0) → z = w := by
    rintro z ⟨hz, hzU⟩ ⟨i, hi⟩
    have hxJ : firstCoords z ∈ ComplexSets.zeroSet J := fun q hq => by
      rw [← M.comap_eq, Ideal.mem_comap] at hq
      have h := hz _ hq
      rw [eval_rename] at h
      exact h
    have hxB : firstCoords z ∈ ComplexSets.zeroSet (Ideal.span {B}) := fun q hq => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hq
      rw [eval_mul, hB, map_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
    by_contra hne
    exact hzU ⟨⟨hz, hxJ, hxB⟩, hne⟩
  intro z hz z' hz' hzz
  by_cases hbz : ∀ i, eval (firstCoords z) (b i) ≠ 0
  · have hbz' : ∀ i, eval (firstCoords z') (b i) ≠ 0 := hzz ▸ hbz
    rw [M.eq_graph_of_mem_zeroSetIn a b hab z hz.1 hbz, M.eq_graph_of_mem_zeroSetIn a b hab z' hz'.1 hbz', hzz]
  · simp only [not_forall, not_not] at hbz
    have hbz' : ∃ i, eval (firstCoords z') (b i) = 0 := hzz ▸ hbz
    rw [hnear z hz hbz, hnear z' hz' hbz']

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceBranchExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem PlaceBranchExists.proof (h₁ : PlaceOnComponent.Statement) (h₂ : PrimePlaceBranchExists.Statement) :
    PlaceBranchExists.Statement := by
  intro n I q hrad hdim P
  obtain ⟨J, hJ, -, hdimJ, P', hP'⟩ := h₁ n I q hrad hdim P
  obtain ⟨ν, hν⟩ := h₂ n J q hJ.1.1 hdimJ P'

  let ν' : VarBranch I 1 q :=
    { radius := ν.radius, radius_pos := ν.radius_pos, toFun := ν.toFun, differentiableOn := ν.differentiableOn,
      injOn := ν.injOn, map_zero := ν.map_zero,
      mapsTo := fun t ht g hg ↦ ν.mapsTo ht g (hJ.1.2 hg) }
  have hord : ∀ f, branchOrder ν' f = branchOrder ν f := fun _ ↦ rfl
  exact ⟨ν', fun f ↦ (hP' f).trans ((hν f).trans (hord f).symm)⟩

end GroundTheory.Heights₂.Heights
end

