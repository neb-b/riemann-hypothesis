module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0115
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMinimalPrimePlace

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem LinearNoetherNormalization.ringKrullDim_quotient_le {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) W) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ W) := (ringKrullDim_quotient W).symm
    _ ≤ k := h W hW

theorem LinearNoetherNormalization.exists_nat_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x)
    (hd : x ≤ d) : ∃ e : ℕ, e ≤ d ∧ x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hd
      exact absurd (WithBot.coe_le_coe.mp h1) (by simp)
    | coe e => exact ⟨e, by exact_mod_cast hd, rfl⟩

theorem LinearNoetherNormalization.exists_monic_of_prefix {d e n : ℕ} (h : e ≤ d)
    (A : Matrix (Fin d) (Fin n) ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : IsFiniteProjection P (A.submatrix (Fin.castLE h) id)) (j : Fin n) :
    ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
      f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
  obtain ⟨g, hg, hg0⟩ := hP.finite.to_isIntegral (Ideal.Quotient.mk P (X j))
  refine ⟨g.map (rename (R := ℂ) (Fin.castLE h)).toRingHom, hg.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
  refine (congrArg (fun φ => Polynomial.eval₂ φ (Ideal.Quotient.mk P (X j)) g) ?_).trans hg0
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [projHom, pullback]
    rfl
  · intro i
    simp [projHom, pullback, linPoly]

theorem LinearNoetherNormalization.proof : LinearNoetherNormalization.Statement := by
  classical
  intro n d J hJ

  have hdim : ∀ P ∈ J.minimalPrimes, ∃ e : ℕ, e ≤ d ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = e := by
    intro P hP
    have : P.IsPrime := hP.1.1
    refine LinearNoetherNormalization.exists_nat_of_le ringKrullDim_nonneg_of_nontrivial ?_
    rw [← hJ]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
      (Ideal.Quotient.factor_surjective hP.1.2)

  have htop : ∃ P ∈ J.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = d := by
    by_contra hne
    push Not at hne
    rcases d with _ | d'
    · have hJt : J ≠ ⊤ := by
        rintro rfl
        have : Subsingleton (MvPolynomial (Fin n) ℂ ⧸ (⊤ : Ideal (MvPolynomial (Fin n) ℂ))) :=
          Ideal.Quotient.subsingleton_iff.mpr rfl
        rw [ringKrullDim_eq_bot_of_subsingleton] at hJ
        simp at hJ
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
      obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (J := M) hJM
      obtain ⟨e, he, he'⟩ := hdim P hP
      exact hne P hP (by rw [he', Nat.le_zero.mp he])
    · have hle := LinearNoetherNormalization.ringKrullDim_quotient_le J (d' : WithBot ℕ∞)
        (fun P hP => by
          obtain ⟨e, he, he'⟩ := hdim P hP
          have hne' : e ≠ d' + 1 := fun h => hne P hP (by rw [he', h])
          rw [he']
          exact_mod_cast (by omega : e ≤ d'))
      rw [hJ] at hle
      exact absurd hle (by norm_cast; omega)
  obtain ⟨P₀, hP₀, hP₀d⟩ := htop
  have hP₀p : P₀.IsPrime := hP₀.1.1
  obtain ⟨W₀, ⟨S₀, rfl⟩, ⟨A₀, p₀, hp₀S, hp₀⟩, hW₀⟩ :=
    FiniteProjectionsContainOpen.full n d P₀ hP₀p hP₀d
  have hp₀0 : p₀ ≠ 0 := fun h => hp₀ (by rw [h, map_zero])

  have hq : ∀ P ∈ J.minimalPrimes, ∃ q : MvPolynomial (Fin d × Fin n) ℂ, q ≠ 0 ∧
      ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) q ≠ 0 →
        ∀ j, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
          f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
    intro P hP
    have : P.IsPrime := hP.1.1
    obtain ⟨e, he, hPe⟩ := hdim P hP
    obtain ⟨W, ⟨S, rfl⟩, ⟨B, p, hpS, hp⟩, hW⟩ := FiniteProjectionsContainOpen.full n e P this hPe
    refine ⟨rename (Prod.map (Fin.castLE he) id) p, fun h0 => ?_, fun A hA j => ?_⟩
    · apply hp
      rw [rename_injective _ ((Fin.castLE_injective he).prodMap Function.injective_id)
        (h0.trans (map_zero _).symm), map_zero]
    · rw [eval_rename] at hA
      exact LinearNoetherNormalization.exists_monic_of_prefix he A P (hW ⟨p, hpS, hA⟩) j
  choose! q hq0 hqA using hq
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hQ : p₀ * ∏ P ∈ hfin.toFinset, q P ≠ 0 :=
    mul_ne_zero hp₀0 (Finset.prod_ne_zero_iff.mpr fun P hP => hq0 P (hfin.mem_toFinset.mp hP))

  obtain ⟨x, hx⟩ : ∃ x, eval x (p₀ * ∏ P ∈ hfin.toFinset, q P) ≠ 0 := by
    by_contra! h
    exact hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])
  let A : Matrix (Fin d) (Fin n) ℂ := Matrix.of fun i j => x (i, j)
  have hxA : (fun ij : Fin d × Fin n => A ij.1 ij.2) = x := rfl
  rw [← hxA, map_mul, map_prod] at hx
  have hall := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hx)
  have hA₀ : IsFiniteProjection P₀ A := hW₀ ⟨p₀, hp₀S, left_ne_zero_of_mul hx⟩

  have hint : ∀ j, (projHom J A).toRingHom.IsIntegralElem (Ideal.Quotient.mk J (X j)) := by
    intro j
    have hf : ∀ P ∈ J.minimalPrimes, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
        f.eval₂ (pullback A).toRingHom (X j) ∈ P :=
      fun P hP => hqA P hP A (hall P (hfin.mem_toFinset.mpr hP)) j
    choose! f hfm hfP using hf
    have hFm : (∏ P ∈ hfin.toFinset, f P).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun P hP => hfm P (hfin.mem_toFinset.mp hP)
    have hFrad : (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) ∈ J.radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      rw [show (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) =
          ∏ P ∈ hfin.toFinset, (f P).eval₂ (pullback A).toRingHom (X j) from
        map_prod (Polynomial.eval₂RingHom (pullback A).toRingHom (X j)) _ _]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
        (fun P => (f P).eval₂ (pullback A).toRingHom (X j)) (hfin.mem_toFinset.mpr hP)
      rw [hc]
      exact Ideal.mul_mem_right c P (hfP P hP)
    obtain ⟨m, hm⟩ := hFrad
    refine ⟨(∏ P ∈ hfin.toFinset, f P) ^ m, hFm.pow m, ?_⟩
    rw [← Polynomial.eval₂_pow, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂] at hm
    exact hm
  refine ⟨A, fun a b hab => hA₀.injective ?_, ?_⟩
  · have hfac : ∀ c, projHom P₀ A c = Ideal.Quotient.factor hP₀.1.2 (projHom J A c) :=
      fun c => (Ideal.Quotient.factor_mk hP₀.1.2 _).symm
    rw [hfac, hfac, hab]
  · have hI : (projHom J A).toRingHom.IsIntegral := by
      intro y
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      induction p using MvPolynomial.induction_on with
      | C a =>
        have : Ideal.Quotient.mk J (C a) = (projHom J A).toRingHom (C a) := by
          simp [projHom, pullback]
          rfl
        rw [this]
        exact (projHom J A).toRingHom.isIntegralElem_map
      | add p q hp hq => rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ hp hq
      | mul_X p i hp => rw [map_mul]; exact RingHom.IsIntegralElem.mul _ hp (hint i)
    refine hI.to_finite ?_
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial (Fin d) ℂ))
    rw [show (projHom J A).toRingHom.comp (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) =
      algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J) from (projHom J A).comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceOnComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {p : Ideal R} (hp : p ∈ minimalPrimes R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = p) : ringKrullDim S = 1 := by
  have hpp : p.IsPrime := hp.1.1
  refine le_antisymm (hR ▸ ringKrullDim_le_of_surjective φ hφ) ?_
  obtain ⟨x, y, hxy⟩ := Order.one_le_krullDim_iff.1 (le_of_eq hR.symm : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
  have hxm : x.asIdeal < IsLocalRing.maximalIdeal R :=
    lt_of_lt_of_le hxy (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)
  have hpm : p < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun h ↦ ?_
    have hpx : p ≤ x.asIdeal := hp.2 ⟨x.isPrime, bot_le⟩ (h ▸ hxm.le)
    exact (lt_of_le_of_lt hpx hxm).ne h
  have hk : ∀ K : Ideal R, p ≤ K → (K.map φ).comap φ = K := fun K hK ↦ by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.2 hK]
  have h0 : (p.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hker.le
  have h1 : ((IsLocalRing.maximalIdeal R).map φ).IsPrime :=
    Ideal.map_isPrime_of_surjective hφ (hker.le.trans hpm.le)
  refine Order.one_le_krullDim_iff.2 ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩
  change p.map φ < (IsLocalRing.maximalIdeal R).map φ
  refine lt_of_le_of_ne (Ideal.map_mono hpm.le) fun h ↦ hpm.ne ?_
  rw [← hk p le_rfl, h, hk _ hpm.le]

theorem PlaceOnComponent.proof (h₁ : ReducedNormalisationPlace.Statement)
    (h₂ : CurveMinimalPrimeQuotient.Statement) : PlaceOnComponent.Statement := by
  intro n I q hrad hdim P
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  have : Nontrivial (curveLocalRing I q) := by
    refine not_subsingleton_iff_nontrivial.1 fun h ↦ ?_
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨p, hp, hS⟩ := h₁ (curveLocalRing I q) P
  obtain ⟨J, hJ, hJq, φ, hφ, hker, hφf⟩ := h₂ n I q p hp
  obtain ⟨P', hP'⟩ := hS (curveLocalRing J q) φ hφ hker
  refine ⟨J, hJ, hJq, ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes hdim hp φ hφ hker, P', fun f ↦ ?_⟩
  have e := hP' (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hφf] at e
  exact e

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionInjectiveOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem ProjectionInjectiveOffHypersurface.proof (hF : FrameJacobianGeneric.Statement) :
    ProjectionInjectiveOffHypersurface.Statement := by
  classical
  intro σ _ I k hI hk
  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ := renameEquiv ℂ e
  let J : Ideal (MvPolynomial (Fin n) ℂ) := I.map φ
  have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hJk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
    rw [← hk]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J φ rfl).symm)
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, -, hcard, hfJ, -, hdet, -⟩ := hF n k J hJ hJk b

  let T : (σ → ℂ) → EuclideanSpace ℂ (Fin n) := fun x => WithLp.toLp 2 (x ∘ e.symm)
  have hT : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ),
      eval (fun i => T x i) p = eval x (φ.symm p) := by
    intro x p
    have : φ.symm p = rename e.symm p := rfl
    rw [this, eval_rename]
  have hTinj : Function.Injective T := by
    intro x y hxy
    funext s
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v (e s)) hxy
    simpa [T] using this
  have hTc : Continuous T :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _)
  refine ⟨φ.symm (frameJacobianDet b I₀ f), ?_, ?_⟩
  · intro hmem
    apply hdet
    exact (Ideal.mem_map_of_equiv φ _).2 ⟨_, hmem, by simp⟩
  intro z hz hzh
  have hf0 : ∀ x ∈ zeroSetIn I, ∀ j, eval (fun i => T x i) (f j) = 0 := by
    intro x hx j
    obtain ⟨q, hq, hqf⟩ := (Ideal.mem_map_of_equiv φ (f j)).1 (hfJ j)
    rw [hT, ← hqf, AlgEquiv.symm_apply_apply]
    exact hx q hq
  have hz' : eval (fun i => T z i) (frameJacobianDet b I₀ f) ≠ 0 := by rwa [hT]
  obtain ⟨Ω, V, g, -, hV, hzV, -, -, hpg, hgraph⟩ :=
    FrameImplicitGraph.proof n b I₀ f (T z) (hf0 z hz) hz' Set.univ isOpen_univ (Set.mem_univ _)
  let c : Fin k ≃ I₀ := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let A : (σ → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm (c j : Fin n))
  refine ⟨T ⁻¹' V, hV.preimage hTc, hzV, A, ?_⟩

  have hback : ∀ x ∈ zeroSetIn I ∩ T ⁻¹' V, g (GroundTheory.Heights₂.Heights.frameProj b I₀ (T x)) = T x := by
    rintro x ⟨hx, hxV⟩
    have hmem : T x ∈ {y : EuclideanSpace ℂ (Fin n) | ∀ j, eval (fun i => y i) (f j) = 0} ∩ V :=
      ⟨hf0 x hx, hxV⟩
    rw [hgraph] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    rw [← hwx, hpg w hw]
  intro x hx y hy hAxy
  apply hTinj
  have hproj : GroundTheory.Heights₂.Heights.frameProj b I₀ (T x) = GroundTheory.Heights₂.Heights.frameProj b I₀ (T y) := by
    funext i
    have := congrFun hAxy (c.symm i)
    show inner ℂ (b i) (T x) = inner ℂ (b i) (T y)
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]
    simpa [A, T] using this
  rw [← hback x hx, ← hback y hy, hproj]

theorem ProjectionInjectiveOffHypersurface.proof_of_rank (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : ProjectionInjectiveOffHypersurface.Statement :=
  ProjectionInjectiveOffHypersurface.proof (FrameJacobianGeneric.proof hR hC)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PReducedNormalisationPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets MinimalPrimePlace

noncomputable section

namespace ReducedNormalisationPlace

variable {A B : Type*} [CommRing A] [CommRing B]

theorem fracMap_mk'_eq_zero_iff [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A)
    (u : nonZeroDivisors A) :
    fracMap π hker (IsLocalization.mk' (FractionRing A) a u) = 0 ↔ a ∈ RingHom.ker π := by
  rw [IsLocalization.map_mk', IsFractionRing.mk'_eq_zero_iff_eq_zero, RingHom.mem_ker]

theorem fracMap_eq_zero_iff {C : Type*} [CommRing C] [IsDomain B] [IsDomain C] (π : A →+* B) (π' : A →+* C)
    (hker : RingHom.ker π ∈ minimalPrimes A) (hker' : RingHom.ker π' ∈ minimalPrimes A)
    (h : RingHom.ker π = RingHom.ker π') (z : FractionRing A) :
    fracMap π hker z = 0 ↔ fracMap π' hker' z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  rw [fracMap_mk'_eq_zero_iff, fracMap_mk'_eq_zero_iff, h]

theorem eq_zero_of_forall_num_mem [IsReduced A] (z : FractionRing A)
    (h : ∀ p ∈ minimalPrimes A, ∀ (a : A) (u : nonZeroDivisors A),
      z = IsLocalization.mk' (FractionRing A) a u → a ∈ p) : z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  show IsLocalization.mk' (FractionRing A) a u = 0
  rw [eq_zero_of_forall_mem_minimalPrimes fun p hp ↦ h p hp a u rfl, IsLocalization.mk'_zero]

theorem exists_idempotent [IsNoetherianRing A] [IsReduced A] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    ∃ e : integralClosure A (FractionRing A), ∀ (B : Type) [CommRing B] [IsDomain B] (π : A →+* B),
      Function.Surjective π → ∀ hker : RingHom.ker π = p,
        fracMap π (by rw [hker]; exact hp) e = 1 ∧
          ∀ z, fracMap π (by rw [hker]; exact hp) z = 0 → (e : FractionRing A) * z = 0 := by
  have := hp.1.1
  have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes A := by rwa [Ideal.mk_ker]
  obtain ⟨e, he1, hek, -⟩ := exists_fracMap_unit (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective hk
  have he : IsIntegral A e := by
    simpa using isIntegral_mul_of_fracMap _ Ideal.Quotient.mk_surjective hk (x := 1) he1 hek
      (by rw [map_one]; exact isIntegral_one)
  refine ⟨⟨e, he⟩, fun B _ _ π _ hker ↦ ⟨?_, fun z hz ↦ hek z ?_⟩⟩
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    rw [← sub_eq_zero, ← map_one (fracMap π hπ), ← map_sub,
      fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]), map_sub, he1, map_one,
      sub_self]
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    exact (fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]) z).1 hz

end ReducedNormalisationPlace


open ReducedNormalisationPlace in
theorem ReducedNormalisationPlace.proof : ReducedNormalisationPlace.Statement := by
  intro R _ _ _ P
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have := P.isMaximal.isPrime
  choose! e he using fun p (hp : p ∈ minimalPrimes R) ↦ exists_idempotent p hp
  have hprodK : ∏ p ∈ hfin.toFinset, (1 - (e p : FractionRing R)) = 0 := by
    refine eq_zero_of_forall_num_mem _ fun p hp a u hz ↦ ?_
    have := hp.1.1
    have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes R := by rwa [Ideal.mk_ker]
    have h0 : fracMap (Ideal.Quotient.mk p) hk (∏ q ∈ hfin.toFinset, (1 - (e q : FractionRing R))) = 0 := by
      rw [map_prod]
      refine Finset.prod_eq_zero (hfin.mem_toFinset.2 hp) ?_
      rw [map_sub, map_one,
        (he p hp (R ⧸ p) (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective Ideal.mk_ker).1, sub_self]
    rw [hz, fracMap_mk'_eq_zero_iff, Ideal.mk_ker] at h0
    exact h0
  have hprod : ∏ p ∈ hfin.toFinset, (1 - e p) = 0 := Subtype.ext (by push_cast; exact hprodK)
  obtain ⟨p, hpT, hp1⟩ := (Ideal.IsPrime.prod_mem_iff (p := P.asIdeal)).1
    (by rw [hprod]; exact P.asIdeal.zero_mem)
  have hpmin : p ∈ minimalPrimes R := hfin.mem_toFinset.1 hpT
  have hepP : e p ∉ P.asIdeal := fun h ↦
    P.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.asIdeal.add_mem h hp1))
  refine ⟨p, hpmin, fun S _ φ hφ hkerφ ↦ ?_⟩
  have hpr : (RingHom.ker φ).IsPrime := hkerφ ▸ hpmin.1.1
  have : IsDomain S :=
    MulEquiv.isDomain (R ⧸ RingHom.ker φ) (RingHom.quotientKerEquivOfSurjective hφ).symm.toMulEquiv
  have hker : RingHom.ker φ ∈ minimalPrimes R := by rw [hkerφ]; exact hpmin
  obtain ⟨he1, hek⟩ := he p hpmin S φ hφ hkerφ
  obtain ⟨_, -, -, hsurj⟩ := exists_fracMap_unit φ hφ hker
  have hN : Function.Surjective (normMap φ hker) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hint : IsIntegral R ((e p : FractionRing R) * x) :=
      isIntegral_mul_of_fracMap φ hφ hker he1 hek (by rw [hx]; exact y.2)
    refine ⟨⟨_, hint⟩, Subtype.ext ?_⟩
    show fracMap φ hker ((e p : FractionRing R) * x) = y
    rw [map_mul, he1, one_mul, hx]
  have hε1 : normMap φ hker (e p) = 1 := Subtype.ext he1
  have hε : ∀ z, normMap φ hker z = 0 → e p * z = 0 := fun z hz ↦
    Subtype.ext (hek z (congrArg Subtype.val hz))
  have hkerP : RingHom.ker (normMap φ hker) ≤ P.asIdeal := fun z hz ↦
    (P.isMaximal.isPrime.mem_or_mem (by rw [hε z hz]; exact P.asIdeal.zero_mem)).resolve_left hepP
  have hcm : (P.asIdeal.map (normMap φ hker)).comap (normMap φ hker) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ hN, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hkerP]
  have hmax : (P.asIdeal.map (normMap φ hker)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hN P.isMaximal).resolve_left fun h ↦
      P.isMaximal.ne_top (by rw [← hcm, h, Ideal.comap_top])
  obtain ⟨E, hE⟩ := exists_localization_ringEquiv (normMap φ hker) hN (e p) hε1 hε
    (P.asIdeal.map (normMap φ hker))
  refine ⟨⟨_, hmax⟩, fun x ↦ ?_⟩
  have key : ∀ (Q : Ideal (integralClosure R (FractionRing R))) [Q.IsPrime], Q = P.asIdeal →
      ∀ E' : Localization.AtPrime Q ≃+* Localization.AtPrime (P.asIdeal.map (normMap φ hker)),
        (∀ r, E' (algebraMap _ _ r) = algebraMap _ _ (normMap φ hker r)) →
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap R (integralClosure R (FractionRing R)) x)) =
          Ring.ord (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
            (algebraMap _ (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
              (algebraMap S (integralClosure S (FractionRing S)) (φ x))) := by
    rintro Q _ rfl E' hE'
    rw [← ord_ringEquiv (R := Localization.AtPrime P.asIdeal)
      (S := Localization.AtPrime (P.asIdeal.map (normMap φ hker))) E', hE', normMap_algebraMap]
  exact key _ hcm E hE

end

end GroundTheory.Heights₂.Heights
end

