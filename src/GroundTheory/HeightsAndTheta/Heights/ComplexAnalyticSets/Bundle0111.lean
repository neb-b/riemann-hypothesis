module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0107
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0110
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.NormalModelFibreNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets Metric

noncomputable section

namespace NormalModelFibre

variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

theorem firstCoords_mem_zeroSet {w : Fin n ⊕ Fin M.m → ℂ} (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ zeroSet J := by
  intro f hf
  have h1 : f ∈ M.ideal.comap
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := by
    rw [M.comap_eq]
    exact hf
  have h0 := hw _ (Ideal.mem_comap.1 h1)
  rw [eval_rename] at h0
  exact h0

theorem exists_mem_fibre {q : Fin n → ℂ} (hq : q ∈ zeroSet J) :
    ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q := by
  have : M.ideal.IsPrime := M.isPrime
  have h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
    intro h
    obtain ⟨f, hf, hf0⟩ := Submonoid.mem_map.1 h
    apply (Ideal.mem_primeCompl_iff).1 hf
    rw [RingHom.mem_ker]
    have h1 : rename Sum.inl f ∈ M.ideal := Ideal.Quotient.eq_zero_iff_mem.1 hf0
    have h2 : f ∈ J := by
      rw [← M.comap_eq]
      exact h1
    exact hq f h2
  have hle := le_nonZeroDivisors_of_noZeroDivisors h0
  have : Nontrivial (Localization (normalModelSubmonoid M q)) :=
    (IsLocalization.injective (M := normalModelSubmonoid M q)
      (S := Localization (normalModelSubmonoid M q)) hle).nontrivial
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (Localization (normalModelSubmonoid M q))
  obtain ⟨w, hw, hwq, -⟩ := ModelLocalizationMaximalPoint.proof n J q M P hP
  exact ⟨w, hw, hwq⟩

theorem fibre_finite (q : Fin n → ℂ) :
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}.Finite := by
  choose P hPm hP using M.integral
  have hroots : (Set.univ.pi fun i : Fin M.m => {a : ℂ | ((P i).map (eval q)).IsRoot a}).Finite :=
    Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map _).ne_zero
  refine (hroots.image fun y : Fin M.m → ℂ => Sum.elim q y).subset ?_
  rintro w ⟨hw, rfl⟩
  refine ⟨fun i => w (Sum.inr i), fun i _ => ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.isRoot_map_eval_of_mem_zeroSetIn hw i (P i) (hP i)
  · funext s
    rcases s with i | i <;> rfl

theorem isClosed_zeroSetIn : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) := by
  have h : IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal = ⋂ f ∈ M.ideal, {z | eval z f = 0} := by
    ext z
    simp [IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem continuous_firstCoords : Continuous (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (n := n) (m := M.m)) :=
  continuous_pi fun _ => continuous_apply _

theorem eventually_mem_of_fibre_subset {q : Fin n → ℂ} {U : Set (Fin n ⊕ Fin M.m → ℂ)} (hU : IsOpen U)
    (hfib : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q → w ∈ U) :
    ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ∈ U := by
  set K : Set (Fin n ⊕ Fin M.m → ℂ) := {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ closedBall q 1} ∩ Uᶜ with hKdef
  have hKb : Bornology.IsBounded K :=
    (IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof n J M (closedBall q 1) isBounded_closedBall).subset
      Set.inter_subset_left
  have hKc : IsClosed K :=
    ((isClosed_zeroSetIn M).inter (isClosed_closedBall.preimage (continuous_firstCoords M))).inter
      hU.isClosed_compl
  have hK : IsCompact K := isCompact_of_isClosed_isBounded hKc hKb
  have hKi : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K) :=
    (hK.image (continuous_firstCoords M)).isClosed
  have hq : q ∉ IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K := by
    rintro ⟨w, ⟨⟨hw, -⟩, hwU⟩, hwq⟩
    exact hwU (hfib w hw hwq)
  refine ⟨closedBall q 1 ∩ (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K)ᶜ,
    inter_mem (closedBall_mem_nhds q one_pos) (hKi.isOpen_compl.mem_nhds hq), ?_⟩
  intro w hw hwN
  by_contra hwU
  exact hwN.2 ⟨w, ⟨⟨hw, hwN.1⟩, hwU⟩, rfl⟩

end NormalModelFibre

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

noncomputable section

namespace FormIntegralPositivity

variable {n : ℕ}

theorem analyticAt_sheet {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    AnalyticAt ℂ s (A *ᵥ x) := by
  obtain ⟨U, hU, hxU, hsU, -⟩ := hs
  rw [analyticAt_pi_iff]
  intro i
  exact ReciprocityTheory.ChartRestriction.G.Geo.osgood d U (fun y => s y i) hU
    (fun y hy => differentiableWithinAt_pi.mp (hsU y hy) i) (A *ᵥ x) hxU

end FormIntegralPositivity


end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ImageDimLe.proof : ImageDimLe.Statement := by
  intro n m P Q hP
  set φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mkₐ ℂ P).comp (aeval Q) with hφ
  have : P.IsPrime := hP
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ)
  obtain ⟨t, ht1, ht2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin n) ℂ ⧸ P)
  have hle : Algebra.trdeg ℂ (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ) ≤
      Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) :=
    trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)
  rw [hs2, ht2] at hle
  have hst : s ≤ t := by exact_mod_cast hle
  rw [hs1, ht1]
  exact_mod_cast hst

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDisc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormalModelDisc.proof (hreg : NormalCurveRegularPoint.Statement) : NormalModelDisc.Statement := by
  intro n J M w _ hdim hw
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  obtain ⟨A, O, V, g, hO, -, hwV, hg, hAg, hZV⟩ :=
    hreg (Fin n ⊕ Fin M.m) M.ideal w M.isPrime M.isIntegrallyClosed hdim' hw
  have hwg : w ∈ g '' O := hZV ▸ ⟨hw, hwV⟩
  obtain ⟨y₀, hy₀, hgy₀⟩ := hwg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
  have hmem : ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) r, y₀ + τ ∈ O := fun τ hτ ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hτ)
  refine ⟨r, hr, fun τ ↦ g (y₀ + τ), ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact ((hg _ (hmem τ hτ)).differentiableAt.comp τ
      (differentiableAt_const y₀ |>.add differentiableAt_id)).differentiableWithinAt
  · intro s hs t ht hst
    have h := congrArg A hst
    simp only at h
    rw [hAg _ (hmem s hs), hAg _ (hmem t ht)] at h
    exact add_left_cancel h
  · intro τ hτ
    have h : g (y₀ + τ) ∈ g '' O := ⟨_, hmem τ hτ, rfl⟩
    rw [← hZV] at h
    exact h.1
  · simp [hgy₀]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelPointOfPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem NormalModelPointOfPlace.proof (hLoc : NormalisationModelLocalization.Statement)
    (hMax : ModelLocalizationMaximalPoint.Statement) (hAt : LocalizationAtPrimeQuotient.Statement.{0}) :
    NormalModelPointOfPlace.Statement := by
  intro n J q M hJ P
  obtain ⟨e, he⟩ := hLoc n J q M hJ
  obtain ⟨P', hP'def⟩ : ∃ P' : @Ideal (Localization (normalModelSubmonoid M q)) CommSemiring.toSemiring,
      P' = P.asIdeal.comap (e.symm : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q) :=
    ⟨_, rfl⟩
  have hP' : P'.IsMaximal := by
    rw [hP'def]
    exact Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hPp : P'.IsPrime := by
    rw [hP'def]
    infer_instance
  obtain ⟨w, hw, hq, hcomap⟩ := hMax n J q M P' hP'
  obtain ⟨eAt, heAt⟩ := hAt (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) M.ideal (normalModelSubmonoid M q) P'
    (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) hcomap
  let eP : Localization.AtPrime P.asIdeal ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (M := P.asIdeal.primeCompl) (T := P'.primeCompl)
      (Localization.AtPrime P.asIdeal) (Localization.AtPrime P') e (by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          subst hP'def
          show e.symm (e x) ∉ P.asIdeal
          simpa using hx
        · intro hy
          subst hP'def
          exact ⟨e.symm y, hy, by simp⟩)
  refine ⟨w, hw, hq, fun f ↦ ?_⟩
  rw [← ord_ringEquiv (eP.trans eAt)]
  congr 1
  rw [RingEquiv.trans_apply, IsLocalization.ringEquivOfRingEquiv_eq, he, heAt]
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimePlaceBranchExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem PrimePlaceBranchExists.proof (hA : NormalModelPointOfPlace.Statement) (hB : NormalModelDisc.Statement)
    (hC : NormalModelProjectionLocallyInjective.Statement) (hO : NormalCurveBranchOrder.Statement) :
    PrimePlaceBranchExists.Statement := by
  intro n J q hJ hdim P

  have hq : q ∈ zeroSet J := by
    by_contra h
    have := curveLocalRing_subsingleton J q h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have hloc : ringKrullDim (curveLocalRing J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have hdim1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) := by
    rw [he]
    rw [hloc] at hdim
    exact_mod_cast hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨w, hw, hwq, hord⟩ := hA n J q M hJ P
  obtain ⟨r, hr, φ, hφd, hφi, hφm, hφ0⟩ := hB n J M w hJ hdim1 hw
  obtain ⟨U, hU, hUi⟩ := hC n J M w hJ hdim1 hw

  have hcont : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hφ0 ▸ hU))
  have hρ : 0 < min r ε := lt_min hr hε
  have hsub : Metric.ball (0 : Fin 1 → ℂ) (min r ε) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsubU : ∀ t ∈ Metric.ball (0 : Fin 1 → ℂ) (min r ε), φ t ∈ U := fun t ht ↦
    hεU (Metric.ball_subset_ball (min_le_right _ _) ht)
  let ν : VarBranch J 1 q :=
    { radius := min r ε, radius_pos := hρ, toFun := fun t i ↦ φ t (Sum.inl i),
      differentiableOn := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 (hφd.mono hsub) (Sum.inl i),
      injOn := fun a ha b hb hab ↦ hφi (hsub ha) (hsub hb)
        (hUi ⟨hφm (hsub ha), hsubU a ha⟩ ⟨hφm (hsub hb), hsubU b hb⟩ hab),
      map_zero := by
        funext i
        rw [hφ0]
        exact congrFun hwq i,
      mapsTo := fun t ht g hg ↦ by
        have hg' : rename Sum.inl g ∈ M.ideal := Ideal.mem_comap.1 (M.comap_eq.symm ▸ hg)
        have h := hφm (hsub ht) _ hg'
        rw [eval_rename] at h
        exact h }
  refine ⟨ν, fun f ↦ ?_⟩
  rw [hord f, hO n J M w (min r ε) φ hJ hdim1 hρ (hφd.mono hsub) (hφi.mono hsub) (fun t ht ↦ hφm (hsub ht)) hφ0]
  unfold branchOrder
  simp only [eval_rename]
  rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnChart.proof (hD : ComplexSets.DiscriminantCover.Statement) (hL : CutOffLimit.Statement) :
    StokesOnChart.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
      (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → chartInt J A f (vecCons g φ) = chartInt J A g (vecCons f φ) := by
    intro n d J A f g φ hJ hdim hAf hf hg hφ hc
    obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

    have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
      intro x hx hPx
      obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
      obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
      refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
      · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
        exact hw'.1
      · rintro x' hx' -
        rw [hZV] at hx'
        obtain ⟨w, hw, rfl⟩ := hx'
        rw [hAs w hw]
    obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
    obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
    refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
    obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
    obtain ⟨V, hV, hZV, hfV⟩ := hf
    have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
    refine (StokesOffDiscriminant.proof n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
      ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
    rw [hχ0 x hx, zero_mul]
  intro n d J A f g φ hJ hdim hAf hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J A f g φ hJ hdim hAf hf hg hφ hc
  · exact (key n d J A g f φ hJ hdim hAf hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserBranchSimpleZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserBranchSimpleZero.proof (hloc : UniformiserLocallyInjective.Statement)
    (hder : InjectiveHolomorphicDerivNeZero.Statement) : UniformiserBranchSimpleZero.Statement := by
  intro σ _ I w t r φ hI hic hdim ht hr hdiff hinj hmaps hw0
  have hball : ∀ {ρ : ℝ} {τ : ℂ}, τ ∈ Metric.ball (0 : ℂ) ρ →
      (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) ρ := by
    intro ρ τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  obtain ⟨U, hU, hUinj⟩ := hloc σ I w t hI hic hdim hwZ ht
  have hφc : ContinuousAt φ 0 :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds 0 hr)).continuousAt
  have hc1 : Continuous fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ) := continuous_pi fun _ ↦ continuous_id
  have hcont : ContinuousAt (fun τ : ℂ ↦ φ fun _ ↦ τ) 0 :=
    ContinuousAt.comp_of_eq (g := φ) (f := fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) hφc hc1.continuousAt rfl
  have hpre : (fun τ : ℂ ↦ φ fun _ ↦ τ) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds (by rw [← hw0] at hU; exact hU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hpre (Metric.ball_mem_nhds 0 hr))
  have hfd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) :=
    (differentiable_eval_pointLocal t).comp_differentiableOn (hdiff.comp
      (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn fun τ hτ ↦ hball (hεU hτ).2)
  have hfi : Set.InjOn (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) := by
    intro a ha b hb hab
    have hab' := hUinj ⟨hmaps (hball (hεU ha).2), (hεU ha).1⟩ ⟨hmaps (hball (hεU hb).2), (hεU hb).1⟩ hab
    exact congrFun (hinj (hball (hεU ha).2) (hball (hεU hb).2) hab') 0
  have hd := hder _ _ Metric.isOpen_ball hfd hfi 0 (Metric.mem_ball_self hε)
  have hf0 : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 0 := by
    change eval (φ 0) t = 0
    rw [hw0, htw]
  exact (analyticAt_eval_disc hr hdiff t).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hd

end GroundTheory.Heights₂.Heights
end

