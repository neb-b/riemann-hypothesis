module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem le_originIdeal_of_isHomogeneous {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hne : I ≠ ⊤) : I ≤ originIdeal n := by
  intro f hf
  rw [originIdeal_eq_ker, RingHom.mem_ker]
  by_contra h0
  have h1 : homogeneousComponent 0 f ∈ I := by
    have := hI 0 hf
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin n) ℂ) f 0 : MvPolynomial (Fin n) ℂ)
      = homogeneousComponent 0 f from decomposition.decompose'_apply _ _] at this
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h1
  exact hne (I.eq_top_of_isUnit_mem h1 (isUnit_iff_ne_zero.2 h0 |>.map C))

theorem isMaximal_of_isPrime_of_quotient_dim_le_zero {R : Type*} [CommRing R] {K Q : Ideal R}
    (hK : ringKrullDim (R ⧸ K) ≤ 0) (hQ : Q.IsPrime) (hKQ : K ≤ Q) : Q.IsMaximal := by
  have : Ring.KrullDimLE 0 (R ⧸ K) := Ring.krullDimLE_iff.2 (by exact_mod_cast hK)
  have hsurj := Ideal.Quotient.mk_surjective (I := K)
  have : (Q.map (Ideal.Quotient.mk K)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
  have hmax := Ideal.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk K))
  have := Ideal.comap_isMaximal_of_surjective _ hsurj (K := Q.map (Ideal.Quotient.mk K))
  rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    sup_eq_left.2 hKQ] at this

theorem HomogDimZeroPow.proof : HomogDimZeroPow.Statement := by
  intro n K hK hdim
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hKP, hP⟩ => ?_
  set 𝒜 := homogeneousSubmodule (Fin n) ℂ
  have hcP : (P.homogeneousCore 𝒜).toIdeal.IsPrime := hP.homogeneousCore
  have hKc : K ≤ (P.homogeneousCore 𝒜).toIdeal := by
    rw [← hK.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hKP
  have hmax := isMaximal_of_isPrime_of_quotient_dim_le_zero hdim hcP hKc
  have hle := le_originIdeal_of_isHomogeneous (P.homogeneousCore 𝒜).isHomogeneous hmax.ne_top
  exact ((hmax.eq_of_le (originIdeal_isMaximal n).ne_top hle).symm.le).trans
    (Ideal.toIdeal_homogeneousCore_le 𝒜 P)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleFiniteGermProjectionOpenAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

theorem IrreducibleFiniteGermProjectionOpenAt.proof
    (hpts : IrreducibleGermPointsOffDiscriminant.Statement) :
    IrreducibleFiniteGermProjectionOpenAt.Statement := by
  intro σ _ X x d A hX hirr hiso hinj V hV
  obtain ⟨δ, hδa, hδne, hδpts⟩ := hpts σ X x d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hNo.mem_nhds hxN))
  set r' := r / 2 with hr'
  have hr'0 : 0 < r' := by positivity
  have hcb : closedBall x r' ⊆ V ∩ N := (closedBall_subset_ball (by linarith)).trans hrV

  set K : Set (σ → ℂ) := closedBall x r' ∩ ⋂ i, (closedBall x r' ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x r').of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono (hcb.trans inter_subset_right)).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKV : A '' K ⊆ A '' (X ∩ V) := by
    refine image_mono fun z hz => ?_
    have hzN : z ∈ N := (hcb hz.1).2
    have hzX : z ∈ X ∩ N := by
      rw [hXN]
      exact ⟨hzN, fun i => by simpa using ((mem_iInter.mp hz.2) i).2⟩
    exact ⟨hzX.1, (hcb hz.1).1⟩
  have hball : ∀ z ∈ X ∩ ball x r', z ∈ K := by
    intro z hz
    have hzcb : z ∈ closedBall x r' := ball_subset_closedBall hz.2
    have hzN : z ∈ X ∩ N := ⟨hz.1, (hcb hzcb).2⟩
    rw [hXN] at hzN
    exact ⟨hzcb, mem_iInter.mpr fun i => ⟨hzcb, by simpa using hzN.2 i⟩⟩

  obtain ⟨ε₁, hε₁, hε₁a⟩ := hδa.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hε₂p⟩ := Metric.eventually_nhds_iff.mp (hδpts (ball x r') (ball_mem_nhds x hr'0))
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ (ball (A x) ε) := hε₁a.mono (ball_subset_ball (min_le_left _ _))
  have hsub : {y | y ∈ ball (A x) ε ∧ δ y ≠ 0} ⊆ A '' K := by
    rintro y ⟨hy, hδy⟩
    have hy2 : dist y (A x) < ε₂ := lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)
    obtain ⟨x', hx', rfl⟩ := hε₂p hy2 hδy
    exact ⟨x', hball x' hx', rfl⟩
  have hD : ball (A x) ε ⊆ A '' K := by
    intro y hy
    refine (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsub (mem_closure_iff_frequently.mpr ?_)
    intro hev
    have hev' : δ =ᶠ[𝓝 y] 0 := by
      filter_upwards [hev, isOpen_ball.mem_nhds hy] with z hz hzD
      by_contra hz0
      exact hz ⟨hzD, hz0⟩
    have hzero := hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (A x) ε).isPreconnected hy hev'
    apply hδne
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hzero hz
  exact Filter.mem_of_superset (ball_mem_nhds (A x) hε) (hD.trans hKV)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem IrreducibleGermComplementConnected.proof (hdense : RegularLocusDense.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement)
    (hzeros : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermComplementConnected.Statement := by
  intro σ _ X w h hX hirr hh hnot U hU
  obtain ⟨N, hNo, hwN, hN⟩ := hdense σ X w hX
  have hU' : U ∩ N ∩ {z | AnalyticAt ℂ h z} ∈ 𝓝 w :=
    inter_mem (inter_mem hU (hNo.mem_nhds hwN)) hh.eventually_analyticAt
  obtain ⟨B, hBo, hwB, hBU, hR⟩ := hconn σ X w hX hirr _ hU'
  have hBh : ∀ z ∈ B, AnalyticAt ℂ h z := fun z hz => (hBU hz).2
  have hcl : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hN B hBo fun z hz => (hBU hz).1.2

  have hcl' : (X ∩ B) \ {z | h z = 0} ⊆ closure (regLocus (X ∩ B) \ {z | h z = 0}) := by
    rintro z ⟨hzXB, hz0⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have hne : {y | h y ≠ 0} ∈ 𝓝 z := (hBh z hzXB.2).continuousAt.eventually_ne hz0
    obtain ⟨y, ⟨hyt, hyh⟩, hyR⟩ := mem_closure_iff_nhds.1 (hcl hzXB) _ (inter_mem ht hne)
    exact ⟨y, hyt, hyR, hyh⟩

  have hex : ∃ x ∈ regLocus (X ∩ B), h x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    filter_upwards [hBo.mem_nhds hwB] with z hzB hzX
    by_contra hz0
    obtain ⟨y, hyR, hyh⟩ := closure_nonempty_iff.1 ⟨z, hcl' ⟨⟨hzX, hzB⟩, hz0⟩⟩
    exact hyh (hcon y hyR)
  have hRc : IsPreconnected (regLocus (X ∩ B) \ {z | h z = 0}) :=
    hzeros σ _ h hR (fun x hx => isRegularPointOf_regLocus hx)
      (fun x hx => hBh x (regLocus_subset _ hx).2) hex
  exact ⟨B, hBo, hwB, fun z hz => (hBU hz).1.1,
    hRc.subset_closure (Set.sdiff_subset_sdiff_left (regLocus_subset _)) hcl'⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermProjectionImageNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Set

theorem le_of_isolated_fibres (hfi : HolomorphicFibreInfinite.Statement) {e d : ℕ} {O : Set (Fin e → ℂ)}
    {φ : (Fin e → ℂ) → Fin d → ℂ} (hO : IsOpen O) (hne : O.Nonempty) (hφ : DifferentiableOn ℂ φ O)
    (hiso : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → φ v = φ t → v = t) : e ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hy0)
  obtain ⟨y, hy⟩ := hfi e d (ball y0 ρ) φ hlt isOpen_ball ⟨y0, mem_ball_self hρ⟩
    (hφ.mono (ball_subset_closedBall.trans hρO))
  obtain ⟨p, hpK, hpacc⟩ := hy.exists_accPt_of_subset_isCompact (isCompact_closedBall y0 ρ)
    (fun t ht => ball_subset_closedBall ht.1)
  have hpO : p ∈ O := hρO hpK
  have hcl : p ∈ closure {t | t ∈ ball y0 ρ ∧ φ t = y} := mem_closure_iff_nhds.2 fun U hU => by
    obtain ⟨q, hq, -⟩ := accPt_iff_nhds.1 hpacc U hU
    exact ⟨q, hq⟩
  have hφp : φ p = y := by
    have h1 := mem_closure_image ((hφ p hpO).differentiableAt (hO.mem_nhds hpO)).continuousAt hcl
    have h2 : φ '' {t | t ∈ ball y0 ρ ∧ φ t = y} ⊆ {y} := by
      rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    simpa using closure_mono h2 h1
  obtain ⟨W, hW, hWiso⟩ := hiso p hpO
  obtain ⟨q, ⟨hqW, hqB, hqy⟩, hqp⟩ := accPt_iff_nhds.1 hpacc W hW
  exact hqp (hWiso q hqW (hρO (ball_subset_closedBall hqB)) (hqy.trans hφp.symm))

theorem IrreducibleGermProjectionImageNear.proof (hdim : IrreducibleGermRegularDimGe.Statement)
    (hisoN : IsolatedFibreNear.Statement) (hreg : RegularLocusDense.Statement)
    (hopen : HolomorphicIsolatedFibreOpen.Statement) (hfi : HolomorphicFibreInfinite.Statement) :
    IrreducibleGermProjectionImageNear.Statement := by
  intro σ _ X w d A hX hirr hfin hnd
  obtain ⟨N1, hN1, hdimN⟩ := hdim σ X w d A hX hirr hfin hnd
  obtain ⟨N2, hN2, hisoX⟩ := hisoN σ X w d A hX hfin
  obtain ⟨N3, hN3o, hwN3, hdense⟩ := hreg σ X w hX
  refine ⟨interior (N1 ∩ N2) ∩ N3,
    inter_mem (interior_mem_nhds.2 (inter_mem hN1 hN2)) (hN3o.mem_nhds hwN3), ?_⟩
  have hBo : IsOpen (interior (N1 ∩ N2) ∩ N3) := isOpen_interior.inter hN3o
  rintro x ⟨hxX, hxB⟩ h hh hvan
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨V, hV, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hvan
  set V1 := V ∩ (interior (N1 ∩ N2) ∩ N3) ∩ A ⁻¹' ball (A x) ε with hV1
  have hV1o : IsOpen V1 := (hVo.inter hBo).inter (isOpen_ball.preimage A.continuous)
  have hxV1 : x ∈ V1 := ⟨⟨hxV, hxB⟩, by exact Set.mem_preimage.mpr (mem_ball_self hε)⟩
  have hcl := hdense V1 hV1o (fun z hz => hz.1.2.2) ⟨hxX, hxV1⟩
  obtain ⟨r, hr⟩ : (regLocus (X ∩ V1)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, closure_empty] at hcl
    exact hcl
  obtain ⟨hrX, e, A', O, V', g, hO, hV', hrV', hg, hA'g, hXV'⟩ := hr
  have hgX : ∀ t ∈ O, g t ∈ X ∩ V1 := fun t ht => by
    have : g t ∈ X ∩ V1 ∩ V' := hXV' ▸ mem_image_of_mem g ht
    exact this.1
  have hN12 : ∀ z ∈ V1, z ∈ N1 ∩ N2 := fun z hz => interior_subset hz.1.2.1
  have hchart : X ∩ (V1 ∩ V') = g '' O := by rw [← hXV']; exact (inter_assoc X V1 V').symm
  have hde : d ≤ e := hdimN r ⟨hrX.1, (hN12 r hrX.2).1⟩ e A' O (V1 ∩ V') g hO (hV1o.inter hV')
    ⟨hrX.2, hrV'⟩ hg hA'g hchart
  have hφ : DifferentiableOn ℂ (fun y => A (g y)) O :=
    A.differentiable.comp_differentiableOn hg.differentiableOn
  have hisoC : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → A (g v) = A (g t) → v = t := by
    intro t ht
    obtain ⟨W, hW, hiW⟩ := hisoX (g t) ⟨(hgX t ht).1, (hN12 _ (hgX t ht).2).2⟩
    refine ⟨g ⁻¹' W, (hg t ht).continuousAt.preimage_mem_nhds hW, fun v hvW hvO hv => ?_⟩
    have hgv := hiW (g v) ⟨(hgX v hvO).1, hvW⟩ hv
    rw [← hA'g v hvO, ← hA'g t ht, hgv]
  obtain ⟨y0, hy0O, hy0r⟩ : r ∈ g '' O := hXV' ▸ ⟨hrX, hrV'⟩
  have hed : e ≤ d := le_of_isolated_fibres hfi hO ⟨y0, hy0O⟩ hφ hisoC
  obtain rfl : e = d := le_antisymm hed hde
  have hop := hopen e O (fun y => A (g y)) y0 hO hy0O hφ (hisoC y0 hy0O) O (hO.mem_nhds hy0O)
  have hzero : ∀ y ∈ (fun y => A (g y)) '' O, h y = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hV (hgX t ht).2.1.1 (hgX t ht).1
  have hAr : A (g y0) ∈ ball (A x) ε := (hgX y0 hy0O).2.2
  have hEq : EqOn h 0 (ball (A x) ε) :=
    hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hAr
      (Filter.mem_of_superset hop fun y hy => hzero y hy)
  filter_upwards [ball_mem_nhds (A x) hε] with y hy using hEq hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem exists_minimalPrime_mem_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by
  have hJ : J ≤ RingHom.ker (eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJ
  exact ⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩

theorem mem_isolatedFibrePts_of_le {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by
  obtain ⟨-, hQ, V, hV, hiso⟩ := hx
  exact ⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩

theorem encard_biUnion_finset_le {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add_right ih _)

theorem IsolatedPointsCount.proof (hPrime : IsolatedPointsCountPrime.Statement) :
    IsolatedPointsCount.Statement := by
  classical
  intro n m J Q
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hN : ∀ P ∈ J.minimalPrimes, ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N :=
    fun P hP => hPrime n m P hP.1.1 Q
  choose! N hN using hN
  refine ⟨∑ P ∈ hfin.toFinset, N P, fun z => ?_⟩
  have hsub : isolatedFibrePts J Q z ⊆ ⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_minimalPrime_mem_zeroSet J hx.1
    exact Set.mem_biUnion (hfin.mem_toFinset.2 hP) (mem_isolatedFibrePts_of_le hP.1.2 Q z hx hxP)
  calc (isolatedFibrePts J Q z).encard
      ≤ (⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z).encard := Set.encard_le_encard hsub
    _ ≤ ∑ P ∈ hfin.toFinset, (isolatedFibrePts P Q z).encard := encard_biUnion_finset_le _ _
    _ ≤ ∑ P ∈ hfin.toFinset, ((N P : ℕ) : ℕ∞) :=
        Finset.sum_le_sum fun P hP => hN P (hfin.mem_toFinset.1 hP) z
    _ = ((∑ P ∈ hfin.toFinset, N P : ℕ) : ℕ∞) := by push_cast; rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem leadForm_ne_zero {f : MvPolynomial (Fin n) ℂ} (hf : f ≠ 0) : leadForm f ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => m.sum fun _ e => e)
  intro h0
  have hc := congrArg (AddMonoidAlgebra.coeff · d) h0
  rw [leadForm, coeff_homogeneousComponent] at hc
  rw [if_pos (by rw [totalDegree, hdeg]; rfl)] at hc
  apply (mem_support_iff.mp hd)
  simpa [AddMonoidAlgebra.coeff] using hc

theorem vars_leadForm_subset (f : MvPolynomial (Fin n) ℂ) : (leadForm f).vars ⊆ f.vars := by
  intro i hi
  rw [mem_vars_iff_mem_support] at hi ⊢
  obtain ⟨d, hd, hid⟩ := hi
  refine ⟨d, ?_, hid⟩
  rw [mem_support_iff, leadForm, coeff_homogeneousComponent] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

theorem aeval_mk_X (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (q : MvPolynomial u ℂ) :
    aeval (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) q =
      Ideal.Quotient.mk I (rename Subtype.val q) := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [aeval_C, rename_C]; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem algebraicIndependent_mk_X_iff (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n)) :
    AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) ↔
      ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ I → q = 0 := by
  rw [algebraicIndependent_iff]
  simp only [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem]

theorem rename_mem_of_leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (h : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ leadIdeal J → q = 0)
    (q : MvPolynomial u ℂ) (hq : rename Subtype.val q ∈ J) : q = 0 := by
  by_contra hq0
  have hf : rename Subtype.val q ≠ 0 := by
    rwa [Ne, ← map_zero (rename (Subtype.val : u → Fin n)),
      (rename_injective _ Subtype.val_injective).eq_iff]
  have hvars : ((leadForm (rename Subtype.val q)).vars : Set (Fin n)) ⊆
      Set.range (Subtype.val : u → Fin n) := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := mem_vars_rename _ _ (vars_leadForm_subset _ hi)
    exact ⟨j, rfl⟩
  obtain ⟨r, hr⟩ := exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective hvars
  have hr0 : r = 0 := h r (hr ▸ Ideal.subset_span ⟨_, hq, rfl⟩)
  exact leadForm_ne_zero hf (by rw [← hr, hr0, map_zero])

theorem quotient_dim_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

theorem exists_vars_isTranscendenceBasis (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime] :
    ∃ u : Set (Fin n), AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk P (X (i : Fin n))) ∧
      Cardinal.mk u = Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set x : Fin n → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (X i) with hx
  have hrange : Set.range x = Ideal.Quotient.mkₐ ℂ P '' Set.range X := by
    rw [← Set.range_comp]; rfl
  have hadj : Algebra.adjoin ℂ (Set.range x) = ⊤ := by
    rw [hrange, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℂ P
  have _ : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range x)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    ⟨fun a => isAlgebraic_algebraMap (R := Algebra.adjoin ℂ (Set.range x))
      (⟨a, hadj ▸ Algebra.mem_top⟩ : Algebra.adjoin ℂ (Set.range x))⟩
  have _ := (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Fin n) ℂ ⧸ P)).mpr
    (algebraMap ℂ _).injective
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range x)
  obtain ⟨u, hu, hinj⟩ := Set.exists_image_eq_injOn_of_subset_range hts
  let g : u → t := fun i => ⟨x i, hu ▸ Set.mem_image_of_mem x i.2⟩
  have hg : Function.Injective g := fun i j hij =>
    Subtype.ext (hinj i.2 j.2 (congrArg Subtype.val hij))
  refine ⟨u, ht.1.comp g hg, ?_⟩
  rw [← ht.cardinalMk_eq_trdeg, ← hu, Cardinal.mk_image_eq_of_injOn _ _ hinj]

theorem LeadIdealDim.proof : LeadIdealDim.Statement := by
  intro n J
  apply quotient_dim_le_of_minimalPrimes
  intro P hP
  have _ : P.IsPrime := hP.1.1
  obtain ⟨u, hu, hcard⟩ := exists_vars_isTranscendenceBasis P
  have hJ : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ J → q = 0 :=
    rename_mem_of_leadIdeal J u fun q hq => (algebraicIndependent_mk_X_iff P u).mp hu q (hP.1.2 hq)

  let M : Submonoid (MvPolynomial (Fin n) ℂ) :=
    (nonZeroDivisors (MvPolynomial u ℂ)).map (rename (R := ℂ) (Subtype.val : u → Fin n))
  have hdis : Disjoint (J : Set (MvPolynomial (Fin n) ℂ)) M := by
    rw [Set.disjoint_left]
    rintro _ hJf ⟨q, hq, rfl⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hq) (hJ q hJf)
  obtain ⟨Q, hQ, hJQ, hQM⟩ := Ideal.exists_le_prime_disjoint J M hdis
  have hQu : AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk Q (X (i : Fin n))) := by
    rw [algebraicIndependent_mk_X_iff]
    intro q hq
    by_contra hq0
    exact Set.disjoint_left.mp hQM hq ⟨q, mem_nonZeroDivisors_of_ne_zero hq0, rfl⟩
  obtain ⟨a, haP, htP⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ P)
  obtain ⟨b, hbQ, htQ⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ Q)
  have hab : a ≤ b := by
    have h := hQu.cardinalMk_le_trdeg
    rw [hcard, htP, htQ] at h
    exact_mod_cast h
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = a := haP
    _ ≤ b := by exact_mod_cast hab
    _ = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) := hbQ.symm
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJQ) (Ideal.Quotient.factor_surjective hJQ)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

