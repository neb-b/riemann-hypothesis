module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0115
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGoodPointBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

theorem DivisorGoodPointBranches.proof : DivisorGoodPointBranches.Statement := by
  intro n d J u M q _hJ _hdim _hu hqJ hqu hreg hchart hdouble
  obtain ⟨A, O, V, g, -, hV, hqV, hg, hAg, hS⟩ := hreg
  obtain ⟨N₀, hN₀, hdbl⟩ := hdouble
  let F : Set (Fin n ⊕ Fin M.m → ℂ) :=
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}
  have hmemF : ∀ w, w ∈ F ↔ (w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q) :=
    fun w => Iff.rfl
  have hFfin : F.Finite := NormalModelFibre.fibre_finite M q
  obtain ⟨G, hGo, hGd⟩ := hFfin.t2_separation
  let _ : Fintype F := hFfin.fintype
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  have hbr : ∀ b : Fin (Fintype.card F), ∃ γ : VarBranch J (d + 1) q, ∃ ord : ℕ,
      (∃ U ∈ 𝓝 (e b : Fin n ⊕ Fin M.m → ℂ), ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G (e b), IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius ord ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
    intro b
    have hb := (hmemF _).1 (e b).2
    obtain ⟨r, φ, k, hr, hφd, hφi, hφ0, hφZ, hφU, hvan, hinjD⟩ := hchart (e b) hb.1 hb.2
    obtain ⟨γ, h⟩ := GoodPointBranch.exists_branch M hqu hV hqV hg hAg hS hN₀ hdbl hb.2 hr hφd hφi hφ0
      hφZ hφU hvan hinjD ((hGo _).2.mem_nhds (hGo _).1)
    exact ⟨γ, k, h⟩
  choose γ ord hcovw himg hslice hvan hbij using hbr
  refine ⟨Fintype.card F, γ, ord, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)),
    ?_, ?_, ?_, hvan, hbij⟩
  · choose U hU hUc using hcovw
    obtain ⟨N, hN, hNU⟩ := NormalModelFibre.eventually_mem_of_fibre_subset M (q := q)
      (isOpen_iUnion fun b => isOpen_interior (s := U b)) (fun w hw hwq => by
        obtain ⟨b, hb⟩ := e.surjective ⟨w, (hmemF w).2 ⟨hw, hwq⟩⟩
        refine mem_iUnion.2 ⟨b, mem_interior_iff_mem_nhds.2 ?_⟩
        have hbw : (e b : Fin n ⊕ Fin M.m → ℂ) = w := congrArg Subtype.val hb
        rw [← hbw]
        exact hU b)
    refine ⟨N, hN, fun x hx => ?_⟩
    obtain ⟨w, hw, rfl⟩ := NormalModelFibre.exists_mem_fibre M hx.1
    obtain ⟨b, hb⟩ := mem_iUnion.1 (hNU w hw hx.2)
    exact mem_iUnion.2 ⟨b, hUc b w ⟨hw, interior_subset hb⟩⟩
  · choose N' hN' hN'c using hslice
    exact ⟨⋂ b, N' b, Filter.iInter_mem.2 hN',
      fun x hx hxu b => hN'c b x ⟨hx.1, mem_iInter.1 hx.2 b⟩ hxu⟩
  · intro b b' hbb' x hx
    obtain ⟨hxN, w, ⟨hw, hwG⟩, rfl⟩ := himg b x hx.1
    obtain ⟨-, w', ⟨hw', hw'G⟩, hww'⟩ := himg b' _ hx.2
    have hne : w ≠ w' := by
      rintro rfl
      have hdisj : Disjoint (G (e b)) (G (e b')) :=
        hGd (e b).2 (e b').2 (fun h => hbb' (e.injective (Subtype.ext h)))
      exact Set.disjoint_left.1 hdisj hwG hw'G
    exact hdbl w hw w' hw' hww'.symm hxN hne

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPolyFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IsolatedFibreOpenPoly.full : IsolatedFibreOpenPoly.Statement :=
  IsolatedFibreOpenPoly.proof
    (IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric.proof
      (IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.equiv.mp ComplexSets.GenericProjectionFinite.full)
      IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCountPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem IsolatedPointsCountPrime.exists_dim_eq {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  have h1 := ringKrullDim_quotient_le J
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k => exact ⟨k, rfl⟩

theorem IsolatedPointsCountPrime.eval_aeval {n m : ℕ} (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (f : MvPolynomial (Fin m) ℂ) (x : Fin n → ℂ) :
    eval x (aeval Q f) = eval (fun i => eval x (Q i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p p' hp hp' => rw [map_add (f := _), map_add (f := _), hp, hp', map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

theorem IsolatedPointsCountPrime.exists_eval_ne_zero {d : ℕ} {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0)
    {w : Fin d → ℂ} {S : Set (Fin d → ℂ)} (hS : S ∈ 𝓝 w) : ∃ w' ∈ S, eval w' Δ ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hΔ
  refine funext_set (fun i => Metric.ball (w i) ε)
    (fun i => infinite_of_mem_nhds (w i) (Metric.ball_mem_nhds (w i) hε)) (fun y hy => ?_)
  rw [map_zero]
  refine h y (hball ?_)
  rw [ball_pi w hε]
  exact hy

theorem IsolatedPointsCountPrime.proof (hOpen : IsolatedFibreOpenPoly.Statement)
    (hDom : DominantFibreBound.Statement) (hDim : ImageDimLe.Statement) :
    IsolatedPointsCountPrime.Statement := by
  classical
  intro n m P hP Q

  have hKp : (RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))).IsPrime := RingHom.ker_isPrime _
  set K := RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q)) with hK
  obtain ⟨d, hd⟩ := IsolatedPointsCountPrime.exists_dim_eq P
  obtain ⟨r, hr⟩ := IsolatedPointsCountPrime.exists_dim_eq K
  have hrd : r ≤ d := by
    have h := hDim n m P Q hP
    rw [← hK, hr, hd] at h
    exact_mod_cast h
  obtain ⟨B, hB⟩ := (GenericProjectionFinite.full m r K hKp hr).2.1
  have hfib := FibreBound.full m r K B hKp hr hB

  set Qm : (Fin n → ℂ) → (Fin m → ℂ) := fun x i => eval x (Q i) with hQm
  have hQZ : ∀ x ∈ zeroSet P, Qm x ∈ zeroSet K := by
    intro x hx f hf
    have hf' : aeval Q f ∈ P := by
      rw [hK, RingHom.mem_ker] at hf
      simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hf
    rw [← IsolatedPointsCountPrime.eval_aeval]
    exact hx _ hf'
  have hQc : Continuous Qm := continuous_pi fun i => MvPolynomial.continuous_eval _

  set q : Fin r → MvPolynomial (Fin n) ℂ := fun i => aeval Q (linPoly B i) with hq
  have hqe : ∀ x, (fun i => eval x (q i)) = B.mulVec (Qm x) := by
    intro x
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, IsolatedPointsCountPrime.eval_aeval, linPoly, map_sum, map_mul, eval_C, eval_X,
      Matrix.mulVec, dotProduct, hQm]

  have step1 : ∀ z x, x ∈ isolatedFibrePts P Q z →
      ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (q i) = eval x (q i)) → x' = x := by
    rintro z x ⟨hxP, hxQ, V, hV, hiso⟩
    have hQx : Qm x = z := funext hxQ
    have hfin : (GroundTheory.Heights₂.Heights.ComplexSets.fibre K B (B.mulVec z) \ {z}).Finite := (hfib (B.mulVec z)).2.1.subset Set.sdiff_subset
    have hO : (GroundTheory.Heights₂.Heights.ComplexSets.fibre K B (B.mulVec z) \ {z})ᶜ ∈ 𝓝 (Qm x) := by
      rw [hQx]
      exact hfin.isClosed.compl_mem_nhds fun h => h.2 rfl
    refine ⟨V ∩ Qm ⁻¹' (GroundTheory.Heights₂.Heights.ComplexSets.fibre K B (B.mulVec z) \ {z})ᶜ,
      Filter.inter_mem hV (hQc.continuousAt.preimage_mem_nhds hO), ?_⟩
    rintro x' ⟨hx'P, hx'V, hx'O⟩ hx'q
    refine hiso x' ⟨hx'P, hx'V⟩ fun i => congrFun (?_ : Qm x' = z) i
    have h1 : B.mulVec (Qm x') = B.mulVec z := by
      rw [← hqe, ← hQx, ← hqe]
      funext i
      exact hx'q i
    by_contra hne
    exact hx'O ⟨⟨hQZ x' hx'P, h1⟩, hne⟩
  rcases lt_or_eq_of_le hrd with hlt | rfl
  ·
    refine ⟨0, fun z => ?_⟩
    suffices isolatedFibrePts P Q z = ∅ by simp [this]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨W, hW, hiso⟩ := step1 z x hx
    set p : Fin d → MvPolynomial (Fin n) ℂ := fun i => if h : (i : ℕ) < r then q ⟨i, h⟩ else 0 with hp
    have hiso' : ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x :=
      ⟨W, hW, fun x' hx' h => hiso x' hx' fun i => by
        simpa [hp, i.isLt] using h ⟨i, i.isLt.trans hlt⟩⟩
    have himg := hOpen n d P p x hP hd hx.1 hiso' Set.univ Filter.univ_mem
    set px : Fin d → ℂ := fun i => eval x (p i) with hpx
    set j : Fin d := ⟨r, hlt⟩
    have hsub : (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ Set.univ) ⊆
        {w | w j = 0} := by
      rintro _ ⟨y, -, rfl⟩
      simp [hp, j]
    have hc : Continuous fun t : ℂ => Function.update px j t := continuous_const.update j continuous_id
    have h1 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ∈ 𝓝 (px j) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      rw [Function.update_eq_self]
      exact Filter.mem_of_superset himg hsub
    have h2 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ⊆ {0} := by
      intro t ht
      simpa using ht
    exact (infinite_of_mem_nhds (px j) (Filter.mem_of_superset h1 h2)) (Set.finite_singleton 0)
  ·
    have hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval q)) := by
      have hcomp : aeval q = (aeval Q).comp (pullback B) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp [hq, pullback]
      intro a b hab
      apply hB.injective
      simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab ⊢
      rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub] at hab
      rw [hK, RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hab
    obtain ⟨e, Δ, hΔ, hbound⟩ := hDom n r P q hP hd hinj
    refine ⟨e, fun z => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
    have htc' : t.encard = ((e + 1 : ℕ) : ℕ∞) := by rw [htc]; push_cast; rfl
    have htf : t.Finite := Set.finite_of_encard_eq_coe htc'
    obtain ⟨U, hUo, hUd⟩ := htf.t2_separation
    have hw : ∀ x ∈ t, (fun x' : Fin n → ℂ => fun i => eval x' (q i)) '' (zeroSet P ∩ U x) ∈
        𝓝 (B.mulVec z) := by
      intro x hx
      have hx' := hts hx
      obtain ⟨W, hW, hiso⟩ := step1 z x hx'
      have h := hOpen n r P q x hP hd hx'.1 ⟨W, hW, hiso⟩ (U x) ((hUo x).2.mem_nhds (hUo x).1)
      have e1 : (fun i => eval x (q i)) = B.mulVec z := by
        rw [hqe]
        congr 1
        exact funext hx'.2.1
      rwa [e1] at h
    have hI := (Filter.biInter_mem htf).2 hw
    obtain ⟨w', hw'I, hΔw'⟩ := IsolatedPointsCountPrime.exists_eval_ne_zero hΔ hI
    have hpick : ∀ x ∈ t, ∃ y, y ∈ zeroSet P ∩ U x ∧ (fun i => eval y (q i)) = w' :=
      fun x hx => Set.mem_iInter₂.1 hw'I x hx
    choose! g hg1 hg2 using hpick
    have hinjg : Set.InjOn g t := by
      intro x hx y hy hxy
      by_contra hne
      refine Set.disjoint_left.1 (hUd hx hy hne) (hg1 x hx).2 ?_
      rw [hxy]
      exact (hg1 y hy).2
    have himg : g '' t ⊆ {x | x ∈ zeroSet P ∧ ∀ i, eval x (q i) = w' i} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hg1 x hx).1, fun i => congrFun (hg2 x hx) i⟩
    have hle := (Set.encard_le_encard himg).trans (hbound w' hΔw')
    rw [hinjg.encard_image, htc'] at hle
    have hle' : e + 1 ≤ e := by exact_mod_cast hle
    omega

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianRankOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem JacobianRankOffHypersurface.eval_pderiv_sum_mul {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (c g : ι → MvPolynomial σ ℂ) (hg : ∀ k, eval w (g k) = 0) (x : σ) :
    eval w (pderiv x (∑ k, c k * g k)) = ∑ k, eval w (c k) * eval w (pderiv x (g k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Derivation.leibniz, smul_eq_mul, hg]

theorem JacobianRankOffHypersurface.grad_mem_span {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (a p : MvPolynomial σ ℂ) (c g : ι → MvPolynomial σ ℂ) (hsum : ∑ k, c k * g k = a * p)
    (hg : ∀ k, eval w (g k) = 0) (hp : eval w p = 0) (ha : eval w a ≠ 0) :
    (fun x ↦ eval w (pderiv x p)) ∈
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (g k))) := by
  have key : (fun x ↦ eval w (pderiv x p)) =
      (eval w a)⁻¹ • ∑ k, eval w (c k) • (fun x ↦ eval w (pderiv x (g k))) := by
    funext x
    have h1 := congrArg (fun f ↦ eval w (pderiv x f)) hsum
    simp only [JacobianRankOffHypersurface.eval_pderiv_sum_mul w c g hg x, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, hp, zero_mul, add_zero] at h1
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1]
    rw [inv_mul_cancel_left₀ ha]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem JacobianRankOffHypersurface.finrank_of_generators {σ ι : Type*} [Fintype σ] [Fintype ι]
    (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ) (t : MvPolynomial σ ℂ)
    (hqQ : ∀ j, q j ∈ Q) (hgen : ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q))
    (f : ι → MvPolynomial σ ℂ) (s δ : MvPolynomial σ ℂ) (hfQ : ∀ k, f k ∈ Q)
    (hs : ∀ p ∈ Q, s * p ∈ Ideal.span (Set.range f))
    (hδ : ∀ w : σ → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (f k)))
    (hcard : Fintype.card ι + d = Fintype.card σ) (w : σ → ℂ) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q)
    (hμ : eval w (s * t * δ) ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j)))) + d =
      Fintype.card σ := by
  have hw' : ∀ p ∈ Q, eval w p = 0 := hw
  simp only [map_mul, mul_ne_zero_iff] at hμ
  obtain ⟨⟨hs0, ht0⟩, hδ0⟩ := hμ
  have heq : Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j))) =
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (f k))) := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs (q j) (hqQ j))
      exact JacobianRankOffHypersurface.grad_mem_span w s (q j) c f hc (fun k ↦ hw' _ (hfQ k))
        (hw' _ (hqQ j)) hs0
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro k
      obtain ⟨i, hi⟩ := hgen (f k) (hfQ k)
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
      refine JacobianRankOffHypersurface.grad_mem_span w (t ^ i) (f k) c q hc (fun j ↦ hw' _ (hqQ j))
        (hw' _ (hfQ k)) ?_
      rw [map_pow]
      exact pow_ne_zero _ ht0
  rw [heq, finrank_span_eq_card (hδ w hδ0)]
  exact hcard

theorem JacobianRankOffHypersurface.exists_fin (hF : FrameJacobianGeneric.Statement) {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s δ : MvPolynomial (Fin n) ℂ),
      Fintype.card {j // j ∉ I₀} + d = n ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ δ ∉ J ∧
        (∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)) ∧
        ∀ w : Fin n → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k l ↦ eval w (pderiv l (f k)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, s, hcard, hfJ, hsJ, hδJ, hgen⟩ := hF n d J hJ hd b
  refine ⟨I₀, f, s, frameJacobianDet b I₀ f, ?_, hfJ, hsJ, hδJ, hgen, ?_⟩
  · have h1 : Fintype.card {j // j ∉ I₀} = n - I₀.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have h2 : I₀.card ≤ n := (Finset.card_le_univ I₀).trans_eq (Fintype.card_fin n)
    omega
  · intro w hw
    let M : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun j l ↦ b j l
    have hdet := hw
    rw [frameJacobianDet, RingHom.map_det] at hdet
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hrows : (fun k ↦ ((eval w).mapMatrix (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) =
        (Matrix.mulVecLin M) ∘ fun k l ↦ eval w (pderiv l (f k)) := by
      funext k j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [frameDeriv, M, Matrix.mulVec, dotProduct, map_sum]
    change LinearIndependent ℂ (fun k ↦ ((eval w).mapMatrix
      (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) at hli
    rw [hrows] at hli
    exact hli.of_comp _

theorem JacobianRankOffHypersurface.proof_of_frame (hF : FrameJacobianGeneric.Statement) :
    JacobianRankOffHypersurface.Statement := by
  intro σ _ Q d r q t hQ hd hqQ htQ hgen
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval x (φ p) = eval (x ∘ e.symm) p := fun x p ↦ by
    simp [φ, eval_rename]
  have hJd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    rw [← hd]
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q J φ.toRingEquiv.symm ?_)).symm
    exact (Ideal.map_symm (I := Q) φ.toRingEquiv).symm
  obtain ⟨I₀, f, s, δ, hcard, hfJ, hsJ, hδJ, hsgen, hlin⟩ :=
    JacobianRankOffHypersurface.exists_fin hF J hJ hJd
  have hfQ : ∀ k, φ (f k) ∈ Q := fun k ↦ Ideal.mem_comap.mp (hfJ k)
  have hsQ : φ s ∉ Q := fun h ↦ hsJ (Ideal.mem_comap.mpr h)
  have hδQ : φ δ ∉ Q := fun h ↦ hδJ (Ideal.mem_comap.mpr h)
  have hs : ∀ p ∈ Q, φ s * p ∈ Ideal.span (Set.range fun k ↦ φ (f k)) := by
    intro p hp
    have hp' : φ.symm p ∈ J := Ideal.mem_comap.mpr (by rwa [AlgEquiv.apply_symm_apply])
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hsgen _ hp')
    refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun k ↦ φ (c k), ?_⟩
    have := congrArg φ hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, AlgEquiv.apply_symm_apply] at this
    simpa [map_mul] using this
  have hδ : ∀ w : σ → ℂ, eval w (φ δ) ≠ 0 →
      LinearIndependent ℂ fun k x ↦ eval w (pderiv x (φ (f k))) := by
    intro w hw
    rw [hφ] at hw
    have hL := (hlin _ hw).map' (LinearMap.funLeft ℂ ℂ e)
      (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _ e.surjective))
    have hfam : (fun k x ↦ eval w (pderiv x (φ (f k)))) =
        (LinearMap.funLeft ℂ ℂ e) ∘ fun k l ↦ eval (w ∘ e.symm) (pderiv l (f k)) := by
      funext k x
      simp only [Function.comp_apply, LinearMap.funLeft_apply]
      have hx : pderiv x (φ (f k)) = φ (pderiv (e x) (f k)) := by
        have := pderiv_rename (R := ℂ) e.symm.injective (e x) (f k)
        rw [Equiv.symm_apply_apply] at this
        exact this
      rw [hx, hφ]
    rw [hfam]
    exact hL
  have hμQ : φ s * t * φ δ ∉ Q := by
    intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hsQ h
      · exact htQ h
    · exact hδQ h
  exact ⟨φ s * t * φ δ, hμQ, fun w hw hμ ↦
    JacobianRankOffHypersurface.finrank_of_generators Q d r q t hqQ hgen (fun k ↦ φ (f k)) (φ s) (φ δ) hfQ hs hδ
      hcard w hw hμ⟩

theorem JacobianRankOffHypersurface.proof : JacobianRankOffHypersurface.Statement :=
  JacobianRankOffHypersurface.proof_of_frame
    (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)

end

end GroundTheory.Heights₂.Heights
end

