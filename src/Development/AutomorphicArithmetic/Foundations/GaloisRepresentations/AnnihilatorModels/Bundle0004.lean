module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGaussLin
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.gaussLin_of :
    GaussLin := by
  intro A ι _ c s hs hc
  by_contra hc0
  have hmem : ∀ a : A, a ∈ (Submodule.span A {c}).annihilator ↔ a * c = 0 := by
    intro a
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hIt : (Submodule.span A {c}).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1:A) ∈ (Submodule.span A {c}).annihilator := by
      rw [h]; exact Submodule.mem_top
    rw [hmem, one_mul] at h1
    exact hc0 h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hIt
  haveI := hM
  letI := Ideal.Quotient.field M
  have hprod : MvPolynomial.map (Ideal.Quotient.mk M) s.prod = 0 := by
    ext m
    change (MvPolynomial.map (Ideal.Quotient.mk M) s.prod).coeff m = 0
    rw [MvPolynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    apply hIM
    rw [hmem, mul_comm, ← MvPolynomial.coeff_C_mul, hc]
    rfl
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨p, hp, hp0⟩ := hprod
  obtain ⟨m, hm⟩ := hs p hp
  have h2 := congrArg (AddMonoidAlgebra.coeff · m) hp0
  rw [MvPolynomial.coeff_map, hm, map_one, MvPolynomial.coeff_zero] at h2
  exact one_ne_zero h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenChart
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genChart_of :
    GenChart := by
  intro Y π U hU V _ _ f hmin
  set πU := Y.presheaf.map (homOfLE le_top).op π with hπU
  let P : PrimeSpectrum Γ(Y, U) := ⟨Ideal.comap f (IsLocalRing.maximalIdeal V), inferInstance⟩
  have hx : ptOf hU V f (IsLocalRing.closedPoint V) = hU.fromSpec P := rfl
  have hinU : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ U := by
    intro q
    have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  have hmem : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ Y.basicOpen π ↔ πU ∉ q.asIdeal := by
    intro q
    have h1 : q ∈ PrimeSpectrum.basicOpen πU ↔ hU.fromSpec q ∈ Y.basicOpen πU := by
      rw [← hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← PrimeSpectrum.mem_basicOpen, h1, hπU, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hinU q, h⟩, fun h => h.2⟩
  rw [hx]
  refine ⟨?_, ?_⟩
  · rw [hmem, not_not]
    exact hmin.1.2 (Ideal.subset_span (Set.mem_singleton _))
  · intro x' hx' hsp
    have hx'U : x' ∈ U := hsp.mem_open U.isOpen (hinU P)
    obtain ⟨q, rfl⟩ : x' ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hx'U
    have hqp : q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp
    have hqp' : q.asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes (R := Γ(Y, U)) q P).mpr hqp
    have hπq : πU ∈ q.asIdeal := by
      by_contra h
      exact hx' ((hmem q).mpr h)
    have hPq : P.asIdeal ≤ q.asIdeal :=
      hmin.2 ⟨q.2, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπq)⟩ hqp'
    congr 1
    exact PrimeSpectrum.ext (le_antisymm hqp' hPq)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenMul
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genMul_of :
    GenericMulOfProd := by
  intro K _ n α hα t hcard hmem hprod
  classical
  by_cases hn : Nonempty (Fin n)
  · let g := Function.invFun α
    have hg : ∀ x ∈ t, α (g x) = x := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (hmem x hx)
      exact Function.invFun_eq ⟨i, rfl⟩
    let u := t.map g
    have hu : u.map α = t := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id t]
      exact Multiset.map_congr rfl hg
    have key := hα (fun i => u.count i) ?_ ?_
    · have hu1 : u = Finset.univ.val := Multiset.ext.2 fun i => by
        rw [key i, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ i)]
      rw [← hu, hu1]
    · rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      simp [u, hcard]
    · calc ∏ i, α i ^ u.count i = (u.map α).prod := by
            rw [Finset.prod_multiset_map_count]
            exact (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
              rw [Multiset.count_eq_zero.2 (by simpa using hi), pow_zero])).symm
        _ = t.prod := by rw [hu]
        _ = ∏ i, α i := by rw [hprod, Finset.prod_eq_multiset_prod]
  · have h0 : (Finset.univ : Finset (Fin n)).val = 0 := by
      rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn)]
      rfl
    rw [h0, Multiset.map_zero] at hcard ⊢
    exact Multiset.card_eq_zero.1 hcard
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PIdemCover
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private lemma idem_prod_one_sub {B : Type} [CommRing B] (s : Finset B)
    (hs : ∀ e ∈ s, IsIdempotentElem e) : IsIdempotentElem (∏ e ∈ s, (1 - e)) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e he => (hs e he).one_sub

private lemma one_sub_prod_mem {B : Type} [CommRing B] (I : Ideal B) (s : Finset B)
    (hs : ∀ e ∈ s, e ∈ I) : 1 - ∏ e ∈ s, (1 - e) ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : a ∈ I := hs a (Finset.mem_insert_self a s)
    have h2 := ih fun e he => hs e (Finset.mem_insert_of_mem he)
    have : 1 - (1 - a) * ∏ e ∈ s, (1 - e) = (1 - ∏ e ∈ s, (1 - e)) + a * ∏ e ∈ s, (1 - e) := by ring
    rw [this]
    exact I.add_mem h2 (I.mul_mem_right _ h1)

private lemma cover_step {B : Type} [CommRing B] (Λ : Type) [Fintype Λ] (J : Λ → Ideal B)
    (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ σ, ∃ e ∈ J σ, IsIdempotentElem e ∧ e ∉ 𝔪) :
    ∃ f : Λ → B, (∀ σ, IsIdempotentElem (f σ)) ∧ (∀ σ, f σ ∈ J σ) ∧ ∏ σ, (1 - f σ) = 0 := by
  classical
  let E : Set B := {e | IsIdempotentElem e ∧ ∃ σ, e ∈ J σ}
  have hE : Ideal.span E = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨σ, e, he, hi, hn⟩ := h 𝔪 hm
    exact hn (hle (Ideal.subset_span ⟨hi, σ, he⟩))
  obtain ⟨t, htE, ht⟩ := (Ideal.span_eq_top_iff_finite E).1 hE
  refine ⟨fun σ => 1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e), fun σ => ?_, fun σ => ?_, ?_⟩
  · exact (idem_prod_one_sub _ fun e he => (htE (Finset.mem_filter.1 he).1).1).one_sub
  · exact one_sub_prod_mem _ _ fun e he => (Finset.mem_filter.1 he).2
  · set g : B := ∏ σ, (1 - (1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e))) with hg
    have hkill : ∀ e ∈ t, e * g = 0 := by
      intro e he
      obtain ⟨hi, σ, hσ⟩ := htE he
      have hef : e ∈ t.filter (· ∈ J σ) := Finset.mem_filter.2 ⟨he, hσ⟩
      obtain ⟨c, hc⟩ : (1 - e) ∣ g := by
        refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ σ))
        rw [sub_sub_cancel]
        exact Finset.dvd_prod_of_mem _ hef
      have h0 : e * (1 - e) = 0 := by
        have : e * e = e := hi
        rw [mul_sub, mul_one, this, sub_self]
      rw [hc, ← mul_assoc, h0, zero_mul]
    have hall : ∀ x ∈ Ideal.span (t : Set B), x * g = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hkill x hx
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
    have := hall 1 (by rw [ht]; trivial)
    rwa [one_mul] at this

theorem UpperTheory.Gal.crystallineComparison.idemCover_of :
    IdemCover := by
  intro B _ Λ _ J h
  classical
  obtain ⟨f, hfi, hfJ, hf0⟩ := cover_step Λ J h
  letI : LinearOrder Λ := LinearOrder.lift' (Fintype.equivFin Λ) (Equiv.injective _)
  let P : Λ → B := fun σ => ∏ τ ∈ Finset.univ.filter (· < σ), (1 - f τ)
  have hP : ∀ σ, IsIdempotentElem (P σ) := by
    intro σ
    show P σ * P σ = P σ
    simp only [P]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => (hfi τ).one_sub
  have hkill : ∀ σ τ, τ < σ → P σ * f τ = 0 := by
    intro σ τ hτ
    obtain ⟨c, hc⟩ : (1 - f τ) ∣ P σ :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ τ, hτ⟩)
    have h0 : (1 - f τ) * f τ = 0 := by
      have : f τ * f τ = f τ := hfi τ
      rw [sub_mul, one_mul, this, sub_self]
    rw [hc, mul_comm (1 - f τ) c, mul_assoc, h0, mul_zero]
  have hlt : ∀ σ τ, τ < σ → (f σ * P σ) * (f τ * P τ) = 0 := by
    intro σ τ hτ
    have : (f σ * P σ) * (f τ * P τ) = f σ * (P σ * f τ) * P τ := by ring
    rw [this, hkill σ τ hτ, mul_zero, zero_mul]
  refine ⟨fun σ => f σ * P σ, ⟨⟨fun σ => (hfi σ).mul (hP σ), ?_⟩, ?_⟩, fun σ => (J σ).mul_mem_right _ (hfJ σ)⟩
  · intro σ τ hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · show (f σ * P σ) * (f τ * P τ) = 0
      rw [mul_comm]
      exact hlt τ σ hl
    · exact hlt σ τ hl
  · have := Finset.prod_one_sub_ordered (Finset.univ : Finset Λ) f
    rw [hf0] at this
    exact (sub_eq_zero.1 this.symm).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PInjSplit
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private def baseChangePts {R A S K : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing K]
    [Algebra R A] [Algebra R S] [Algebra A K] [Algebra R K] [IsScalarTower R A K] :
    (A ⊗[R] S →ₐ[A] K) ≃ (S →ₐ[R] K) where
  toFun f := (f.restrictScalars R).comp Algebra.TensorProduct.includeRight
  invFun g := Algebra.TensorProduct.lift (Algebra.ofId A K) g fun _ _ => Commute.all _ _
  left_inv f := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext s
      simp [Algebra.ofId_apply]
  right_inv g := by
    ext s
    simp [Algebra.ofId_apply]

theorem UpperTheory.Gal.crystallineComparison.injSplit_of :
    RankOfDeg → SplitsOfEquiv → InjSplit := by
  intro hRank hSplitEq l d R S _ _ _ hE
  haveI := hE.fin
  haveI := hE.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (Localization.Away (l : R)) K],
      Nat.card (Localization.Away (l : R) ⊗[R] S →ₐ[Localization.Away (l : R)] K) = d := by
    intro K _ _ _
    letI : Algebra R K := ((algebraMap (Localization.Away (l : R)) K).comp
      (algebraMap R (Localization.Away (l : R)))).toAlgebra
    haveI : IsScalarTower R (Localization.Away (l : R)) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hl : (l : K) ≠ 0 := by
      have hu : IsUnit (algebraMap R (Localization.Away (l : R)) (l : R)) :=
        IsLocalization.Away.algebraMap_isUnit (l : R)
      have hu' := hu.map (algebraMap (Localization.Away (l : R)) K)
      simpa using hu'.ne_zero
    rw [Nat.card_congr baseChangePts]
    exact hE.deg K hl
  have hn := hRank (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) d hdeg
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  obtain ⟨n, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  obtain ⟨z, hz⟩ := hSplitEq (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) T (Fin n) e
  exact ⟨T, inferInstance, inferInstance, n, z,
    FaithfulSMul.algebraMap_injective (Localization.Away (l : R)) T, hz⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PJoinAbs
section
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.joinAbs_of :
    NilEmb → NilSubq → NilOfAnn → AnnSub → AnnExt → AdmExact → JoinAbs := by
  intro hEmb hSubq hOfAnn hAnnSub hAnnExt hAdmExact
  intro F G B _ _ _ _ σ ψ hσψ L _ _ e hB V _ _ _ ρ q n T hAdm hAnn U _ _ ρU i TU θ hi hinj hT hTg hTT hnil
    W _ _ _ _ ρW I _ C _ _ ρC f hsub hf hsep
  letI : Module F U := Module.compHom _ (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : ∀ a, Module F (C a) := fun a => Module.compHom _ (algebraMap F L)
  haveI : ∀ a, IsScalarTower F L (C a) := fun a => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  obtain ⟨hE1, hE2⟩ := hAnnExt F G B σ ψ L V ρ
  have hAdmL := hE1 e hAdm
  have hAnnL := hE2 q n T hAnn
  have hAdmU : admitted σ e ρU :=
    (hAdmExact F G B σ L e hB U (L ⊗[F] V) ρU (extRep L ρ) i hi).1 hinj hAdmL
  have hAnnU : AnnD σ ψ q n ρU TU :=
    hAnnSub F G B σ ψ L U (L ⊗[F] V) ρU (extRep L ρ) i hi hinj q n TU
      (fun j => (T j).baseChange L) hT hAnnL
  have hNilU : NilD σ ψ ρU (heckePol q n θ) :=
    hOfAnn F G B σ ψ hσψ L U ρU q n TU θ hTg hTT hnil hAnnU
  have hNilC : ∀ a, NilD σ ψ (ρC a) (heckePol q n θ) := fun a =>
    (hSubq F G B σ ψ L e hB U (C a) ρU (ρC a) (hsub a) hAdmU).2 _ hNilU
  exact hEmb F G B σ ψ L W ρW I C ρC f hf hsep _ hNilC
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PLiftP
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.liftingProperty :
    LiftP := by
  intro R T ι _ _ f N' h
  have hl : N' ∈ Polynomial.lifts (MvPolynomial.map (σ := ι) f) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro a
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact h a m
  rw [Polynomial.lifts_iff_set_range] at hl
  obtain ⟨N, hN⟩ := hl
  exact ⟨N, hN⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PLinFactor
section
namespace UpperTheory.Gal.crystallineComparison

private theorem exists_min_dvd {B ι : Type} [CommRing B] (w : B) (d : ι → B)
    (hd : ∀ k k', d k ∣ w → d k ∣ d k' ∨ d k' ∣ d k) (s : Finset ι) (hs : s.Nonempty)
    (hw : ∀ k ∈ s, d k ∣ w) : ∃ k₀ ∈ s, ∀ k ∈ s, d k₀ ∣ d k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    by_cases hs' : s.Nonempty
    · obtain ⟨k₁, hk₁, hmin⟩ := ih hs' (fun k hk => hw k (Finset.mem_insert_of_mem hk))
      rcases hd a k₁ (hw a (Finset.mem_insert_self a s)) with h | h
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact dvd_refl _
        · exact h.trans (hmin k hk)
      · refine ⟨k₁, Finset.mem_insert_of_mem hk₁, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact h
        · exact hmin k hk
    · rw [Finset.not_nonempty_iff_eq_empty] at hs'
      subst hs'
      refine ⟨a, by simp, fun k hk => ?_⟩
      simp at hk
      subst hk
      exact dvd_refl _

theorem linFactor_of : LinFactor := by
  intro B ι _ _ w d hex hd
  classical
  obtain ⟨k₀, hk₀, hmin⟩ := exists_min_dvd w d hd (Finset.univ.filter fun k => d k ∣ w)
    (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by simpa using hk⟩)
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hk₀w : d k₀ ∣ w := (Finset.mem_filter.mp hk₀).2
  have hall : ∀ k, d k₀ ∣ d k := by
    intro k
    rcases hd k₀ k hk₀w with h | h
    · exact h
    · exact hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans hk₀w⟩)
  refine ⟨d k₀, fun k => if k = k₀ then 1 else (hall k).choose, k₀, hk₀w, by simp, ?_⟩
  intro k
  by_cases hk : k = k₀
  · subst hk
    simp
  · simp only [hk, if_false]
    exact (hall k).choose_spec

end UpperTheory.Gal.crystallineComparison
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatRep
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matRep_of :
    MatRep := by
  intro R S _ _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R S
  set e : Fin n → S := fun k => f (Pi.single k 1) with he
  have hsum : ∀ s : S, ∑ k, g s k • e k = s := by
    intro s
    have h1 : f (g s) = s := LinearMap.congr_fun hfg s
    conv_rhs => rw [← h1, pi_eq_sum_univ (g s)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, e]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨n, fun s => Matrix.of fun j k => g (s * e k) j, ?_⟩
  intro B _ _ I _ _ z hz
  let φ := AlgEquiv.ofBijective (splitMap z) hz
  let G : Fin n → (B ⊗[R] S →ₗ[B] B) := fun j =>
    (TensorProduct.AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ ((LinearMap.proj j ∘ₗ g).baseChange B)
  have hG : ∀ j b s, G j (b ⊗ₜ s) = algebraMap R B (g s j) * b := by
    intro j b s
    simp [G, LinearMap.baseChange_tmul, Algebra.smul_def]
  have hK : ∀ x i, ∑ k, z i (e k) * G k x = splitMap z x i := by
    intro x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
      rw [splitMap_tmul]
      simp only [hG]
      conv_rhs => rw [← hsum s]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Algebra.smul_def]
      ring
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hx, hy, Pi.add_apply]
  have hL : ∀ t : S, ∑ i, z i t • φ.symm (Pi.single i 1) = (1 : B) ⊗ₜ t := by
    intro t
    apply φ.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, AlgEquiv.apply_symm_apply]
    funext i'
    simp [φ, splitMap_tmul, Finset.sum_apply, Pi.single_apply]
    show (z i') t = splitMap z (1 ⊗ₜ t) i'
    rw [splitMap_tmul, one_mul]
  refine ⟨Matrix.of fun i k => z i (e k), Matrix.of fun j i => G j (φ.symm (Pi.single i 1)), ?_, ?_⟩
  · ext i i'
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [hK]
    have h2 : splitMap z (φ.symm (Pi.single i' 1)) = Pi.single i' 1 := φ.apply_symm_apply _
    rw [h2, Matrix.one_apply, Pi.single_apply]
  · intro s
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.map_apply]
    have h3 : (algebraMap R B) (g (s * e k) j) = G j ((1 : B) ⊗ₜ (s * e k)) := by
      rw [hG, mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h3, ← hL, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.POrdCount
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ordCount_of :
    OrdDecomp → Telescope → OrdCount := by
  intro hD hT q n P F I _ v hR
  obtain ⟨A, hA, h0, hs⟩ := hD q n P F I v hR
  have key := hT q n P F (fun j => Multiset.map (v j) Finset.univ.val) A hA h0 hs
  simp only [Multiset.map_map] at key
  exact key
end

