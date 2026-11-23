module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMemIff
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylCombInt

open Formalism.L2.DIV

theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν = WeylLatticeDuality.weyl ℤ N N le_rfl ν := rfl

theorem eval_ten {K Lt : Type} [Field K] [Fintype Lt] {N : ℕ} (f : Lt → MvPolynomial (Fin N × Fin N) K)
    (z : Lt × Fin N × Fin N → K) : eval z (ten f) = ∏ s, eval (fun v => z (s, v)) (f s) := by
  unfold ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Formalism.GradedWeylDivisibility.blockEmb, eval_rename]
  rfl

theorem fockB_ten_dual {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {K : Type} [Field K] [CharZero K]
    (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) (κ' κ : ∀ s, ι s) :
    fockB (ten fun s => map (algebraMap ℚ K) (b s (κ' s))) (ten fun s => map (algebraMap ℚ K) (g s (κ s))) =
      if κ' = κ then ∏ s, (Nc s : K) else 0 := by
  rw [GlobalTheory.WeylMinorDual.fockB_ten]
  simp only [GlobalTheory.WeylMinorDual.fockB_map, hbg]
  split_ifs with h
  · subst h; simp
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

theorem coeff_unique (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T]
    (e : Lt → T) (he : Function.Bijective e) (N : ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    [∀ s, DecidableEq (ι s)] (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hNc : ∀ s, Nc s ≠ 0) (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0)
    (c : (∀ s, ι s) → ℂ_[p])
    (h : ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p], ∑ κ, c κ * ∏ s, MvPolynomial.eval
      (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) = 0) :
    c = 0 := by
  set E := Equiv.ofBijective e he with hE
  set P : (∀ s, ι s) → MvPolynomial (Lt × Fin N × Fin N) ℂ_[p] :=
    fun κ => ten fun s => map (algebraMap ℚ ℂ_[p]) (g s (κ s)) with hP
  have h0 : ∑ κ, c κ • P κ = 0 := by
    apply MvPolynomial.funext
    intro z
    have hz := h (fun τ => Matrix.of fun i j => z (E.symm τ, i, j))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum]
    rw [← hz]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [smul_eval, hP]
    simp only [eval_ten]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    have hs : E.symm (e s) = s := by
      rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
    simp only [Matrix.of_apply, hs]
  funext κ'
  have h1 := congrArg (fockB (ten fun s => map (algebraMap ℚ ℂ_[p]) (b s (κ' s)))) h0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← fockBL_apply, ← fockBL_apply, map_sum, map_zero] at h1
  simp only [map_smul, fockBL_apply, hP, fockB_ten_dual ι b g Nc hbg, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  have hne : ∏ s, (Nc s : ℂ_[p]) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => by exact_mod_cast hNc s
  simpa [hne] using h1

theorem map_intQ (p : ℕ) [Fact p.Prime] (N : ℕ) (w : MvPolynomial (Fin N × Fin N) ℤ) :
    map (algebraMap ℚ ℂ_[p]) (Formalism.GradedWeylDivisibility.intQ N N w) = map (Int.castRingHom ℂ_[p]) w := by
  have : Formalism.GradedWeylDivisibility.intQ N N w = map (Int.castRingHom ℚ) w := rfl
  rw [this, map_map, show (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ_[p] from
    RingHom.ext_int _ _]

theorem comb_mem_iff : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (ν : T → Fin N → ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ), (∀ s, Nc s ≠ 0) →
    (∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) →
    (∀ s, Submodule.span ℤ (Set.range (g s)) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (ν (e s))).map (Formalism.GradedWeylDivisibility.intQ N N)) →
    ∀ a : (∀ s, ι s) → ℂ_[p],
      ((fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s)))) ∈ WeylLatticeDuality.DelW p T N ν ↔
        ∀ κ, ‖a κ‖ ≤ 1) := by
  intro p _ Lt T _ _ _ e he N ν ι _ _ b g Nc hNc hbg hspan a
  set E := Equiv.ofBijective e he with hE
  have hs : ∀ s, E.symm (e s) = s := fun s => by
    rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
  set G : (∀ s, ι s) → (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p] := fun κ y =>
    ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) with hG
  constructor
  · intro hmem
    let S : AddSubgroup ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :=
      { carrier := {F | ∃ a' : (∀ s, ι s) → ℂ_[p], (∀ κ, ‖a' κ‖ ≤ 1) ∧ F = fun y => ∑ κ, a' κ * G κ y}
        zero_mem' := ⟨0, fun _ => by simp, by funext y; simp⟩
        add_mem' := by
          rintro F F' ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩
          refine ⟨a1 + a2, fun κ => ?_, ?_⟩
          · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 κ) (h2 κ))
          · funext y; simp [add_mul, Finset.sum_add_distrib]
        neg_mem' := by
          rintro F ⟨a1, h1, rfl⟩
          refine ⟨-a1, fun κ => by simpa using h1 κ, ?_⟩
          funext y; simp [neg_mul, Finset.sum_neg_distrib] }
    have hle : WeylLatticeDuality.DelW p T N ν ≤ S := by
      unfold WeylLatticeDuality.DelW
      rw [AddSubgroup.closure_le]
      rintro F ⟨r, f, hr, hf, rfl⟩
      have hn : ∀ s, ∃ n : ι s → ℤ, ∑ k, n k • g s k = Formalism.GradedWeylDivisibility.intQ N N (f (e s)) := by
        intro s
        rw [← Submodule.mem_span_range_iff_exists_fun, hspan s, weyl_eq]
        exact Submodule.mem_map_of_mem (hf (e s))
      choose n hn using hn
      refine ⟨fun κ => r * ∏ s, ((n s (κ s) : ℤ) : ℂ_[p]), fun κ => ?_, ?_⟩
      · rw [norm_mul, norm_prod]
        exact mul_le_one₀ hr (by positivity)
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [← he.prod_comp]
        have hterm : ∀ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f (e s))) =
            ∑ k, ((n s k : ℤ) : ℂ_[p]) * MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
              (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) := by
          intro s
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← map_intQ, ← hn s, map_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_zsmul, map_zsmul, zsmul_eq_mul]
        simp only [hterm, Fintype.prod_sum, Finset.mul_sum, hG]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    obtain ⟨a', ha', heq⟩ := hle hmem
    have hc := coeff_unique p Lt T e he N ι b g Nc hNc hbg (a - a') (fun y => by
      have := congrFun heq y
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]; exact this)
    have : a = a' := sub_eq_zero.mp hc
    subst this; exact ha'
  · intro ha
    have hw : ∀ s k, ∃ w ∈ WeylLatticeDuality.weyl ℤ N N le_rfl (ν (e s)), Formalism.GradedWeylDivisibility.intQ N N w = g s k := by
      intro s k
      have : g s k ∈ Submodule.span ℤ (Set.range (g s)) := Submodule.subset_span (Set.mem_range_self k)
      rw [hspan s, weyl_eq] at this
      exact this
    choose w hw hwg using hw
    have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) =
        ∑ κ : (∀ s, ι s), fun y => a κ * G κ y := by
      funext y; simp [Finset.sum_apply]
    show (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) ∈ _
    rw [hfun]
    refine AddSubgroup.sum_mem _ fun κ _ => AddSubgroup.subset_closure ?_
    refine ⟨a κ, fun τ => w (E.symm τ) (κ (E.symm τ)), ha κ, fun τ => ?_, ?_⟩
    · have := hw (E.symm τ) (κ (E.symm τ))
      rwa [show e (E.symm τ) = τ from E.apply_symm_apply τ] at this
    · funext y
      congr 1
      rw [← he.prod_comp]
      refine Finset.prod_congr rfl fun s _ => ?_
      dsimp only
      rw [hs s, ← hwg s (κ s), map_intQ]

end GlobalTheory.WeylCombInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
section
open IsLocalRing

namespace GlobalTheory.EtaleCompletionNormal

theorem formallyUnramified_of_map_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R (ResidueField S)]
    (H : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallyUnramified R S := by
  constructor
  rw [← IsLocalRing.subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]

theorem isDomain_and_isIntegrallyClosed : ∀ (D E : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [CommRing E] [IsLocalRing E] (h : D →+* E), IsNoetherianRing D → IsDomain (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsNoetherianRing E → IsAdicComplete (IsLocalRing.maximalIdeal E) E → IsLocalHom h → GlobalTheory.Toroidal.IsEtaleCompletion h → ((IsLocalRing.residue E).comp h).FormallyUnramified → IsDomain E ∧ IsIntegrallyClosed E := by
  intro D E _ _ _ _ _ h hD hAd hAi hE hEc _ het hfu
  obtain ⟨hflat, hmap, hfin⟩ := het
  haveI := hD; haveI := hE; haveI := hEc; haveI := hAd; haveI := hAi
  let A := AdicCompletion (maximalIdeal D) D
  haveI : IsNoetherianRing A := AdicNoeth.isNoetherianRing_adicCompletion D _
  haveI : IsAdicComplete ((maximalIdeal D).map h) E := by rw [hmap]; exact hEc
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal D) h
  letI : Algebra A E := g.toAlgebra
  have hgA : ∀ a, g (algebraMap D A a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal A).map (algebraMap A E) = maximalIdeal E := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal D).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap A E) := ((local_hom_tfae _).out 1 3).mpr hmA.le

  have hres : ((residue E).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap D A) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite A (E ⧸ (maximalIdeal A).map (algebraMap A E)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap A E)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal A).map (algebraMap A E)) E := by rw [hmA]; infer_instance
  haveI : Module.Finite A E := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

  haveI : Module.Flat A E := by
    refine LocalFlat.flat_of_relationsLift E (I := maximalIdeal A)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    letI : Algebra D E := h.toAlgebra
    haveI : Module.Flat D E := hflat
    have fg := (maximalIdeal D).fg_of_isNoetherianRing
    have hkerA : ∀ x : A, AdicCompletion.evalₐ (maximalIdeal D) n x = 0 ↔ x ∈ maximalIdeal A ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem D,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal A ^ n).map (algebraMap A E) = (maximalIdeal D ^ n).map (algebraMap D E) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal D ^ n).map (g.comp _) = _
      rw [hg]
      rfl
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal D) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal D ^ n).map (algebraMap D E)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal D) n x)
      have hx : x - algebraMap D A a ∈ maximalIdeal A ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap A E x - h a ∈ (maximalIdeal D ^ n).map (algebraMap D E) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap A E x - g (algebraMap D A a) = algebraMap A E (x - algebraMap D A a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor E (maximalIdeal D ^ n)).toLinearEquiv

  haveI : Algebra.FormallyUnramified A (ResidueField E) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap A (ResidueField E)).comp (algebraMap D A) = (residue E).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap D A) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified A E := formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation A E :=
    (Algebra.FinitePresentation.of_finiteType (R := A) (A := E)).1 inferInstance
  haveI : Algebra.Etale A E := Algebra.Etale.of_formallyUnramified_of_flat
  haveI : IsLocalization.AtPrime E (maximalIdeal E) :=
    IsLocalization.self fun a ha => by_contra fun h' => ha h'
  exact isDomain_and_isIntegrallyClosed_atPrime_of_etale A (maximalIdeal E) E

end GlobalTheory.EtaleCompletionNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousConjA
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom conj_map_mem_unitaryGroup)
open scoped TensorProduct

namespace GlobalTheory.ConjAutProps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem continuous_conjA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

end GlobalTheory.ConjAutProps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualBasesColProd
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

def fockQRight {σ : Type} (f : MvPolynomial σ ℚ) : MvPolynomial σ ℚ →ₗ[ℚ] ℚ where
  toFun g := Formalism.GradedWeylDivisibility.fockQ f g
  map_add' g g' := by
    show Formalism.GradedWeylDivisibility.fockQ f (g + g') = Formalism.GradedWeylDivisibility.fockQ f g + Formalism.GradedWeylDivisibility.fockQ f g'
    rw [(Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g g' f 1).1, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1,
      (Formalism.GradedWeylDivisibility.fockQPos σ g' f).1]
  map_smul' c g := by
    show Formalism.GradedWeylDivisibility.fockQ f (c • g) = c • Formalism.GradedWeylDivisibility.fockQ f g
    rw [smul_eq_mul, (Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g 0 f c).2, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1]

theorem fockQRight_apply {σ : Type} (f g : MvPolynomial σ ℚ) : fockQRight f g = Formalism.GradedWeylDivisibility.fockQ f g := rfl

theorem dual_bases_colProd : (∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h) →
  ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b g : ι → MvPolynomial (Fin N × Fin N) ℚ)
    (c : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ι → ℤ) (d : ι → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ℤ) (Nc : ℚ), Nc ≠ 0 ∧
    (∀ J, GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = ∑ k, (c J k : ℚ) • b k) ∧
    (∀ k, b k = ∑ J, (d k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ k, g k = ∑ J, (c J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0) ∧
    Submodule.span ℤ (Set.range g) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
  classical
  intro H N Y hY
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  haveI : Fintype (Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r)) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N _).fintype
  obtain ⟨b, d, hb, hd, hbd⟩ := GlobalTheory.StdDual.exists_dual_bases N (fun r : Fin N => Y.rowLen r) hanti
  set Nc := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) with hNc
  have hNc0 : Nc ≠ 0 := ((Formalism.GradedWeylDivisibility.fockQPos _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have H' := H N Y hY
  clear H
  set C := GlobalTheory.WeylMinorDual.colProd ℚ N Y hY with hCdef
  have hspanC : Submodule.span ℤ (GlobalTheory.StdDual.bidSet ℚ N (fun r : Fin N => Y.rowLen r)) =
      Submodule.span ℤ (Set.range C) := by
    rw [← GlobalTheory.StdDual.dualWeyl_intQ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY, Submodule.map_span,
      ← Set.range_comp]
    congr 2
    funext J
    exact Formalism.L2.DIV.fk_map_bidet (Int.castRingHom ℚ) _ _ _
  have hbC : Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range C) := hb.trans hspanC
  have hCb : ∀ J, C J ∈ Submodule.span ℤ (Set.range b) := fun J => hbC ▸ Submodule.subset_span ⟨J, rfl⟩
  have hbCm : ∀ k, b k ∈ Submodule.span ℤ (Set.range C) := fun k => hbC ▸ Submodule.subset_span ⟨k, rfl⟩
  choose c hc using fun J => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hCb J)
  choose d' hd' using fun k => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hbCm k)
  have hcQ : ∀ J, C J = ∑ k, (c J k : ℚ) • b k := fun J => by
    rw [← hc J]; simp only [Int.cast_smul_eq_zsmul]
  have hdQ : ∀ k, b k = ∑ J, (d' k J : ℚ) • C J := fun k => by
    rw [← hd' k]; simp only [Int.cast_smul_eq_zsmul]
  set g := fun k => ∑ J, (c J k : ℚ) • C J with hg
  have hdb : ∀ j k, Formalism.GradedWeylDivisibility.fockQ (d j) (b k) = if k = j then Nc else 0 := fun j k =>
    (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1.trans (hbd k j)
  have hdC : ∀ j J, Formalism.GradedWeylDivisibility.fockQ (d j) (C J) = (c J j : ℚ) * Nc := by
    intro j J
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hcQ J, ← fockQRight_apply, map_sum]
    simp only [map_smul, fockQRight_apply, hdb, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hgi : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = ∑ J, (c J k : ℚ) * Formalism.GradedWeylDivisibility.fockQ (b i) (C J) := by
    intro i k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← fockQRight_apply, hg, map_sum]
    simp only [map_smul, fockQRight_apply, smul_eq_mul]
  have key : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0 := by
    intro i k
    have hmem : b i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.span_le_restrictScalars ℤ ℚ _ (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    have h1 := congrArg (fockQRight (d k)) (H' (b i) hmem)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul] at h1
    simp only [map_smul, fockQRight_apply, smul_eq_mul, hdC] at h1
    rw [hdb] at h1
    rw [hgi]
    apply mul_right_cancel₀ hNc0
    rw [Finset.sum_mul]
    exact Eq.trans (Finset.sum_congr rfl fun J _ => by ring) (h1.trans (mul_comm _ _))
  have hgd : ∀ k, g k = d k := by
    intro k
    have hg1 : g k ∈ Submodule.span ℤ (Set.range b) := by
      rw [hbC, hg]
      refine Submodule.sum_mem _ fun J _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)
    have hd1 : d k ∈ Submodule.span ℤ (Set.range b) := by
      have h2 : d k ∈ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
        rw [GlobalTheory.StdDual.weyl_intQ, ← hd]
        exact Submodule.subset_span ⟨k, rfl⟩
      have h3 := Submodule.map_mono (f := Formalism.GradedWeylDivisibility.intQ N N) (Formalism.GradedWeylDivisibility.weylLeDual ℤ N N le_rfl _ hanti) h2
      rwa [GlobalTheory.StdDual.dualWeyl_intQ, ← hb] at h3
    have hx := Submodule.sub_mem _ hg1 hd1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have horth : ∀ i, Formalism.GradedWeylDivisibility.fockQ (g k - d k) (b i) = 0 := by
      intro i
      rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← fockQRight_apply, map_sub, fockQRight_apply, fockQRight_apply, key,
        ← (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, hdb]
      split_ifs with h1 h2 h2 <;> first | rfl | simp | (exact absurd h1.symm h2) | (exact absurd h2.symm h1)
    have h0 : Formalism.GradedWeylDivisibility.fockQ (g k - d k) (g k - d k) = 0 := by
      rw [← fockQRight_apply]
      nth_rewrite 2 [← ha]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, fockQRight_apply, horth, smul_zero]
    by_contra hne
    exact (ne_of_gt ((Formalism.GradedWeylDivisibility.fockQPos _ (g k - d k) (g k - d k)).2 (sub_ne_zero.mpr hne))) h0
  refine ⟨Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r), inferInstance, inferInstance, b, g, c, d', Nc, hNc0,
    hcQ, hdQ, fun k => rfl, key, ?_⟩
  have : g = d := funext hgd
  rw [this, hd, GlobalTheory.StdDual.weyl_intQ]

end GlobalTheory.WeylLatDualProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
section
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem exists_isInfFam_family : ∀ D : D7, ∃ θ : InfFam D, IsInfFam θ :=
  fun D => GlobalTheory.DualPairCompare.exists_infFam D

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkAlt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2


set_option maxHeartbeats 1600000 in
theorem TDat.laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  intro E K _ _ _ _ n S ST A T hS hA
  have h1 := _root_.GlobalTheory.Mem.Col2.LRank.ranks A T hS hA
  have h2 := _root_.GlobalTheory.Mem.Col2.fv_te_laws A T hS hA
  have h3 := _root_.GlobalTheory.Mem.Col2.diamond_action_on_classes A T hS hA
  have h4 := _root_.GlobalTheory.Mem.Col2.DilFv.dil_fv A T hS hA
  exact ⟨h1.1, h1.2, h2.2.1, h2.2.2, h3.1, h3.2.1, h4, h3.2.2⟩

end GlobalTheory.Mem.Col2
end

