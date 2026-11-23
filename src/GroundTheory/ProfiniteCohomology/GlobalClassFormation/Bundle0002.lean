module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ABHNPrep
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassSplit
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction.ExistsInfIdelesLocalResIdelesResFieldEqZeroOfInf
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.LocalInf
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExistsUnitsToIdelesEqOfIdelesSumInvEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum GroundTheory.Global.SemiLocal

noncomputable section

theorem idelesToClasses_idelesResField (K E : FiniteSubfield) [Fact (K ≤ E)] (y : cohomology (limitRep K) 2) :
    (idelesToClasses E 2).hom ((idelesResField K E 2).hom y) =
      (classResField K E 2).hom ((idelesToClasses K 2).hom y) := by
  have hc : cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (idelesResMor K E) ≫
      cochainsMap (idelesShortComplexRes E).g =
      cochainsMap (idelesShortComplexRes K).g ≫
        cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (classResMor K E) := by
    ext m x : 3
    apply Subtype.ext
    funext g
    rfl
  have e1 : idelesResField K E 2 ≫ idelesToClasses E 2 = HomologicalComplex.homologyMap
      (cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (idelesResMor K E) ≫
        cochainsMap (idelesShortComplexRes E).g) 2 :=
    (HomologicalComplex.homologyMap_comp _ _ 2).symm
  have e2 : idelesToClasses K 2 ≫ classResField K E 2 = HomologicalComplex.homologyMap
      (cochainsMap (idelesShortComplexRes K).g ≫
        cochainsMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (classResMor K E)) 2 :=
    (HomologicalComplex.homologyMap_comp _ _ 2).symm
  have h : idelesResField K E 2 ≫ idelesToClasses E 2 = idelesToClasses K 2 ≫ classResField K E 2 := by
    rw [e1, e2, hc]
    rfl
  exact congrArg (fun φ => φ.hom y) h

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

theorem idelesSumInv_eq_zero_of_idelesToClasses_eq_zero (w : cohomology (limitRep K) 2)
    (hw : (idelesToClasses K 2).hom w = 0) : idelesSumInv ι w = 0 := by
  obtain ⟨x, rfl⟩ := exists_unitsToIdeles_eq K 2 w hw
  exact idelesSumInv_unitsToIdeles ι x

theorem eq_zero_of_mk_div_eq_zero {k n : ℕ} (hk : k < n) (h : QZ.mk ((k : ℚ) / n) = 0) : k = 0 := by
  rw [QZ.mk_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (Nat.zero_le k).trans_lt hk
  have h1 : (z : ℚ) < 1 := by
    rw [hz, div_lt_one hnpos]
    exact_mod_cast hk
  have h2 : (0 : ℚ) ≤ z := by
    rw [hz]
    positivity
  have hz0 : z = 0 := by
    have h1' : z < 1 := by exact_mod_cast h1
    have h2' : 0 ≤ z := by exact_mod_cast h2
    omega
  rw [hz0, Int.cast_zero, eq_comm, div_eq_zero_iff] at hz
  rcases hz with hz | hz
  · exact_mod_cast hz
  · exact absurd hz hnpos.ne'

theorem exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero (y : cohomology (limitRep K) 2)
    (hy : idelesSumInv ι y = 0) : ∃ x, (unitsToIdeles K 2).hom x = y := by
  classical
  obtain ⟨a₀, ha₀⟩ := exists_sub_unitsToIdeles_iChar_inl_eq_zero ι y
  set y' := y - (unitsToIdeles K 2).hom (globalCupClass (iChar K) a₀) with hy'def
  have hy' : idelesSumInv ι y' = 0 := by
    rw [hy'def, map_sub, hy, idelesSumInv_unitsToIdeles, sub_zero]
  suffices h : ∃ x, (unitsToIdeles K 2).hom x = y' by
    obtain ⟨x, hx⟩ := h
    exact ⟨x + globalCupClass (iChar K) a₀, by rw [map_add (f := _), hx, hy'def, sub_add_cancel]⟩
  obtain ⟨m, hm0, hm⟩ := exists_nsmul_eq_zero_limitRep y'
  let S : Finset (HeightOneSpectrum (𝓞 K.1)) :=
    (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨E, _, hgal, hcyc, -, hdeg⟩ := CyclotomicLayer.exists_cyclic_layer_dvd_localDegree K S hm0
  have hres : (idelesResField K E 2).hom y' = 0 := by
    refine idelesResField_eq_zero ι y' ha₀ fun v w => ?_
    by_cases hv : v ∈ S
    · obtain ⟨k, hk⟩ := hdeg v hv w
      rw [hk, mul_comm, mul_smul]
      have h0 : m • placeInv (K := K) (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y' (.inr v)) = 0 := by
        rw [← map_nsmul, ← DFinsupp.smul_apply, ← map_nsmul, hm, map_zero]
        exact map_zero _
      rw [h0, smul_zero]
    · have h0 : idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y' (.inr v) = 0 := by
        by_contra h
        exact hv (by rw [Finset.mem_preimage, DFinsupp.mem_support_iff]; exact h)
      rw [h0, map_zero, smul_zero]
  obtain ⟨Z, hZ, hZinf, hZfin⟩ := exists_idelesSumInv_eq_one_div ι E
  have hresZ : (idelesResField K E 2).hom Z = 0 := idelesResField_eq_zero ι Z hZinf hZfin
  set n := Module.finrank K.1 E.1 with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hM : Nat.card (LinearMap.ker (classResField K E 2).hom) = n := natCard_ker_classResField_of_isCyclic K E
  have hmemM : ∀ w : cohomology (limitRep K) 2, (idelesResField K E 2).hom w = 0 →
      (idelesToClasses K 2).hom w ∈ LinearMap.ker (classResField K E 2).hom := by
    intro w hw
    rw [LinearMap.mem_ker, ← idelesToClasses_idelesResField, hw, map_zero]
  have hT : ∀ k : ℕ, idelesSumInv ι (k • Z) = QZ.mk ((k : ℚ) / n) := by
    intro k
    rw [map_nsmul, hZ, ← QZ.mk_nsmul, nsmul_eq_mul, mul_one_div]
  let f : Fin n → LinearMap.ker (classResField K E 2).hom := fun k =>
    ⟨(idelesToClasses K 2).hom ((k : ℕ) • Z), hmemM _ (by rw [map_nsmul, hresZ, smul_zero])⟩
  have finj : Function.Injective f := by
    intro k k' hkk
    have h1 : (idelesToClasses K 2).hom ((k : ℕ) • Z) = (idelesToClasses K 2).hom ((k' : ℕ) • Z) :=
      congrArg Subtype.val hkk
    have key : ∀ a b : Fin n, (b : ℕ) ≤ a →
        (idelesToClasses K 2).hom ((a : ℕ) • Z) = (idelesToClasses K 2).hom ((b : ℕ) • Z) → a = b := by
      intro a b hba hab
      have hw : (idelesToClasses K 2).hom (((a : ℕ) - b) • Z) = 0 := by
        rw [sub_nsmul _ hba, ← sub_eq_add_neg, map_sub, hab, sub_self]
      have h2 := idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hw
      rw [hT] at h2
      have := eq_zero_of_mk_div_eq_zero (lt_of_le_of_lt (Nat.sub_le _ _) a.2) (by exact_mod_cast h2)
      exact Fin.ext (by omega)
    rcases le_total (k' : ℕ) k with h | h
    · exact key k k' h h1
    · exact (key k' k h h1.symm).symm
  have : Finite (LinearMap.ker (classResField K E 2).hom) := Nat.finite_of_card_ne_zero (hM ▸ hn0)
  have fsurj := (finj.bijective_of_nat_card_le (by rw [hM, Nat.card_eq_fintype_card, Fintype.card_fin])).2
  obtain ⟨k, hk⟩ := fsurj ⟨(idelesToClasses K 2).hom y', hmemM y' hres⟩
  have hk' : (idelesToClasses K 2).hom (y' - (k : ℕ) • Z) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact (congrArg Subtype.val hk).symm
  have h2 := idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hk'
  rw [map_sub, hy', hT, zero_sub, neg_eq_zero] at h2
  have hk0 : (k : ℕ) = 0 := eq_zero_of_mk_div_eq_zero k.2 h2
  rw [hk0, zero_smul, sub_zero] at hk'
  exact exists_unitsToIdeles_eq K 2 y' hk'

theorem sumPlaceInv_eq_zero_iff (y : ⨁ v : Place K.1, localGaloisCohomology K 2 v) :
    sumPlaceInv K y = 0 ↔ ∃ x, brauerLocal ι x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ι
      ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm y) (by
        rw [idelesSumInv_apply, AddEquiv.apply_symm_apply, hy])
    exact ⟨x, by rw [brauerLocal_apply, hx, AddEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    exact brauerSumInv_eq_zero ι x

end

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver DirectSum

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)] (ι : LocalEmbeddings K) (ιE : LocalEmbeddings E)

section Places


set_option maxHeartbeats 4000000 in
theorem placeInv_idelesResField_inr (y : cohomology (limitRep K) 2) (v : HeightOneSpectrum (𝓞 K.1))
    (w : PlacesOver E.1 v) :
    placeInv (.inr w.1) (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inr w.1)) =
      Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) •
        placeInv (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inr v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inr, idelesLimitCohomologyEquiv_apply_inr]
  obtain ⟨ι', hι'⟩ := exists_placeOfEmbedding_eq w
  have key : ∀ u : PlacesOver E.1 v, placeOfEmbedding ι' E = u →
      placeInv (K := E) (.inr u.1) ((idelesLocalRes (ιE.fin u.1) 2).hom ((idelesResField K E 2).hom y)) =
        Module.finrank (v.adicCompletion K.1) (u.1.adicCompletion E.1) •
          placeInv (K := K) (.inr v) ((idelesLocalRes (ι.fin v) 2).hom y) := by
    rintro u rfl
    rw [idelesLocalRes_eq_of_algHom ι' (ι.fin v)]
    exact brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField v ι' (ιE.fin _) y
  exact key w hι'


set_option maxHeartbeats 4000000 in
theorem placeInv_idelesResField_inl (y : cohomology (limitRep K) 2) (v : InfinitePlace K.1) (w : v.placesOver E.1) :
    placeInv (.inl (w : InfinitePlace E.1))
        (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inl w)) =
      Module.finrank v.Completion (w : InfinitePlace E.1).Completion •
        placeInv (.inl v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inl v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inl, idelesLimitCohomologyEquiv_apply_inl]
  by_cases hw : (w : InfinitePlace E.1).IsComplex
  · have h0 : placeInv (K := E) (.inl (w : InfinitePlace E.1))
        ((infIdelesLocalRes (ιE.inf (w : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) = 0 := by
      have : Subsingleton (cohomology (galUnitsZ (w : InfinitePlace E.1).Completion
          (AlgebraicClosure (w : InfinitePlace E.1).Completion)) 2) :=
        subsingleton_cohomology_two_of_isComplex _ hw
      exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
    rw [h0]
    by_cases hv : v.IsReal
    · rw [(InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace E.1)).2 ⟨hv, hw⟩]
      rcases placeInv_inl_eq_zero_or_eq_half v ((infIdelesLocalRes (ι.inf v) 2).hom y) with h | h
      · rw [h, smul_zero]
      · rw [h, two_nsmul, QZ.mk_half_add_mk_half]
    · have h0 : placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) = 0 := by
        have : Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) :=
          subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)
        exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
      rw [h0, smul_zero]
  · have h1 : Module.finrank v.Completion (w : InfinitePlace E.1).Completion = 1 :=
      (InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace E.1)).2 fun h => hw h.2
    rw [h1, one_smul]
    obtain ⟨ι', hι'⟩ := exists_infPlaceOfEmbedding_eq w
    have key : ∀ u : v.placesOver E.1, infPlaceOfEmbedding ι' E = u →
        Module.finrank v.Completion (u : InfinitePlace E.1).Completion = 1 →
        placeInv (K := E) (.inl (u : InfinitePlace E.1))
            ((infIdelesLocalRes (ιE.inf (u : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) =
          placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) := by
      rintro u rfl hu
      rw [infIdelesLocalRes_eq_of_algHom ι' (ι.inf v)]
      exact quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one ι' (ιE.inf _) y hu
    exact key w hι' h1

end Places

section Sum

theorem sumPlaceInv_eq_sum (D : ⨁ w : Place E.1, localGaloisCohomology E 2 w) (S : Finset (Place E.1))
    (hS : ∀ w ∉ S, D w = 0) : sumPlaceInv E D = ∑ w ∈ S, placeInv w (D w) := by
  classical
  have hD : D = ∑ w ∈ S, DirectSum.of _ w (D w) := by
    refine DFinsupp.ext fun w => ?_
    rw [DFinsupp.finsetSum_apply]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb))
        (fun h => absurd hw h), DirectSum.of_eq_same]
    · rw [hS w hw, Finset.sum_eq_zero fun b hb => DirectSum.of_eq_of_ne _ _ _ (by rintro rfl; exact hw hb)]
  conv_lhs => rw [hD]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => sumPlaceInv_of w (D w)


set_option maxHeartbeats 4000000 in
open Classical in
theorem idelesSumInv_idelesResField_of (u : Place K.1) (t : localGaloisCohomology K 2 u) :
    idelesSumInv ιE ((idelesResField K E 2).hom
        ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t))) =
      Module.finrank K.1 E.1 •
        idelesSumInv ι ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    set y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t) with hy_def
    have hy : idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y = DirectSum.of _ u t :=
      AddEquiv.apply_symm_apply _ _
    set D := idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) with hD_def
    rw [idelesSumInv_apply, idelesSumInv_apply, hy, sumPlaceInv_of]
  
    have hinl : ∀ w : InfinitePlace E.1, placeInv (.inl w) (D (.inl w)) =
        Module.finrank (w.comap (algebraMap K.1 E.1)).Completion w.Completion •
          placeInv (.inl (w.comap (algebraMap K.1 E.1)))
            (DirectSum.of (localGaloisCohomology K 2) u t (.inl (w.comap (algebraMap K.1 E.1)))) := fun w => by
      rw [← hy]
      exact placeInv_idelesResField_inl ι ιE y (w.comap (algebraMap K.1 E.1)) ⟨w, ⟨rfl⟩⟩
    have hinr : ∀ w : HeightOneSpectrum (𝓞 E.1), placeInv (.inr w) (D (.inr w)) =
        Module.finrank ((AdeleBaseChange.below K.1 w).adicCompletion K.1) (w.adicCompletion E.1) •
          placeInv (.inr (AdeleBaseChange.below K.1 w))
            (DirectSum.of (localGaloisCohomology K 2) u t (.inr (AdeleBaseChange.below K.1 w))) := fun w => by
      rw [← hy]
      exact placeInv_idelesResField_inr ι ιE y (AdeleBaseChange.below K.1 w) ⟨w, AdeleBaseChange.liesOver_below w⟩
    rcases u with v | v
    ·
      let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : v.placesOver E.1 => (.inl (w : InfinitePlace E.1) :
        Place E.1), fun a b h => Subtype.ext (Sum.inl_injective h)⟩
      have hS : ∀ w ∉ S, D w = 0 := by
        intro w hw
        apply placeInv_injective w
        rw [map_zero]
        rcases w with w | w
        · rw [hinl]
          by_cases hv : w.comap (algebraMap K.1 E.1) = v
          · exact absurd (Finset.mem_map.2 ⟨(⟨w, by subst hv; exact ⟨rfl⟩⟩ : v.placesOver E.1), Finset.mem_univ _, rfl⟩) hw
          · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inl_injective h)), map_zero, smul_zero]
        · rw [hinr, DirectSum.of_eq_of_ne _ _ _ Sum.inr_ne_inl, map_zero, smul_zero]
      rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
      change ∑ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) = _
      have hw : ∀ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) =
          Module.finrank v.Completion (w : InfinitePlace E.1).Completion • placeInv (.inl v) t := fun w => by
        rw [hD_def, placeInv_idelesResField_inl ι ιE y v w, hy, DirectSum.of_eq_same]
      rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul,
        GroundTheory.Global.InfinitePlace.sum_finrank_completion (L := E.1) v]
    ·
      let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : PlacesOver E.1 v => (.inr w.1 : Place E.1),
        fun a b h => Subtype.ext (Sum.inr_injective h)⟩
      have hS : ∀ w ∉ S, D w = 0 := by
        intro w hw
        apply placeInv_injective w
        rw [map_zero]
        rcases w with w | w
        · rw [hinl, DirectSum.of_eq_of_ne _ _ _ Sum.inl_ne_inr, map_zero, smul_zero]
        · rw [hinr]
          by_cases hv : AdeleBaseChange.below K.1 w = v
          · refine absurd (Finset.mem_map.2 ⟨(⟨w, ?_⟩ : PlacesOver E.1 v), Finset.mem_univ _, rfl⟩) hw
            rw [← hv]
            exact AdeleBaseChange.liesOver_below w
          · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inr_injective h)), map_zero, smul_zero]
      rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
      change ∑ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) = _
      have hw : ∀ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) =
          Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) • placeInv (.inr v) t := fun w => by
        rw [hD_def, placeInv_idelesResField_inr ι ιE y v w, hy, DirectSum.of_eq_same]
      rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul, sum_finrank_eq E.1 v]

theorem idelesSumInv_idelesResField (y : cohomology (limitRep K) 2) :
    idelesSumInv ιE ((idelesResField K E 2).hom y) = Module.finrank K.1 E.1 • idelesSumInv ι y := by
  classical
  set Φ := idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)
  obtain ⟨D, rfl⟩ := Φ.symm.surjective y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_of D, map_sum, map_sum, map_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => idelesSumInv_idelesResField_of ι ιE u (D u)

end Sum

end

end GroundTheory.ProfCoh
end

