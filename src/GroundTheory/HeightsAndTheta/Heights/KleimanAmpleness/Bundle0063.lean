module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0060
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsAlgebraicAdjoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

namespace RatioDim

abbrev graphIdxFintype (N m : ℕ) : ∀ c, Fintype (graphIdx N m c)
  | Sum.inl () => inferInstanceAs (Fintype (Fin (N + 1)))
  | Sum.inr () => inferInstanceAs (Fintype (Fin m))

attribute [local instance] graphIdxFintype

variable {k : Type} [Field k] {N m : ℕ}

abbrev baseRen (k : Type) [Field k] (N m : ℕ) :
    Kleiman.Poly k N →ₐ[k] NumbersDVR.MRing (graphIdx N m) k :=
  rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)

variable (W : Ideal (NumbersDVR.MRing (graphIdx N m) k))

def phi : Kleiman.Poly k N →ₐ[k] FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) :=
  (IsScalarTower.toAlgHom k _ _).comp ((Ideal.Quotient.mkₐ k W).comp (baseRen k N m))

theorem phi_apply (f : Kleiman.Poly k N) :
    phi W f = algebraMap (NumbersDVR.MRing (graphIdx N m) k ⧸ W)
      (FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W)) (Ideal.Quotient.mk W (baseRen k N m f)) := rfl

theorem baseRen_X (a : Fin (N + 1)) : baseRen k N m (X a) = X ⟨baseBlock, a⟩ := rename_X _ _

theorem baseRen_C (c : k) : baseRen k N m (C c) = C c := rename_C _ _

abbrev eta (b : Fin m) : FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) :=
  algebraMap (NumbersDVR.MRing (graphIdx N m) k ⧸ W) _ (Ideal.Quotient.mk W (X ⟨Sum.inr (), b⟩))

theorem map_eq_zero_iff (f : NumbersDVR.MRing (graphIdx N m) k) :
    algebraMap (NumbersDVR.MRing (graphIdx N m) k ⧸ W) (FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W))
      (Ideal.Quotient.mk W f) = 0 ↔ f ∈ W := by
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem ker_phi : RingHom.ker (phi W) = W.comap (baseRen k N m) := by
  ext f
  rw [RingHom.mem_ker, phi_apply, map_eq_zero_iff, Ideal.mem_comap]

abbrev bideg (d c : ℕ) : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => d) (fun _ => c)

theorem isMultiHomog_term (F : Kleiman.Poly k N) (d c : ℕ) (b : Fin m) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (graphIdx N m))
      (baseRen k N m (homogeneousComponent d F) * X ⟨Sum.inr (), b⟩ ^ c) (bideg d c) := by
  have h1 : IsWeightedHomogeneous (NumbersDVR.blockWeight (graphIdx N m))
      (baseRen k N m (homogeneousComponent d F)) (Sum.elim (fun _ => d) (fun _ => 0)) := by
    rw [rename_base_homogeneousComponent]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have h2 := (isWeightedHomogeneous_X k (NumbersDVR.blockWeight (graphIdx N m))
    (⟨Sum.inr (), b⟩ : Σ c, graphIdx N m c)).pow c
  convert h1.mul h2 using 1
  funext x
  rcases x with ⟨⟩ | ⟨⟩ <;> simp [NumbersDVR.blockWeight]

theorem transcendental_eta [W.IsPrime] (hH : NumbersDVR.IsMultiHomogIdeal W) (j : Fin m)
    (hj : (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W) :
    Transcendental (phi W).range (eta W j) := by
  classical
  rw [transcendental_iff]
  intro p hp
  have hq : ∀ c, ∃ f, phi W f = ((p.coeff c : (phi W).range) :
      FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W)) := fun c => (p.coeff c).2
  choose f hf using hq
  set Y := (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) with hY
  set s := p.support
  set G := ∑ c ∈ s, ∑ d ∈ Finset.range ((f c).totalDegree + 1),
    baseRen k N m (homogeneousComponent d (f c)) * Y ^ c with hGdef
  have hGc : ∀ c, ∑ d ∈ Finset.range ((f c).totalDegree + 1),
      baseRen k N m (homogeneousComponent d (f c)) * Y ^ c = baseRen k N m (f c) * Y ^ c := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum, sum_homogeneousComponent]

  have hG : G ∈ W := by
    rw [← map_eq_zero_iff W, ← hp, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, hGdef]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hGc, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← phi_apply, hf c]
    rfl

  have hcomp : ∀ c ∈ s, ∀ d ∈ Finset.range ((f c).totalDegree + 1),
      weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) (bideg d c) G =
        baseRen k N m (homogeneousComponent d (f c)) * Y ^ c := by
    intro c hc d hd
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hGdef, map_sum, Finset.sum_eq_single c, map_sum, Finset.sum_eq_single d]
    · exact (isMultiHomog_term (f c) d c j).weightedHomogeneousComponent_same
    · intro d' _ hne
      refine (isMultiHomog_term (f c) d' c j).weightedHomogeneousComponent_ne _ fun e => hne ?_
      have := congrFun e (Sum.inl ())
      simp only [bideg, Sum.elim_inl] at this
      omega
    · intro h
      exact absurd hd h
    · intro c' _ hne
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun d' _ => ?_
      refine (isMultiHomog_term (f c') d' c' j).weightedHomogeneousComponent_ne _ fun e => hne ?_
      have := congrFun e (Sum.inr ())
      simp only [bideg, Sum.elim_inr] at this
      omega
    · intro h
      exact absurd hc h

  have hmemF : ∀ c ∈ s, baseRen k N m (f c) ∈ W := by
    intro c hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_homogeneousComponent (f c), map_sum]
    refine Ideal.sum_mem _ fun d hd => ?_
    have hmem : baseRen k N m (homogeneousComponent d (f c)) * Y ^ c ∈ W := by
      rw [← hcomp c hc d hd]
      exact hH G hG _
    exact (Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right
      fun h => hj (Ideal.IsPrime.mem_of_pow_mem ‹_› c h)
  refine Polynomial.ext fun c => ?_
  rw [Polynomial.coeff_zero]
  by_cases hc : c ∈ s
  · have := hf c
    rw [phi_apply, (map_eq_zero_iff W _).2 (hmemF c hc)] at this
    exact Subtype.ext this.symm
  · exact Polynomial.notMem_support_iff.mp hc

theorem isAlgebraic_adjoin [W.IsPrime] (j : Fin m)
    (hrat : ∀ b : Fin m, ∃ f g : Kleiman.Poly k N, baseRen k N m g ∉ W ∧
      baseRen k N m g * X ⟨Sum.inr (), b⟩ - baseRen k N m f * X ⟨Sum.inr (), j⟩ ∈ W) :
    Algebra.IsAlgebraic (Algebra.adjoin (phi W).range (Set.range fun _ : Unit => eta W j))
      (FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W)) := by
  set R := NumbersDVR.MRing (graphIdx N m) k ⧸ W
  set L := FractionRing R
  set T := Algebra.adjoin (phi W).range (Set.range fun _ : Unit => eta W j)
  have hT : ∀ x ∈ T, IsAlgebraic T x := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : T)
  have hA : ∀ f, phi W f ∈ T := fun f => T.algebraMap_mem (⟨phi W f, f, rfl⟩ : (phi W).range)
  have hη : eta W j ∈ T := Algebra.subset_adjoin ⟨(), rfl⟩
  have hbase : ∀ a : Fin (N + 1), IsAlgebraic T (algebraMap R L (Ideal.Quotient.mk W (X ⟨Sum.inl (), a⟩))) := by
    intro a
    refine hT _ ?_
    have := hA (X a)
    rwa [phi_apply, baseRen_X] at this
  have hvar : ∀ v, IsAlgebraic T (algebraMap R L (Ideal.Quotient.mk W (X v))) := by
    rintro ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, i⟩
    · exact hbase i
    · obtain ⟨f, g, hg, hfg⟩ := hrat i
      have hg0 : phi W g ≠ 0 := by
        rw [phi_apply, Ne, map_eq_zero_iff]
        exact hg
      have hrel := (map_eq_zero_iff W _).2 hfg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_mul] at hrel
      have e : algebraMap R L (Ideal.Quotient.mk W (X ⟨Sum.inr (), i⟩)) = phi W f * eta W j / phi W g := by
        rw [eq_div_iff hg0, phi_apply, phi_apply]
        linear_combination hrel
      rw [e, div_eq_mul_inv]
      exact (hT _ (T.mul_mem (hA f) hη)).mul (IsAlgebraic.inv_iff.mpr (hT _ (hA g)))
  have hR : ∀ r : R, IsAlgebraic T (algebraMap R L r) := by
    intro r
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction F using MvPolynomial.induction_on with
    | C c =>
      refine hT _ ?_
      have := hA (C c)
      rwa [phi_apply, baseRen_C] at this
    | add f g hf hg =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_add (f := _)]
      exact hf.add hg
    | mul_X f v hf => rw [map_mul, map_mul]; exact hf.mul (hvar v)
  refine ⟨fun x => ?_⟩
  obtain ⟨a, d, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [div_eq_mul_inv]
  exact (hR a).mul (IsAlgebraic.inv_iff.mpr (hR d))

end RatioDim


open RatioDim in
theorem RatioDim.full : RatioDim.Statement := by
  intro k _ N m W hW hH j hj hrat
  have := hW
  set R := NumbersDVR.MRing (graphIdx N m) k ⧸ W
  set L := FractionRing R
  set A := (phi W).range
  have hb : IsTranscendenceBasis A (fun _ : Unit => eta W j) :=
    (algebraicIndependent_unique_type_iff.mpr (transcendental_eta W hH j hj)).isTranscendenceBasis_iff_isAlgebraic.mpr
      (isAlgebraic_adjoin W j hrat)
  have h1 : Algebra.trdeg A L = 1 := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  have : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k A).injective
  have hkA : Algebra.trdeg k A = Algebra.trdeg k (Kleiman.Poly k N ⧸ W.comap (baseRen k N m)) := by
    rw [← ker_phi]
    exact (Ideal.quotientKerEquivRange (phi W)).trdeg_eq.symm
  have htot : Algebra.trdeg k R = Algebra.trdeg k (Kleiman.Poly k N ⧸ W.comap (baseRen k N m)) + 1 := by
    rw [← GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := k) (A := R) L,
      ← trdeg_add_eq k A (A := L), h1, hkA]
  change ringKrullDim R = ringKrullDim (Kleiman.Poly k N ⧸ W.comap (baseRen k N m)) + 1
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k (A := R),
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k (A := Kleiman.Poly k N ⧸ W.comap (baseRen k N m)),
    htot, map_add, map_one]
  rfl

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeEmbed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated (cellRes_mk cellMon_mono isMultiHomog_monomial)

noncomputable section

namespace KHFreeEmbed

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem cellRes_monoFrac {J I : ∀ k, Finset (ι k)} (hJI : ∀ k, J k ⊆ I k) (a : (Σ k, ι k) → ℤ)
    (hJ : ∀ k, negSet a k ⊆ J k) :
    KH.cellRes S (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) J I (monoFrac S J a) = monoFrac S I a := by
  have hI : ∀ k, negSet a k ⊆ I k := fun k => (hJ k).trans (hJI k)
  unfold monoFrac
  rw [dite_eq_left hJ, dite_eq_left hI, cellRes_mk (cellMon_mono hJI)]

theorem blockSum_add_negExp (a : (Σ k, ι k) → ℤ) (k : K) :
    blockSum a k + ((∑ i, negExp a ⟨k, i⟩ : ℕ) : ℤ) = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ) := by
  unfold blockSum
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [negExp, posExp, Finsupp.coe_equivFunOnFinite_symm]
  omega

theorem isMultiHomog_posExp (a : (Σ k, ι k) → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial (posExp a) (1 : S) : MRingOver S ι) fun k => ∑ i, posExp a ⟨k, i⟩ :=
  isMultiHomog_monomial _ _ _ fun _ => rfl

theorem mk_posExp_mem (a : (Σ k, ι k) → ℤ) (e : K → ℤ) (he : ∀ k, e k = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ)) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (posExp a) 1) ∈
      KH.quotPart S (⊥ : Ideal (MRingOver S ι)) e := by
  unfold KH.quotPart
  refine Submodule.subset_span ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩
  · rw [he k]; exact Int.natCast_nonneg _
  · have : (fun k => (e k).toNat) = fun k => ∑ i, posExp a ⟨k, i⟩ := funext fun k => by rw [he k]; rfl
    rw [this]
    exact isMultiHomog_posExp a

theorem update_erase_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl; rw [Function.update_self]; exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]


open Classical in
theorem embed_apply (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) (I : KH.Cell K ι n) :
    embed S a n f I = if h : ∀ k, negSet a k ⊆ I.1 k then f ⟨I, h⟩ • monoFrac S I.1 a else 0 := by
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl


open Classical in
theorem cechD_apply (n : ℕ) (x : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n)
    (I : KH.Cell K ι (n + 1)) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n x I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        KH.faceSign I.1 k i • KH.cellRes S _ (Function.update I.1 k ((I.1 k).erase i)) I.1
          (x ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  unfold KH.cechD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl


open Classical in
theorem combD_apply (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
          ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
        KH.faceSign I.1.1 k i • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by
  unfold combD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

theorem embed_comm (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
      embed S a (n + 1) (combD S (negSet a) n f) := by
  classical
  funext I
  rw [cechD_apply, embed_apply]
  by_cases hI : ∀ k, negSet a k ⊆ I.1 k
  · rw [dite_eq_left hI]
    erw [combD_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n
    · rw [dite_eq_left hc]
      erw [embed_apply]
      by_cases hJ : ∀ l, negSet a l ⊆ Function.update I.1 k ((I.1 k).erase i) l
      · rw [dite_eq_left hJ, dite_eq_left ⟨hc, hJ⟩, LinearMap.map_smul_of_tower,
          cellRes_monoFrac (update_erase_subset I.1 k i) a hJ, smul_assoc]
      · rw [dite_eq_right hJ, dite_eq_right (fun h => hJ h.2), map_zero]
        simp
    · rw [dite_eq_right hc, dite_eq_right (fun h => hc h.1), zero_smul]
  · rw [dite_eq_right hI]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hc
    · erw [embed_apply]
      rw [dite_eq_right (fun hJ => hI fun l => (hJ l).trans (update_erase_subset I.1 k i l)), map_zero]
      simp
    · rfl

theorem embed_mem (a : (Σ k, ι k) → ℤ) (c d : K → ℤ) (h : blockSum a = c + d) (n : ℕ)
    (f : CombC S (negSet a) n) :
    embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n := by
  classical
  unfold KH.cechCc
  refine Submodule.mem_pi.mpr fun I _ => ?_
  erw [embed_apply]
  split_ifs with hI
  · refine Submodule.smul_mem _ _ ?_
    unfold monoFrac
    rw [dite_eq_left hI]
    refine Submodule.subset_span ⟨_, _, fun k => ∑ i, negExp a ⟨k, i⟩,
      isMultiHomog_monomial _ _ _ fun _ => rfl, ?_, rfl⟩
    refine mk_posExp_mem a _ fun k => ?_
    have hk := blockSum_add_negExp a k
    rw [h] at hk
    simp only [Pi.add_apply] at hk ⊢
    linarith
  · exact zero_mem _

theorem monoFrac_of_nonneg (a : (Σ k, ι k) → ℤ) (ha : ∀ p, 0 ≤ a p) :
    ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1 := by
  classical
  have hneg : ∀ k, negSet a k = ∅ := fun k =>
    Finset.filter_eq_empty_iff.mpr fun i _ => not_lt.mpr (ha _)
  have hnegExp : negExp a = 0 := by
    ext p
    simp only [negExp, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
    have := ha p
    omega
  refine ⟨_, mk_posExp_mem a _ fun k => ?_, fun I => ?_⟩
  · have hk := blockSum_add_negExp a k
    rw [hnegExp] at hk
    simpa using hk
  · have hI : ∀ k, negSet a k ⊆ I k := fun k => by rw [hneg k]; exact Finset.empty_subset _
    unfold monoFrac
    rw [dite_eq_left hI]
    congr 1
    exact Subtype.ext (by simp [hnegExp])

theorem full : KHFreeEmbed.Statement := by
  intro S _ K _ _ ι _ _ a
  exact ⟨fun n f => embed_comm a n f, fun c d h n f => embed_mem a c d h n f, monoFrac_of_nonneg a⟩

end KHFreeEmbed

end

end GroundTheory.Heights₂.Heights.Kleiman
end

