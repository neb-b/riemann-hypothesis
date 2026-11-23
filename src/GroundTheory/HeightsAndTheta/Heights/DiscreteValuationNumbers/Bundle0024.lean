module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVNumCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem VNumCut.proof (h : CutByForm.Statement.{u}) : VNumCut.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ G n hGp hGh hϖG hdim s c hs hsG bs
  set π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hπ
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => rfl
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := ker_map_residue_eq_span hϖ

  have hGbp : (specialIdeal G).IsPrime :=
    (SpecialIdealCorresp.proof O ϖ hϖ K ι G G hGp hϖG).1
  have hGbh : IsMultiHomogIdeal (specialIdeal G) := SpecialIdealMultiHomog.proof O K ι G hGh
  have hdimb : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal G) <
      ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.proof O ϖ hϖ K ι G hϖG]; exact hdim
  have hsb : IsMultiHomog (π s) c := isWeightedHomogeneous_map_of _ _ hs
  have hsbG : π s ∉ specialIdeal G := by
    intro hm
    apply hsG
    have hcm : (G.map π).comap π = G := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker, sup_eq_left, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hϖG
    rw [← hcm]
    exact hm

  have hcut := h (IsLocalRing.ResidueField O) K ι n (specialIdeal G) hGbp hGbh hdimb (π s) c hsb
    hsbG bs

  have hJ : G ⊔ Ideal.span {s} ⊔ Ideal.span {C ϖ} = G ⊔ Ideal.span {s} := by
    rw [sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left hϖG
  have hdiv : divCycle G s = divCycle (G ⊔ Ideal.span {s}) (C ϖ) := by
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hJ]
  have hmapJ : specialIdeal (G ⊔ Ideal.span {s}) = specialIdeal G ⊔ Ideal.span {π s} := by
    rw [hsp, hsp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have htr := SpecialCycleEval.proof SpecialIdealCorresp.proof SpecialIdealSurj.proof
    SpecialMultAt.proof O ϖ hϖ K ι (G ⊔ Ideal.span {s})
    (fun V => intNum (IsLocalRing.ResidueField O) V bs)
  rw [hmapJ, ← divCycle_eq_idealCycle] at htr
  show intNum (IsLocalRing.ResidueField O) (specialIdeal G) _ =
    cycEval (fun U => intNum (IsLocalRing.ResidueField O) (specialIdeal U) bs) (divCycle G s)
  rw [hcut, hdiv, htr]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVertCutEff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Helpers

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_form_pair_left {P H : Ideal (MRing ι R)} [hP : P.IsPrime]
    (hPm : IsMultiHomogIdeal P) (hPH : P ≤ H) {f g u v : MRing ι R} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hfP : f ∉ P) (hu : u ∉ H)
    (h : u * f - v * g ∈ P) :
    ∃ (u' v' : MRing ι R) (e d : K → ℕ), IsMultiHomog u' e ∧ IsMultiHomog v' d ∧
      d + bg = e + bf ∧ u' ∉ H ∧ u' * f - v' * g ∈ P := by
  classical
  obtain ⟨e, he⟩ := exists_component_not_mem hu
  set u' := weightedHomogeneousComponent (blockWeight ι) e u with hu'
  have hc := hPm _ h (e + bf)
  rw [map_sub, weightedHomogeneousComponent_mul_form hf, weightedHomogeneousComponent_mul_form hg,
    if_pos le_add_self, add_tsub_cancel_right, ← hu'] at hc
  by_cases hle : bg ≤ e + bf
  · rw [if_pos hle] at hc
    exact ⟨u', _, e, e + bf - bg, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, tsub_add_cancel_of_le hle, he, hc⟩
  · rw [if_neg hle, sub_zero] at hc
    exact ((hP.mem_or_mem hc).elim (fun h' => he (hPH h')) hfP).elim

end Helpers

theorem VertCutEff.proof (h1 : VNumCut.Statement.{u}) (h2 : DivisorIdealCycle.Statement.{u})
    (h3 : IntNumAddFirst.Statement.{u}) : VertCutEff.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n hmodel b f g hE W x hxP hWmin hrel hWmh hϖW hcyc L
  have hP : P.IsPrime := hmodel.multiProj.isPrime
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨hV, hreg⟩ := hE
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  obtain ⟨u₀, v₀, hu₀, h₀⟩ := hreg W hWp hPW hrel
  obtain ⟨u, v, e, d, hu, hv, hde, huW, huv⟩ :=
    exists_form_pair_left hmodel.multiProj.multiHomog hPW hf hg hV.num_not_mem hu₀ h₀
  have huP : u ∉ P := fun h => huW (hPW h)

  have hvW : v ∉ W := by
    intro hvW
    have hvP : v ∉ P := by
      intro hvP
      have hufP : u * f ∈ P := by
        have h' := P.add_mem huv (P.mul_mem_right g hvP)
        rwa [sub_add_cancel] at h'
      exact (hP.mem_or_mem hufP).elim huP hV.num_not_mem
    have hmul := mem_minimalPrimes_sup_span_mul (P := P) (x := x) (y := v) hvP hWmin
    have hWv : W ∈ (P ⊔ Ideal.span {v}).minimalPrimes :=
      ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hvW)⟩, fun Q hQ hQW =>
        hmul.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) ((Ideal.span_singleton_le_iff_mem _).mpr
          (Q.mul_mem_left x (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v)))))⟩ hQW⟩
    have hpos : divCycle P v W ≠ 0 := by
      unfold divCycle
      rw [dite_eq_left ⟨hWv, hrel⟩]
      have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {v}) W hWv
      have hnz : multAt (P ⊔ Ideal.span {v}) W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
          Ideal.Quotient.eq_zero_iff_mem] at hr0
        exact hr (hWv.1.2 hr0)
      have htn : (multAt (P ⊔ Ideal.span {v}) W).toNat ≠ 0 :=
        fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
      exact_mod_cast htn
    have hu0 : divCycle P u W = 0 := by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h, -⟩
      exact huW (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self u)))
    have e1 := congrFun (DivCycleMul.proof O K ι P u f hP huP hV.num_not_mem) W
    have e2 := congrFun (DivCycleMul.proof O K ι P v g hP hvP hV.den_not_mem) W
    have e3 := congrFun (divCycle_eq_of_sub_mem huv) W
    simp only [Pi.add_apply] at e1 e2
    unfold ratDiv at hcyc
    omega

  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hmodel.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdim : ringKrullDim (MRing ι O ⧸ W) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have h' := DimStrictDrop.proof (MRing ι O) P W hlt
    rw [hmodel.dim, show n + 1 + 1 + Fintype.card K = n + 2 + Fintype.card K by omega] at h'
    exact withBotENat_lt_of_add_one_le h'

  have hcu := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim u e hu huW L
  have hcv := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim v d hv hvW L
  have hWbar : (specialIdeal W).IsPrime := (SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW).1
  have hadd := h3 (IsLocalRing.ResidueField O) K ι n (specialIdeal W) hWbar
    (SpecialIdealMultiHomog.proof O K ι W hWmh)
    (by rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]; exact hdim) b (fun k => (e k : ℤ)) L
  have hdeg : (fun k => (d k : ℤ)) = b + fun k => (e k : ℤ) := by
    rw [← hb]
    funext k
    have hk := congrFun hde k
    simp only [Pi.add_apply] at hk ⊢
    omega
  have key : vNum W (Matrix.vecCons b L) = vNum W (Matrix.vecCons (fun k => (d k : ℤ)) L) -
      vNum W (Matrix.vecCons (fun k => (e k : ℤ)) L) := by
    rw [hdeg]
    unfold vNum
    rw [hadd]
    ring
  rw [key, hcv, hcu, ← h2 O K ι P W f g u v hP hWp hPW hV.den_not_mem
    (fun U hU hWU hUrel => hreg U hU (hPW.trans hWU) hUrel) huW hvW huv]

  unfold cycEval ratDiv
  rw [← finsum_sub_distrib
    ((DivCycleFiniteSupport.proof O K ι W v).subset (Function.support_mul_subset_left _ _))
    ((DivCycleFiniteSupport.proof O K ι W u).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun U => ?_
  ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalComponentFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalComponentFibre.proof (h : FibreVarieties.Statement.{0}) :
    VerticalComponentFibre.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP f b hf hfP W hW hrel hϖW
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro hmem
    have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hP.noTorsion, Ideal.mem_bot] at this
    exact hϖ.ne_zero this

  have hmin : W ∈ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).minimalPrimes := by
    refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hϖW)⟩, ?_⟩
    rintro Q ⟨hQ, hQle⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun e => hWQ (e ▸ le_rfl))
    have hPQ : P ≤ Q := le_sup_left.trans hQle
    have hϖQ : (C ϖ : MRing ι O) ∈ Q := hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    let π := Ideal.Quotient.mk P
    have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
    have : (W.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPW)
    have : (Q.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPQ)
    have hle1 : (W.map π).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    have hlt' : Q.map π < W.map π := by
      refine (Ideal.map_mono hlt.le).lt_of_not_ge fun e => hlt.not_ge ?_
      have := Ideal.comap_mono (f := π) e
      rwa [Ideal.comap_map_of_surjective' π hsurj, Ideal.comap_map_of_surjective' π hsurj,
        Ideal.mk_ker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ] at this
    have : (W.map π).FiniteHeight := ⟨Or.inr (hle1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
    have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt').trans_le hle1
    rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
    have hbot : Q.map π ≤ ⊥ := h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    have : π (C ϖ) ∈ (⊥ : Ideal (MRing ι O ⧸ P)) := hbot (Ideal.mem_map_of_mem π hϖQ)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hϖP this

  have hdiv : divCycle P (C ϖ) W ≠ 0 := by
    unfold divCycle
    rw [dite_eq_left ⟨hmin, hrel⟩]
    have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
        ((P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W),
        Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
      exact hmin
    have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
    have : Nontrivial (Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
    have hpos := Module.length_pos (R := Localization.AtPrime W)
      (M := Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W)))
    rw [multAt, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
    exact_mod_cast (ENat.toNat_pos hpos.ne' hne).ne'
  exact (h O ϖ hϖ K ι P d hP).2 W hdiv

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section JoinPullback

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}

theorem joinCoords_inl {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (k : K)
    (i : ι k) : joinCoords y y' ⟨Sum.inl k, i⟩ = y ⟨k, i⟩ := rfl

theorem pointConeMap_joinCoords_joinForm {Ω : Type*} [Field Ω] (R : Type*) [CommRing R]
    [Algebra R Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    pointConeMap R (joinCoords y y') (joinForm f) =
      rename (Sum.inl : K → K ⊕ K') (pointConeMap R y f) := by
  simp only [pointConeMap, joinForm, aeval_rename]
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    obtain ⟨k, i⟩ := v
    simp [hp, joinCoords_inl]

theorem joinForm_mem_pointIdeal_iff {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    joinForm f ∈ pointIdeal R (joinCoords y y') ↔ f ∈ pointIdeal R y := by
  simp only [pointIdeal, RingHom.mem_ker, pointConeMap_joinCoords_joinForm]
  exact map_eq_zero_iff _ (rename_injective _ Sum.inl_injective)

theorem isMultiHomog_joinForm [DecidableEq K] [DecidableEq K'] {R : Type*} [CommRing R]
    {f : MRing ι R} {bf : K → ℕ} (hf : IsMultiHomog f bf) :
    IsMultiHomog (joinForm (ι' := ι') f) (Sum.elim bf 0) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa [joinForm] using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [joinForm, map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    simp only [joinForm, rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
      Finsupp.weight_apply]
    funext s
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight]
    rcases s with k | k
    · simp [Pi.single_apply]
    · simp

end JoinPullback

theorem VerticalDivisorJoinPullback.proof : VerticalDivisorJoinPullback.Statement := by
  intro O _ _ _ ϖ Ω _ _ K _ _ ι _ K' _ _ ι' _ y y' b f g hD
  refine IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨Sum.elim bf 0, Sum.elim bg 0, isMultiHomog_joinForm hf, isMultiHomog_joinForm hg, ?_⟩
    funext s
    rcases s with k | k
    · simp [joinDeg, ← hb]
    · simp [joinDeg]
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.num_not_mem
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.den_not_mem
  · intro W hW hPW hrel hϖ
    let φ : MRing ι O →ₐ[O] MRing (Sum.elim ι ι') O :=
      rename (fun p : (Σ k, ι k) => (⟨Sum.inl p.1, p.2⟩ : Σ s : K ⊕ K', Sum.elim ι ι' s))
    have hφ : ∀ h, joinForm (ι' := ι') h = φ h := fun _ => rfl
    have hle : pointIdeal O y ≤ W.comap φ := by
      intro h hh
      rw [Ideal.mem_comap, ← hφ]
      exact hPW ((joinForm_mem_pointIdeal_iff O y y' h).mpr hh)
    have hrel' : IsRelevant (W.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap]; simpa [φ, rename_X] using hi⟩
    have hϖ' : (C ϖ : MRing ι O) ∉ W.comap φ := by
      rw [Ideal.mem_comap]; simpa [φ, rename_C] using hϖ
    obtain ⟨u, v, hu, hv, huv⟩ :=
      hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ'
    refine ⟨joinForm u, joinForm v, hu, hv, ?_⟩
    have := (joinForm_mem_pointIdeal_iff O y y' _).mpr huv
    simpa [hφ, map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RingKrullDimQuotientLeComapAddOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem ringKrullDim_quotient_le_comap_add_one {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {J : Type} {R : Type*} [CommRing R] [IsNoetherianRing R]
    (G' : Ideal (MRing (extIdx ι J) R)) [G'.IsPrime] (j₀ : J)
    (hY : ∀ j, j ≠ j₀ → (newVar j : MRing (extIdx ι J) R) ∈ G') :
    ringKrullDim (MRing (extIdx ι J) R ⧸ G') ≤
      ringKrullDim (MRing ι R ⧸ G'.comap (liftForm (J := J) (ι := ι) (R := R))) + 1 := by
  set G := G'.comap (liftForm (J := J) (ι := ι) (R := R)) with hGdef
  let φ : (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Ideal.quotientMap G' (liftForm (J := J) (ι := ι) (R := R)).toRingHom le_rfl
  let ψ : Polynomial (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Polynomial.eval₂RingHom φ (Ideal.Quotient.mk G' (newVar j₀))
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨Polynomial.C (Ideal.Quotient.mk G (C a)), ?_⟩
      simp [ψ, φ, Ideal.quotientMap_mk, liftForm]
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [ψ.map_add, ha, hb, (Ideal.Quotient.mk G').map_add]⟩
    | mul_X p v hp =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨o, i⟩ := v
      cases o with
      | none =>
        by_cases hi : i = j₀
        · subst hi
          refine ⟨a * Polynomial.X, ?_⟩
          rw [map_mul, ha, map_mul]
          congr 1
          simp [ψ, newVar]
        · refine ⟨0, ?_⟩
          rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
          exact G'.mul_mem_left _ (hY i hi)
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk G (X ⟨k, i⟩)), ?_⟩
        rw [map_mul, ha, map_mul]
        congr 1
        simp [ψ, φ, Ideal.quotientMap_mk, liftForm, rename_X]
  calc ringKrullDim (MRing (extIdx ι J) R ⧸ G')
      ≤ ringKrullDim (Polynomial (MRing ι R ⧸ G)) := ringKrullDim_le_of_surjective ψ hψ
    _ = ringKrullDim (MRing ι R ⧸ G) + 1 := Polynomial.ringKrullDim_of_isNoetherianRing

theorem mem_minimalPrimes_of_ringKrullDim {A : Type*} [CommRing A] (P G : Ideal A) [P.IsPrime]
    [G.IsPrime] (s : A) (hsP : s ∉ P) (N : ℕ) (hP : ringKrullDim (A ⧸ P) = (N : WithBot ℕ∞))
    (hle : P ⊔ Ideal.span {s} ≤ G) (hG : (N : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ G) + 1) :
    G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
  refine ⟨⟨inferInstance, hle⟩, fun Q hQ hQG => ?_⟩
  have : Q.IsPrime := hQ.1
  by_contra hGQ
  have hsQ : s ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h => hsP (h ▸ hsQ)
  have h1 := DimStrictDrop.proof A Q G (lt_of_le_not_ge hQG hGQ)
  have h2 := DimStrictDrop.proof A P Q hPQ
  have h3 : (N : WithBot ℕ∞) + 1 ≤ (N : WithBot ℕ∞) :=
    calc (N : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ G) + 1 + 1 := by gcongr
      _ ≤ ringKrullDim (A ⧸ Q) + 1 := by gcongr
      _ ≤ N := hP ▸ h2
  have h4 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : N + 1 ≤ N := by exact_mod_cast h4
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinIntNum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx)

def JoinIntNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι F)) (n : ℕ) (bs : Fin n → K → ℤ),
    intNum F (V.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (bs j)) =
      intNum F V bs

end GroundTheory.Heights₂.Heights.NumbersDVR
end

