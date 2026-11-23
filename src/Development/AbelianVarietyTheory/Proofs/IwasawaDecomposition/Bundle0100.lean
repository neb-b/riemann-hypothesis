module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem exists_units_hom {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field K] [TopologicalSpace K]
    (F : Γ →* K) (hF : Continuous F) : ∃ f : Γ →* Kˣ, Continuous f ∧ ∀ x, ((f x : Kˣ) : K) = F x :=
  ⟨F.toHomUnits, Units.continuous_iff.mpr ⟨hF, hF.comp continuous_inv⟩, fun _ => rfl⟩

theorem exists_infPow_hom : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* ℂˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : ℂˣ) : ℂ) = infPow n x := by
  intro E _ _ n
  have h0 : ∀ (x : Ideles E) (w : InfinitePlace E), (x : AdeleRing (𝓞 E) E).1 w ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)
  haveI : ∀ w : InfinitePlace E, Fintype {i : w.Completion →+* ℂ // Continuous i} := fun w =>
    @Fintype.ofFinite _ (finite_contEmbInf w)
  have e : ∀ x : Ideles E, infPow n x = ∏ w : InfinitePlace E, ∏ i : {i : w.Completion →+* ℂ // Continuous i},
      i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion)) := fun x =>
    Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
  let F : Ideles E →* ℂ :=
    { toFun := infPow n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (infPow n)
  rw [funext e]
  refine continuous_finsetProd _ fun w _ => continuous_finsetProd _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))

theorem exists_lPow_hom : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* (Qbar l)ˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : (Qbar l)ˣ) : Qbar l) = lPow ι n x := by
  intro E _ _ l _ ι n
  have hl : l.Prime := Fact.out
  have h0 : ∀ (x : Ideles E) (v : HeightOneSpectrum (𝓞 E)), (x : AdeleRing (𝓞 E) E).2 v ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) x.mul_inv)
  haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype {j : v.adicCompletion E →+* Qbar l // Continuous j} := fun v =>
    @Fintype.ofFinite _ (finite_contEmb v)
  have hI : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  have e : ∀ x : Ideles E, lPow ι n x = ∏ v ∈ (Ideal.finite_factors hI).toFinset,
      ∏ j : {j : v.adicCompletion E →+* Qbar l // Continuous j}, j.1 ((x : AdeleRing (𝓞 E) E).2 v) ^
        n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E))) := fun x => by
    unfold lPow
    rw [finprod_eq_prod_of_mulSupport_subset (s := (Ideal.finite_factors hI).toFinset)]
    · exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
    · intro v hv
      by_contra h
      refine hv (locPow_of_notMem ι n (fun hm => h ?_) _)
      exact Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Ideal.dvd_span_singleton.mpr hm))
  let F : Ideles E →* Qbar l :=
    { toFun := lPow ι n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (lPow ι n)
  rw [funext e]
  refine continuous_finsetProd _ fun w _ => continuous_finsetProd _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((RestrictedProduct.continuous_eval w).comp (continuous_snd.comp Units.continuous_val))

theorem infPow_diagUnits : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ), infPow n (diagUnits E k) = ∏ φ : E →+* ℂ, φ (k : E) ^ n φ := by
  intro E _ _ n k
  classical
  let J : InfinitePlace E → Type := fun w => {i : w.Completion →+* ℂ // Continuous i}
  let res : (Σ w, J w) → (E →+* ℂ) := fun p => p.2.1.comp (algebraMap E p.1.Completion)
  have hd : ∀ w : InfinitePlace E, DenseRange (algebraMap E w.Completion) := fun w => by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, by simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]⟩
  have hmk : ∀ p : Σ w, J w, InfinitePlace.mk (res p) = p.1 := by
    rintro ⟨w, i⟩
    have hn : ∀ y : w.Completion, ‖i.1 y‖ = ‖y‖ := fun y => by
      rcases w.isReal_or_isComplex with hw | hw
      · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry
        have h1 := Complex.ringHom_eq_ofReal_of_continuous (f := i.1.comp e.symm.toRingHom) (i.2.comp he.continuous)
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_real z)
      · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := i.1.comp e.symm.toRingHom)
          (i.2.comp he.continuous) with h1 | h1
        · exact congrArg norm (DFunLike.congr_fun h1 z)
        · exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_conj z)
    refine InfinitePlace.ext _ _ fun a => ?_
    rw [InfinitePlace.apply]
    apply (hn _).trans
    simpa [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
      (InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ a))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    obtain rfl : v = v' := (hmk ⟨v, j⟩).symm.trans ((congrArg InfinitePlace.mk h).trans (hmk ⟨v', j'⟩))
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (hd v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨j, hj, e⟩ := GlobalTheory.InfTypeLocal.exists_ext φ
    exact ⟨⟨_, j, hj⟩, RingHom.ext e⟩
  haveI : ∀ w, Fintype (J w) := fun w => @Fintype.ofFinite _ (finite_contEmbInf w)
  rw [← Fintype.prod_bijective res ⟨hinj, hsurj⟩ (fun p => res p (k : E) ^ n (res p)) _ fun _ => rfl,
    Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _

theorem isOpenEmbedding_val_inf (E : Type) [Field E] [NumberField E] :
    Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
  Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)

theorem isOpen_connectedComponentOfOne_inf : ∀ (E : Type) [Field E] [NumberField E], IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) : Set (InfiniteAdeleRing E)ˣ) := by
  intro E _ _
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := (isOpenEmbedding_val_inf E).locallyConnectedSpace
  exact isOpen_connectedComponent

theorem denseRange_units_inf : ∀ (E : Type) [Field E] [NumberField E], DenseRange (fun k : Eˣ => (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ)) := by
  intro E _ _
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap E).exists_mem_open
    ((isOpenEmbedding_val_inf E).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    rw [map_zero] at hk
    have h1 := congrFun v.mul_inv w
    rw [hk, zero_mul] at h1
    exact zero_ne_one (α := w.Completion) h1
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem pos_of_mem_connectedComponentOfOne : ∀ (E : Type) [Field E] [NumberField E] (k : Eˣ), (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ → ∀ φ : E →+* ℝ, 0 < φ (k : E) := by
  intro E _ _ k hk φ
  obtain ⟨e, he, hek⟩ := GlobalTheory.InfTypeLocal.exists_ext (Complex.ofRealHom.comp φ)
  let w := InfinitePlace.mk (Complex.ofRealHom.comp φ)
  have hd : DenseRange (algebraMap E w.Completion) := by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, by simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]⟩
  have him : ∀ y : w.Completion, (e y).im = 0 := fun y =>
    congrFun (hd.equalizer (g := fun y => (e y).im) (h := fun _ => 0) (Complex.continuous_im.comp he)
      continuous_const (funext fun a => (congrArg Complex.im (hek a)).trans (by simp))) y
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => (e ((u : InfiniteAdeleRing E) w)).re
  have hg : Continuous g :=
    Complex.continuous_re.comp (he.comp ((continuous_apply w).comp Units.continuous_val))
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : e ((u : InfiniteAdeleRing E) w) = 0 := Complex.ext h (him _)
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) ((map_eq_zero e).mp h1)
  have hg1 : g 1 = 1 := by
    show (e 1).re = 1
    simp
  have hgk : g (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = φ k := by
    show (e (algebraMap E _ (k : E))).re = _
    rw [hek]
    simp
  by_contra hneg
  have := isPreconnected_connectedComponent.intermediate_value hk mem_connectedComponent hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by rw [hgk]; exact not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  obtain ⟨u, -, hu⟩ := this
  exact hg0 u hu

end GlobalTheory.HeckeGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Chr.IdlFact

namespace GlobalTheory.Mem.Chr.KDVal

variable {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]


open Classical in
theorem valAt_locF (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    valAt w (locF (L := L) F v k) =
      if w.under (𝓞 F) = v then WithZero.exp (-ordF w (upF F k)) else 1 := by
  unfold locF
  rw [map_prod]
  have hm : ∀ Q : HeightOneSpectrum (𝓞 L), Q ∈ aboveF (L := L) F v ↔ Q.under (𝓞 F) = v := fun Q => by
    simp [aboveF]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w ((hm w).2 hw) (fun Q _ hQ => valAt_localIdele_ne hQ.symm _),
      valAt_localIdele_self]
    have h0 : w.valuation L ((upF F k : Lˣ) : L) ≠ 0 := by simp
    unfold ordF
    rw [neg_neg, WithZero.exp_log h0]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  · exact Finset.prod_eq_one fun Q hQ => valAt_localIdele_ne (fun e : w = Q => hw (by rw [e]; exact (hm Q).1 hQ)) _

def balanced : Subgroup (Ideles L) where
  carrier := {a | ∀ w w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) → valAt w a = valAt w' a}
  one_mem' := fun w w' _ => by rw [map_one, map_one]
  mul_mem' := fun {a b} ha hb w w' h => by rw [map_mul, map_mul, ha w w' h, hb w w' h]
  inv_mem' := fun {a} ha w w' h => by rw [map_inv, map_inv, ha w w' h]

theorem unitIdl_le_balanced : unitIdl L ≤ balanced (L := L) F := fun a ha w w' _ =>
  (ha w).trans (ha w').symm

variable {F}

theorem locF_mem_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : locF (L := L) F v k ∈ balanced (L := L) F := fun w w' h => by
  rw [valAt_locF, valAt_locF, hu, hu, h]

theorem mem_sup_of_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (G : Subgroup (Ideles L)) (hG : ∀ v k, locF (L := L) F v k ∈ G) (a : Ideles L)
    (ha : a ∈ balanced (L := L) F) : a ∈ G ⊔ unitIdl L := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 F)
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles L := ∏ v ∈ T, locF (L := L) F v (unif v) ^ m v
  have hb : b ∈ G := prod_mem fun v _ => zpow_mem (hG _ _) _
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 F) → valAt w (locF (L := L) F v (unif v) ^ m v) = 1 := fun v hv => by
      rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul]
      have hex : ∃ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) := ⟨w, rfl⟩
      have hm : m (w.under (𝓞 F)) = -WithZero.log (valAt w a) := by
        simp only [m]
        rw [dite_eq_left hex, ha w hex.choose hex.choose_spec]
      rw [hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl L := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)
  rw [← mul_inv_cancel_left b a]
  exact Subgroup.mul_mem_sup hb hu'

end GlobalTheory.Mem.Chr.KDVal


open GlobalTheory.Mem.Chr.KDVal in
open Classical in
theorem GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : Ideles H.E), a ∈ KD H ⊔ unitIdl H.E ↔ ∀ w w', IsConjPl H w w' → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w) = Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w') := by
  intro R H a
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hiff : ∀ w w' : HeightOneSpectrum (𝓞 H.E),
      w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ (w' = w ∨ IsConjPl H w w') := fun w w' => by
    rw [under_eq_iff_conjPl c hcm.rank hcm.ne, conjPl_main.2.1 R H w w']
    have : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
    rw [this]
  constructor
  · intro ha w w' h
    have hle : KD H ⊔ unitIdl H.E ≤ balanced (L := H.E) H.F := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) (unitIdl_le_balanced _)
      rintro x (hx | ⟨v, k, rfl⟩)
      · exact unitIdl_le_balanced _ hx.1
      · exact locF_mem_balanced hu v k
    exact hle ha w w' ((hiff w w').2 (Or.inr h))
  · intro h
    refine mem_sup_of_balanced hu _ (locF_mem_KD H) a fun w w' hw => ?_
    rcases (hiff w w').1 hw with rfl | h'
    · rfl
    · exact h w w' h'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPowUnitsOfUnderEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Chr

theorem twist_pow_units_of_under_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (ξ : HChar H.E), IsTwist H S ξ → ∀ (Q Q' : HeightOneSpectrum (𝓞 H.E)), Q.under (𝓞 H.F) = Q'.under (𝓞 H.F) → ∀ n : ℕ, (∀ x, IsUnitAt Q' x → ξ.loc Q' x ^ n = 1) → ∀ x, IsUnitAt Q x → ξ.loc Q x ^ n = 1 := by
  intro R H S ξ hξ Q Q' hu n hn x hx
  by_cases hQ : Q = Q'
  · subst hQ
    exact hn x hx
  by_cases hur : ξ.UnrAt Q
  · rw [hur x hx, one_pow]
  obtain ⟨-, htriv, htame, hram⟩ := hξ
  obtain ⟨-, hq, -, -⟩ := hram Q hur
  obtain ⟨a, k, hcop, hk, hcong⟩ := (GlobalTheory.localUnit_congr_global H.E Q x hx).2 _ hq rfl
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hqQ : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q.asIdeal := Ideal.absNorm_mem Q.asIdeal
  have hqQ' : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q'.asIdeal := by
    have h1 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ (Q.under (𝓞 H.F)).asIdeal := by
      show algebraMap (𝓞 H.F) (𝓞 H.E) _ ∈ Q.asIdeal
      rw [map_natCast]
      exact hqQ
    rw [hu] at h1
    have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ Q'.asIdeal := h1
    rwa [map_natCast] at h2
  have hkQ : IsUnitAt Q (atFin Q k) := isUnitAt_nat (H := H) hqQ hcop hk
  have hkQ' : IsUnitAt Q' (atFin Q' k) := isUnitAt_nat (H := H) hqQ' hcop hk
  have hxk : IsUnitAt Q (x * (atFin Q k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : ξ.loc Q (x * (atFin Q k)⁻¹) = 1 := htame Q _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have ha0 : (a : H.F) ≠ 0 := by
    intro h
    have h0 : a = 0 := by exact_mod_cast h
    apply k.ne_zero
    rw [hk, h0, Nat.cast_zero]
  have hup : upF H.F (Units.mk0 (a : H.F) ha0) = k := by
    apply Units.ext
    rw [hk]
    exact map_natCast (algebraMap H.F H.E) a
  have hab : aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) = {Q, Q'} := by
    have hc' : ConjPl c.toRingEquiv Q Q' :=
      ((under_eq_iff_conjPl c hcm.rank hcm.ne Q Q').1 hu.symm).resolve_left (Ne.symm hQ)
    ext P
    have hm : P ∈ aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = Q.under (𝓞 H.F) := by
      unfold aboveF
      rw [Set.Finite.mem_toFinset]
      rfl
    rw [hm, under_eq_iff_conjPl c hcm.rank hcm.ne Q P, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h => (existsUnique_conjPl _ Q).unique h hc', ?_⟩
    rintro rfl
    exact hc'
  have h2 := htriv.1 (Q.under (𝓞 H.F)) (Units.mk0 (a : H.F) ha0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hQ, hup] at h2
  have h3 : ξ.loc Q (atFin Q k) * ξ.loc Q' (atFin Q' k) = 1 := h2
  have h4 := congrArg (· ^ n) h3
  simp only [mul_pow, hn _ hkQ', mul_one, one_pow] at h4
  rw [h1, h4]

end GlobalTheory.Mem.Chr
end

