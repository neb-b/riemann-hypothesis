module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.RatLattice

variable {F : Type} [Field F] [NumberField F]

theorem closure_range_rat (N : ℕ) :
    AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) =
      AddSubgroup.pi Set.univ fun _ : Fin N => (algebraMap F (AF F)).range.toAddSubgroup := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩
  · intro u hu
    choose ξ hξ using fun l => hu l trivial
    have : u = rat ξ := funext fun l => (hξ l).symm
    rw [this]
    exact AddSubgroup.subset_closure ⟨ξ, rfl⟩

theorem mem_closure_iff (N : ℕ) (u : Fin N → AF F) :
    u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ↔ ∃ ξ, u = rat ξ := by
  rw [closure_range_rat]
  constructor
  · intro hu
    choose ξ hξ using fun l => hu l trivial
    exact ⟨ξ, funext fun l => (hξ l).symm⟩
  · rintro ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩

theorem rat_injective (N : ℕ) : Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) := by
  haveI : Nontrivial (AF F) := by
    show Nontrivial (AdeleRing (𝓞 F) F)
    unfold AdeleRing
    infer_instance
  intro ξ η h
  funext l
  exact (algebraMap F (AF F)).injective (congrFun h l)

theorem isFD_pi {Y : Type} [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {A : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain A D ν) (n : ℕ) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : Fin n => A) (Set.univ.pi fun _ : Fin n => D)
      (Measure.pi fun _ : Fin n => ν) := by
  have hq (i : Fin n) := Measure.quasiMeasurePreserving_eval (fun _ : Fin n => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : Fin n => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

end GlobalTheory.SWQ.RatLattice

open GlobalTheory.SWQ.RatLattice in
theorem GlobalTheory.SWQ.rat_lattice_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  intro F _ _ N ν hν
  obtain ⟨hH, D₀, hD₀m, hD₀, hD₀1⟩ := hν
  haveI := hH
  refine ⟨?_, mem_closure_iff N, rat_injective N, ?_, ?_⟩
  · unfold muV
    infer_instance
  · obtain ⟨K, hK, hKc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨Set.univ.pi fun _ => K, isCompact_univ_pi fun _ => hK, fun u => ?_⟩
    choose ξ hξ using fun l => hKc (u l)
    exact ⟨ξ, fun l _ => hξ l⟩
  · refine ⟨Set.univ.pi fun _ => D₀, MeasurableSet.univ_pi fun _ => hD₀m, ?_, ?_⟩
    · rw [closure_range_rat]
      exact isFD_pi ν hD₀ N
    · unfold muV
      rw [Measure.pi_pi]
      simp [hD₀1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Polynomial

theorem GlobalTheory.unramified_adjoin_sqrt_of_not_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : 𝓞 (maximalRealSubfield L)) (δ : L), δ ^ 2 = ((a : maximalRealSubfield L) : L) → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), 2 * a ∉ (w.under (𝓞 (maximalRealSubfield L))).asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ a δ hδ hδK w ha

  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    exact (RingOfIntegers.isIntegral_coe a).algebraMap
  let d : 𝓞 L := ⟨δ, hint⟩
  have hd : algebraMap (𝓞 L) L d = δ := rfl
  have hdA : IsIntegral (𝓞 (maximalRealSubfield L)) d := Algebra.IsIntegral.isIntegral d
  have hδR : IsIntegral (maximalRealSubfield L) δ := Algebra.IsIntegral.isIntegral δ
  have hsq : d ^ 2 = algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hd, hδ, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L]
    rfl

  have hfin : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hdegK : (minpoly (maximalRealSubfield L) δ).natDegree = 2 := by
    refine le_antisymm (hfin ▸ minpoly.natDegree_le δ) ?_
    rw [minpoly.two_le_natDegree_iff hδR]
    rintro ⟨x, hx⟩
    exact hδK (hx ▸ x.2)
  have hdeg : (minpoly (𝓞 (maximalRealSubfield L)) d).natDegree = 2 := by
    rw [← hdegK, ← hd, minpoly.isIntegrallyClosed_eq_field_fractions (maximalRealSubfield L) L hdA,
      (minpoly.monic hdA).natDegree_map]

  have hpoly : minpoly (𝓞 (maximalRealSubfield L)) d = X ^ 2 - C a := by
    have hm : (X ^ 2 - C a : (𝓞 (maximalRealSubfield L))[X]).Monic := monic_X_pow_sub_C a two_ne_zero
    have hroot : aeval d (X ^ 2 - C a) = 0 := by
      rw [map_sub, aeval_X_pow, aeval_C, hsq, sub_self]
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hdA) hm
      (minpoly.isIntegrallyClosed_dvd hdA hroot) ?_).symm
    rw [hdeg, natDegree_X_pow_sub_C _]

  have hadj : Algebra.adjoin (maximalRealSubfield L) {algebraMap (𝓞 L) L d} = ⊤ := by
    have htop : IntermediateField.adjoin (maximalRealSubfield L) {δ} = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_le le_top (by
        rw [IntermediateField.finrank_top', hfin, IntermediateField.adjoin.finrank hδR, hdegK])
    rw [hd, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hδR.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]

  have hmem : 2 * d ∈ differentIdeal (𝓞 (maximalRealSubfield L)) (𝓞 L) := by
    have := aeval_derivative_mem_differentIdeal (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L d hadj
    simpa [hpoly, derivative_X_pow, one_add_one_eq_two, map_ofNat] using this

  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  have h2d : 2 * d ∈ w.asIdeal := Ideal.dvd_iff_le.mp hdvd hmem
  have h4a : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) (2 * (2 * a)) ∈ w.asIdeal := by
    have := w.asIdeal.mul_mem_left (2 * d) h2d
    convert this using 1
    rw [map_mul, map_mul, map_ofNat, ← hsq]
    ring
  have h4a' : 2 * (2 * a) ∈ (w.under (𝓞 (maximalRealSubfield L))).asIdeal := h4a
  rcases (w.under (𝓞 (maximalRealSubfield L))).isPrime.mem_or_mem h4a' with h | h
  · exact ha (Ideal.mul_mem_right a _ h)
  · exact ha h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitOfSquare

private theorem valued_v_algebraMap_adicCompletion_foundation {F : Type} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x :=
  u.valuedAdicCompletion_eq_valuation' x

theorem exists_valuation_lt_one {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0)
    (h : IsSquare (algebraMap F (u.adicCompletion F) a)) : ∃ c : F, u.valuation F (1 / 4 - c ^ 2 * a) < 1 := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ha
    simpa using hs
  obtain ⟨π, hπ⟩ := u.valuation_exists_uniformizer F
  have hπ1 : u.valuation F π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set h2 : u.adicCompletion F := algebraMap F (u.adicCompletion F) 2⁻¹ with hh2
  set p : u.adicCompletion F := algebraMap F (u.adicCompletion F) π with hp
  have hp0 : p ≠ 0 := (map_ne_zero _).mpr hπ0
  have hvp : Valued.v p < 1 := by rw [hp, valued_v_algebraMap_adicCompletion_foundation]; exact hπ1
  have hI := Valued.isOpen_integer (u.adicCompletion F)
  have hcont : Continuous (fun y : u.adicCompletion F => (y * s - h2) * p⁻¹) :=
    ((continuous_id.mul continuous_const).sub continuous_const).mul continuous_const
  obtain ⟨c, hc⟩ := (u.denseRange_algebraMap F).exists_mem_open (hI.preimage hcont) ⟨h2 * s⁻¹, by
    simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff]
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self, zero_mul, map_zero]
    exact zero_le⟩
  refine ⟨c, ?_⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff] at hc
  set y := algebraMap F (u.adicCompletion F) c
  set z := y * s - h2 with hz_def
  have hz : Valued.v z < 1 := by
    calc Valued.v z = Valued.v (z * p⁻¹) * Valued.v p := by
          rw [← map_mul, inv_mul_cancel_right₀ hp0]
      _ ≤ 1 * Valued.v p := by gcongr
      _ < 1 := by rw [one_mul]; exact hvp
  have hhalf : h2 + h2 = 1 := by
    rw [hh2, ← map_add (f := _), ← map_one (algebraMap F (u.adicCompletion F))]
    congr 1
    norm_num
  have hkey : algebraMap F (u.adicCompletion F) (1 / 4 - c ^ 2 * a) = -z * (1 + z) := by
    have e1 : (1 / 4 : F) = 2⁻¹ * 2⁻¹ := by norm_num
    rw [e1, map_sub, map_mul, map_mul, map_pow, hs, ← hh2]
    rw [hz_def]
    linear_combination (h2 - y * s) * hhalf
  rw [← valued_v_algebraMap_adicCompletion_foundation, hkey]
  have h1z : Valued.v (1 + z) ≤ 1 := by
    calc Valued.v (1 + z) ≤ max (Valued.v (1 : u.adicCompletion F)) (Valued.v z) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := by rw [map_one]; exact max_le le_rfl hz.le
  calc Valued.v (-z * (1 + z)) = Valued.v z * Valued.v (1 + z) := by
        rw [map_mul, Valuation.map_neg]
    _ ≤ Valued.v z * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hz

theorem valuation_complexConj_of_not_split {L : Type} [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ IsSplitAt w) (y : L) :
    w.valuation L (IsCMField.complexConj L y) = w.valuation L y := by
  set σ : L ≃+* L := (IsCMField.complexConj L).toRingEquiv with hσ
  have hne : w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) ≠ ⊥ := by
    intro hbot
    apply w.ne_bot
    rw [eq_bot_iff] at hbot ⊢
    intro x hx
    have hx' : (RingOfIntegers.mapRingEquiv σ).symm x ∈
        w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hx
    have h0 := hbot hx'
    rw [Ideal.mem_bot] at h0 ⊢
    simpa using h0
  obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 L),
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) :=
    ⟨⟨_, Ideal.comap_isPrime _ _, hne⟩, rfl⟩
  have hfix : ∀ x : 𝓞 (maximalRealSubfield L),
      RingOfIntegers.mapRingEquiv σ (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_apply]
    have hx : ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) =
        algebraMap (maximalRealSubfield L) L (x : maximalRealSubfield L) := rfl
    rw [hx]
    exact (IsCMField.complexConj L).commutes _
  have hsame : w' = w := by
    by_contra hne'
    apply hw
    refine ⟨w', hne', ?_⟩
    ext x
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, hw', hfix]
  have key := GlobalTheory.QNorm.valuation_of_eq_comap σ w w' hw' y
  rw [hsame] at key
  exact key.symm

theorem isSplitAt_of_isSquare : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : maximalRealSubfield L) (δ : L), δ ^ 2 = a → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), IsSquare (algebraMap (maximalRealSubfield L) ((w.under (𝓞 (maximalRealSubfield L))).adicCompletion (maximalRealSubfield L)) a) → IsSplitAt w := by
  intro L _ _ _ a δ hδ hδL w hsq
  by_contra hw
  set u := w.under (𝓞 (maximalRealSubfield L)) with hu
  have ha : a ≠ 0 := by
    rintro rfl
    apply hδL
    have h0 : δ = 0 := by simpa using hδ
    rw [h0]
    exact zero_mem _
  obtain ⟨c, hc⟩ := exists_valuation_lt_one u a ha hsq
  have hconj : IsCMField.complexConj L δ = -δ := by
    have h1 : (IsCMField.complexConj L δ) ^ 2 = δ ^ 2 := by
      rw [← map_pow, hδ, IsCMField.complexConj_apply_eq_self]
    have h2 : IsCMField.complexConj L δ ≠ δ := fun h =>
      hδL ((IsCMField.complexConj_eq_self_iff L δ).mp h)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact absurd h h2
    · exact h
  set x : L := 2⁻¹ + (c : L) * δ with hx
  have hcc : IsCMField.complexConj L (c : L) = c := IsCMField.complexConj_apply_eq_self L c
  have hx' : IsCMField.complexConj L x = 2⁻¹ - (c : L) * δ := by
    rw [hx, map_add (f := _), map_mul, hcc, hconj, map_inv₀, map_ofNat]
    ring
  have hsum : x + IsCMField.complexConj L x = 1 := by
    rw [hx', hx]
    ring
  have hprod : x * IsCMField.complexConj L x =
      algebraMap (maximalRealSubfield L) L (1 / 4 - c ^ 2 * a) := by
    rw [hx', hx]
    simp only [map_sub, map_mul, map_pow, map_div₀, map_one, map_ofNat]
    change _ = 1 / 4 - (c : L) ^ 2 * (a : L)
    linear_combination (-(c : L) ^ 2) * hδ
  have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have hlt : w.valuation L (x * IsCMField.complexConj L x) < 1 := by
    rw [hprod, ← HeightOneSpectrum.valuation_liesOver L u w]
    exact pow_lt_one₀ zero_le hc
      (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal u.ne_bot).ne'
  have heq := valuation_complexConj_of_not_split w hw x
  rw [map_mul, heq] at hlt
  have hx1 : w.valuation L x < 1 := by
    by_contra hge
    push Not at hge
    exact absurd hlt (not_lt.mpr (one_le_mul hge hge))
  have hadd := Valuation.map_add (w.valuation L) x (IsCMField.complexConj L x)
  rw [hsum, map_one, heq, max_self] at hadd
  exact absurd (lt_of_le_of_lt hadd hx1) (lt_irrefl 1)

end GlobalTheory.SplitOfSquare
end

