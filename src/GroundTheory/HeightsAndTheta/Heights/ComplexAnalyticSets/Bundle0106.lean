module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0098
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0040

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMParameterQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem IsCohenMacaulayLocalRing.of_ringEquiv {A C : Type*} [CommRing A] [CommRing C]
    [IsCohenMacaulayLocalRing A] (e : A ≃+* C) : IsCohenMacaulayLocalRing C := by
  have : Nontrivial C := e.injective.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv A e
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  refine { exists_isWeaklyRegular := ⟨rs.map e, ?_, ?_, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs' := hm s hs
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs' ⊢
    exact fun h => hs' (by simpa using h.map e.symm)
  · have := RingHomInvPair.of_ringEquiv e
    have := RingHomInvPair.symm (↑e : A →+* C) (e.symm : C →+* A)
    exact (e.toSemilinearEquiv.isWeaklyRegular_congr' rs).1 hreg
  · rw [← ringKrullDim_eq_of_ringEquiv e, hdim, List.length_map]

theorem exists_nat_of_add_natCast_eq {a : WithBot ℕ∞} {m n : ℕ}
    (h : a + (m : WithBot ℕ∞) = (n : WithBot ℕ∞)) : ∃ k : ℕ, a = k ∧ k + m = n := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj, top_add] at h
      exact absurd h (ENat.top_ne_natCast n)
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

theorem CMParameterQuotient.proof (hreg : CMRegularElement.Statement.{0}) :
    CMParameterQuotient.Statement := by
  intro B _ _ d
  induction d generalizing B with
  | zero =>
    intro x _ _
    have h0 : Ideal.span (Set.range x) = ⊥ := by
      rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsCohenMacaulayLocalRing.of_ringEquiv
      ((RingEquiv.quotientBot B).symm.trans (Ideal.quotEquivOfEq h0.symm))
  | succ d ih =>
    classical
    intro x hx hdim
    let x' : Fin d → B ⧸ Ideal.span {x 0} := fun i => Ideal.Quotient.mk _ (x i.succ)
    have hIJ : Ideal.span (Set.range x) =
        Ideal.span {x 0} ⊔ Ideal.span (Set.range (Fin.tail x)) := by
      rw [Fin.range_fin_succ, Ideal.span_insert]
    have hmap : (Ideal.span (Set.range (Fin.tail x))).map (Ideal.Quotient.mk (Ideal.span {x 0})) =
        Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let e : (B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x') ≃+* B ⧸ Ideal.span (Set.range x) :=
      (Ideal.quotEquivOfEq hmap.symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hIJ.symm))
    have hIne : Ideal.span {x 0} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hx 0)))
    have : Nontrivial (B ⧸ Ideal.span {x 0}) := Ideal.Quotient.nontrivial_iff.2 hIne
    have : IsLocalRing (B ⧸ Ideal.span {x 0}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x 0})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hx' : ∀ i, x' i ∈ maximalIdeal (B ⧸ Ideal.span {x 0}) := fun i =>
      (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal _).1 (hx i.succ) (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hu)
    obtain ⟨rs, -, -, hD⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
    have he := ringKrullDim_eq_of_ringEquiv e
    obtain ⟨k, hk, hkn⟩ := exists_nat_of_add_natCast_eq (hdim.trans hD)

    have hKrull : ringKrullDim (B ⧸ Ideal.span {x 0}) ≤ (k : WithBot ℕ∞) + (d : WithBot ℕ∞) := by
      have hs : ((Finset.univ.image x' : Finset _) : Set _) ⊆ SetLike.coe (Ring.jacobson (B ⧸ Ideal.span {x 0})) := by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        intro z hz
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hz
        obtain ⟨i, rfl⟩ := hz
        exact hx' i
      have h1 := ringKrullDim_le_ringKrullDim_quotient_add_card _ hs
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, he, hk] at h1
      refine h1.trans ?_
      gcongr
      exact_mod_cast Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_fin d)).le
    have hmin : ∀ p ∈ minimalPrimes B, x 0 ∉ p := by
      intro p hp hyp
      have hle : Ideal.span {x 0} ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hyp
      have h1 := ringKrullDim_quotient_eq_of_mem_minimalPrimes hp
      have h2 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ Ideal.span {x 0}) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
      have h3 := (h1.symm.trans_le h2).trans hKrull
      rw [hD] at h3
      have h4 : rs.length ≤ k + d := by exact_mod_cast h3
      omega
    obtain ⟨hnzd, hCM⟩ := hreg B (x 0) (hx 0) hmin
    have hdimI : ringKrullDim (B ⧸ Ideal.span {x 0}) + ((1 : ℕ) : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) := by
      rw [Nat.cast_one, ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd (hx 0),
        hD]
    obtain ⟨k', hk', hk'n⟩ := exists_nat_of_add_natCast_eq hdimI
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x')) + (d : WithBot ℕ∞) =
        ringKrullDim (B ⧸ Ideal.span {x 0}) := by
      rw [he, hk, hk']
      exact_mod_cast (by omega : k + d = k')
    have : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {x 0}) := hCM
    have := ih (B ⧸ Ideal.span {x 0}) x' hx' hdim'
    exact IsCohenMacaulayLocalRing.of_ringEquiv e

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMQuotientUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem map_mem_associatedPrimes_quotient {B : Type*} [CommRing B] [IsNoetherianRing B] (I p : Ideal B)
    (hp : p ∈ associatedPrimes B (B ⧸ I)) :
    I ≤ p ∧ p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (B ⧸ I) (B ⧸ I) := by
  obtain ⟨hprime, a, rfl⟩ := (isAssociatedPrime_iff (I := p) (M := B ⧸ I)).1 hp
  have hI : I ≤ Submodule.colon (⊥ : Submodule B (B ⧸ I)) {a} := fun b hb => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
  refine ⟨hI, (isAssociatedPrime_iff).2 ⟨?_, a, ?_⟩⟩
  · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  · ext c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective, Submodule.mem_colon_singleton]
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rw [← hbb']
      simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using hb'
    · intro h
      exact ⟨b, by simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using h, rfl⟩

theorem CMQuotientUnmixed.proof (hQ : CMParameterQuotient.Statement) (hU : CMRingUnmixed.Statement) :
    CMQuotientUnmixed.Statement := by
  intro B _ _ d x hx hdim p hp
  set I := Ideal.span (Set.range x) with hIdef
  have hCM : IsCohenMacaulayLocalRing (B ⧸ I) := hQ B d x hx hdim
  obtain ⟨hIp, hq⟩ := map_mem_associatedPrimes_quotient I p hp
  obtain ⟨hmin, hdq⟩ := hU (B ⧸ I) _ hq
  have hcomap : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.2 hIp]
  refine ⟨?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨_, hmin, hcomap⟩
  · rw [← hdq]
    exact (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIp)).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMRegularElement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise

universe u

theorem mem_minimalPrimes_of_mem_associatedPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {p : Ideal B} (hp : p ∈ associatedPrimes B B) : p ∈ minimalPrimes B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  obtain ⟨hprime, m, hpm⟩ := isAssociatedPrime_iff.mp hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hpm, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs m hm0 hm hreg
  rw [← hpm] at hD
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
  by_cases hqp' : q = p
  · exact hqp' ▸ hq
  exfalso
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hqp')
  have : q.IsPrime := hq.1.1
  have hnzd : Ideal.Quotient.mk q a ∈ nonZeroDivisors (B ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have heq : (B ⧸ q) ⧸ Ideal.span {Ideal.Quotient.mk q a} ≃+* B ⧸ (q ⊔ Ideal.span {a}) := by
    have : Ideal.span {Ideal.Quotient.mk q a} = (Ideal.span {a}).map (Ideal.Quotient.mk q) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [this]
    exact DoubleQuot.quotQuotEquivQuotSup q (Ideal.span {a})
  rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
  have hle : q ⊔ Ideal.span {a} ≤ p := sup_le hqp ((Ideal.span_singleton_le_iff_mem p).mpr hap)
  have h1 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have h2 : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  have h3 : ringKrullDim (B ⧸ p) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hdim] at h2 h3
  have h4 : ringKrullDim (B ⧸ p) = (rs.length : WithBot ℕ∞) := le_antisymm h3 hD
  have h5 : ringKrullDim (B ⧸ p) + 1 ≤ (rs.length : WithBot ℕ∞) :=
    ((by gcongr : ringKrullDim (B ⧸ p) + 1 ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) + 1).trans hd2).trans h2
  rw [h4] at h5
  norm_cast at h5
  omega

theorem mem_nonZeroDivisors_of_not_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B] {y : B}
    (hy : ∀ p ∈ minimalPrimes B, y ∉ p) : y ∈ nonZeroDivisors B := by
  by_contra h
  have h' : y ∈ (nonZeroDivisors B : Set B)ᶜ := h
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂] at h'
  obtain ⟨p, hp, hyp⟩ := h'
  exact hy p (mem_minimalPrimes_of_mem_associatedPrimes hp) hyp

theorem exists_isRegular_quotSMulTop {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {rs : List B} (hm : ∀ r ∈ rs, r ∈ maximalIdeal B) (hreg : IsWeaklyRegular B rs)
    {y : B} (hy : IsSMulRegular B y) (hym : y ∈ maximalIdeal B) :
    ∃ rs' : List B, rs'.length = rs.length - 1 ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧
      IsRegular (QuotSMulTop y B) rs' := by
  have key : ∀ (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] [Nontrivial X],
      maximalIdeal B • (⊤ : Submodule B X) < ⊤ := fun X _ _ _ _ => by
    refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
    have H : Module.annihilator B X ≠ ⊤ := fun h => not_subsingleton X (Module.annihilator_eq_top_iff.mp h)
    exact (jacobson_eq_maximalIdeal _ H).ge
  have hne : (y • (⊤ : Submodule B B)) ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ y • (⊤ : Submodule B B) := by rw [h]; exact Submodule.mem_top
    obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact (mem_maximalIdeal _).mp hym (IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hb))
  have : Nontrivial (QuotSMulTop y B) := Submodule.Quotient.nontrivial_iff.mpr hne
  let M : ModuleCat.{u} B := ModuleCat.of B B
  let S := ModuleCat.smulShortComplex M y
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact (M := M) hy
  let N : ModuleCat.{u} B := ModuleCat.of B (Shrink.{u} (B ⧸ maximalIdeal B))
  have hregB : IsRegular B rs := (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hreg
  have hextB : ∀ i < rs.length, Subsingleton (Ext N M i) :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) rs.length M (key B)).out 2 4).mpr
      (⟨rs, rfl, hm, hregB⟩ : ∃ rs' : List B, rs'.length = rs.length ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧ IsRegular M rs')
  have hext3 : ∀ i < rs.length - 1, Subsingleton (Ext N S.X₃ i) := by
    intro i hi
    have hex := Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl
    have h1 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₂ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB i (by omega))
    have h3 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₁ (i + 1))) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero (hex.isZero_of_both_zeros (h1.eq_of_src _ _) (h3.eq_of_tgt _ _))
  have : Module.Finite B S.X₃ := inferInstanceAs (Module.Finite B (QuotSMulTop y B))
  have : Nontrivial S.X₃ := inferInstanceAs (Nontrivial (QuotSMulTop y B))
  obtain ⟨rs', hlen, hm', hreg'⟩ :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) (rs.length - 1) S.X₃ (key S.X₃)).out 2 4).mp hext3
  exact ⟨rs', hlen, hm', hreg'⟩

theorem CMRegularElement.proof : CMRegularElement.Statement.{u} := by
  intro B _ _ y hym hy
  have hnzd := mem_nonZeroDivisors_of_not_mem_minimalPrimes hy
  refine ⟨hnzd, ?_⟩
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hyreg : IsSMulRegular B y := Module.Flat.isSMulRegular_of_nonZeroDivisors hnzd
  obtain ⟨rs', hlen, hm', hreg'⟩ := exists_isRegular_quotSMulTop hm hreg hyreg hym
  set I := Ideal.span {y} with hIdef
  have hI : I ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal _).mp hym)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I (by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hym)
  have hsub : (y • (⊤ : Submodule B B)) = I := by
    rw [hIdef, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop y B ≃ₗ[B] B ⧸ I := Submodule.quotEquivOfEq _ _ hsub
  have hw : IsWeaklyRegular (B ⧸ I) (rs'.map (algebraMap B (B ⧸ I))) :=
    (isWeaklyRegular_map_algebraMap_iff (S := B ⧸ I) (M := B ⧸ I) rs').mpr
      ((e.isWeaklyRegular_congr rs').mp hreg'.toIsWeaklyRegular)
  have hdimq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hym
  refine { exists_isWeaklyRegular := ⟨rs'.map (algebraMap B (B ⧸ I)), ?_, hw, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact map_nonunit (Ideal.Quotient.mk I) s (hm' s hs)
  · rw [List.length_map, hlen]
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ I) := ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at hdimq
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (B ⧸ I) = d :=
      (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)).imp fun _ h => h.symm
    rw [hd] at hdimq ⊢
    have h2 : d + 1 = (rs.length : ℕ∞) := by exact_mod_cast hdimq
    induction d using ENat.recTopCoe with
    | top => simp at h2
    | coe k =>
      norm_cast at h2 ⊢
      rw [show k = rs.length - 1 by omega]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMRingUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

theorem CMRingUnmixed.proof : CMRingUnmixed.Statement := by
  intro A _ _ p hp
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  obtain ⟨hprime, y, hy⟩ := isAssociatedPrime_iff.mp hp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  have heq : ringKrullDim (A ⧸ p) = ringKrullDim A :=
    le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD
  refine ⟨⟨⟨hprime, bot_le⟩, fun q hq hqp => ?_⟩, heq⟩
  by_contra hpq
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hpq (h ▸ le_rfl)
  have hq' : q.IsPrime := hq.1
  have h1 := Order.coheight_add_one_le (α := PrimeSpectrum A) (a := ⟨p, hprime⟩) (b := ⟨q, hq'⟩) hlt
  have h2 : ringKrullDim (A ⧸ q) ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [ringKrullDim_quotient_eq_coheight, hdim] at h2
  rw [ringKrullDim_quotient_eq_coheight, hdim] at heq
  have e1 : Order.coheight (⟨p, hprime⟩ : PrimeSpectrum A) = (rs.length : ℕ∞) := by exact_mod_cast heq
  have e2 : Order.coheight (⟨q, hq'⟩ : PrimeSpectrum A) ≤ (rs.length : ℕ∞) := by exact_mod_cast h2
  rw [e1] at h1
  have h3 : ((rs.length + 1 : ℕ) : ℕ∞) ≤ (rs.length : ℕ) := by exact_mod_cast h1.trans e2
  have h4 : rs.length + 1 ≤ rs.length := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorOneComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

namespace DivisorOneComponent

theorem mem_zeroSet_iff {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    q ∈ zeroSet K ↔ K ≤ RingHom.ker (eval q) :=
  ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h _ hf => RingHom.mem_ker.1 (h hf)⟩

theorem isClosed_zeroSet {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet K) := by
  have : zeroSet K = ⋂ f ∈ K, {x : Fin n → ℂ | eval x f = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem exists_bound (d : ℕ) : ∃ N : WithBot ℕ∞, N < (d : WithBot ℕ∞) ∧
    ∀ x : WithBot ℕ∞, x + 1 ≤ (d : WithBot ℕ∞) → x ≤ N := by
  rcases d with _ | k
  · refine ⟨⊥, WithBot.bot_lt_coe _, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe y =>
      have : y + 1 ≤ 0 := by exact_mod_cast hx
      simp at this
  · refine ⟨(k : WithBot ℕ∞), by exact_mod_cast Nat.lt_succ_self k, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe y =>
      have h1 : y + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
      have h2 : y ≤ (k : ℕ∞) := by
        cases y using ENat.recTopCoe with
        | top => simp at h1
        | coe y =>
          have h3 : y + 1 ≤ k + 1 := by exact_mod_cast h1
          exact_mod_cast (by omega : y ≤ k)
      exact_mod_cast h2

theorem dim_sup_add_one_le {n d : ℕ} {J W W' : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime] {u : Fin n → ℂ}
    (hu : linForm u ∉ J) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes)
    (hW' : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) (hne : W ≠ W') :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1 ≤ (d : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  obtain ⟨x, hxW', hxW⟩ : ∃ x ∈ W', x ∉ W := by
    by_contra! h
    exact hne (le_antisymm (hW.2 hW'.1 h) h)
  have hle : W ⊔ Ideal.span {x} ≤ W ⊔ W' := sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hxW') _
  have hx : x ∈ W ⊔ Ideal.span {x} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hr : Ideal.Quotient.mk W x ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hsurj : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) ≤
      ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor
      (le_sup_left.trans hle)) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _
        (Ideal.Quotient.factor_surjective _))
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h0 : Ideal.Quotient.mk (W ⊔ W') (c' * x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (hle hx))
    simpa [Ideal.Quotient.factor_mk, map_mul] using h0
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1
      ≤ ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) + 1 := by gcongr
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    _ = (d : WithBot ℕ∞) := ringKrullDim_component hu hW hdim

end DivisorOneComponent


open DivisorOneComponent in
theorem DivisorOneComponent.proof : DivisorOneComponent.Statement := by
  classical
  intro n d J u hJ hdim hu
  have hKq : ∀ x ∈ zeroSet J, linEval u x = 0 → J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x) := by
    intro x hxJ hxu
    refine sup_le ((mem_zeroSet_iff J x).1 hxJ) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    simpa [linForm, linEval] using hxu
  generalize hK : J ⊔ Ideal.span {linForm u} = K at hKq ⊢
  have hM : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨S, hS⟩ : ∃ S : Finset (Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ)),
      ∀ p, p ∈ S ↔ p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 :=
    ⟨(hM.prod hM).toFinset.filter fun p => p.1 ≠ p.2, fun p => by rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod, and_assoc]⟩
  obtain ⟨I, hI⟩ : ∃ I, I = S.inf fun p => p.1 ⊔ p.2 := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 := fun p hp => (hS p).1 hp
  have hpair : ∀ W W', W ∈ K.minimalPrimes → W' ∈ K.minimalPrimes → W ≠ W' → I ≤ W ⊔ W' :=
    fun W W' hW hW' hne => by
      have h := Finset.inf_le (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ((hS (W, W')).2 ⟨hW, hW', hne⟩)
      rw [hI]; exact h
  have hKI : K ≤ I := by
    have h := Finset.le_inf (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) (a := K) (s := S) fun p hp => (hmemS p hp).1.1.2.trans le_sup_left
    rw [hI]; exact h
  obtain ⟨N, hN, hxN⟩ := exists_bound d
  refine ⟨I, hKI, ?_, ?_⟩
  · refine lt_of_le_of_lt (ComplexSets.quotient_dim_le_of_minimalPrimes I fun Z hZ => ?_) hN
    have hZI : S.inf (fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ≤ Z := by rw [← hI]; exact hZ.1.2
    obtain ⟨p, hp, hpZ⟩ := (Ideal.IsPrime.inf_le' (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) hZ.1.1).1 hZI
    obtain ⟨h1, h2, h12⟩ := hmemS p hp
    exact (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hpZ)).trans
      (hxN _ (dim_sup_add_one_le hu hdim (by rw [hK]; exact h1) (by rw [hK]; exact h2) h12))
  · intro q hqJ hqu hqI
    obtain ⟨W, hW, hWq⟩ := Ideal.exists_minimalPrimes_le (hKq q hqJ hqu)
    have huniq : ∀ W' ∈ K.minimalPrimes, q ∈ zeroSet W' → W' = W := by
      intro W' hW' hq'
      by_contra hne
      exact hqI ((mem_zeroSet_iff I q).2 ((hpair W W' hW hW' (Ne.symm hne)).trans
        (sup_le hWq ((mem_zeroSet_iff W' q).1 hq'))))
    refine ⟨W, hW, (mem_zeroSet_iff W q).2 hWq, huniq, ⋂ W' ∈ K.minimalPrimes \ {W}, (zeroSet W')ᶜ, ?_, ?_⟩
    · refine (biInter_mem (hM.subset Set.sdiff_subset)).2 fun W' hW' => (isClosed_zeroSet W').isOpen_compl.mem_nhds ?_
      exact fun hq' => hW'.2 (huniq W' hW'.1 hq')
    · rintro x ⟨hxJ, hxU⟩ hxu
      obtain ⟨W'', hW'', hW''x⟩ := Ideal.exists_minimalPrimes_le (hKq x hxJ hxu)
      by_cases h : W'' = W
      · subst h; exact (mem_zeroSet_iff W'' x).2 hW''x
      · exact absurd ((mem_zeroSet_iff W'' x).2 hW''x) (Set.mem_iInter₂.1 hxU W'' ⟨hW'', h⟩)

end

end GroundTheory.Heights₂.Heights
end

