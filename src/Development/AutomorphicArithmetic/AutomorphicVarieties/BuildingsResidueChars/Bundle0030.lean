module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AbsoluteBoundOfPartialBoundOfOrbitBound
section
open UpperTheory.V.Af.CohB in
theorem UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound :
    UpperTheory.V.Af.CohB.PartBound → UpperTheory.V.Af.CohB.OrbBound → UpperTheory.V.Af.CohB.AbsBound := by
  intro hP hO Γ Y _ _ hT hB
  obtain ⟨T, hT⟩ := hT
  choose cf hcf using fun t : ↥T => hO Γ Y t.1 (hB t.1)
  refine ⟨∑ t, cf t, ?_⟩
  intro X _ p hp D hD d ξ
  let r : MulAction.orbitRel.Quotient Γ Y → ↥T := fun q =>
    ⟨Classical.choose (hT q.out) • q.out, Classical.choose_spec (hT q.out)⟩
  let cl : X → ↥T := fun x => r (Quotient.mk (MulAction.orbitRel Γ Y) (p x))
  have hcl : ∀ (γ : Γ) (x : X), cl (γ • x) = cl x := by
    intro γ x
    simp only [cl, hp]
    congr 1
    exact Quotient.sound ⟨γ, rfl⟩
  refine (hP Γ X ↥T cl hcl d ξ).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hsurj : ∀ x : ↥(UpperTheory.V.Af.CohB.part cl hcl t), ∃ g : Γ, g • p x.1 = t.1 := by
    rintro ⟨x, hx⟩
    change cl x = t at hx
    obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ Y) (p x)))
    refine ⟨Classical.choose (hT (Quotient.mk (MulAction.orbitRel Γ Y) (p x)).out) * h, ?_⟩
    rw [mul_smul]
    simp only at hh ⊢
    rw [hh]
    exact congrArg Subtype.val hx
  refine hcf t ↥(UpperTheory.V.Af.CohB.part cl hcl t) (fun x => p x.1) (fun γ x => hp γ x.1) hsurj D
    (le_trans (Cardinal.mk_le_of_injective
      (f := fun z : {x : ↥(UpperTheory.V.Af.CohB.part cl hcl t) // p x.1 = t.1} => (⟨z.1.1, z.2⟩ : {x // p x = t.1}))
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))) (hD t.1)) d ξ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiberCard
section
theorem UpperTheory.adelic_cohomology_fiber_card :
    UpperTheory.V.Af.CohB.FibCard := by
  intro G _ U U' h hne y
  set e := Subgroup.quotientEquivProdOfLE h with he
  have key : ∀ x : G ⧸ U, (e x).1 = Subgroup.quotientMapOfLE h x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  have e1 : {x // Subgroup.quotientMapOfLE h x = y} ≃ (U' ⧸ U.subgroupOf U') :=
    { toFun := fun x => (e x.1).2
      invFun := fun b => ⟨e.symm (y, b), by rw [← key, Equiv.apply_symm_apply]⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change e.symm (y, (e x).2) = x
        rw [← hx, ← key]
        exact e.symm_apply_apply x
      right_inv := by
        intro b
        change (e (e.symm (y, b))).2 = b
        rw [Equiv.apply_symm_apply] }
  rw [Cardinal.mk_congr e1]
  have : Finite (U' ⧸ U.subgroupOf U') := Subgroup.index_ne_zero_iff_finite.mp hne
  rw [← Nat.cast_card]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiniteOrbitBound
section
theorem UpperTheory.adelic_cohomology_finite_orbit_bound :
    UpperTheory.V.Af.CohB.FinOrbAbs := by
  classical
  intro G H _ _ ι Γ U K hΓ hU ⟨T, hT⟩
  haveI : Fintype (H ⧸ Γ) := Subgroup.fintypeOfIndexNeZero hΓ.index_ne_zero
  haveI : Fintype (K ⧸ U.subgroupOf K) := Subgroup.fintypeOfIndexNeZero hU
  refine ⟨((Finset.univ : Finset (H ⧸ Γ)) ×ˢ T ×ˢ (Finset.univ : Finset (K ⧸ U.subgroupOf K))).image
    (fun x => ι (x.1.out)⁻¹ * x.2.1 * ((x.2.2.out : K) : G)), fun g => ?_⟩
  obtain ⟨h, t, ht, k, hk, rfl⟩ := hT g
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ h⁻¹
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨k, hk⟩ : K)
  have huU : (((u : K) : G))⁻¹ ∈ U := U.inv_mem (Subgroup.mem_subgroupOf.1 u.2)
  refine ⟨γ, γ.2, _, Finset.mem_image.2 ⟨(QuotientGroup.mk h⁻¹, t, QuotientGroup.mk ⟨k, hk⟩), ?_, rfl⟩,
    _, huU, ?_⟩
  · simp [ht]
  · simp only [hγ, hu, mul_inv_rev, inv_inv, map_mul, map_inv, Subgroup.coe_mul]
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupLevelOne
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

private theorem alg_mem_Ohat {F : Type} [Field F] [NumberField F] (x : F) :
    algebraMap F (Af F) x ∈ Ohat F ↔ ∃ r : 𝓞 F, (r : F) = x := by
  rw [← GlobalTheory.AdelicMatLat.algebraMap_mem_iff, GlobalTheory.AdelicMatLat.mem_intAdeles, Ohat, Subring.mem_iInf]
  rfl

theorem UpperTheory.arithmetic_subgroup_level_one :
    UpperTheory.V.Af.CohB.ArithOne := by
  intro F _ _ n
  ext g
  rw [Subgroup.mem_comap, mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    rw [← map_inv] at hb
    have ha' : ∀ a b, ∃ r : 𝓞 F, (r : F) = g a b := fun a b => (alg_mem_Ohat _).1 (ha a b)
    have hb' : ∀ a b, ∃ r : 𝓞 F, (r : F) = (g⁻¹ : GL (Fin n) F) a b := fun a b => (alg_mem_Ohat _).1 (hb a b)
    choose A hA using ha'
    choose B hB using hb'
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F)) := fun x y h =>
      Matrix.ext fun a b => IsFractionRing.injective (𝓞 F) F (congrFun (congrFun h a) b)
    have eA : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of A) = g.val :=
      Matrix.ext fun a b => hA a b
    have eB : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of B) = (g⁻¹).val :=
      Matrix.ext fun a b => hB a b
    refine ⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, Units.ext eA⟩
    · rw [map_mul, map_one, eA, eB]; exact g.mul_inv
    · rw [map_mul, map_one, eA, eB]; exact g.inv_mul
  · rintro ⟨k, rfl⟩
    have h1 : ∀ (k : GL (Fin n) (𝓞 F)) a b, (CohB.ratAf F n
        (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F) k)) a b ∈ Ohat F :=
      fun k a b => (alg_mem_Ohat _).2 ⟨k a b, rfl⟩
    refine ⟨h1 k, fun a b => ?_, fun a b => ⟨_, ?_, by rw [Nat.cast_one]; exact (one_mul _).symm⟩⟩
    · rw [← map_inv, ← map_inv]; exact h1 _ a b
    · refine sub_mem (h1 k a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupsCommensurable
section
open UpperTheory.V.Af UpperTheory.V.Af.CohB GlobalTheory.CuspRep in
private theorem relIndex_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

private theorem comm_comap {G H : Type} [Group G] [Group H] (f : H →* G) (U K : Subgroup G)
    (h : U.relIndex K ≠ 0) : (U.comap f).relIndex (K.comap f) ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h0
  exact h (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le f K) h0)

theorem UpperTheory.arithmetic_subgroups_commensurable :
    UpperTheory.V.Af.CohB.ArithComm := by
  intro F _ _ n Γ hΓ g U hUo hUc
  set U' := U.comap (MulAut.conj g⁻¹).toMonoidHom with hU'
  have hc : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g⁻¹ * x * g) := by fun_prop
  have hc' : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g * x * g⁻¹) := by fun_prop
  have e1 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g⁻¹ * x * g) ⁻¹' U := by
    ext x; simp [hU']
  have e2 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g * x * g⁻¹) '' U := by
    rw [e1]
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  have ho : IsOpen (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e1 ▸ hUo.preimage hc
  have hk : IsCompact (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e2 ▸ hUc.image hc'
  have h1 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact U' _ ho (UpperTheory.V.Af.isCompact_KLev (F := F) (n := n) le_rfl))
  have h2 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact _ U' (UpperTheory.V.Af.isOpen_KLev (F := F) (n := n) le_rfl) hk)
  have h3 : Γ.relIndex ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)) ≠ 0 := fun h0 =>
    hΓ.index_ne_zero (by
      rw [← Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_eq_zero_of_le_right le_top h0)
  have h4 := Subgroup.relIndex_inf_ne_zero h3 h1
  have h5 : ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)).relIndex (Γ ⊓ UpperTheory.V.Af.CohB.arith g U) ≠ 0 :=
    fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  first
    | exact ⟨h4, h5⟩
    | exact ⟨⟨h4⟩, ⟨h5⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BaseChangeAttachedOfFrobeniusRestriction
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have norm_eq {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [norm_eq w, norm_eq (w.under (𝓞 K))]
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]

theorem UpperTheory.baseChange_attached_of_frobenius_restriction :
    UpperTheory.V.Af.Bc.FrobRes → UpperTheory.V.Af.Bc.BcAtt := by
  intro hres F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π P hbc
  refine ⟨fun hreg => (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun hatt hss => ⟨hss, ?_⟩⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F E)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hbc.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · filter_upwards [hbc.unr, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
    obtain ⟨B, hB, hP⟩ := h1 (w.under (𝓞 F)) rfl _ (normV_under (K := F) w)
    obtain ⟨B', hB', hF⟩ := h2
    obtain rfl := TR.CuspSub.HasSat.unique hB hB'
    refine ⟨_, hP, ?_⟩
    have h3 := (hres F E Ω l ι w _ (normV_under (K := F) w)).1 n r _ hF
    rw [← algSat_pow, ← normV_under] at h3
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BaseChangeNoSelfTwistOfFrobeniusSignIrreducible
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

private theorem sat_of_isoTwist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n}
    {η : HChar F} (h : IsoTwist π η) {v : HeightOneSpectrum (𝓞 F)} (hη : η.UnrAt v) {B : Multiset ℂˣ}
    (hB : π.HasSat v B) : B = B.map (· * η.val v) := by
  obtain ⟨T, hT, -⟩ := h
  refine hB.unique (GlobalTheory.SphGal.hasSatGL_of_twist hη T.symm (fun g x => ?_) hB)
  obtain ⟨x, rfl⟩ := T.surjective x
  apply T.injective
  rw [LinearEquiv.symm_apply_apply, TR.CuspSub.locRep_eq, hT, map_smul, LinearEquiv.apply_symm_apply,
    TR.CuspSub.chiDet_locGL]
  rfl

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

theorem UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible :
    UpperTheory.V.Af.IsoOfFrob → UpperTheory.V.Af.Bc.FrobTw → UpperTheory.V.Af.Bc.SignEx → UpperTheory.V.Af.Bc.SignFrob → UpperTheory.V.Af.Bc.SchurTw → UpperTheory.V.Af.Bc.IrrBasic → UpperTheory.V.Af.Bc.NoTwist := by
  intro hIso hTw hEx hFr hSch hIrr F E Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι h2 n r π hc hatt hirr η hη hT
  obtain ⟨δ, hδc, hδ1, hδs, hδu⟩ := hEx F E Ω l h2
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    exact Algebra.IsAlgebraic.trans F E Ω⟩
  refine hδ1 (hSch _ _ _ n r (res F Ω E) δ hirr ?_ ?_)
  · ext s
    have := (hδs.1 _).2 ⟨s, rfl⟩
    simpa using this
  · refine hIso F Ω l ι n r _ hc (hIrr.2 _ _ n r δ hc hδc) hatt.1 ((hIrr.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hδu, eventually_under (F := F) hη] with v hv hu hw
    obtain ⟨w, rfl, hw⟩ := hw
    obtain ⟨B, hB, hE⟩ := hv
    obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
    refine ⟨_, hE, ?_⟩
    have h4 := hTw F Ω l ι n r δ _ _ _ hE (hFr F E Ω l ι δ hδs w hu)
    convert h4 using 1
    conv_lhs => rw [sat_of_isoTwist hT h1 hB]
    have h5 : ((η.val (w.under (𝓞 F)) : ℂˣ) : ℂ) = if normV w = normV (w.under (𝓞 F)) then 1 else -1 := by
      refine (congrArg Units.val h3).trans ?_
      change ((if normV w = normV (w.under (𝓞 F)) then 1 else -1 : ℂˣ) : ℂ) = _
      split_ifs <;> simp
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [← h5]
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardOhatQuotientNatCast
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

private theorem card_int_mod (F : Type) [Field F] [NumberField F] (N : ℕ) :
    Nat.card (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) = N ^ Module.finrank ℚ F := by
  have h := Ideal.absNorm_span_singleton (N : 𝓞 F)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  rw [h, ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow,
    Int.natAbs_natCast]

theorem UpperTheory.card_ohat_quotient_natCast :
    UpperTheory.V.Af.CohB.CardOhat := by
  intro F _ _ N hN
  have hm : ∀ x : Af F, x ∈ Ohat F ↔ x ∈ Formalism.UG.intAd F := fun x => by
    rw [Ohat, Subring.mem_iInf]
    rfl
  let f : 𝓞 F →+* ↥(Ohat F) :=
    ((algebraMap F (Af F)).comp (algebraMap (𝓞 F) F)).codRestrict (Ohat F) fun a =>
      mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a)
  let g : (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) →+* (↥(Ohat F) ⧸ Ideal.span {(N : ↥(Ohat F))}) :=
    Ideal.quotientMap _ f (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨s, c, hc, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod N hN y.1 ((hm _).1 y.2)
    refine ⟨Ideal.Quotient.mk _ s, ?_⟩
    change Ideal.Quotient.mk _ (f s) = _
    refine (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨c, (hm _).2 hc⟩, Subtype.ext ?_⟩)).symm
    change y.1 - algebraMap F (Af F) (algebraMap (𝓞 F) F s) = (N : Af F) * c
    exact sub_eq_of_eq_add' e
  haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) :=
    Nat.finite_of_card_ne_zero (by rw [card_int_mod]; exact pow_ne_zero _ (by omega))
  exact ⟨Finite.of_surjective g hg, (Nat.card_le_card_of_surjective g hg).trans (card_int_mod F N).le⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionCommuteRightTranslation
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.centerU_action_commute_rightTranslation :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∀ z ∈ (isExpLieAlgebra K n).centerU, ∀ g, Commute (uAction z) (rt (K := K) (n := n) g) := by
  intro K _ _ n z hz g
  obtain ⟨ι, hι, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  have hinf : Commute (uAction z) (rtInf (archPart g)) := by
    have hsub : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤
        Subalgebra.centralizer ℂ {rtInf (archPart g)} := by
      rw [Algebra.adjoin_le_iff]
      rintro x ⟨τ, u, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro y rfl
      exact (UpperTheory.capOp_commute_rightTranslation K n ι D τ u (archPart g)).eq.symm
    have hm := hsub (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz)
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact (hm _ rfl).symm
  have hfin : Commute (uAction z) (rtFin (finPart g)) := by
    refine LinearMap.ext fun φ => ?_
    exact uAction_rtFin z (finPart g) φ
  exact hinf.mul_right hfin
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyBoundedEquiv
section
theorem UpperTheory.cohomology_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv := by
  intro Γ Γ' _ _ ⟨φ⟩ ⟨c, hc⟩
  refine ⟨c, fun A => ?_⟩
  have key := hc (Rep.res φ.toMonoidHom A)
  have heq : ∀ q, Module.rank ℂ (groupCohomology (Rep.res φ.toMonoidHom A) q) =
      Module.rank ℂ (groupCohomology A q) := fun q =>
    ((groupCohomology.mapIso φ (LinearEquiv.refl ℂ A.V) (fun g => rfl) q).toLinearEquiv).rank_eq
  unfold UpperTheory.V.Af.CohB.totCoh at key ⊢
  simp only [heq] at key
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartBoundOfSumBound
section
private theorem card_sum_finset_swap {I : Type} (s : Finset I) (f : ℕ → I → Cardinal.{0}) :
    (Cardinal.sum fun q => ∑ i ∈ s, f q i) = ∑ i ∈ s, Cardinal.sum fun q => f q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Cardinal.sum_add_distrib', ih]

theorem UpperTheory.cohomology_part_bound_of_sum_bound :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.CohB.PartSplit → UpperTheory.V.Af.CohB.PartBound := by
  intro h1 h2 Γ X I _ _ _ c hc d ξ
  obtain ⟨π, ι, h⟩ := h2 Γ X I c hc d ξ
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [← card_sum_finset_swap]
  exact Cardinal.sum_le_sum _ _ fun q => h1 Γ I _ _ π ι h q
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartSplit
section
open CategoryTheory UpperTheory.V.Af.CohB

theorem UpperTheory.cohomology_part_split :
    UpperTheory.V.Af.CohB.PartSplit := by
  classical
  intro Γ X I _ _ _ c hc d ξ
  let p : ∀ i, (X → Fin d → ℂ) →ₗ[ℂ] (↥(part c hc i) → Fin d → ℂ) := fun i =>
    { toFun := fun f x => f x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : ∀ i, (↥(part c hc i) → Fin d → ℂ) →ₗ[ℂ] (X → Fin d → ℂ) := fun i =>
    { toFun := fun f x => if h : c x = i then f ⟨x, h⟩ else 0
      map_add' := fun f g => funext fun x => by
        by_cases h : c x = i <;> simp [h]
      map_smul' := fun a f => funext fun x => by
        by_cases h : c x = i <;> simp [h] }
  refine ⟨fun i => Rep.ofHom ⟨p i, fun γ => ?_⟩, fun i => Rep.ofHom ⟨e i, fun γ => ?_⟩, ?_⟩
  · refine LinearMap.ext fun f => funext fun x => ?_
    rfl
  · refine LinearMap.ext fun f => funext fun x => ?_
    change (if h : c x = i then (funRep ↥(part c hc i) ξ γ f) ⟨x, h⟩ else 0) =
      Matrix.mulVec (ξ γ) (if h : c (γ⁻¹ • x) = i then f ⟨γ⁻¹ • x, h⟩ else 0)
    by_cases h : c x = i
    · rw [dite_eq_left h, dite_eq_left ((hc _ _).trans h)]
      rfl
    · rw [dite_eq_right h, dite_eq_right (fun h' => h ((hc _ _).symm.trans h')), Matrix.mulVec_zero]
  · apply Rep.hom_ext
    rw [Rep.sum_hom]
    apply Representation.IntertwiningMap.ext
    refine LinearMap.ext fun f => funext fun x => ?_
    rw [Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply, Finset.sum_apply]
    change ∑ i, (if h : c x = i then f x else 0) = f x
    simp
end

