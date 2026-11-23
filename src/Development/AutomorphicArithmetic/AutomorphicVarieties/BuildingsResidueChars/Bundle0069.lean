module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0002
public import GroundTheory.AutomorphicForms.ReductionDirichlet
public import GroundTheory.AutomorphicForms.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticFieldSplitPrimeTwoPlaces
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

private theorem two_primes {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {w w' : HeightOneSpectrum (𝓞 K)} (hne : w ≠ w') (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) (hw' : ((p : ℕ) : 𝓞 K) ∈ w'.asIdeal) :
    Ideal.absNorm w.asIdeal = p ∧ Ideal.span {((p : ℕ) : 𝓞 K)} = w.asIdeal * w'.asIdeal := by
  have hco : IsCoprime w.asIdeal w'.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact w.isMaximal.coprime_of_ne w'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
  have hd : w.asIdeal * w'.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 K)} :=
    hco.mul_dvd (Ideal.dvd_span_singleton.2 hw) (Ideal.dvd_span_singleton.2 hw')
  obtain ⟨J, hJ⟩ := hd
  have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  have e := congrArg Ideal.absNorm hJ
  rw [hn, map_mul, map_mul] at e
  have a1 := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have a2 := NumberField.HeightOneSpectrum.one_lt_absNorm w'
  generalize Ideal.absNorm w.asIdeal = a at *
  generalize Ideal.absNorm w'.asIdeal = b at *
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show a ∣ p ^ 2 from ⟨b * Ideal.absNorm J, by rw [e, mul_assoc]⟩)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show b ∣ p ^ 2 from ⟨p ^ i * Ideal.absNorm J, by rw [e]; ring⟩)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (show Ideal.absNorm J ∣ p ^ 2 from ⟨p ^ i * p ^ j, by rw [e]; ring⟩)
  rw [hk, ← pow_add, ← pow_add] at e
  have e2 := Nat.pow_right_injective hp.two_le e
  have i0 : i ≠ 0 := by rintro rfl; simp at a1
  have j0 : j ≠ 0 := by rintro rfl; simp at a2
  have i1 : i = 1 := by omega
  have k0 : k = 0 := by omega
  rw [k0, pow_zero, Ideal.absNorm_eq_one_iff] at hk
  refine ⟨by rw [i1, pow_one], ?_⟩
  rw [hJ, hk, Ideal.mul_top]

private theorem only_two {K : Type} [Field K] [NumberField K] {I : Ideal (𝓞 K)}
    {w w' u : HeightOneSpectrum (𝓞 K)} (h : I = w.asIdeal * w'.asIdeal) (hu : I ≤ u.asIdeal) : u = w ∨ u = w' := by
  rw [h] at hu
  rcases u.isPrime.mul_le.1 hu with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)
  · exact Or.inr (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)

theorem UpperTheory.quadratic_field_split_prime_two_places :
    UpperTheory.V.Sd.S2.QuadSplit := by
  intro Ω _ _ _ k₀ _ h2 p hp hs
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure k₀ Ω := ⟨inferInstance, inferInstance⟩
  have key : ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ g : G ℚ Ω, g ∉ k₀.fixingSubgroup →
      (∀ y, g y ∈ A ↔ y ∈ A') → ∃ w w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal ∧
        IsPlaceOver A w ∧ IsPlaceOver A' w' := by
    intro A A' hA g hg hAA
    have hA' : A'.valuation (p : Ω) < 1 := by
      rw [valuation_lt_one_iff'] at hA ⊢
      rw [← hAA, ← hAA, map_inv₀, map_natCast]
      exact hA
    obtain ⟨a1, a2, a3, -⟩ := places k₀ Ω p A
    obtain ⟨b1, b2, b3, -⟩ := places k₀ Ω p A'
    obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hA
    obtain ⟨u, hu⟩ := b1 fun h => (b2 h).2 hA'
    refine ⟨v, u, ?_, (a3 v hv).1 hA, (b3 u hu).1 hA', hv, hu⟩
    rintro rfl
    obtain ⟨h, hh⟩ := exists_smul_eq_of_isPlaceOver hv hu
    have hm : g * galEmb ℚ k₀ Ω h ∈ Dec (F := ℚ) A := by
      have e : g • A' = A := by
        ext y
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hAA]
        exact iff_of_eq (congrArg (· ∈ A) (g.apply_symm_apply y))
      show (g * galEmb ℚ k₀ Ω h) • A = A
      rw [mul_smul, show galEmb ℚ k₀ Ω h • A = A' from hh, e]
    have hk : galEmb ℚ k₀ Ω h ∈ k₀.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => h.commutes ⟨x, hx⟩
    exact hg ((Subgroup.mul_mem_cancel_right _ hk).1 (hs A hA hm))
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ k₀.fixingSubgroup := by
    by_contra hc
    push Not at hc
    haveI : IsGalois ℚ Ω := {}
    have e : k₀ = ⊥ := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup k₀, (Subgroup.eq_top_iff' _).2 hc, InfiniteGalois.fixedField_bot]
    rw [IntermediateField.finrank_eq_one_iff.2 e] at h2
    omega
  have other : ∀ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal → ∃ w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal := by
    intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨v, u, hne, hv, hu, h1, -⟩ := key A (A.comap g.toRingEquiv.toRingHom)
      (((places k₀ Ω p A).2.2.1 w hA).2 hw) g hg fun _ => Iff.rfl
    have e : v = w := HeightOneSpectrum.ext (Ideal.ext fun x => (h1 x).symm.trans (hA x))
    exact ⟨u, e ▸ hne, hu⟩
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨h1, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨h1, fun h => hne ?_⟩
    rw [← Ideal.dvd_span_singleton, h3, sq, mul_dvd_mul_iff_left w.ne_bot, Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top h).symm
  · obtain ⟨w, hw⟩ : ∃ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal := by
      have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 k₀)}) = p ^ 2 := by
        rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
      have ht : Ideal.span {((p : ℕ) : 𝓞 k₀)} ≠ ⊤ := fun h => by
        rw [Ideal.absNorm_eq_one_iff.2 h] at hn
        exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hn
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ ht
      have hpM := (Ideal.span_singleton_le_iff_mem _).1 hle
      refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hpM⟩
      rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hpM
      exact hp.ne_zero hpM
    obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨-, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨w, w', hne, hw, hw', fun A A' hA g hg hAA => ?_⟩
    obtain ⟨v, u, hvu, hv, hu, h1, h4⟩ := key A A' hA g hg hAA
    rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hv) with rfl | rfl <;>
      rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hu) with rfl | rfl
    exacts [absurd rfl hvu, Or.inl ⟨h1, h4⟩, Or.inr ⟨h1, h4⟩, absurd rfl hvu]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RayClassGroupFinite
section
open UpperTheory.V.Sd.Eis
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V

private theorem idele_split (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom x) * finId F (Units.map (pFin F).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h3, h4]

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) :
    Continuous fun x : Ad F => TR.pInf F x v :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp
    ((continuous_apply v).comp continuous_fst)

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ray_class_group_finite :
    UpperTheory.V.Sd.Eis.RayFin := by
  intro F _ _ _ H hK hR hf
  have hopen : IsOpen (H : Set (Ideles F)) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    have c1 : Continuous (Units.map (pFin F).toMonoidHom : Ideles F → (Af F)ˣ) :=
      Continuous.units_map _ continuous_snd
    have h1 : ∀ᶠ x : Ideles F in 𝓝 1, finId F (Units.map (pFin F).toMonoidHom x) ∈ H := by
      have := c1.continuousAt (x := 1)
      rw [ContinuousAt, map_one] at this
      exact this hf
    have h2 : ∀ᶠ x : Ideles F in 𝓝 1, ∀ v, 0 < TR.pInf F x.val v := by
      rw [Filter.eventually_all]
      intro v
      have c : Continuous fun x : Ideles F => TR.pInf F x.val v := (cont_pInf F v).comp Units.continuous_val
      refine c.continuousAt.eventually (lt_mem_nhds ?_)
      simp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← idele_split F x]
    exact H.mul_mem (hR _ hx2) hx1
  refine ⟨hopen, ?_⟩
  have hsq : ∀ (ρ : ℝ) (hρ : 0 < ρ), ((posIdele ρ hρ : IdeleGroup F) : Ideles F) ^ 2 ∈ H := by
    intro ρ hρ
    set z : Ideles F := (posIdele ρ hρ : IdeleGroup F) with hz
    have e : Units.map (pFin F).toMonoidHom z = 1 := by
      refine Units.ext ?_
      ext v
      exact congrArg _ (posIdele_finite ρ hρ v)
    have e2 := idele_split F z
    rw [e, map_one, mul_one] at e2
    rw [← e2, ← map_pow]
    refine hR _ fun v => ?_
    set y := Units.map (TR.pInf F).toMonoidHom z
    have hy : y.val v ≠ 0 := by
      have := congrFun y.mul_inv v
      exact left_ne_zero_of_mul_eq_one this
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
    positivity
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  have hcov : ∀ t : Ideles F, ∃ s ∈ S, s⁻¹ * t ∈ H := by
    intro t
    have hn : 2 * Module.finrank ℚ F ≠ 0 := mul_ne_zero two_ne_zero Module.finrank_pos.ne'
    have ht : 0 < (ideleModule F t : ℝ) := (ideleModule F t).2
    set ρ : ℝ := (ideleModule F t : ℝ) ^ (((2 * Module.finrank ℚ F : ℕ) : ℝ)⁻¹) with hρdef
    have hρ : 0 < ρ := Real.rpow_pos_of_pos ht _
    have hρn : ρ ^ (2 * Module.finrank ℚ F) = (ideleModule F t : ℝ) := Real.rpow_inv_natCast_pow ht.le hn
    have hzH := hsq ρ hρ
    have hzt : ideleModule F (posIdele ρ hρ ^ 2) = ideleModule F t := by
      refine Subtype.ext ?_
      rw [sq, map_mul, ← hρn, two_mul, pow_add, ← ideleModule_posIdele ρ hρ]
      rfl
    generalize (posIdele ρ hρ : IdeleGroup F) ^ 2 = z at hzH hzt
    have h1 : (ideleModule F (t * z⁻¹) : ℝ) = 1 := by
      rw [map_mul, map_inv, hzt, mul_inv_cancel]; rfl
    obtain ⟨c, hcS⟩ := hSm (t * z⁻¹) h1.ge h1.le
    refine ⟨_, hcS, ?_⟩
    have e : (diagonal F c * (t * z⁻¹))⁻¹ * t = z * (diagonal F c)⁻¹ := by
      rw [mul_inv, mul_inv, inv_inv, mul_assoc, mul_right_comm, inv_mul_cancel, one_mul, mul_comm]
    rw [e]
    exact H.mul_mem hzH (H.inv_mem (hK c))
  haveI : DiscreteTopology (Ideles F ⧸ H) := QuotientGroup.discreteTopology hopen
  have hfin : ((QuotientGroup.mk : Ideles F → Ideles F ⧸ H) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  haveI : Finite (Ideles F ⧸ H) := by
    refine Set.finite_univ_iff.1 (hfin.subset fun q _ => ?_)
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, hst⟩ := hcov t
    exact ⟨s, hs, QuotientGroup.eq.2 hst⟩
  exact Subgroup.finiteIndex_of_finite_quotient
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidualCharactersPsiNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws UpperTheory.V.Sd

private theorem closed_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F E : IntermediateField ℚ Ω) :
    IsClosed ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) := by
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) =
      ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rfl
  rw [e]
  exact isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)

private theorem lim_pt {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (S : Set Γ) (hS : IsClosed S) (g : Γ)
    (hg : (l : ℤ_[l]) ∣ (ε g : ℤ_[l]) - 1) (hm : ∀ n : ℕ, g ^ l ^ n ∈ S) : ∃ h ∈ S, ε h = 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have h2 := dvd_sub_pow_of_dvd_sub hg n
    rw [one_pow] at h2
    have h3 := (pow_dvd_pow _ n.le_succ).trans h2
    rw [map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h3
  obtain ⟨h, hh, hc⟩ := hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))
  refine ⟨h, hh, Units.ext ?_⟩
  have hc' := hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt
  exact eq_of_nhds_neBot (hc'.clusterPt.mono ht)

private theorem dvd_of_om {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.om g = 1) : (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - 1 := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  have h := hD.om_bar g
  simp only [Raw.bar, hg, Units.val_one] at h
  have h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0 := by
    rw [map_sub, map_sub, map_one, h, sub_eq_zero]
    rfl
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := fun hu => h1 (hu.map _)
  rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  (T : Tower D)

private noncomputable def eta : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt wPs)

private theorem eta_val (g : G T.F Ω) : (eta T g : ResidueField c.O) = T.rb wPs g := rfl

private theorem eta_sq (hT : T.Two) (g : G T.F Ω) : eta T g ^ 2 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, eta_val, hT.sq, Units.val_one])

private theorem eta_om (hD : D.Good) (hT : T.Two) (hne : ∀ g ∈ T.G', T.rb wPs g = 1) (g : G T.F Ω) (hg' : g ∈ T.GalL)
    (hg : D.om (resQ T.F g) = 1) : eta T g = 1 := by
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  obtain ⟨k₀, -, -, -, hk⟩ := hT.quad
  have hk' : ∀ g, eta T g = 1 ↔ g ∈ k₀.fixingSubgroup.comap (resQ T.F) := fun g => by
    rw [Subgroup.mem_comap, ← hk, ← eta_val, Units.val_eq_one]
  have hc : Continuous fun h : G T.F Ω => g⁻¹ * h := continuous_const_mul _
  have h0 : IsClosed (T.GalL : Set (G T.F Ω)) := closed_fix T.F T.K
  have hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1 := dvd_of_om D hD (resQ T.F g) hg
  obtain ⟨h, ⟨h1, h2⟩, h3⟩ := lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _
    (h0.inter ((closed_fix T.F k₀).preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by
      refine (hk' _).1 ?_
      obtain ⟨m, hm⟩ := (hl.out.odd_of_ne_two hD.l_odd).pow (n := n)
      rw [map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, eta_sq T hT, one_pow, one_mul, inv_mul_cancel]⟩)
  have h4 : eta T h = 1 := by
    rw [← Units.val_eq_one, eta_val]
    exact hne h ⟨h1, h3⟩
  have h5 := (hk' _).2 h2
  rwa [map_mul, h4, mul_one, map_inv, inv_eq_one] at h5

private theorem eta_mul (g : G T.F Ω) :
    eta T g * Raw.bar (chi D T.pr 2) (resQ T.F g) = Raw.bar (chi D T.pr 0) (resQ T.F g) ∧
    eta T g * Raw.bar (chi D T.pr 3) (resQ T.F g) = Raw.bar (chi D T.pr 1) (resQ T.F g) := by
  have e : (T.fr ∅).rt wPs g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹ := by
    show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (0 : ℤ) *
      (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (1 : ℤ) = _
    rw [zpow_zero, zpow_one, one_mul]
  have e' : (T.fr ∅).rt wPs g = chi D T.pr 1 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹ := by
    rw [e]
    generalize resQ T.F g = s
    cases T.pr
    · show D.al s * D.Psi s * (D.al s)⁻¹ = D.Psi s * 1⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_comm]
    · show D.al s * (D.al s * D.Psi s)⁻¹ = 1 * (D.Psi s)⁻¹
      rw [one_mul, mul_inv, mul_inv_cancel_left]
  rw [eta_val]
  constructor
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]

private theorem eta_mul' (hT : T.Two) (g : G T.F Ω) {u v : ResidueField c.O} (h : eta T g * u = v) : eta T g * v = u := by
  rw [← h, ← mul_assoc, ← Units.val_mul, ← pow_two, eta_sq T hT, Units.val_one, one_mul]

private noncomputable def etaL : T.GalL →* (ResidueField c.O)ˣ := (eta T).comp T.GalL.subtype

private theorem etaL_app (g : T.GalL) : etaL T g = eta T g := rfl

private theorem etaL_sq (hT : T.Two) : etaL T ^ 2 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, eta_sq T hT]

private theorem etaL_perm (hT : T.Two) (i : Fin 4) : ∃ j, ∀ g : T.GalL, etaL T g * Raw.bar (chi D T.pr i) (resQ T.F g) =
      Raw.bar (chi D T.pr j) (resQ T.F g) := by
  simp only [etaL_app]
  match i with
  | 0 => exact ⟨2, fun g => eta_mul' T hT g (eta_mul T g).1⟩
  | 1 => exact ⟨3, fun g => eta_mul' T hT g (eta_mul T g).2⟩
  | 2 => exact ⟨0, fun g => (eta_mul T g).1⟩
  | 3 => exact ⟨1, fun g => (eta_mul T g).2⟩

end

theorem UpperTheory.residual_characters_psi_ne :
    UpperTheory.V.Sd.S2.PsiNe := by
  intro Ω _ _ _ l hl c D T hD hO hT
  by_contra hne
  have hne' : ∀ g ∈ T.G', T.rb wPs g = 1 := fun g hg => by_contra fun h => hne ⟨g, hg, h⟩
  have key := hO.g3' (etaL T) (etaL_sq T hT)
    (fun g hg => by rw [etaL_app]; exact eta_om T hD hT hne' g g.2 hg) (etaL_perm T hT)
  obtain ⟨g, hg, hg'⟩ := hO.g3 wPs (by decide)
  have h1 := etaL_app T ⟨g, hg⟩
  rw [key, MonoidHom.one_apply] at h1
  apply hg'
  rw [← eta_val, ← h1, Units.val_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeLineExists
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem col_eq {k : Type} [Field k] (g r : GL (Fin 2) k) (a b : k) (h10 : (g * r * g⁻¹ : GL (Fin 2) k) 1 0 = 0)
    (h00 : (g * r * g⁻¹ : GL (Fin 2) k) 0 0 = a) (h11 : (g * r * g⁻¹ : GL (Fin 2) k) 1 1 = b) :
    r 0 0 * g⁻¹ 0 0 + r 0 1 * g⁻¹ 1 0 = a * g⁻¹ 0 0 ∧ r 1 0 * g⁻¹ 0 0 + r 1 1 * g⁻¹ 1 0 = a * g⁻¹ 1 0 ∧
      r 0 0 + r 1 1 = a + b := by
  have e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) =
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e0 e1
  have t : Matrix.trace ((g * r * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.trace (r : Matrix (Fin 2) (Fin 2) k) := by
    rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, inv_mul_cancel_left]
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at t
  rw [h10, h00] at e0 e1
  rw [h00, h11] at t
  refine ⟨?_, ?_, t.symm⟩
  · rw [e0]; ring
  · rw [e1]; ring

theorem UpperTheory.symmetric_cube_line_exists :
    UpperTheory.V.Sd.S3.LineEx := by
  intro l _ Γ _ H ρ ξ κ hρ ⟨g, hg⟩ hκ ⟨s₀, hs₀, hne⟩
  have key := fun s : H => col_eq g (ρ s) _ _ ((hg s).1 1 0 (by decide)) ((hg s).2 0) ((hg s).2 1)
  have hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 -
      (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    have := (g⁻¹).det_ne_zero
    rwa [Matrix.det_fin_two] at this
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet
  have hge : 1 ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ := by
    by_contra hlt
    apply hne
    have h1 : ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - (ξ s₀ : Qbar l)‖ < 1 := hκ ⟨s₀, hs₀⟩
    rw [norm_sub_rev] at h1
    have e : (ξ s₀ : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((ξ s₀ : Qbar l) - (κ 0 ⟨s₀, hs₀⟩ : Qbar l)) +
        (((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) + (ρ s₀ 1 1 - 1)) := by
      rw [Units.val_one]; ring
    unfold Cong
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) (hρ s₀).1)
  have hqp : ‖q‖ ≤ ‖p‖ := by
    have e : ((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) * q = ρ s₀ 1 0 * p := by
      have := (key ⟨s₀, hs₀⟩).2.1
      simp only at this
      linear_combination -this
    calc ‖q‖ ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hge
      _ = ‖ρ s₀ 1 0‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]
      _ ≤ ‖p‖ := mul_le_of_le_one_left (norm_nonneg _) (hρ s₀).2
  have hp : p ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_le_zero_iff] at hqp
    simp [hqp] at hdet
  refine ⟨q / p, ?_, fun s => ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ hqp (norm_nonneg _)
  · obtain ⟨k1, k2, k3⟩ := key s
    have a1 : ρ s 0 0 + ρ s 0 1 * (q / p) = κ 0 s := by
      field_simp
      linear_combination k1
    refine ⟨a1, ?_, ?_⟩
    · field_simp
      linear_combination k2
    · linear_combination k3 - a1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TeichmullerCharacterSpec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.teichmuller_character_spec :
    UpperTheory.V.Sd.S3.Teich := by
  intro l _ c x m hcop hx hres
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l c.O
  have hnd : ¬ l ∣ m := fun h =>
    (Nat.Prime.one_lt (Fact.out : l.Prime)).ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hm := hunit m hnd
  have hX : (x : c.O) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hgeom : (∑ i ∈ Finset.range m, (x : c.O) ^ i) * ((x : c.O) - 1) = 0 := by
    rw [geom_sum_mul, hX, sub_self]
  have hres' : residue c.O (∑ i ∈ Finset.range m, (x : c.O) ^ i) = residue c.O (m : c.O) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_pow, hres]
  have hS : IsUnit (∑ i ∈ Finset.range m, (x : c.O) ^ i) := by
    rw [← isUnit_map_iff (residue c.O), hres', isUnit_map_iff]
    exact hm
  have h0 : (x : c.O) - 1 = 0 := hS.mul_right_eq_zero.mp hgeom
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h0)
end

