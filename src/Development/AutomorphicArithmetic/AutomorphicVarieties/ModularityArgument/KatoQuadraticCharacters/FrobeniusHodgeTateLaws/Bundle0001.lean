module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CoefUb
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.coefUb :
    UpperTheory.V.Z.Kato.Joint.CoefUb := by
  intro l _ c c' F hF
  obtain ⟨d, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
  obtain ⟨d', h3, h4⟩ := (UpperTheory.V.Th.Nm.inOf d).1 {x // x ∈ F} (fun x => x.1) (fun x => hF x.1 x.2)
  exact ⟨d', h1.trans h3, h2.trans h3, fun x hx => h4 ⟨x, hx⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.DetIne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint Polynomial

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_of_apply [IsAlgClosure ℚ Ω] {Y : Type} [TopologicalSpace Y] (ζ : Ω) (f : G ℚ Ω → Y)
    (h : ∀ s t : G ℚ Ω, s ζ = t ζ → f s = f t) : Continuous f := by
  have hint : IsIntegral ℚ ζ :=
    ((IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hH : IsOpen (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
      Set (Ω ≃ₐ[ℚ] Ω)) := IntermediateField.fixingSubgroup_isOpen _
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hU : IsOpen ((fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω))) := hH.preimage (continuous_const_mul _)
  have ht : t ∈ (fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω)) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  refine (continuousAt_const (y := f t)).congr ?_
  filter_upwards [hU.mem_nhds ht] with s hs
  have h1 : (t⁻¹ * s) ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ
      (IntermediateField.mem_adjoin_simple_self ℚ ζ)
  have h2 : s ζ = t ζ := by
    have h3 := congrArg t h1
    rw [AlgEquiv.mul_apply] at h3
    simpa using h3
  exact (h s t h2).symm

private theorem root_pow {M n : ℕ} (hM : M ≠ 0) {B : ValuationSubring Ω} {v : Pl} (hB : IsPlaceOver B v)
    (hv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {s : G ℚ Ω} {ζ : Ω} (hζ : ζ ^ M = 1)
    (hs : ∀ x, B.valuation x ≤ 1 → B.valuation (s x - x ^ n) < 1) : s ζ = ζ ^ n := by
  have hN : ¬ B.valuation (M : Ω) < 1 := fun h => hv ((hB _).1 (by simpa using h))
  refine eq_of_pow_eq_one B hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one B hM hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem expo_eq {M a b : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (h : ζ ^ a = ζ ^ b) :
    (a : ZMod M) = b := by
  have hu := hζ.isUnit (NeZero.ne M)
  have h1 : IsPrimitiveRoot hu.unit M := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  have h2 : hu.unit ^ a = hu.unit ^ b := Units.ext (by simpa using h)
  rw [pow_eq_pow_iff_modEq, ← h1.eq_orderOf] at h2
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2

private theorem det_of_charpoly {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.det = d := by
  have h0 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h
  simp [Polynomial.coeff_map] at h0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simp [h0]

end

theorem UpperTheory.V.Z.Kato.Joint.detIne :
    UpperTheory.V.Z.Kato.Joint.DetIne := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt s hs
  have hM : g.M ≠ 0 := g.pos.ne'
  haveI : NeZero g.M := ⟨hM⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((g.M : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hM⟩
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hl0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω g.M
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  let F : Ω → Qbar l := fun x =>
    ι.symm (g.χ ((Classical.epsilon (fun k : ℕ => ζ ^ k = x) : ℕ) : ZMod g.M))
  have hF : ∀ k : ℕ, F (ζ ^ k) = ι.symm (g.χ k) := by
    intro k
    have h1 : ζ ^ (Classical.epsilon (fun j : ℕ => ζ ^ j = ζ ^ k)) = ζ ^ k :=
      Classical.epsilon_spec (p := fun j : ℕ => ζ ^ j = ζ ^ k) ⟨k, rfl⟩
    show ι.symm (g.χ _) = _
    rw [expo_eq hζ h1]
  let f : G ℚ Ω → Qbar l := fun t => ((dt W t * (χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)
  have hf'c : Continuous (fun t : G ℚ Ω => F (t ζ)) :=
    cont_of_apply ζ _ (fun a b h => by simp only [h])
  have hcop : ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro w hlw hmem
    obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) (g.M : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl)
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : (a : 𝓞 ℚ) * (l : 𝓞 ℚ) + (b : 𝓞 ℚ) * (g.M : 𝓞 ℚ) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) hab
    rw [← h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlw) (Ideal.mul_mem_left _ _ hmem)
  have key : f = fun t => F (t ζ) := by
    have hχc : Continuous (fun t : G ℚ Ω => (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)) := by
      refine cont_of_apply η _ (fun a b hab => ?_)
      have h0 : χ (b⁻¹ * a) = 1 := hK (b⁻¹ * a) (fun x hx => by
        obtain ⟨i, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hx
        rw [map_pow]
        simp [AlgEquiv.mul_apply, hab])
      rw [map_mul, map_inv, inv_mul_eq_one] at h0
      rw [h0]
    have hdt : ∀ t, ((W t : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((dt W t : (Qbar l)ˣ) : Qbar l) := fun t => rfl
    have hdc : Continuous (fun t : G ℚ Ω => ((dt W t : (Qbar l)ˣ) : Qbar l)) := by
      simp only [← hdt]
      exact (Units.continuous_val.comp hN.cont).matrix_det
    have hfc : Continuous f := by
      have h3 : f = fun t => ((dt W t : (Qbar l)ˣ) : Qbar l) *
          (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l) := by
        funext t
        simp only [f, Units.val_mul]
      rw [h3]
      exact hdc.mul hχc
    have hbad := Filter.eventually_cofinite.1 hAtt.2
    have hI : Ideal.span {((g.M * l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (mul_ne_zero hM hl0)
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (hbad.union (Ideal.finite_factors hI)) hfc hf'c ?_
    intro w hw _ B hB σ hσ
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    obtain ⟨hP, hdiv⟩ := hw
    have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ h4
    have hMw : ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h4
    have hσζ : σ ζ = ζ ^ normV w := root_pow hM hB hMw hζ.pow_eq_one hσ.2
    show f σ = F (σ ζ)
    rw [hσζ, hF]
    have hch := (hP B hB).2 σ hσ
    rw [Newform.heckePoly] at hch
    have hdet := det_of_charpoly ι hch
    have hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
      have h5 := cycZ_of_isFrob hlw hB hσ
      simp [cycBar, h5]
    rw [tw_val, Matrix.det_smul, Fintype.card_fin, hdt] at hdet
    simp [map_inv, hcyc] at hdet
    have hd0 : ι ((dt W σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hx0 : ι ((χ σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hn0 : (normV w : ℂ) ≠ 0 := by
      have h6 : (normV w : Qbar l) ≠ 0 := hcyc ▸ Units.ne_zero _
      exact_mod_cast (Nat.cast_ne_zero.1 h6)
    apply ι.injective
    rw [RingEquiv.apply_symm_apply]
    simp only [f]
    simp [map_inv]
    apply mul_right_cancel₀ (pow_ne_zero (2 * e) hn0)
    rw [← hdet]
    field_simp
    ring
  obtain ⟨v, hv, hlv⟩ := hN.atL
  have hs' : s ∈ Inertia A := hs
  have hsζ : s ζ = ζ ^ 1 :=
    root_pow hM hv (hcop v hlv) hζ.pow_eq_one (fun x hx => by simpa using hs'.2 x hx)
  have h1 := congrFun key s
  simp only [f, hsζ, hF, Nat.cast_one, map_one, Units.val_eq_one] at h1
  rw [inv_pow, mul_inv_eq_one] at h1
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.EulerSystemNorms
section
open UpperTheory.V.Z.Kato.Joint Topology Filter

private theorem mem_fixingSubgroup_of_fixes_finite_set (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] :
    ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ E.fixingSubgroup := by
  have h1 : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite K E))
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, fun g hg => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : Algebra.adjoin K (t : Set Ω) ≤ AlgHom.equalizer (g : Ω →ₐ[K] Ω) (AlgHom.id K Ω) :=
    Algebra.adjoin_le (fun y hy => by
      rw [SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg y hy)
  have hx1 : x ∈ Submodule.span K (t : Set Ω) := by
    rw [ht]
    exact hx
  have hx2 : x ∈ Algebra.adjoin K (t : Set Ω) := Algebra.span_le_adjoin K _ hx1
  have hx3 := hle hx2
  rw [AlgHom.mem_equalizer] at hx3
  simpa using hx3

private theorem uniform_continuity_galois_group (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {X : Type} [NormedAddCommGroup X]
    (f : (Ω ≃ₐ[K] Ω) → X) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[K] Ω, (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ := by
  classical
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have key : ∀ s : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ g ∈ E.fixingSubgroup, ‖f (s * g) - f s‖ < δ / 2 := by
    intro s
    have hc : Continuous fun g : Ω ≃ₐ[K] Ω => ‖f (s * g) - f s‖ :=
      ((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).norm
    have hA : {g : Ω ≃ₐ[K] Ω | ‖f (s * g) - f s‖ < δ / 2} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
      IsOpen.mem_nhds (isOpen_lt hc continuous_const) (by simp [hδ2])
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hA
    exact ⟨E, hE, fun g hg => hsub hg⟩
  choose E hEf hE using key
  let U : (Ω ≃ₐ[K] Ω) → Set (Ω ≃ₐ[K] Ω) := fun i => {h | i⁻¹ * h ∈ (E i).fixingSubgroup}
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    haveI := hEf i
    exact (IntermediateField.fixingSubgroup_isOpen (E i)).preimage (continuous_const.mul continuous_id)
  have hUc : Set.univ ⊆ ⋃ i, U i := by
    intro h _
    refine Set.mem_iUnion.2 ⟨h, ?_⟩
    show h⁻¹ * h ∈ (E h).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have hT : ∀ i, ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ (E i).fixingSubgroup := by
    intro i
    haveI := hEf i
    exact mem_fixingSubgroup_of_fixes_finite_set K Ω (E i)
  choose T hT using hT
  refine ⟨S.biUnion T, fun s s' hs' => ?_⟩
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ s))
  have hi' : i⁻¹ * s ∈ (E i).fixingSubgroup := hi
  have hs'i : s' ∈ (E i).fixingSubgroup :=
    hT i s' (fun x hx => hs' x (Finset.mem_biUnion.2 ⟨i, hiS, hx⟩))
  have h1 := hE i _ (mul_mem hi' hs'i)
  have h2 := hE i _ hi'
  rw [← mul_assoc, mul_inv_cancel_left] at h1
  rw [mul_inv_cancel_left] at h2
  have h3 : f (s * s') - f s = (f (s * s') - f i) - (f s - f i) := by abel
  rw [h3]
  have := norm_sub_le (f (s * s') - f i) (f s - f i)
  linarith

theorem UpperTheory.V.Z.Kato.Joint.unif :
    UpperTheory.V.Z.Kato.Joint.Unif := by
  intro l _ Ω _ _ _ f hf δ hδ
  haveI : IsGalois ℚ Ω := inferInstance
  exact uniform_continuity_galois_group ℚ Ω f hf δ hδ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FrobUNormV
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open UpperTheory.V.Z.Kato.Joint

private theorem frobU_normV {p : ℕ} (hp : p.Prime) {v : Pl} (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = p := by
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hspan : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_singleton]
    have h1 : ((p : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
    simp
  have hle : Ideal.span {((p : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hv
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [hspan] at hd
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exact absurd (Ideal.absNorm_eq_one_iff.1 h1) v.isPrime.ne_top
  · rw [hN, h1]

theorem UpperTheory.V.Z.Kato.Joint.frobU :
    UpperTheory.V.Z.Kato.Joint.FrobU := by
  intro l hl Ω _ _ _ e S A W hW
  refine ⟨?_, fun s hs => ?_, fun s => ?_⟩
  · obtain ⟨v, hA, hv⟩ := hW.atL
    obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hA
    rw [frobU_normV hl.out hv] at hσ
    exact ⟨σ, mem_Dec.2 hσ.1, hσ⟩
  · obtain ⟨c, hc⟩ := hW.int
    have hm : mat W s * mat W s⁻¹ = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h11 : mat W s 1 1 * mat W s⁻¹ 1 1 = 1 := by
      have h := congrFun (congrFun hm 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, hW.upper s hs, zero_mul, zero_add, Matrix.one_apply_eq] at h
      exact h
    have ha := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s 1 1)
    have hb := GlobalTheory.Ord2.CupCob.norm_le_one_of_mem c (hc s⁻¹ 1 1)
    have hn : ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ = 1 := by rw [← norm_mul, h11, norm_one]
    refine le_antisymm ha ?_
    calc (1 : ℝ) = ‖mat W s 1 1‖ * ‖mat W s⁻¹ 1 1‖ := hn.symm
      _ ≤ ‖mat W s 1 1‖ := mul_le_of_le_one_right (norm_nonneg _) hb
  · have h : eps l s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := rfl
    rw [h, norm_algebraMap']
    exact PadicInt.norm_units _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Imports
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.mono :
    UpperTheory.V.Z.Kato.Joint.Mono := by
  intro l _ Ω _ _ c c' h
  refine ⟨?_, ?_, ?_⟩
  · rintro W y S' ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun s i j => h (h1 s i j), h2, fun s i => h (h3 s i), h4, fun n hn w hw hd ψ hk hs => ?_⟩
    obtain ⟨Y, P, u, b, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h5 n hn w hw hd ψ hk hs
    refine ⟨Y, P, u, b, a1, fun s x i => h (a2 s x i), h a3, a4, fun i => h (a5 i), a6, a7, a8, fun q hq hl => ?_⟩
    obtain ⟨B, hB, t, ht, ht'⟩ := a9 q hq hl
    exact ⟨B, hB, t, fun x i => h (ht x i), ht'⟩
  · rintro A ν Z ⟨h1, h2, h3⟩
    exact ⟨h1, fun r => ⟨fun s x => h ((h2 r).1 s x), (h2 r).2⟩, h3⟩
  · rintro A Z j m₀ c₀ Rhs ⟨ζ, hζ, H⟩
    refine ⟨ζ, hζ, fun m hm => ?_⟩
    obtain ⟨ι, inst, P, o, ⟨p1, p2, p3, p4, p5⟩, hc⟩ := H m hm
    exact ⟨ι, inst, P, o, ⟨p1, p2, fun i => h (p3 i), p4, p5⟩, hc⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.JEx
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.jEx :
    UpperTheory.V.Z.Kato.Joint.JEx := by
  intro l _ Ω _ _ _ A hA
  obtain ⟨v, hv, hl⟩ := hA
  have hAl : A.valuation ((l : ℕ) : Ω) < 1 := by
    have := (hv ((l : ℕ) : NumberField.RingOfIntegers ℚ)).2 hl
    simpa using this
  exact ⟨(ValuationSubring.mem_nonunits_iff _).2 hAl, Formalism.BasicNotions.Examples₂.LB.exists_emb A hAl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.LawMono
section
open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem cg_scale {l : ℕ} [Fact l.Prime] (K : Qbar l) : ∃ N : ℕ, ∀ m, N ≤ m → ∀ (c₀ : ℕ) (u x y : Qbar l),
    ‖u‖ = 1 → Cg (2 * m) x y → Cg (m - c₀) (u * K * y) (u * K * x) := by
  have hl0 : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have hl1 := norm_l_lt_one l
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ 1 := by
    rcases eq_or_ne ‖K‖ 0 with hK | hK
    · exact ⟨0, by rw [hK, mul_zero]; exact zero_le_one⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK))) hl1
      refine ⟨N, ?_⟩
      have hKpos : 0 < ‖K‖ := lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK)
      calc ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ ‖K‖⁻¹ * ‖K‖ :=
            mul_le_mul_of_nonneg_right hN.le hKpos.le
        _ = 1 := inv_mul_cancel₀ hK
  refine ⟨N, fun m hm c₀ u x y hu hxy => ?_⟩
  unfold Cg at hxy ⊢
  rw [norm_pow] at hxy ⊢
  have hdiff : u * K * y - u * K * x = -(u * K * (x - y)) := by ring
  rw [hdiff, norm_neg, norm_mul, norm_mul, hu, one_mul]
  have hmN : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ N := pow_le_pow_of_le_one hl0 hl1.le hm
  have hmc : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) :=
    pow_le_pow_of_le_one hl0 hl1.le (Nat.sub_le m c₀)
  have hKm : ‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hmN (norm_nonneg K)) hN
  calc ‖K‖ * ‖x - y‖ ≤ ‖K‖ * ‖((l : ℕ) : Qbar l)‖ ^ (2 * m) :=
        mul_le_mul_of_nonneg_left hxy (norm_nonneg K)
    _ = (‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖) * ‖((l : ℕ) : Qbar l)‖ ^ m := by ring
    _ ≤ 1 * ‖((l : ℕ) : Qbar l)‖ ^ m :=
        mul_le_mul_of_nonneg_right hKm (pow_nonneg hl0 m)
    _ ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) := by rw [one_mul]; exact hmc

private theorem law_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {c : Coef l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l} {m₀ m₁ c₀ : ℕ}
    {R : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (hm : m₀ ≤ m₁) (h : HTLawCsOfCoef A c Z j m₀ c₀ R) :
    HTLawCsOfCoef A c Z j m₁ c₀ R := by
  obtain ⟨ζ, hζ, hlaw⟩ := h
  exact ⟨ζ, hζ, fun m hm' => hlaw m (hm.trans hm')⟩

open Classical in
private theorem cg_cases {l : ℕ} [Fact l.Prime] {κ₀ κ : Qbar l} (hκ : κ ≠ 0) : ∃ N : ℕ, ∀ m, N ≤ m →
    ∀ (c₀ : ℕ) (v a p s X b g w : Qbar l), ‖v‖ = 1 → ‖a‖ = 1 → p ^ 2 = 1 → s ^ 2 = 1 →
    (p = s → Cg (2 * m) X (κ * b * g * w)) → (p = -s → Cg (2 * m) X 0) →
    Cg (m - c₀) (if p = s then v * κ₀ * a ^ m * (b * g * w) else 0) (v * (κ₀ / κ) * a ^ m * X) := by
  obtain ⟨N, hN⟩ := cg_scale (κ₀ / κ)
  refine ⟨N, fun m hm c₀ v a p s X b g w hv ha hp hs h1 h2 => ?_⟩
  have hu : ‖v * a ^ m‖ = 1 := by rw [norm_mul, norm_pow, hv, ha, one_pow, one_mul]
  by_cases hE : p = s
  · rw [if_pos hE]
    have h3 := hN m hm c₀ (v * a ^ m) X (κ * b * g * w) hu (h1 hE)
    have e1 : v * a ^ m * (κ₀ / κ) * (κ * b * g * w) = v * κ₀ * a ^ m * (b * g * w) := by
      field_simp
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [e1, e2] at h3
    exact h3
  · have hps : p ^ 2 = s ^ 2 := by rw [hp, hs]
    have hO : p = -s := (sq_eq_sq_iff_eq_or_eq_neg.1 hps).resolve_left hE
    rw [if_neg hE]
    have h3 := hN m hm c₀ (v * a ^ m) X 0 hu (h2 hO)
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [mul_zero, e2] at h3
    exact h3

theorem UpperTheory.V.Z.Kato.Joint.pinOf :
    UpperTheory.V.Z.Kato.Joint.PinOf := by
  intro hM hU hMo l _ Ω _ _ ι e A W c ν Z j u w ψ α B cc v n β t hl he hα hj hν hσ hμ hv ht hne hE
  obtain ⟨cO, L, κ, φ, n₀, r₁, hκ, hL, hφ, h1, h2, h3⟩ :=
    hM l ι e _ u w ψ α B cc v n β t hl he rfl hμ hv ht hne
  obtain ⟨c', hc, hcO, -⟩ := hU l c cO ∅ (fun x hx => absurd hx (Finset.notMem_empty x))
  obtain ⟨κ₀, vv, m₀, c₀, hκ₀, hvv, hH⟩ := hE
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := hσ
  obtain ⟨N, hN⟩ := cg_cases (κ₀ := κ₀) hκ
  have hH' := law_mono (le_max_left m₀ (max N 1)) ((hMo l Ω c c' hc).2.2 A Z j m₀ c₀ _ hH)
  refine ⟨c', hc, ?_⟩
  unfold Pin7
  refine ⟨ν σ, ι.symm α, κ₀ / κ, vv, j, _, L, φ, max m₀ (max N 1), c₀, n₀, hν, ⟨σ, hσ1, hσ2, rfl⟩, hσ3, hα, hvv,
    div_ne_zero hκ₀ hκ, hj, fun k => hcO (hL k), hH', ?_, ?_, r₁, h3⟩
  · intro m hm ψ' _ z hz
    have hm1 : 1 ≤ m := by omega
    have hmN : N ≤ m := by omega
    have ha : ψ' (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    have hb : (ι.symm ((-1) ^ e * ψ (-1))) ^ 2 = 1 := by
      rw [← map_pow, mul_pow, ← map_pow, ← pow_mul, mul_comm e 2, pow_mul, neg_one_sq, neg_one_sq, one_pow, map_one,
        one_mul, map_one]
    exact hN m hmN c₀ _ _ _ _ _ _ _ _ (hvv m).1 hα ha hb (fun hs => h1 m hm1 ψ' hs z hz) (fun hs => h2 m hm1 ψ' hs z hz)
  · intro r _ x
    apply ι.injective
    rw [map_inv₀, hφ, MulChar.inv_apply_eq_inv', inv_inv]
    exact ι.apply_symm_apply _
end

