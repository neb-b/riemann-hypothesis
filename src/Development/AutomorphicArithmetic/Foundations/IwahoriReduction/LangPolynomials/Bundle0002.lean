module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem frobEx_norm {l : ℕ} (hl : l.Prime) {v : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = l := by
  haveI : Fact l.Prime := ⟨hl⟩
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
    apply hmax.eq_of_le
    · intro htop
      apply v.isPrime.ne_top
      exact (Ideal.map_eq_top_of_bijective _ e.bijective).1 htop
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have := Ideal.mem_map_of_mem (e : 𝓞 ℚ →+* ℤ) hv
      simpa using this
  unfold normV
  rw [Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ e hJ).toEquiv,
    Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

theorem UpperTheory.Kd.C7.pFrobEx :
    UpperTheory.Kd.C7.SFrobEx := by
  intro l _ _ Ω _ _ _ A hA
  obtain ⟨v, hv, hlv⟩ := hA
  have hnorm : normV v = l := frobEx_norm Fact.out hlv
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  refine ⟨?_, fun σ _ σ' _ hσ hσ' => inv_mul_mem_Ine_of_isFrob hσ hσ',
    GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hv
  rw [hnorm] at hσ
  obtain ⟨ι, hι, hιu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval (cycZ ℚ Ω l σ)⁻¹
  have hfr : IsFrob A l (σ * ι) := isFrob_mul_of_mem_Ine hσ hι
  refine ⟨σ * ι, hfr.1, hfr, ?_⟩
  unfold cycBar
  rw [MonoidHom.comp_apply, map_mul, hιu, mul_inv_cancel, map_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.InertiaInvariantValuationUniformizerBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem unramified_uniformizer_divides {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (π : 𝓞 K) (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p = Ideal.span {π}) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver p]
    (h : Algebra.IsUnramifiedAt (𝓞 K) P) (x : 𝓞 E) (hx : x ∈ P) :
    ∃ t y : 𝓞 E, t ∉ P ∧ t * x = algebraMap (𝓞 K) (𝓞 E) π * y := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  have h2 := ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 K) p P).1 h).2
  have h3 : algebraMap (𝓞 E) (Localization.AtPrime P) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P x).2 hx
  rw [← h2] at h3
  have h4 : Ideal.map (algebraMap (𝓞 K) (Localization.AtPrime P)) p =
      Ideal.span {algebraMap (𝓞 K) (Localization.AtPrime P) π} := by
    rw [hp, Ideal.map_span, Set.image_singleton]
  rw [h4, Ideal.mem_span_singleton'] at h3
  obtain ⟨z, hz⟩ := h3
  obtain ⟨⟨y, t⟩, hyt⟩ := IsLocalization.surj P.primeCompl z
  refine ⟨t, y, t.2, ?_⟩
  apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  simp only at hyt
  rw [map_mul, map_mul, ← hz, ← hyt, ← IsScalarTower.algebraMap_apply]
  ring

private theorem valuation_le_uniformizer_div {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (u : HeightOneSpectrum (𝓞 E)) (hu : IsPlaceOver A u) (π : 𝓞 E)
    (h : ∀ x ∈ u.asIdeal, ∃ t y : 𝓞 E, t ∉ u.asIdeal ∧ t * x = π * y) (z : E)
    (hz : A.valuation (algebraMap E Ω z) < 1) :
    A.valuation (algebraMap E Ω z) ≤ A.valuation (algebraMap E Ω (π : E)) := by
  have h1 : ∀ s : 𝓞 E, s ∉ u.asIdeal → A.valuation (algebraMap E Ω (s : E)) = 1 := fun s hs =>
    le_antisymm (CompanionTheory.FamInh.val_int_le_one A s) (not_lt.1 ((hu s).not.2 hs))
  obtain ⟨n, d, e | e⟩ := u.exists_primeCompl_mul_eq_or_mul_eq z
  · have e' : z * ((d : 𝓞 E) : E) = (n : E) := e
    have h2 : A.valuation (algebraMap E Ω z) = A.valuation (algebraMap E Ω (n : E)) := by
      rw [← e', map_mul, map_mul, h1 d d.2, mul_one]
    obtain ⟨t, y, ht, e2⟩ := h n ((hu n).1 (h2 ▸ hz))
    have e3 : (t : E) * (n : E) = (π : E) * (y : E) := by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) e2
    have h3 := congrArg (fun a : E => A.valuation (algebraMap E Ω a)) e3
    simp only [map_mul] at h3
    rw [h1 t ht, one_mul] at h3
    rw [h2, h3]
    exact mul_le_of_le_one_right' (CompanionTheory.FamInh.val_int_le_one A y)
  · have e' : z * (n : E) = ((d : 𝓞 E) : E) := e
    have h2 := h1 d d.2
    rw [← e', map_mul, map_mul] at h2
    exact absurd h2 ((mul_le_of_le_one_right' (CompanionTheory.FamInh.val_int_le_one A n)).trans_lt hz).ne

private theorem valuation_le_uniformizer_inertia {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hv : IsPlaceOver A v) (π : 𝓞 K)
    (hπ : v.asIdeal = Ideal.span {π}) (x : Ω) (hx : ∀ s ∈ Ine (F := K) A, s x = x) (h1 : A.valuation x < 1) :
    A.valuation x ≤ A.valuation (algebraMap K Ω (π : K)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : IsGalois K Ω := {}
  let M : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)).toIntermediateField
  have hxM : x ∈ M := FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set Ω) rfl
  haveI : NumberField M := NumberField.of_module_finite K M
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  haveI : IsAlgClosure M Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨w, hw, hwv⟩ := CompanionTheory.FamInh.exists_place_between (L := M) hv
  let E : IntermediateField K M := IntermediateField.fixedField (w.asIdeal.inertia Gal(M/K))
  haveI : NumberField E := NumberField.of_module_finite K E
  have hxE : (⟨x, hxM⟩ : M) ∈ E := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := CompanionTheory.FamInh.exists_lift_ine hw hτ
    apply (algebraMap M Ω).injective
    exact (AlgEquiv.restrictNormal_commutes σ M _).trans (hx σ hσ)
  have hun : Algebra.IsUnramifiedAt (𝓞 K) (w.asIdeal.under (𝓞 E)) :=
    (GroundTheory.ProfCoh.isUnramifiedAt_under_iff_inertia (F := K) (E := E) (M := M) w.asIdeal).2
      fun σ hσ y => (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ hσ
  have hu : IsPlaceOver A (w.under (𝓞 E)) := fun y => by
    have := hw (algebraMap (𝓞 E) (𝓞 M) y)
    exact this
  haveI : (w.asIdeal.under (𝓞 E)).LiesOver v.asIdeal := inferInstance
  have := valuation_le_uniformizer_div A (w.under (𝓞 E)) hu (algebraMap (𝓞 K) (𝓞 E) π)
    (unramified_uniformizer_divides π v.asIdeal hπ (w.asIdeal.under (𝓞 E)) hun) ⟨_, hxE⟩ h1
  exact this

theorem UpperTheory.Kd.C7.inertia_invariant_valuation_uniformizer_bound :
    UpperTheory.Kd.C7.FixedIntegersIsUnitOfNotMemPrimeSpan := by
  intro l hl _ Ω _ _ _ A ⟨v, hv, hlv⟩ x hx
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpr : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have h0 : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
    have := (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm).2 h0
    simpa using this
  have hπ : v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    have hm : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal (by simpa using hpr.ne_zero)
    exact (hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hlv)).symm
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  by_cases h1 : A.valuation (x : Ω) < 1
  · exfalso
    have h2 := valuation_le_uniformizer_inertia A v hv _ hπ x x.2.2 h1
    have h3 : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [h3] at h2
    have h4 : (x : Ω) / l ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ h2 zero_le
    refine hx (Ideal.mem_span_singleton'.2 ⟨⟨(x : Ω) / l, h4, fun s hs => ?_⟩, Subtype.ext ?_⟩)
    · rw [map_div₀, x.2.2 s hs, map_natCast]
    · push_cast
      exact div_mul_cancel₀ _ hl0
  · have h2 : A.valuation (x : Ω) = 1 := le_antisymm ((A.valuation_le_one_iff _).2 x.2.1) (not_lt.1 h1)
    have h0 : (x : Ω) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      exact zero_ne_one h2
    have h4 : (x : Ω)⁻¹ ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀, h2, inv_one]
    refine IsUnit.of_mul_eq_one ⟨(x : Ω)⁻¹, h4, fun s hs => ?_⟩ (Subtype.ext ?_)
    · rw [map_inv₀, x.2.2 s hs]
    · exact mul_inv_cancel₀ h0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.IntShift
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem truncSub {R : Type} [CommRing R] (H : PowerSeries R) (g N : ℕ) (t : R) :
    ∃ y : R, ∑ n ∈ Finset.range N, (sb g H).coeff n * t ^ n =
      ∑ n ∈ Finset.range N, H.coeff n * ((1 + t) ^ g - 1) ^ n + t ^ N * y := by
  set P : Polynomial R := H.trunc N with hP
  set Q : Polynomial R := P.comp ((1 + Polynomial.X) ^ g - 1) with hQ
  have h1 : (PowerSeries.X : PowerSeries R) ^ N ∣ H - (P : PowerSeries R) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [hP, PowerSeries.coeff_trunc, hm]
  have hX : sb (R := R) g PowerSeries.X = (1 + PowerSeries.X) ^ g - 1 := by
    unfold sb; rw [PowerSeries.substAlgHom_X]
  have h2 : sb g (P : PowerSeries R) = (Q : PowerSeries R) := by
    rw [hQ]
    generalize P = S
    induction S using Polynomial.induction_on' with
    | add f h hf hh => simp only [Polynomial.coe_add, map_add (f := _), hf, hh, Polynomial.add_comp]
    | monomial n a =>
      have hC : sb g (PowerSeries.C a : PowerSeries R) = PowerSeries.C a := (sb (R := R) g).commutes a
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [hC, hX]
  have h3 : (PowerSeries.X : PowerSeries R) ^ N ∣ sb g H - (Q : PowerSeries R) := by
    obtain ⟨u, hu⟩ := h1
    rw [← h2, ← map_sub, hu, map_mul, map_pow, hX]
    refine Dvd.dvd.mul_right (pow_dvd_pow_of_dvd ?_ N) _
    rw [PowerSeries.X_dvd_iff]
    simp
  have h4 : (Polynomial.X : Polynomial R) ^ N ∣ (sb g H).trunc N - Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    have := PowerSeries.X_pow_dvd_iff.1 h3 m hm
    simpa [PowerSeries.coeff_trunc, hm] using this
  obtain ⟨v, hv⟩ := h4
  have hev : ∀ (F : PowerSeries R) (s : R), (F.trunc N).eval s = ∑ n ∈ Finset.range N, F.coeff n * s ^ n := by
    intro F s
    have := PowerSeries.eval₂_trunc_eq_sum_range s (RingHom.id R) N F
    simpa using this
  refine ⟨v.eval t, ?_⟩
  have h5 := congrArg (Polynomial.eval t) hv
  rw [Polynomial.eval_sub, hev, hQ, Polynomial.eval_comp, hP, hev] at h5
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
    Polynomial.eval_mul] at h5
  linear_combination h5

private theorem orth {K : Type} [Field K] (q : ℕ) (hq : 0 < q) (ξ : K) (hξ : IsPrimitiveRoot ξ q) (x j : ℕ) (hx : x < q) :
    ∑ m ∈ Finset.range q, ξ ^ (q - (m * x) % q) * (ξ ^ j) ^ m = if j % q = x then (q : K) else 0 := by
  have h0 : ξ ≠ 0 := hξ.ne_zero hq.ne'
  have hmod : ∀ a : ℕ, ξ ^ (a % q) = ξ ^ a := fun a => by
    conv_rhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hξ.pow_eq_one, one_pow, mul_one]
  have h1 : ∀ m : ℕ, ξ ^ (q - (m * x) % q) * (ξ ^ j) ^ m = (ξ ^ j / ξ ^ x) ^ m := by
    intro m
    rw [pow_sub₀ _ h0 (Nat.mod_lt _ hq).le, hξ.pow_eq_one, hmod, div_pow, ← pow_mul ξ x m, mul_comm x m]
    field_simp
  simp only [h1]
  split_ifs with h
  · have : ξ ^ j / ξ ^ x = 1 := by rw [← hmod j, h, div_self (pow_ne_zero _ h0)]
    simp [this]
  · have hne : ξ ^ j / ξ ^ x ≠ 1 := by
      intro e
      rw [div_eq_one_iff_eq (pow_ne_zero _ h0), ← hmod j] at e
      exact h (hξ.pow_inj (Nat.mod_lt _ hq) hx e)
    have : (ξ ^ j / ξ ^ x) ^ q = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm j, mul_comm x, pow_mul, pow_mul, hξ.pow_eq_one]; simp
    rw [geom_sum_eq hne, this]; simp

private def OO (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' ha := by simpa using ha

private theorem rootBd (l : ℕ) [Fact l.Prime] (r : ℕ) (z : OO l) (hz : z ^ l ^ r = 1) :
    ‖((z : Qbar l) - 1) ^ l ^ (3 * r)‖ ≤ ‖(l : Qbar l) ^ (2 * r)‖ := by
  have hp : l.Prime := Fact.out
  obtain ⟨y, hy⟩ := exists_add_pow_prime_pow_eq hp (z - 1) 1 r
  have h1 : ‖((z : Qbar l) - 1) ^ l ^ r‖ ≤ ‖(l : Qbar l)‖ := by
    have e : (z - 1) ^ l ^ r = -((l : OO l) * ((z - 1) * y)) := by
      rw [sub_add_cancel, hz, one_pow] at hy
      linear_combination -hy
    have e2 : ((z : Qbar l) - 1) ^ l ^ r = -((l : Qbar l) * (((z - 1) * y : OO l) : Qbar l)) := by
      have := congrArg (OO l).subtype e
      simpa using this
    rw [e2, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((z - 1) * y).2
  have hl : ‖(l : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  rw [show 3 * r = r + 2 * r by ring, pow_add, pow_mul, norm_pow, norm_pow (l : Qbar l)]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hl (Nat.lt_pow_self hp.one_lt).le)

private theorem tvalShift (l : ℕ) [Fact l.Prime] (H : PowerSeries (Qbar l)) (hH : ∀ n, ‖H.coeff n‖ ≤ 1) (g r : ℕ)
    (z : Qbar l) (hz : z ^ l ^ r = 1) :
    ‖tval (sb g H) (l ^ (3 * r)) z - tval H (l ^ (3 * r)) (z ^ g)‖ ≤ ‖(l : Qbar l) ^ (2 * r)‖ := by
  have hp : l.Prime := Fact.out
  have hz1 : ‖z‖ ≤ 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_pos hp.pos r).ne').1 this).le
  let z' : OO l := ⟨z, hz1⟩
  let H' : PowerSeries (OO l) := PowerSeries.mk fun n => ⟨H.coeff n, hH n⟩
  have hm : PowerSeries.map (OO l).subtype H' = H := by
    ext n; simp [H']
  have hs : PowerSeries.map (OO l).subtype (sb g H') = sb g H := by
    rw [← hm]
    unfold sb
    rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
    refine Eq.trans (PowerSeries.map_subst (hasSubst_pow (R := OO l) g) (h := (OO l).subtype) H') ?_
    congr 1
    change PowerSeries.map (OO l).subtype _ = _
    simp
  obtain ⟨y, hy⟩ := truncSub H' g (l ^ (3 * r)) (z' - 1)
  have h2 := congrArg (OO l).subtype hy
  have h3 : tval (sb g H) (l ^ (3 * r)) z - tval H (l ^ (3 * r)) (z ^ g) = (z - 1) ^ l ^ (3 * r) * (y : Qbar l) := by
    unfold tval
    rw [← hs, sub_eq_iff_eq_add']
    simpa [H', z'] using h2
  rw [h3, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) y.2).trans (rootBd l r z' (Subtype.ext hz))

private theorem tvalExp (l : ℕ) [Fact l.Prime] (H : PowerSeries (Qbar l)) (hH : ∀ n, ‖H.coeff n‖ ≤ 1) (N : ℕ) :
    ∃ (M : ℕ) (a : ℕ → Qbar l), (∀ i, ‖a i‖ ≤ 1) ∧ ∀ z, tval H N z = ∑ i ∈ Finset.range M, a i * z ^ i := by
  let S : Polynomial (OO l) := ∑ n ∈ Finset.range N, Polynomial.C (⟨H.coeff n, hH n⟩ : OO l) * (Polynomial.X - 1) ^ n
  refine ⟨S.natDegree + 1, fun i => (OO l).subtype (S.coeff i), fun i => (S.coeff i).2, fun z => ?_⟩
  rw [← Polynomial.eval₂_eq_sum_range]
  simp [S, tval, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow]

private theorem sumJ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (k r : ℕ) (ξ : Qbar l)
    (hξ : IsPrimitiveRoot ξ (l ^ r)) (M g : ℕ) (a : ℕ → Qbar l) :
    ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ k) *
      ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * ∑ i ∈ Finset.range M, a i * ((ξ ^ m) ^ g) ^ i =
    ∑ i ∈ Finset.range M, (l : Qbar l) ^ r * (a i *
      (φ (((g * i) % l ^ r : ℕ) : ZMod l) * ((((g * i) % l ^ r : ℕ) : Qbar l) ^ k))) := by
  have hp : l.Prime := Fact.out
  have hq : 0 < l ^ r := pow_pos hp.pos r
  have h1 : ∀ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ k) *
      ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * ∑ i ∈ Finset.range M, a i * ((ξ ^ m) ^ g) ^ i =
      ∑ i ∈ Finset.range M, if (g * i) % l ^ r = x then (l : Qbar l) ^ r * (a i * (φ (x : ZMod l) * ((x : Qbar l) ^ k))) else 0 := by
    intro x hx
    have hx' : x < l ^ r := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := orth (l ^ r) hq ξ hξ x (g * i) hx'
    have e : ∑ m ∈ Finset.range (l ^ r), φ (x : ZMod l) * ((x : Qbar l) ^ k) *
        (ξ ^ (l ^ r - (m * x) % l ^ r) * (a i * ((ξ ^ m) ^ g) ^ i)) = (a i * (φ (x : ZMod l) * ((x : Qbar l) ^ k))) *
        ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) * (ξ ^ (g * i)) ^ m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [e, h]
    split_ifs
    · push_cast; ring
    · simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have : l ∣ (g * i) % l ^ r := by
      by_contra hc
      exact h (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hq), hc⟩)
    rw [(ZMod.natCast_eq_zero_iff _ _).2 this, MulChar.map_zero]
    simp

private theorem modBd (l : ℕ) [Fact l.Prime] (k r g i : ℕ) :
    ‖((((g * i) % l ^ r : ℕ) : Qbar l) ^ k) - (g : Qbar l) ^ k * (((1 * i) % l ^ r : ℕ) : Qbar l) ^ k‖ ≤ ‖(l : Qbar l) ^ r‖ := by
  have h : g ^ k * ((1 * i) % l ^ r) ^ k ≡ ((g * i) % l ^ r) ^ k [MOD l ^ r] := by
    rw [← mul_pow, one_mul]
    exact (((Nat.mod_modEq i _).mul_left g).trans (Nat.mod_modEq _ _).symm).pow k
  obtain ⟨c, hc⟩ := h.dvd
  have := congrArg (Int.cast : ℤ → Qbar l) hc
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Nat.cast_mul, Int.cast_pow] at this
  rw [this, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)

theorem UpperTheory.Kd.C7.pIntShift :
    UpperTheory.Kd.C7.SIntShift := by
  intro l _ H hH g hg φ k r ξ hr hξ
  have hp : l.Prime := Fact.out
  have hq : 0 < l ^ r := pow_pos hp.pos r
  obtain ⟨M, a, ha, hM⟩ := tvalExp l H hH (l ^ (3 * r))
  have hξ1 : ‖ξ‖ ≤ 1 := by
    have := congrArg norm hξ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hq.ne').1 this).le
  have hA := sumJ l φ k r ξ hξ M g a
  have hB := sumJ l φ k r ξ hξ M 1 a
  simp only [← hM, pow_one] at hA hB
  have hn : ∀ x : ℕ, ‖(x : Qbar l) ^ k‖ ≤ 1 := fun x => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have h1 : ‖intg φ k (sb g H) r ξ - ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
      φ (x : ZMod l) * ((x : Qbar l) ^ k) * ∑ m ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (m * x) % l ^ r) *
        tval H (l ^ (3 * r)) ((ξ ^ m) ^ g)‖ ≤ ‖(l : Qbar l) ^ (2 * r)‖ := by
    unfold intg mass
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (φ.norm_le_one _) (norm_nonneg _) (hn x))).trans ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m _ => ?_
    rw [← mul_sub, norm_mul, norm_pow]
    refine (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hξ1)).trans ?_
    exact tvalShift l H hH g r _ (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow])
  have hc : ∀ j : ℕ, ((j % l ^ r : ℕ) : ZMod l) = (j : ZMod l) := fun j =>
    (ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.mod_modEq j _).of_dvd (dvd_pow_self l (by omega)))
  rw [hA] at h1
  have h2 : intg φ k H r ξ = _ := hB
  unfold Cg
  rw [h2, ← sub_add_sub_cancel]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  have e : (l : Qbar l) ^ r * (a i * (φ (((g * i) % l ^ r : ℕ) : ZMod l) * ((((g * i) % l ^ r : ℕ) : Qbar l) ^ k))) -
      φ (g : ZMod l) * (g : Qbar l) ^ k * ((l : Qbar l) ^ r * (a i *
      (φ (((1 * i) % l ^ r : ℕ) : ZMod l) * ((((1 * i) % l ^ r : ℕ) : Qbar l) ^ k)))) =
      (l : Qbar l) ^ r * ((a i * φ ((g * i : ℕ) : ZMod l)) *
        (((((g * i) % l ^ r : ℕ) : Qbar l) ^ k) - (g : Qbar l) ^ k * (((1 * i) % l ^ r : ℕ) : Qbar l) ^ k)) := by
    rw [hc, hc, one_mul i, Nat.cast_mul g i, map_mul]
    ring
  rw [e, two_mul, pow_add, norm_mul, norm_mul, norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (ha i) (norm_nonneg _) (φ.norm_le_one _))).trans (modBd l k r g i)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.IwOpsRedUn
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem iwOps_red_un {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) (r : ℕ) :
    red l r (un b hb (r + 1)) = un b hb r := by
  ext
  simp only [un, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, map_natCast]

private theorem iwOps_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {A : ValuationSubring Ω} {Z : Sy Ω l} (h : IwI c A Z) (b : ℕ) (hb : ¬ l ∣ b) : IwI c A (tr b hb Z) := by
  refine ⟨fun r s hs x => h.int r s hs _, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.coc r s hs t ht, mul_right_comm]
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.nrm r s hs]
    symm
    refine Finset.sum_equiv (Equiv.mulRight (un b hb (r + 1))) (fun y => ?_) (fun y _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    rw [map_mul, iwOps_red_un, mul_left_inj]

theorem UpperTheory.Kd.C7.pIwOps :
    UpperTheory.Kd.C7.SIwOps := by
  intro l _ _ Ω _ _ _ A _ c Z h b hb
  have h' := iwOps_tr h b hb
  refine ⟨h', fun r s hs x => ?_, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · exact c.O.sub_mem (h.int r s hs x) (c.O.mul_mem (natCast_mem c.O b) (h'.int r s hs x))
  · simp only [sharp]
    rw [h.coc r s hs t ht, h'.coc r s hs t ht]
    ring
  · simp only [sharp]
    rw [h.nrm r s hs, h'.nrm r s hs, Finset.sum_sub_distrib, Finset.mul_sum]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem ka_pw {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {z : Ω} (hz : z ^ N = 1) (a : ℕ) (k : ZMod N)
    (h : (a : ZMod N) = k) : z ^ k.val = z ^ a := by
  rw [← h, ZMod.val_natCast]
  exact (pow_eq_pow_mod a hz).symm

private theorem ka_down {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : ∀ m, ζ (m + 1) ^ l = ζ m) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← Nat.add_assoc, h, ih]

theorem UpperTheory.Kd.C7.pKumAlg :
    UpperTheory.Kd.C7.SKumAlg := by
  intro l hl _ Ω _ _ _ A _ ζ hζ m n _ s _
  have hne : ∀ r : ℕ, NeZero (l ^ r) := fun r => ⟨(pow_pos hl.out.pos r).ne'⟩
  have h1 : ∀ r, ζ r ^ l ^ r = 1 := fun r => (hζ r).1.pow_eq_one
  haveI := hne n
  refine ⟨?_, ?_, ?_⟩
  · rintro u u' k k' ⟨v, rfl, hv⟩ ⟨v', rfl, hv'⟩
    refine ⟨⟨v * v', mul_pow _ _ _, ?_⟩, ⟨v⁻¹, inv_pow _ _, ?_⟩, fun a => ⟨v ^ a, ?_, ?_⟩⟩
    · rw [map_mul, hv, hv', ka_pw (h1 n) (k.val + k'.val) (k + k') (by simp), pow_add]
      ring
    · have e : ζ n ^ (-k).val * ζ n ^ k.val = 1 := by
        rw [← pow_add, ← ka_pw (h1 n) ((-k).val + k.val) 0 (by simp), ZMod.val_zero, pow_zero]
      rw [map_inv₀, hv, mul_inv, eq_inv_of_mul_eq_one_left e]
    · rw [← pow_mul, ← pow_mul, mul_comm]
    · rw [map_pow, hv, ka_pw (h1 n) (k.val * a) (a * k) (by simp [mul_comm]), mul_pow, pow_mul]
  · rintro u k n' hn' - ⟨v, rfl, hv⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn'
    haveI := hne n'
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm], ?_⟩
    rw [map_pow, hv, ka_pw (h1 n') k.val _ rfl, mul_pow, ← pow_mul, mul_comm k.val, pow_mul,
      ka_down (fun r => (hζ r).2)]
  · rintro u k t ⟨v, hu, hv⟩
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
    have ht : t (ζ n) = ζ n ^ ((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω t) (ζ n) (h1 n)
    refine ⟨t v, ?_, ?_⟩
    · rw [← map_pow, hu, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    · rw [← AlgEquiv.mul_apply, inv_mul_cancel_right, AlgEquiv.mul_apply, hv, map_mul, map_pow, ht, ← pow_mul,
        ka_pw (h1 n) (((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val * k.val) _ (by simp)]
end

