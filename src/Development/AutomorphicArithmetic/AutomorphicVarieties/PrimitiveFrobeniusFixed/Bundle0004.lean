module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IneRad
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem ordv_prime (r : ℕ) (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal)
    (a : ℚˣ) (ha : (a : ℚ) = r) : UpperTheory.V.Kum.ordv v a = 1 := by
  have hpr : Prime (r : 𝓞 ℚ) := by
    have h1 : Prime ((Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) (r : 𝓞 ℚ)) := by
      rw [map_natCast]
      exact Nat.prime_iff_prime_int.mp hr
    exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toMulEquiv).mp h1
  have hne : (r : 𝓞 ℚ) ≠ 0 := hpr.ne_zero
  have hspan : v.asIdeal = Ideal.span {(r : 𝓞 ℚ)} := by
    have hP : (Ideal.span {(r : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hpr
    have hbot : Ideal.span {(r : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hne
    have hmax := hP.isMaximal hbot
    have hle : Ideal.span {(r : 𝓞 ℚ)} ≤ v.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hv
    exact (hmax.eq_of_le v.isPrime.ne_top hle).symm
  have hint : v.intValuation (r : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := v.intValuation_singleton hne hspan
  have hval : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ha, ← hint]
    have : ((r : ℚ)) = algebraMap (𝓞 ℚ) ℚ (r : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : v.valuationOfNeZero a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hval]
    rfl
  unfold UpperTheory.V.Kum.ordv
  rw [h2]
  simp

theorem UpperTheory.V.ML.ineRad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (r M : ℕ), r.Prime → M.Coprime r → ∀ A : ValuationSubring Ω, Over A r → ∀ ρ ζ : Ω, ρ ^ M = (r : Ω) → ζ ^ M = 1 → ∃ t ∈ Ine (F := ℚ) A, t ρ = ζ * ρ := by
  intro Ω _ _ _ r M hr hM A hA ρ ζ hρ hζ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp [Nat.coprime_zero_left] at hM
    exact hr.ne_one hM
  haveI : NeZero M := ⟨hM0⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hnot : ¬ Over A M := fun h => pb.2.2.2.1 A M r hM h hA
  have hfix : Ine (F := ℚ) A ≤ fixMu ℚ Ω M := pb.2.2.2.2.1 A M hnot
  have hroot : ∀ g : G ℚ Ω, (g ρ / ρ) ^ M = 1 := by
    intro g
    rw [div_pow, ← map_pow, hρ, map_natCast, div_self hr0]
  have hgne : ∀ g : G ℚ Ω, g ρ / ρ ≠ 0 := fun g =>
    div_ne_zero (by simpa using hρ0) hρ0
  let χ : ↥(Ine (F := ℚ) A) →* Ωˣ :=
    { toFun := fun g => Units.mk0 ((g : G ℚ Ω) ρ / ρ) (hgne g)
      map_one' := by
        ext
        simp [div_self hρ0]
      map_mul' := by
        intro g h
        ext
        have hc : (g : G ℚ Ω) ((h : G ℚ Ω) ρ / ρ) = (h : G ℚ Ω) ρ / ρ :=
          hfix g.2 _ (hroot h)
        have hh : (h : G ℚ Ω) ρ = ((h : G ℚ Ω) ρ / ρ) * ρ := by
          field_simp
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, AlgEquiv.mul_apply]
        rw [hh, map_mul, hc]
        field_simp }
  have hχ : ∀ g, ((χ g : Ωˣ) : Ω) = (g : G ℚ Ω) ρ / ρ := fun g => rfl
  have hle : χ.range ≤ rootsOfUnity M Ω := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, hχ, hroot, Units.val_one]
  haveI : Finite χ.range :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hd0 : 0 < Nat.card χ.range := Nat.card_pos
  have hfixd : ∀ g ∈ Ine (F := ℚ) A, g (ρ ^ Nat.card χ.range) = ρ ^ Nat.card χ.range := by
    intro g hg
    have h1 := congrArg (fun x : χ.range => ((x : Ωˣ) : Ω))
      (pow_card_eq_one' (x := (⟨χ ⟨g, hg⟩, ⟨_, rfl⟩⟩ : χ.range)))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hχ, OneMemClass.coe_one,
      Units.val_one] at h1
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hρ0)] at h1
    rw [map_pow]
    exact h1
  obtain ⟨v, hvA, -, hvr⟩ := pb.2.2.2.2.2.2.2.2.1 A r hr hA
  let a : ℚˣ := Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)
  have ha1 : UpperTheory.V.Kum.ordv v a = 1 := ordv_prime r hr v hvr a rfl
  have hpow : UpperTheory.V.Kum.ordv v (a ^ Nat.card χ.range) = Nat.card χ.range := by
    unfold UpperTheory.V.Kum.ordv at ha1 ⊢
    rw [map_pow, toAdd_pow, nsmul_eq_mul, ← mul_neg, ha1, mul_one]
  have hdv := UpperTheory.V.Kum.dvdOfIne ℚ Ω M A v (ρ ^ Nat.card χ.range) (a ^ Nat.card χ.range) hvA
    (by
      rw [← pow_mul, mul_comm, pow_mul, hρ]
      simp [a]) hfixd
  rw [hpow] at hdv
  have hMd : M ∣ Nat.card χ.range := by exact_mod_cast hdv
  have hMle : M ≤ Nat.card χ.range := Nat.le_of_dvd hd0 hMd
  have hcard : Nat.card χ.range ≤ Nat.card (rootsOfUnity M Ω) := Subgroup.card_le_of_le hle
  have heq : χ.range = rootsOfUnity M Ω :=
    Subgroup.eq_of_le_of_card_ge hle (le_trans (card_rootsOfUnity Ω M) hMle)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hζ
    exact zero_ne_one hζ
  have hu : Units.mk0 ζ hζ0 ∈ rootsOfUnity M Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [hζ]
  rw [← heq] at hu
  obtain ⟨g, hg⟩ := hu
  refine ⟨g, g.2, ?_⟩
  have h2 := congrArg Units.val hg
  rw [hχ, Units.val_mk0, div_eq_iff hρ0] at h2
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolInit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolInit :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F r a : ℕ) [NeZero M] [NeZero F] (hM : M ∣ F), r.Prime → r.Coprime F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω F, h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F 1 ζ δ a y κ → ∀ A₀ : ValuationSubring Ω, Over A₀ r → ∀ k : (ZMod F)ˣ → ℤ, HasOrd F r A₀ (opP δ a y) k →
    ∀ ρ : Ω, ρ ^ M = (r : Ω) → ∀ t ∈ Ine (F := ℚ) A₀, t ρ = ζ * ρ → ∀ (c : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F c σ →
    κ (σ⁻¹ * t * σ) * ZMod.castHom hM (ZMod M) (c : ZMod F) = (k c : ZMod M) := by
  intro Ω _ _ _ M F r a _ _ hM hr hrF ζ hζ δ hδ y hy0 hyfix κ hκ A₀ hA₀ k hk ρ hρ t ht htρ c σ hσ
  have pb := placeBasic Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hM0 : M ≠ 0 := NeZero.ne M
  have hr0 : (r : Ω) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hρ
    exact hr0 hρ.symm
  have hFr : F.Coprime r := hrF.symm
  have hMr : M.Coprime r := (hrF.coprime_dvd_right hM).symm
  have hnotF : ¬ Over A₀ F := fun h => pb.2.2.2.1 A₀ F r hFr h hA₀
  have hnotM : ¬ Over A₀ M := fun h => pb.2.2.2.1 A₀ M r hMr h hA₀
  have hIneF : Ine (F := ℚ) A₀ ≤ fixMu ℚ Ω F := pb.2.2.2.2.1 A₀ F hnotF
  have hconj : ∀ (h τ : G ℚ Ω), h ∈ fixMu ℚ Ω F → τ⁻¹ * h * τ ∈ fixMu ℚ Ω F := by
    intro h τ hh x hx
    have h1 : h (τ x) = τ x := hh _ (by rw [← map_pow, hx, map_one])
    simp [AlgEquiv.mul_apply, h1]
  have htF : t ∈ fixMu ℚ Ω F := hIneF ht
  have hg : σ⁻¹ * t * σ ∈ fixMu ℚ Ω F := hconj t σ htF
  obtain ⟨Y, hYM, hK⟩ := hκ
  obtain ⟨z, -, hzM, hζκ⟩ := hK _ hg
  rw [hyfix _ hg, div_self hy0] at hzM
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hzM
    exact zero_ne_one hzM
  have hPz : opP δ a z = 1 := by
    unfold opP
    rw [hδ z hzM, div_self (pow_ne_zero _ hz0)]
  rw [hPz, div_one] at hζκ
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0] at hYM
    exact hy0 hYM.symm
  set w := opP δ a Y with hw
  have hw0 : w ≠ 0 := by
    rw [hw]
    unfold opP
    exact div_ne_zero (by simpa using hY0) (pow_ne_zero _ hY0)
  have hζF : ζ ^ F = 1 := (hζ.pow_eq_one_iff_dvd F).mpr hM
  have hσζ : σ ζ = ζ ^ (c : ZMod F).val := hσ ζ hζF
  have h1 : ζ ^ ((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val) = t (σ w) / σ w := by
    rw [pow_mul, ← hσζ, ← map_pow, hζκ, map_div₀]
    congr 1
    simp [AlgEquiv.mul_apply]
  set W := σ w with hW
  have hW0 : W ≠ 0 := by simpa [hW] using hw0
  have hWM : W ^ M = σ (opP δ a y) := by
    rw [hW, ← map_pow, hw]
    unfold opP
    rw [div_pow, ← map_pow, ← pow_mul, mul_comm a M, pow_mul, hYM]
  have hPfix : ∀ h ∈ fixMu ℚ Ω F, h (opP δ a y) = opP δ a y := by
    intro h hh
    unfold opP
    rw [map_div₀, map_pow, hyfix h hh]
    congr 1
    have h2 := congrArg δ (hyfix _ (hconj h δ hh))
    simpa [AlgEquiv.mul_apply] using h2
  have hXt : t (σ (opP δ a y)) = σ (opP δ a y) := by
    have h2 := congrArg σ (hPfix _ hg)
    simpa [AlgEquiv.mul_apply] using h2
  set e := W / ρ ^ (k c) with he
  have heM : e ^ M = σ (opP δ a y) / (r : Ω) ^ (k c) := by
    rw [he, div_pow, hWM, ← zpow_natCast (ρ ^ k c) M, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ]
  have hvr0 : A₀.valuation (r : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have hveM : A₀.valuation e ^ M = 1 := by
    rw [← map_pow, heM, map_div₀, map_zpow₀, hk c σ hσ, div_self (zpow_ne_zero _ hvr0)]
  have hve : A₀.valuation e = 1 := by
    rcases lt_trichotomy (A₀.valuation e) 1 with hlt | heq | hgt
    · exact absurd hveM (ne_of_lt (pow_lt_one₀ zero_le' hlt hM0))
    · exact heq
    · exact absurd hveM (ne_of_gt (one_lt_pow₀ hgt hM0))
  have he0 : e ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hve
    exact zero_ne_one hve
  have hteM : (t e / e) ^ M = 1 := by
    have hX0 : σ (opP δ a y) / (r : Ω) ^ (k c) ≠ 0 := by
      rw [← heM]
      exact pow_ne_zero M he0
    rw [div_pow, ← map_pow, heM, map_div₀, hXt, map_zpow₀, map_natCast]
    exact div_self hX0
  have hin : A₀.valuation (t e - e) < 1 := ht.2 e hve.le
  have hte1 : A₀.valuation (t e / e - 1) < 1 := by
    rw [div_sub_one he0, map_div₀, hve, div_one]
    exact hin
  have hte : t e = e := by
    have h3 := pb.2.2.2.2.2.1 A₀ M (t e / e) hnotM hteM hte1
    rwa [div_eq_one_iff_eq he0] at h3
  have hWe : W = e * ρ ^ (k c) := by
    rw [he, div_mul_cancel₀ _ (zpow_ne_zero _ hρ0)]
  have htW : t W / W = ζ ^ (k c) := by
    rw [div_eq_iff hW0]
    conv_lhs => rw [hWe]
    rw [map_mul, map_zpow₀, hte, htρ, mul_zpow, hWe]
    ring
  rw [htW, ← zpow_natCast] at h1
  have hdvd : (M : ℤ) ∣ (k c) - (((c : ZMod F).val * (κ (σ⁻¹ * t * σ)).val : ℕ) : ℤ) := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hM0), ← h1, div_self (zpow_ne_zero _ (hζ.ne_zero hM0))]
  have h4 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M).mpr hdvd
  push_cast at h4
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← h4, ZMod.natCast_zmod_val, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimRam
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨v, hv⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r)
    (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA v
  refine ⟨σ, hσ, ?_⟩
  apply (Chr.clsFacts ℚ Ω N).2.2.1
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨?_, ?_⟩
  · intro ζ hζ
    have hcop : (N / r ^ N.factorization r).Coprime r :=
      (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
    have hfix := (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA (N / r ^ N.factorization r) hcop ζ hζ).2 σ hσ
    rw [MonoidHom.mem_ker.mp hu, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ,
      pow_one]
    exact hfix
  · rw [← hv, ← hσv]
    rfl

private theorem primRam_l (l : ℕ) [Fact l.Prime] (c : HV.Coef l) : ¬ IsUnit (l : c.O) := by
  intro hu
  haveI := c.fin
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hker : RingHom.ker (algebraMap ℤ_[l] c.O) ≤ IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (IsLocalRing.maximalIdeal ℤ_[l]) hker
  have hl : ((l : ℤ_[l])) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [← hQc, Ideal.mem_comap, map_natCast] at hl
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hl hu)

private theorem primRam_unit (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (n : ℕ) (hn : ¬ l ∣ n) (x : c.O) (hx : x ^ n = 1)
    (h1 : x ≠ 1) : IsUnit (x - 1) := by
  haveI := c.dvr
  by_contra hne
  have hm : x - 1 ∈ IsLocalRing.maximalIdeal c.O := (IsLocalRing.mem_maximalIdeal _).2 hne
  have hsum : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have h := mul_geom_sum x n
    rw [hx, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)
  have hdiff : ∑ i ∈ Finset.range n, (x ^ i - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow x 1 i
    rw [one_pow] at hy
    rw [hy]
    exact Ideal.mul_mem_right _ _ hm
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    zero_sub, neg_mem_iff] at hdiff
  have hlm : (l : c.O) ∈ IsLocalRing.maximalIdeal c.O :=
    (IsLocalRing.mem_maximalIdeal _).2 (primRam_l l c)
  have hcop : IsCoprime ((l : ℤ)) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hn)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom c.O)
  simp only [eq_intCast, Int.cast_natCast] at hab
  have h1m : (1 : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hdiff)
  exact (IsLocalRing.maximalIdeal.isMaximal c.O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)

private theorem exists_prime_dvd_over_of_over_mul_iff (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (hmul : ∀ m n : ℕ, Over A (m * n) ↔ Over A m ∨ Over A n) (n : ℕ) (hn : n ≠ 0) (h : Over A n) :
    ∃ r, r.Prime ∧ r ∣ n ∧ Over A r := by
  refine Nat.recOnMul (motive := fun n => n ≠ 0 → Over A n → ∃ r, r.Prime ∧ r ∣ n ∧ Over A r)
    ?_ ?_ ?_ ?_ n hn h
  · intro h0
    exact absurd rfl h0
  · intro _ h1
    simp [Over] at h1
  · intro p hp _ hpA
    exact ⟨p, hp, dvd_rfl, hpA⟩
  · intro a b iha ihb hab hAab
    rcases (hmul a b).1 hAab with ha | hb
    · obtain ⟨r, hr, hra, hrA⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨r, hr, hra.mul_right b, hrA⟩
    · obtain ⟨r, hr, hrb, hrA⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨r, hr, hrb.mul_left a, hrA⟩

theorem UpperTheory.V.ML.primRam :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f), ψ.IsPrimitive → ¬ l ∣ orderOf ψ →
    (∀ A : ValuationSubring Ω, Over A f → ∃ g ∈ Ine (F := ℚ) A, IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1)) ∧
    (∀ A : ValuationSubring Ω, ¬ Over A f → ∀ g ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ g = 1) ∧ ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 → IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
  intro Ω _ inst _ l _ c f _ ψ hprim hord
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hpb := placeBasic Ω
  have hC : ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 →
      IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
    intro g hg
    apply primRam_unit l c (orderOf ψ) hord
    · show ((MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) : c.Oˣ) : c.O) ^ orderOf ψ = 1
      rw [MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
        MulChar.one_apply_coe]
    · intro h
      exact hg (Units.val_eq_one.mp h)
  refine ⟨?_, ?_, hC⟩
  · intro A hA
    obtain ⟨r, hr, hrf, hAr⟩ := exists_prime_dvd_over_of_over_mul_iff Ω A (hpb.2.2.1 A) f (NeZero.ne f) hA
    have hsub : ¬ (ZMod.unitsMap (Nat.ordCompl_dvd f r)).ker ≤ (MulChar.toUnitHom ψ).ker := by
      intro hle
      have hft := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ψ)
        (Nat.ordCompl_dvd f r)).2 hle
      have hdvd := DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ hft
      rw [(DirichletCharacter.isPrimitive_def ψ).1 hprim] at hdvd
      have hpos : 0 < f / r ^ f.factorization r := Nat.ordCompl_pos r (NeZero.ne f)
      have hlt : f / r ^ f.factorization r < f :=
        Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne f))
          (Nat.one_lt_pow (hr.factorization_pos_of_dvd (NeZero.ne f) hrf).ne' hr.one_lt)
      exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hlt)
    obtain ⟨u, hu, hψu⟩ := SetLike.not_le_iff_exists.mp hsub
    obtain ⟨σ, hσ, hσu⟩ := primRam_lift Ω f r hr A hAr u hu
    refine ⟨σ, hσ, hC σ ?_⟩
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f σ) ≠ 1
    rw [hσu]
    exact fun h => hψu (MonoidHom.mem_ker.mpr h)
  · intro A hA g hg
    have hk := (Chr.clsFacts ℚ Ω f).2.2.2.2 A hA hg
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one]
end

