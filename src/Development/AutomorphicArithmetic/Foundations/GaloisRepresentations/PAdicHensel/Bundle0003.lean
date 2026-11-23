module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
public import GroundTheory.GlobalFields.LocalAtPlace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocUnit
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem field_rep (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (d s : k) (hd : d ≠ 0) :
    ∃ a b : k, a ^ 2 - d * b ^ 2 = s := by
  classical
  haveI := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C s) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) s)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd))
    (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

private theorem two_ne_zero_residueField_of_isUnit_two (R : Type) [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) :
    (2 : IsLocalRing.ResidueField R) ≠ 0 := by
  have := (IsLocalRing.residue_ne_zero_iff_isUnit (2 : R)).2 h2
  rwa [map_ofNat] at this

private theorem local_rep (R : Type) [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)]
    (hens : ∀ (f : Polynomial R) (a₀ : R), f.Monic → ¬ IsUnit (f.eval a₀) →
      IsUnit (f.derivative.eval a₀) → ∃ a, f.eval a = 0)
    (h2 : IsUnit (2 : R)) (D u : R) (hD : IsUnit D) (hu : IsUnit u) :
    ∃ X Y : R, X ^ 2 - D * Y ^ 2 = u := by
  classical
  have h2k : (2 : IsLocalRing.ResidueField R) ≠ 0 := two_ne_zero_residueField_of_isUnit_two R h2
  have hDk : IsLocalRing.residue R D ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit D).2 hD
  have huk : IsLocalRing.residue R u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit u).2 hu
  obtain ⟨a', b', hab'⟩ := field_rep _ h2k (IsLocalRing.residue R D) (IsLocalRing.residue R u) hDk
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a'
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b'
  have hres : IsLocalRing.residue R (a ^ 2 - D * b ^ 2 - u) = 0 := by
    simp only [map_sub, map_mul, map_pow, hab', sub_self]
  have hnu : ¬ IsUnit (a ^ 2 - D * b ^ 2 - u) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, not_not]
    exact hres
  by_cases ha : IsUnit a
  · obtain ⟨X, hX⟩ := hens (Polynomial.X ^ 2 - Polynomial.C (u + D * b ^ 2)) a
      (Polynomial.monic_X_pow_sub_C _ (by norm_num))
      (by
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        intro hh
        apply hnu
        convert hh using 1
        ring)
      (by
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        convert h2.mul ha using 1
        norm_num)
    refine ⟨X, b, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hX
    linear_combination hX
  · have hb : IsUnit b := by
      by_contra hb
      apply huk
      have ha0 : IsLocalRing.residue R a = 0 :=
        (IsLocalRing.residue_eq_zero_iff a).2 ((IsLocalRing.mem_maximalIdeal a).2 ha)
      have hb0 : IsLocalRing.residue R b = 0 :=
        (IsLocalRing.residue_eq_zero_iff b).2 ((IsLocalRing.mem_maximalIdeal b).2 hb)
      rw [← hab', ha0, hb0]
      ring
    have hDi : D * ↑hD.unit⁻¹ = 1 := hD.mul_val_inv
    obtain ⟨Y, hY⟩ := hens (Polynomial.X ^ 2 - Polynomial.C (↑hD.unit⁻¹ * (a ^ 2 - u))) b
      (Polynomial.monic_X_pow_sub_C _ (by norm_num))
      (by
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        intro hh
        apply hnu
        have e : a ^ 2 - D * b ^ 2 - u = -D * (b ^ 2 - ↑hD.unit⁻¹ * (a ^ 2 - u)) := by
          linear_combination (-(a ^ 2 - u)) * hDi
        rw [e]
        exact hD.neg.mul hh)
      (by
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        convert h2.mul hb using 1
        norm_num)
    refine ⟨a, Y, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hY
    linear_combination (-D) * hY + (-(a ^ 2 - u)) * hDi

theorem UpperTheory.Gal.G1.pLocUnit :
    HenselV → LocUnit := by
  intro hH F _ _ v tr nm hv u hu
  have hunit : IsUnit (((2 * (tr ^ 2 - 4 * nm) : ℤ) : HeightOneSpectrum.adicCompletionIntegers F v)) := by
    have h := (GroundTheory.Global.algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (K := F) v
      ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F)).not.2 hv
    rw [map_intCast] at h
    by_contra hc
    exact h ((IsLocalRing.mem_maximalIdeal _).2 hc)
  push_cast at hunit
  have h2 : IsUnit (2 : HeightOneSpectrum.adicCompletionIntegers F v) := isUnit_of_mul_isUnit_left hunit
  have hΔ := isUnit_of_mul_isUnit_right hunit
  have h4u : IsUnit (4 * u) := by
    have h4 := h2.mul h2
    norm_num at h4
    exact h4.mul hu
  obtain ⟨X, Y, hXY⟩ := local_rep _ (fun f a₀ hf hn hd => (hH F v f a₀ hf hn hd).imp fun a ha => ha.1)
    h2 _ (4 * u) hΔ h4u
  have hi : (2 : HeightOneSpectrum.adicCompletionIntegers F v) * ↑h2.unit⁻¹ = 1 := h2.mul_val_inv
  refine ⟨↑h2.unit⁻¹ * (X - tr * Y), Y, ?_⟩
  have ha : 2 * (↑h2.unit⁻¹ * (X - tr * Y)) = X - tr * Y := by rw [← mul_assoc, hi, one_mul]
  apply (h2.mul h2).mul_left_cancel
  unfold qf
  linear_combination (2 * (↑h2.unit⁻¹ * (X - tr * Y)) + X - tr * Y + 2 * tr * Y) * ha + hXY
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PNormTwo
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pNormTwo :
    AdFour → NormTwo := by
  intro hA E _ _ _ A
  let F : Type := maximalRealSubfield E
  have hcF : (A.c : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff E, ← A.bar_eq, A.c_real]
  let cf : F := ⟨(A.c : E), hcF⟩
  have hcfE : algebraMap F E cf = (A.c : E) := rfl
  have hcint : IsIntegral ℤ cf := by
    have h : IsIntegral ℤ (algebraMap F E cf) := by rw [hcfE]; exact A.c.2
    exact (isIntegral_algebraMap_iff ).1 h
  let c0 : 𝓞 F := ⟨cf, hcint⟩
  have hc0 : ((c0 : 𝓞 F) : F) = cf := rfl
  have hc0ne : c0 ≠ 0 := by
    intro h
    have h1 : ((c0 : 𝓞 F) : F) = 0 := by rw [h]; simp
    have h2 : (A.c : E) = 0 := by
      rw [← hcfE, ← hc0, h1, map_zero]
    exact A.c_ne h2
  obtain ⟨a, ha1, ha2⟩ := hA F A.tr A.nm A.disc_neg.ne c0 hc0ne
  let ι := GlobalTheory.AdeleBaseChange.adMap F E
  let ω' : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.ω : E)
  let ωb : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) ((A.bar A.ω : 𝓞 E) : E)
  have hfix : ∀ x : F, (IsCMField.complexConj E).toRingEquiv (algebraMap F E x) = algebraMap F E x := fun x =>
    (IsCMField.complexConj_eq_self_iff E _).2 x.2
  have hcι : ∀ z, cF E (ι z) = ι z := fun z => GlobalTheory.DefU.ClassFin.conjFin_adMap _ hfix z
  have hcω : cF E ω' = ωb := by
    show conjFin _ (algebraMap E _ _) = _
    rw [conjFin_algebraMap]
    show algebraMap E _ (IsCMField.complexConj E (A.ω : E)) = _
    rw [← A.bar_eq]
  have hsum : ω' + ωb = (A.tr : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) + ((A.bar A.ω : 𝓞 E) : E) = (A.tr : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.tr_eq
      simpa using this
    show algebraMap E _ _ + algebraMap E _ _ = _
    rw [← map_add (f := _), h, map_intCast]
  have hprod : ω' * ωb = (A.nm : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) * ((A.bar A.ω : 𝓞 E) : E) = (A.nm : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.nm_eq
      simpa using this
    show algebraMap E _ _ * algebraMap E _ _ = _
    rw [← map_mul, h, map_intCast]
  have hnorm : ∀ s t, (ι s + ι t * ω') * cF E (ι s + ι t * ω') = ι (qf A.tr A.nm s t) := by
    intro s t
    rw [map_add (f := _), map_mul, hcι, hcι, hcω]
    simp only [qf, map_add (f := _), map_mul, map_pow, map_intCast]
    linear_combination (ι s * ι t) * hsum + (ι t) ^ 2 * hprod
  have hcalg : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) =
      ι (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c0 : 𝓞 F) : F)) := by
    rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap]
    rfl
  refine ⟨ι (a 0) + ι (a 1) * ω', ι (a 2) + ι (a 3) * ω', ?_, ?_⟩
  · rw [hnorm, hnorm, hcalg, ← map_add (f := _), ← map_mul, ha1, map_one]
  · intro w q hq hG hqw
    let v : HeightOneSpectrum (𝓞 F) := w.under (𝓞 F)
    have hqv : (q : 𝓞 F) ∈ v.asIdeal := by
      show algebraMap (𝓞 F) (𝓞 E) (q : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hqw
    have hcv : c0 ∉ v.asIdeal := by
      intro hc
      have hcw : A.c ∈ w.asIdeal := hc
      obtain ⟨e, hcop, -, c', hc'⟩ := hG.2
      have hew : (e : 𝓞 E) ∈ w.asIdeal := hc' ▸ w.asIdeal.mul_mem_right c' hcw
      have hb := Nat.isCoprime_iff_coprime.2 hcop
      obtain ⟨u, u', huu⟩ := hb
      have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
        have h2 : (u : 𝓞 E) * (e : 𝓞 E) + (u' : 𝓞 E) * (q : 𝓞 E) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huu
        rw [← h2]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hew) (w.asIdeal.mul_mem_left _ hqw)
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hai : ∀ i, a i v ∈ v.adicCompletionIntegers F :=
      ha2 v q hq hqv hG.1.1 hG.1.2 hcv
    have hιi : ∀ i, pLoc E w (ι (a i)) ∈ w.adicCompletionIntegers E := fun i =>
      GlobalTheory.AdeleBaseChange.locMap_int w _ (hai i)
    have hωi : pLoc E w ω' ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w A.ω
    have hωbi : pLoc E w ωb ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w (A.bar A.ω)
    have hform : ∀ i j, pLoc E w (ι (a i) + ι (a j) * ω') ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add (f := _), map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωi)
    have hformc : ∀ i j, pLoc E w (cF E (ι (a i) + ι (a j) * ω')) ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add (f := _), map_mul, hcι, hcι, hcω, map_add (f := _), map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωbi)
    exact ⟨hform 0 1, hform 2 3, hformc 0 1, hformc 2 3⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicSqFin
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma pow_neg_three_lt_two_norm_sq (q : ℕ) [hq : Fact q.Prime] :
    (q : ℝ) ^ (-3 : ℤ) < ‖(2 : ℤ_[q])‖ ^ 2 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  by_cases h : q = 2
  · subst h
    have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ) ^ (-1 : ℤ) := by
      have := PadicInt.norm_p_pow (p := 2) 1
      simpa using this
    rw [h2]
    norm_num
  · have h1 : ‖(2 : ℤ_[q])‖ = 1 := by
      apply le_antisymm (PadicInt.norm_le_one _)
      by_contra hlt
      push_neg at hlt
      have hd := (PadicInt.norm_int_lt_one_iff_dvd (p := q) 2).1 (by exact_mod_cast hlt)
      have hd' : q ∣ 2 := by exact_mod_cast hd
      exact h ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 hd')
    rw [h1, one_pow, _root_.zpow_neg]
    have hlt : (1 : ℝ) < (q : ℝ) ^ (3 : ℤ) := one_lt_zpow₀ (by linarith) (by norm_num)
    exact inv_lt_one_of_one_lt₀ hlt

private lemma sq_of_close (q : ℕ) [hq : Fact q.Prime] (z : ℤ_[q])
    (hz : ‖(1 : ℤ_[q]) - z‖ < ‖(2 : ℤ_[q])‖ ^ 2) : ∃ x : ℤ_[q], x ^ 2 = z := by
  have hn : ‖Polynomial.aeval (1 : ℤ_[q]) (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q])‖ <
      ‖Polynomial.aeval (1 : ℤ_[q])
        (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q]))‖ ^ 2 := by
    simpa [Polynomial.derivative_X_pow, one_add_one_eq_two] using hz
  obtain ⟨x, hx, -⟩ := hensels_lemma hn
  refine ⟨x, ?_⟩
  simpa [sub_eq_zero] using hx

theorem UpperTheory.Gal.G1.pPadicSqFin :
    PadicSqFin := by
  intro q hq
  haveI : NeZero (q ^ 3) := ⟨pow_ne_zero 3 hq.out.ne_zero⟩
  refine ⟨Fintype.card (ZMod (q ^ 3)), fun u => Fintype.equivFin (ZMod (q ^ 3))
    (if h : ‖u‖ ≤ 1 then PadicInt.toZModPow 3 ⟨u, h⟩ else 0), ?_⟩
  intro u u' hu hu' hk
  simp only [dif_pos hu.le, dif_pos hu'.le, (Fintype.equivFin _).injective.eq_iff] at hk
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[q], (a : ℚ_[q]) = u ∧ PadicInt.toZModPow 3 a =
      PadicInt.toZModPow 3 ⟨u, hu.le⟩ := ⟨⟨u, hu.le⟩, rfl, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ_[q], (b : ℚ_[q]) = u' ∧ PadicInt.toZModPow 3 b =
      PadicInt.toZModPow 3 ⟨u', hu'.le⟩ := ⟨⟨u', hu'.le⟩, rfl, rfl⟩
  have hmem : b - a ∈ RingHom.ker (PadicInt.toZModPow (p := q) 3) := by
    rw [RingHom.sub_mem_ker_iff, ha.2, hb.2]
    exact hk.symm
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hd : ‖u' - u‖ ≤ (q : ℝ) ^ (-3 : ℤ) := by
    have h1 : ‖b - a‖ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
      rw [hc, norm_mul, PadicInt.norm_p_pow]
      have hc1 := PadicInt.norm_le_one c
      have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by positivity
      calc _ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) * 1 := mul_le_mul_of_nonneg_left hc1 hpos
        _ = _ := mul_one _
    rw [PadicInt.norm_def, PadicInt.coe_sub, ha.1, hb.1] at h1
    simpa using h1
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hz : ‖u' / u‖ ≤ 1 := by
    rw [norm_div, hu, hu']
    simp
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[q], (w : ℚ_[q]) = u' / u := ⟨⟨u' / u, hz⟩, rfl⟩
  obtain ⟨x, hx⟩ := sq_of_close q w (by
    have e : ‖(1 : ℤ_[q]) - w‖ = ‖u' - u‖ := by
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hw,
        show (1 : ℚ_[q]) - u' / u = (u - u') / u by field_simp, norm_div, hu, div_one,
        norm_sub_rev]
    rw [e]
    exact lt_of_le_of_lt hd (pow_neg_three_lt_two_norm_sq q))
  refine ⟨x, ?_⟩
  have hx' : (x : ℚ_[q]) ^ 2 = u' / u := by
    rw [← hw, ← hx]
    simp
  rw [hx']
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicUnitNorm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma UpperTheory.Gal.G1.normInt_eq_one {q : ℕ} [Fact q.Prime] {n : ℤ} (h : ¬ (q : ℤ) ∣ n) :
    ‖(n : ℤ_[q])‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((PadicInt.norm_int_lt_one_iff_dvd n).mp hlt))

private lemma UpperTheory.Gal.G1.norm_lt_one_iff_toZMod {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private lemma UpperTheory.Gal.G1.norm_eq_one_of_toZMod {q : ℕ} [Fact q.Prime] {x : ℤ_[q]}
    (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod x).mp hlt))

private lemma UpperTheory.Gal.G1.hens {q : ℕ} [Fact q.Prime] (c d a : ℤ_[q]) (h2 : ‖(2 : ℤ_[q])‖ = 1)
    (hc : ‖c‖ = 1) (ha : ‖a‖ = 1) (h : ‖c * a ^ 2 + d‖ < 1) : ∃ z : ℤ_[q], c * z ^ 2 + d = 0 := by
  let F : Polynomial ℤ_[q] := Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d
  have hF : ∀ t, Polynomial.aeval t F = c * t ^ 2 + d := by
    intro t; simp [F]
  have hF' : ∀ t, Polynomial.aeval t (Polynomial.derivative F) = c * (2 * t) := by
    intro t
    simp [F]
    exact Or.inl (Or.inl one_add_one_eq_two)
  have hn : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [hF', norm_mul, norm_mul, hc, h2, ha]; simp
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hn, hF]; simpa using h)
  exact ⟨z, by rwa [hF] at hz⟩

theorem UpperTheory.Gal.G1.pPadicUnitNorm :
    PadicUnitNorm := by
  intro q _ D hqD u hu
  have hq2 : ¬ (q : ℤ) ∣ 2 := fun h => hqD (Dvd.dvd.mul_right h D)
  have hqd : ¬ (q : ℤ) ∣ D := fun h => hqD (Dvd.dvd.mul_left h 2)
  have h2 : ‖(2 : ℤ_[q])‖ = 1 := by
    have := UpperTheory.Gal.G1.normInt_eq_one (q := q) hq2
    simpa using this
  have hD : ‖(D : ℤ_[q])‖ = 1 := UpperTheory.Gal.G1.normInt_eq_one hqd
  have hodd : Fintype.card (ZMod q) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : q.Prime).eq_two_or_odd with h | h
    · subst h; exact absurd (by norm_num) hq2
    · exact h
  let U : ℤ_[q] := ⟨u, hu.le⟩
  have hU : ‖U‖ = 1 := hu
  have hUc : ((U : ℤ_[q]) : ℚ_[q]) = u := rfl
  have hub : PadicInt.toZMod U ≠ 0 := fun h0 =>
    absurd hU ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod U).mpr h0).ne
  have hDb : -(D : ZMod q) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hqd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2)
    (g := Polynomial.C (-(D : ZMod q)) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X
      + Polynomial.C (-PadicInt.toZMod U))
    (by simp) (Polynomial.degree_quadratic hDb) hodd
  have hab' : a ^ 2 - (D : ZMod q) * b ^ 2 - PadicInt.toZMod U = 0 := by
    simp at hab
    linear_combination hab
  let x0 : ℤ_[q] := (a.val : ℤ_[q])
  let y0 : ℤ_[q] := (b.val : ℤ_[q])
  have hx : PadicInt.toZMod x0 = a := by simp [x0]
  have hy : PadicInt.toZMod y0 = b := by simp [y0]
  have hDz : PadicInt.toZMod (D : ℤ_[q]) = (D : ZMod q) := by simp
  have key : ‖x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U‖ < 1 := by
    rw [UpperTheory.Gal.G1.norm_lt_one_iff_toZMod]
    simp only [map_sub, map_mul, map_pow, hx, hy, hDz]
    exact hab'
  have hor : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hb0⟩ := hcon
    apply hub
    rw [ha0, hb0] at hab'
    simpa using hab'
  rcases hor with ha | hb
  · have hx1 : ‖x0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hx])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens 1 (-((D : ℤ_[q]) * y0 ^ 2 + U)) x0 h2 (by simp) hx1 (by
      have e : 1 * x0 ^ 2 + -((D : ℤ_[q]) * y0 ^ 2 + U) = x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U := by ring
      rw [e]; exact key)
    refine ⟨z, y0, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_neg, PadicInt.coe_one,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination -h3
  · have hy1 : ‖y0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hy])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens (D : ℤ_[q]) (U - x0 ^ 2) y0 h2 hD hy1 (by
      have e : (D : ℤ_[q]) * y0 ^ 2 + (U - x0 ^ 2) = -(x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U) := by ring
      rw [e, norm_neg]; exact key)
    refine ⟨x0, z, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRelOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem key_mat {E : Type} [Field E] {n : ℕ} (H Q b b' R : Matrix (Fin n) (Fin n) E) (hd : H.det ≠ 0) (s : E)
    (h : b' * H⁻¹ = Q * (s • (b * H⁻¹)) * R) : b' = s • (Q * b * (H⁻¹ * R * H)) := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  have h1 : b' = (b' * H⁻¹) * H := (Matrix.nonsing_inv_mul_cancel_right _ _ hu).symm
  rw [h1, h]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem pRelOf : RelOf := by
  intro E _ _ _ A n p _ S B B' s hs P hP h
  have hH := A.det_ne n
  have key := key_mat (A.H n) Pᵀ (mat S ↑B.β) (mat S ↑B'.β) (P.map ⇑(IsCMField.complexConj E)) hH
    (s : E) h
  have hdetT : IsUnit (Pᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hP
  have hu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdetT
  have hHc : (A.H n).map ⇑(IsCMField.complexConj E) = A.H n := by
    have h1 := A.herm n
    calc (A.H n).map ⇑(IsCMField.complexConj E) = (((A.H n).map (cj E))ᵀ)ᵀ :=
          (Matrix.transpose_transpose _).symm
      _ = (A.H n)ᵀ := by rw [h1]
      _ = A.H n := by simp [Arith.H]
  have hsh : MulOpposite.unop (hermStar (A.H n) hH Pᵀ) = (A.H n)⁻¹ * P.map ⇑(IsCMField.complexConj E) * A.H n := by
    rw [hermStar_apply]
    change ((A.H n).map ⇑(IsCMField.complexConj E))⁻¹ * ((Pᵀ).map ⇑(IsCMField.complexConj E))ᵀ *
      (A.H n).map ⇑(IsCMField.complexConj E) = _
    rw [hHc, Matrix.transpose_map, Matrix.transpose_transpose]
  refine ⟨hu.unit, s, hs, ?_⟩
  change mat S ↑B'.β = algebraMap ℚ (Matrix (Fin n) (Fin n) E) s *
    (Pᵀ * mat S ↑B.β * MulOpposite.unop (hermStar (A.H n) hH Pᵀ))
  rw [hsh, key, ← Algebra.smul_def, ← algebraMap_smul E s, eq_ratCast]

end UpperTheory.Gal.G1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitRep
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pSplitRep :
    SplitRep := by
  intro R _ tr nm ρ hρ hd u
  obtain ⟨w, hw⟩ := hd.exists_right_inv
  refine ⟨1 - ((tr : R) - ρ) * ((u - 1) * w), (u - 1) * w, ?_⟩
  unfold qf
  linear_combination ((u - 1) * w) ^ 2 * hρ + (u - 1) * hw
end

