module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmProd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.isCrys_isDR_prod :
    ∀ (l F r : ℕ) (L : List ℕ), AdmL l F r L → admitted l F r L.prod ∧ L.prod ≠ 0 ∧ (∀ q, AdmL l F r (q :: L) → q.Coprime L.prod) ∧ ∀ q, AdmL l F r (q :: L) → AdmL l F r L := by
  intro l F r L hL
  induction L with
  | nil =>
    refine ⟨⟨squarefree_one, fun q hq hd => absurd (Nat.eq_one_of_dvd_one hd) hq.ne_one⟩, by simp, fun q _ => by simp, fun q _ => ⟨List.nodup_nil, by simp⟩⟩
  | cons a L ih =>
    have tail : ∀ (b : ℕ) (M : List ℕ), AdmL l F r (b :: M) → AdmL l F r M := fun b M h =>
      ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem b hq)⟩
    obtain ⟨hA, hne, hcop, -⟩ := ih (tail a L hL)
    have haP : AdmP l F r a := hL.2 a List.mem_cons_self
    have ha : a.Prime := haP.1
    have haL : a.Coprime L.prod := hcop a hL
    rw [List.prod_cons]
    refine ⟨⟨?_, ?_⟩, mul_ne_zero ha.ne_zero hne, ?_, fun q hq => tail q _ hq⟩
    · exact Nat.squarefree_mul_iff.mpr ⟨haL, ha.prime.squarefree, hA.1⟩
    · intro q hq hd
      rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq ha).mp h]
        exact haP
      · exact hA.2 q hq h
    · intro q hq
      have hqa : q ≠ a := fun h => (List.nodup_cons.mp hq.1).1 (h ▸ List.mem_cons_self)
      have hqP : q.Prime := (hq.2 q List.mem_cons_self).1
      have hqL : AdmL l F r (q :: L) :=
        ⟨List.nodup_cons.mpr ⟨fun h => (List.nodup_cons.mp hq.1).1 (List.mem_cons_of_mem a h), (List.nodup_cons.mp (List.nodup_cons.mp hq.1).2).2⟩,
          fun p hp => by
            rcases List.mem_cons.mp hp with h | h
            · exact h ▸ hq.2 q List.mem_cons_self
            · exact hq.2 p (List.mem_cons_of_mem q (List.mem_cons_of_mem a h))⟩
      exact Nat.Coprime.mul_right ((Nat.coprime_primes hqP ha).mpr hqa) (hcop q hqL)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmissiblePrimeNotDvdOrderOfAndNotDvdLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level :
    ∀ (l F r d : ℕ), F ≠ 0 → l.Prime → r.Prime → r ≡ 1 [MOD F] → ML.admitted l F r d → ¬ l ∣ orderOf (r : ZMod (F * d)) ∧ ¬ r ∣ F * d := by
  intro l F r d _ hl hr hrF hd
  obtain ⟨hsq, hq⟩ := hd
  have hone : ∀ p : ℕ, p.Prime → p ≡ 1 [MOD F] → ¬ p ∣ F := fun p hp h hpF => by
    have h1 : p ≡ 1 [MOD p] := h.of_dvd hpF
    have h2 : p ∣ 1 := (h1.dvd_iff dvd_rfl).1 dvd_rfl
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  refine ⟨?_, ?_⟩
  · set n := ∏ q ∈ d.primeFactors, orderOf (r : ZMod q) with hn
    have hln : ¬ l ∣ n := by
      intro h
      obtain ⟨q, hqm, hlq⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
      exact (hq q (Nat.prime_of_mem_primeFactors hqm) (Nat.dvd_of_mem_primeFactors hqm)).2.2.2 hlq
    have hcop : Nat.Coprime F d := by
      apply Nat.coprime_of_dvd
      intro k hk hkF hkd
      exact hone k hk (hq k hk hkd).2.1 hkF
    have hpos : 1 ≤ r ^ n := Nat.one_le_pow _ _ hr.pos
    have hF : r ^ n ≡ 1 [MOD F] := by simpa using hrF.pow n
    have hD : r ^ n ≡ 1 [MOD d] := by
      have h1 : ∏ q ∈ d.primeFactors, q ∣ r ^ n - 1 := by
        apply Finset.prod_primes_dvd
        · intro a ha
          exact (Nat.prime_of_mem_primeFactors ha).prime
        · intro a ha
          have h2 : (r : ZMod a) ^ n = 1 :=
            orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem (fun q : ℕ => orderOf (r : ZMod q)) ha)
          have h3 : r ^ n ≡ 1 [MOD a] := by
            rw [← ZMod.natCast_eq_natCast_iff]
            simpa using h2
          exact (Nat.modEq_iff_dvd' hpos).1 h3.symm
      rw [Nat.prod_primeFactors_of_squarefree hsq] at h1
      exact ((Nat.modEq_iff_dvd' hpos).2 h1).symm
    have hFD : r ^ n ≡ 1 [MOD F * d] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hF, hD⟩
    have h4 : (r : ZMod (F * d)) ^ n = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hFD
      simpa using this
    exact fun h => hln (h.trans (orderOf_dvd_of_pow_eq_one h4))
  · intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hone r hr hrF h
    · exact (hq r hr h).2.2.1 rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GenBUnits
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem th_eq (F b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    (b : ℤ) * (t.val : ℤ) = (((b : ZMod F) * t).val : ℤ) + F * ((t.val * b / F : ℕ) : ℤ) ∧
    th F b t = 2 * ((t.val * b / F : ℕ) : ℤ) - ((b : ℤ) - 1) := by
  have hF : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have h1 : ((b : ZMod F) * t).val = t.val * b % F := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, mul_comm]
  have h0 : 0 < ((b : ZMod F) * t).val := Nat.pos_of_ne_zero fun h => hy ((ZMod.val_eq_zero _).1 h)
  have hlt := ZMod.val_lt ((b : ZMod F) * t)
  have h2 : F * (t.val * b / F) + t.val * b % F = t.val * b := Nat.div_add_mod _ _
  have h3 : F * ((-t).val * b / F) + (-t).val * b % F = (-t).val * b := Nat.div_add_mod _ _
  have h4 : (-t).val * b % F < F := Nat.mod_lt _ hF
  have h5 : (-t).val + t.val = F := by
    rw [ZMod.neg_val, if_neg ht]
    have := ZMod.val_lt t
    omega
  rw [← h1] at h2
  rw [th]
  generalize ((b : ZMod F) * t).val = y at *
  generalize (-t).val * b % F = r at *
  generalize (-t).val * b / F = j' at *
  generalize t.val * b / F = j at *
  generalize (-t).val = s at *
  generalize t.val = u at *
  zify at h0 hlt h2 h3 h4 h5 hF
  have hr : (0 : ℤ) ≤ r := by positivity
  have h6 : (F : ℤ) * (b - j - j') = y + r := by linear_combination -h2 - h3 - b * h5
  have h7 : (0 : ℤ) < b - j - j' := by
    by_contra h
    nlinarith
  have h8 : (b : ℤ) - j - j' < 2 := by
    by_contra h
    nlinarith
  exact ⟨by linear_combination -h2, by omega⟩

private theorem pointwise (F e b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    ∃ z : ℤ, (Stk.dk (e + 1) : ℚ) * ((b : ℚ) ^ e * (th F b t * (t.val : ℚ) ^ e) +
      2 * (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val / (e + 1) -
        (b : ℚ) ^ (e + 1) * (Bern.bcoef F (e + 1) t.val / (e + 1)))) = F * z := by
  have hM0 : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have hM : (F : ℚ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  obtain ⟨h1, h2⟩ := th_eq F b t ht hy
  obtain ⟨z1, hz1⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e ((b : ZMod F) * t).val hM0
  obtain ⟨z2, hz2⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e t.val hM0
  rw [h2]
  generalize ((b : ZMod F) * t).val = y at *
  generalize t.val * b / F = j at *
  generalize t.val = u at *
  obtain ⟨⟨z3, hz3⟩, ⟨w, hw⟩⟩ := Stk.exists_binomial_expansion_mod_sq ((b : ℤ) * u) (-(j : ℤ)) F e
  have h3 : (b : ℤ) * u + F * (-(j : ℤ)) = y := by linear_combination h1
  rw [h3] at hz3 hw
  have q3 : (y : ℚ) ^ (e + 1) =
      ((b : ℚ) * u) ^ (e + 1) + ((e : ℚ) + 1) * ((b : ℚ) * u) ^ e * ((F : ℚ) * (-(j : ℚ))) + (F : ℚ) ^ 2 * z3 := by
    exact_mod_cast hz3
  have qw : (y : ℚ) ^ e = ((b : ℚ) * u) ^ e + (F : ℚ) * w := by
    exact_mod_cast hw
  have hdk : (Stk.dk (e + 1) : ℚ) = 2 * ((e : ℚ) + 1) * (primorial (e + 1 + 1) : ℚ) := by
    rw [Stk.dk]; push_cast; ring
  refine ⟨4 * z1 - 4 * (b : ℤ) ^ (e + 1) * z2 + 4 * (primorial (e + 1 + 1) : ℤ) * z3
    - 2 * ((e : ℤ) + 1) * (primorial (e + 1 + 1) : ℤ) * w, ?_⟩
  rw [Nat.cast_add, Nat.cast_one] at hz1 hz2
  rw [hz1, hz2, q3, qw, hdk]
  push_cast
  field_simp
  ring

private theorem genB_units {R : Type} [CommRing R] [Algebra ℚ R] {F : ℕ} [NeZero F] (hF : 1 < F) (k : ℕ)
    (χ : DirichletCharacter R F) :
    Bern.genB k (χ : ZMod F → R) = ∑ t : (ZMod F)ˣ, χ t * algebraMap ℚ R (Bern.bcoef F k (t : ZMod F).val) := by
  haveI : Fact (1 < F) := ⟨hF⟩
  have h1 : Bern.genB k (χ : ZMod F → R) = ∑ t : ZMod F, χ t * algebraMap ℚ R (Bern.bcoef F k t.val) := by
    rw [← Bern.b_sumicc (fun x : ZMod F => χ x * algebraMap ℚ R (Bern.bcoef F k x.val)), Bern.genB]
    refine Finset.sum_congr rfl fun a ha => ?_
    rcases (Finset.mem_Icc.1 ha).2.lt_or_eq with h | h
    · rw [ZMod.val_cast_of_lt h]
    · rw [h, ZMod.natCast_self, χ.map_nonunit not_isUnit_zero, zero_mul, zero_mul]
  rw [h1]
  symm
  refine Finset.sum_of_injOn (fun t : (ZMod F)ˣ => (t : ZMod F)) (fun a _ b _ h => Units.ext h)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro x _ hx
  rw [χ.map_nonunit, zero_mul]
  rintro ⟨u, rfl⟩
  exact hx ⟨u, by simp, rfl⟩

private theorem norm_chi {R : Type} [NormedField R] {F : ℕ} [NeZero F] (χ : DirichletCharacter R F) (t : (ZMod F)ˣ) :
    ‖χ t‖ = 1 := by
  have h : χ t ^ Fintype.card (ZMod F)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖χ t‖ ^ Fintype.card (ZMod F)ˣ = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

theorem UpperTheory.V.ML.zCong :
    ∀ (l : ℕ) [Fact l.Prime] (F m e b : ℕ) [NeZero F], l ^ m ∣ F → 1 ≤ m → 1 ≤ e → b.Coprime F → ∀ χ : DirichletCharacter (PadicAlgCl l) F, χ (-1) = (-1) ^ (e + 1) →
    ‖(UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)))‖ ≤ ‖(l : PadicAlgCl l) ^ m‖ := by
  intro l hl F m e b _ hm h1m _ hb χ _
  have hF : 1 < F := lt_of_lt_of_le (Nat.one_lt_pow (by omega) hl.out.one_lt)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne F)) hm)
  haveI : Fact (1 < F) := ⟨hF⟩
  set u : (ZMod F)ˣ := ZMod.unitOfCoprime b hb with hu
  have hub : (u : ZMod F) = b := ZMod.coe_unitOfCoprime b hb
  have g1 := genB_units hF (e + 1) χ
  have g2 : Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) = ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val) := by
    rw [g1, ← hub]
    exact (Equiv.sum_comp (Equiv.mulLeft u) (fun t : (ZMod F)ˣ => χ t *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) (t : ZMod F).val))).symm
  have hp : ∀ t : (ZMod F)ˣ, _ := fun t => pointwise F e b (t : ZMod F) t.ne_zero (by
    rw [← hub]; exact (u * t).ne_zero)
  choose z hz using hp
  have key : (UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1))) =
      ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) * ((F : PadicAlgCl l) * z t) := by
    have e1 : 2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)) =
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1)) / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l)
        - 2 / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) := by ring
    rw [e1]
    nth_rewrite 2 [g2]
    rw [g1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := congrArg (algebraMap ℚ (PadicAlgCl l)) (hz t)
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_natCast, map_intCast, map_div₀, map_one, map_ofNat] at h
    rw [← h, map_mul]
    ring
  rw [key]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun t _ => ?_
  obtain ⟨c, hc⟩ := hm
  have hn : ‖χ ((b : ZMod F) * t)‖ = 1 := by
    rw [← hub]; exact norm_chi χ (u * t)
  have hFc : (F : PadicAlgCl l) * z t = (l : PadicAlgCl l) ^ m * (((c : ℤ) * z t : ℤ) : PadicAlgCl l) := by
    have : (F : PadicAlgCl l) = (l : PadicAlgCl l) ^ m * c := by exact_mod_cast congrArg (Nat.cast : ℕ → PadicAlgCl l) hc
    rw [this]; push_cast; ring
  rw [norm_mul, hn, one_mul, hFc, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.HasOrdP
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.hasOrdP :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (F r a : ℕ) [NeZero F], r ≠ 0 → ∀ (A₀ : ValuationSubring Ω) (u : Ω) (k : (ZMod F)ˣ → ℤ), HasOrd F r A₀ u k →
    (∀ (d : (ZMod F)ˣ) (δ : G ℚ Ω), Lifts F d δ → HasOrd F r A₀ (opP δ a u) fun t => k (t * d) - a * k t) ∧ ∀ n : ℕ, HasOrd F r A₀ (u ^ n) fun t => n * k t := by
  intro Ω _ _ _ F r a _ hr A₀ u k hk
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hv0 : A₀.valuation (r : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hr)
  have hk' : ∀ (t : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F t σ → A₀.valuation (σ u) = A₀.valuation (r : Ω) ^ k t := hk
  refine ⟨fun d δ hδ t σ hσ => ?_, fun n t σ hσ => ?_⟩
  · have hδ' : ∀ x : Ω, x ^ F = 1 → δ x = x ^ (d : ZMod F).val := hδ
    have hσ' : ∀ x : Ω, x ^ F = 1 → σ x = x ^ (t : ZMod F).val := hσ
    have hσδ : Lifts F (t * d) (σ * δ) := by
      show ∀ x : Ω, x ^ F = 1 → (σ * δ) x = x ^ ((t * d : (ZMod F)ˣ) : ZMod F).val
      intro x hx
      rw [AlgEquiv.mul_apply, hδ' x hx, map_pow, hσ' x hx, ← pow_mul, Units.val_mul, ZMod.val_mul]
      conv_lhs => rw [← Nat.mod_add_div ((t : ZMod F).val * (d : ZMod F).val) F]
      rw [pow_add, pow_mul, hx, one_pow, mul_one]
    have h1 := hk' (t * d) (σ * δ) hσδ
    have h2 := hk' t σ hσ
    rw [AlgEquiv.mul_apply] at h1
    show A₀.valuation (σ (δ u / u ^ a)) = _
    rw [map_div₀, map_pow, map_div₀, map_pow, h1, h2, ← zpow_natCast, ← zpow_mul, zpow_sub₀ hv0, mul_comm (k t)]
  · show A₀.valuation (σ (u ^ n)) = _
    rw [map_pow, map_pow, hk' t σ hσ, ← zpow_natCast, ← zpow_mul, mul_comm (k t)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Imports
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.chain :
    ∀ (O V St : Type) [CommRing O] [AddCommGroup V] [Module O V] (S : St → Submodule O V) (j : St → ℕ) (J : ℕ), (∀ s, j s ≤ J) →
    (∀ s, S s ≠ ⊥ → ∃ s', j s < j s' ∧ Module.length O (S s) + j s ≤ Module.length O (S s') + j s') → ∀ s, Module.length O (S s) + j s ≤ J := by
  intro O V St _ _ _ S j J hJ hstep
  have key : ∀ (n : ℕ) (s : St), J - j s ≤ n → Module.length O (S s) + j s ≤ J := by
    intro n
    induction n with
    | zero =>
      intro s hs
      by_cases h : S s = ⊥
      · have h0 : Module.length O (S s) = 0 := by
          rw [h]; exact Module.length_eq_zero
        rw [h0, zero_add]
        exact_mod_cast hJ s
      · obtain ⟨s', h1, -⟩ := hstep s h
        have := hJ s'
        omega
    | succ n ih =>
      intro s hs
      by_cases h : S s = ⊥
      · have h0 : Module.length O (S s) = 0 := by
          rw [h]; exact Module.length_eq_zero
        rw [h0, zero_add]
        exact_mod_cast hJ s
      · obtain ⟨s', h1, h2⟩ := hstep s h
        have := hJ s'
        exact h2.trans (ih s' (by omega))
  intro s
  exact key _ s le_rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.NormCyclotomicPrimeLayerEqNrmGenerator
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem cyc_hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] [CharZero Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  have key : f.toRatAlgHom = g.toRatAlgHom := by
    apply AlgHom.ext
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) x
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨n, hn, -, hy1⟩ := hy
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hy1
      exact h y hy1
    | algebraMap c => rw [AlgHom.commutes, AlgHom.commutes]
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  ext x
  exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) key

private theorem card_gal (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K']
    [IsGalois K K'] (hq : q.Prime) (hc : q.Coprime M) : Nat.card (K' ≃ₐ[K] K') = q - 1 := by
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have h1 := IsCyclotomicExtension.finrank K' (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M)))
  have h2 := IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
  rw [IsGalois.card_aut_eq_finrank]
  have htow := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2, Nat.totient_mul hc, Nat.totient_prime hq] at htow
  have hM : 0 < M.totient := Nat.totient_pos.mpr (NeZero.pos M)
  exact Nat.eq_of_mul_eq_mul_left hM (by rw [htow, mul_comm])

theorem UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (ι' : K' →+* Ω), q.Prime → q.Coprime M → ∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ x : K', nrm q τ (ι' x) = ι' (algebraMap K K' (Algebra.norm K x)) := by
  intro Ω _ _ M q _ _ K K' _ _ _ _ _ _ _ ι' hq hc τ hτ hgen x
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsScalarTower ℚ K K' := inferInstance
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  obtain ⟨b, hbgen, hb⟩ := hgen
  have hb' : ∀ y : Ω, y ^ q = 1 → τ y = y ^ (b : ZMod q).val := hb
  have hτM : ∀ y : Ω, y ^ M = 1 → τ y = y := hτ
  have hpm : ∀ {R : Type} [Monoid R] (y : R) (N m n : ℕ), y ^ N = 1 → m ≡ n [MOD N] → y ^ m = y ^ n := by
    intro R _ y N m n hy h
    rw [← Nat.mod_add_div m N, ← Nat.mod_add_div n N, show m % N = n % N from h, pow_add, pow_add,
      pow_mul, pow_mul, hy, one_pow, one_pow]
  obtain ⟨A, hA1, hA0⟩ : ∃ A, A ≡ 1 [MOD q] ∧ A ≡ 0 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 1 0).1, (Nat.chineseRemainder hc 1 0).2.1, (Nat.chineseRemainder hc 1 0).2.2⟩
  obtain ⟨B, hB0, hB1⟩ : ∃ B, B ≡ 0 [MOD q] ∧ B ≡ 1 [MOD M] :=
    ⟨(Nat.chineseRemainder hc 0 1).1, (Nat.chineseRemainder hc 0 1).2.1, (Nat.chineseRemainder hc 0 1).2.2⟩
  obtain ⟨e, he⟩ : ∃ e, e = A * (b : ZMod q).val + B := ⟨_, rfl⟩
  have he_q : e ≡ (b : ZMod q).val [MOD q] := by
    have h := (hA1.mul_right (b : ZMod q).val).add hB0
    rwa [one_mul, add_zero, ← he] at h
  have he_M : e ≡ 1 [MOD M] := by
    have h := (hA0.mul_right (b : ZMod q).val).add hB1
    rwa [zero_mul, zero_add, ← he] at h
  have hτe : ∀ y : Ω, y ^ (q * M) = 1 → τ y = y ^ e := by
    intro y hy
    have hAB : A + B ≡ 1 [MOD q * M] := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨by simpa using hA1.add hB0, by simpa using hA0.add hB1⟩
    obtain ⟨cA, hcA⟩ := (Nat.modEq_zero_iff_dvd.mp hA0)
    obtain ⟨cB, hcB⟩ := (Nat.modEq_zero_iff_dvd.mp hB0)
    have hyA : (y ^ A) ^ q = 1 := by
      rw [← pow_mul, show A * q = q * M * cA by rw [hcA]; ring, pow_mul, hy, one_pow]
    have hyB : (y ^ B) ^ M = 1 := by
      rw [← pow_mul, show B * M = q * M * cB by rw [hcB]; ring, pow_mul, hy, one_pow]
    calc τ y = τ (y ^ A * y ^ B) := by rw [← pow_add, hpm y (q * M) (A + B) 1 hy hAB, pow_one]
      _ = (y ^ A) ^ (b : ZMod q).val * y ^ B := by rw [map_mul, hb' _ hyA, hτM _ hyB]
      _ = y ^ e := by rw [he, ← pow_mul, ← pow_add]
  have hζ := IsCyclotomicExtension.zeta_spec (q * M) ℚ K'
  have he_cop : e.Coprime (q * M) := by
    apply Nat.Coprime.mul_right
    · exact he_q.gcd_eq.trans (ZMod.val_coe_unit_coprime b)
    · exact he_M.gcd_eq.trans (Nat.gcd_one_left M)
  have hμ := hζ.pow_of_coprime e he_cop
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q * M))
  have hσ0ζ := IsCyclotomicExtension.fromZetaAut_spec hμ hirr
  have hσ0 : ∀ z : K', z ^ (q * M) = 1 → IsCyclotomicExtension.fromZetaAut hμ hirr z = z ^ e := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [map_pow, hσ0ζ, ← pow_mul, ← pow_mul, mul_comm e j]
  have hσ0K : ∀ y : K, IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y := by
    have h := cyc_hom_ext M ((IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv.toRingHom.comp (algebraMap K K'))
      (algebraMap K K') (fun y hy => by
        show IsCyclotomicExtension.fromZetaAut hμ hirr (algebraMap K K' y) = algebraMap K K' y
        have h1 : (algebraMap K K' y) ^ M = 1 := by rw [← map_pow, hy, map_one]
        rw [hσ0 _ (by rw [mul_comm, pow_mul, h1, one_pow]), hpm _ M e 1 h1 he_M, pow_one])
    exact fun y => RingHom.congr_fun h y
  let σ1 : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := (IsCyclotomicExtension.fromZetaAut hμ hirr).toRingEquiv) hσ0K
  have hσ1 : ∀ z : K', z ^ (q * M) = 1 → σ1 z = z ^ e := fun z hz => hσ0 z hz
  have hcomm : ∀ z : K', τ (ι' z) = ι' (σ1 z) := by
    have h := cyc_hom_ext (q * M) ((τ : Ω ≃ₐ[ℚ] Ω).toRingEquiv.toRingHom.comp ι') (ι'.comp σ1.toRingEquiv.toRingHom)
      (fun z hz => by
        show τ (ι' z) = ι' (σ1 z)
        rw [hσ1 z hz, map_pow, hτe _ (by rw [← map_pow, hz, map_one])])
    exact fun z => RingHom.congr_fun h z
  have hcommi : ∀ i : ℕ, ∀ z : K', (τ ^ i) (ι' z) = ι' ((σ1 ^ i) z) := by
    intro i
    induction i with
    | zero => intro z; rw [pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]
    | succ i ih => intro z; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcomm, ih]
  have hζq : IsPrimitiveRoot (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) q := by
    have h := hζ.pow_of_dvd (NeZero.ne M) (dvd_mul_left M q)
    rwa [Nat.mul_div_cancel q (NeZero.pos M)] at h
  have hζq1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (q * M) = 1 := by
    rw [pow_mul, hζq.pow_eq_one, one_pow]
  have hσpow : ∀ i : ℕ, (σ1 ^ i) (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M)
      = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hσ1 _ hζq1, map_pow, ih, ← pow_mul, pow_succ]
  have horder : orderOf b = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hbgen, Nat.card_eq_fintype_card, ZMod.card_units]
  have hinj : ∀ i ∈ Finset.range (q - 1), ∀ j ∈ Finset.range (q - 1), σ1 ^ i = σ1 ^ j → i = j := by
    intro i hi j hj hij
    have h1 : (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ i) = (IsCyclotomicExtension.zeta (q * M) ℚ K' ^ M) ^ (e ^ j) := by
      rw [← hσpow, ← hσpow, hij]
    rw [hpm _ q (e ^ i) (e ^ i % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm,
      hpm _ q (e ^ j) (e ^ j % q) hζq.pow_eq_one (Nat.mod_modEq _ _).symm] at h1
    have h2 : e ^ i ≡ e ^ j [MOD q] := hζq.pow_inj (Nat.mod_lt _ hq.pos) (Nat.mod_lt _ hq.pos) h1
    have h3 : ((e : ZMod q)) = (b : ZMod q) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr he_q, ZMod.natCast_zmod_val]
    have h4 : (b : ZMod q) ^ i = (b : ZMod q) ^ j := by
      rw [← h3, ← Nat.cast_pow, ← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2]
    have h5 : b ^ i = b ^ j := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h4])
    have h6 := pow_eq_pow_iff_modEq.mp h5
    rw [horder] at h6
    have h7 : i % (q - 1) = j % (q - 1) := h6
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h7
  have himg : (Finset.range (q - 1)).image (fun i => σ1 ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), Finset.card_range,
      ← Nat.card_eq_fintype_card, card_gal M q K K' hq hc]
  show ∏ i ∈ Finset.range (q - 1), (τ ^ i) (ι' x) = _
  rw [Algebra.norm_eq_prod_automorphisms, map_prod, ← himg, Finset.prod_image (fun i hi j hj h => hinj i hi j hj h)]
  exact Finset.prod_congr rfl (fun i _ => hcommi i x)
end

