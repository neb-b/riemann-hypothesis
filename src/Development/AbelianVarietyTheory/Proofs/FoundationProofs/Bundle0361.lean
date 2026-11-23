module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.InertiaFixedValue

open GlobalTheory.Published.AbVarRed IsLocalRing

theorem valuation_intCast_lt_one_iff {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
  obtain ⟨v, hv, hl⟩ := h
  have hlZ : ((l : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by rw [Int.cast_natCast]; exact hl
  have hiff : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ (l : ℤ) ∣ n := by
    constructor
    · intro hn
      by_contra hnd
      have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
      obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
      apply v.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((a * l + b * n : ℤ) : 𝓞 ℚ) = 1 := by rw [hab, Int.cast_one]
      rw [← e]
      push_cast
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hlZ) (v.asIdeal.mul_mem_left _ hn)
    · rintro ⟨m, rfl⟩
      push_cast
      exact v.asIdeal.mul_mem_right _ (by exact_mod_cast hlZ)
  rw [← hiff, ← hv (n : 𝓞 ℚ)]
  simp

private theorem valuation_intCast_eq_one_of_not_dvd {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : A.valuation (z : Ω) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A z))
    (not_lt.1 fun hlt => hz ((valuation_intCast_lt_one_iff h z).1 hlt))

private theorem not_dvd_den_of_valuation_le_one {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (q : ℚ) (hq : A.valuation (algebraMap ℚ Ω q) ≤ 1) :
    ¬ (l : ℤ) ∣ (q.den : ℤ) := by
  intro hd

  have hn : ¬ (l : ℤ) ∣ q.num := by
    intro hn
    have h1 : l ∣ q.num.natAbs := Int.ofNat_dvd_left.1 hn
    have h2 : l ∣ q.den := by exact_mod_cast hd
    have h3 : l ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [Nat.Coprime.gcd_eq_one q.reduced] at this
    exact (Fact.out : l.Prime).ne_one (Nat.dvd_one.1 h3)
  have e0 : algebraMap ℚ Ω q * ((q.den : ℤ) : Ω) = (q.num : Ω) := by
    rw [← map_intCast (algebraMap ℚ Ω) (q.den : ℤ), ← map_intCast (algebraMap ℚ Ω) q.num, ← map_mul]
    congr 1
    rw [Int.cast_natCast]
    exact Rat.mul_den_eq_num q
  have e : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) = 1 := by
    rw [← map_mul, e0, valuation_intCast_eq_one_of_not_dvd h _ hn]
  have hlt : A.valuation ((q.den : ℤ) : Ω) < 1 := (valuation_intCast_lt_one_iff h _).2 hd
  have hlt1 : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) < 1 :=
    calc A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω)
        ≤ 1 * A.valuation ((q.den : ℤ) : Ω) := by gcongr
      _ = A.valuation ((q.den : ℤ) : Ω) := one_mul _
      _ < 1 := hlt
  rw [e] at hlt1
  exact lt_irrefl _ hlt1

theorem isAbove_of_overL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra ℤ R] [(Ideal.span {(l : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(l : ℤ)})] :
    IsAbove R ℚ A.toSubring := by
  unfold IsAbove
  have hcast : ∀ z : ℤ, algebraMap R ℚ (algebraMap ℤ R z) = z := fun z =>
    eq_intCast ((algebraMap R ℚ).comp (algebraMap ℤ R)) z
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hmk : ∀ (a : ℤ) (s : (Ideal.span {(l : ℤ)}).primeCompl),
      algebraMap R ℚ (IsLocalization.mk' R a s) = (a : ℚ) / ((s : ℤ) : ℚ) := by
    intro a s
    have hne : ((s : ℤ) : ℚ) ≠ 0 := by
      have : (s : ℤ) ≠ 0 := fun h0 => hs0 s (h0 ▸ dvd_zero _)
      exact_mod_cast this
    rw [eq_div_iff hne, ← hcast a, ← hcast (s : ℤ), ← map_mul, IsLocalization.mk'_spec]
  ext x
  rw [Subring.mem_comap, RingHom.mem_range]
  change algebraMap ℚ Ω x ∈ A ↔ _
  rw [← A.valuation_le_one_iff]
  constructor
  · intro hx
    have hden := not_dvd_den_of_valuation_le_one h x hx
    refine ⟨IsLocalization.mk' R x.num
      ⟨(x.den : ℤ), Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩, ?_⟩
    rw [hmk]
    push_cast
    exact Rat.num_div_den x
  · rintro ⟨r, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(l : ℤ)}).primeCompl r
    rw [hmk, map_div₀, map_intCast, map_intCast, map_div₀, valuation_intCast_eq_one_of_not_dvd h _ (hs0 s),
      div_one]
    exact (A.valuation_le_one_iff _).2 (intCast_mem A a)

theorem valuation_eq_zpow_of_fixed {R K Ω : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) {π : R} (hπ : Irreducible π)
    {c : Ω} (hc0 : c ≠ 0) (hc : c ∈ IntermediateField.fixedField (inertia K V)) :
    ∃ k : ℤ, V.valuation c = V.valuation (algebraMap K Ω (algebraMap R K π)) ^ k := by
  set p : Ω := algebraMap K Ω (algebraMap R K π) with hp
  have hpF : p ∈ IntermediateField.fixedField (inertia K V) := IntermediateField.algebraMap_mem _ _
  have hp0 : p ≠ 0 := by
    rw [hp, Ne, map_eq_zero_iff _ (algebraMap K Ω).injective,
      map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero

  have hstep : ∀ n : ℕ, ∀ x : Ω, x ∈ IntermediateField.fixedField (inertia K V) → x ≠ 0 → x ∈ V →
      x / p ^ n ∉ V → ∃ k : ℕ, V.valuation x = V.valuation p ^ k := by
    intro n
    induction n with
    | zero =>
      intro x _ _ hxV hn
      rw [pow_zero, div_one] at hn
      exact absurd hxV hn
    | succ n ih =>
      intro x hxF hx0 hxV hn
      by_cases hxu : x ∈ V.nonunits
      · have hd : x / p ∈ V := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ x hxF hxu
        have hdn : x / p / p ^ n ∉ V := by rwa [div_div, ← pow_succ']
        obtain ⟨k, hk⟩ := ih (x / p) (div_mem hxF hpF) (div_ne_zero hx0 hp0) hd hdn
        refine ⟨k + 1, ?_⟩
        calc V.valuation x = V.valuation (x / p * p) := by rw [div_mul_cancel₀ x hp0]
          _ = V.valuation p ^ (k + 1) := by rw [map_mul, hk, pow_succ]
      · refine ⟨0, ?_⟩
        rw [pow_zero]
        exact le_antisymm ((V.valuation_le_one_iff x).2 hxV)
          (not_lt.1 fun hlt => hxu (V.mem_nonunits_iff.2 hlt))
  by_cases hcV : c ∈ V
  · obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c hc0
    obtain ⟨k, hk⟩ := hstep n c hc hc0 hcV hn
    exact ⟨k, by rw [hk, zpow_natCast]⟩
  · have hi : c⁻¹ ∈ V := (V.mem_or_inv_mem c).resolve_left hcV
    obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c⁻¹ (inv_ne_zero hc0)
    obtain ⟨k, hk⟩ := hstep n c⁻¹ (inv_mem hc) (inv_ne_zero hc0) hi hn
    refine ⟨-(k : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← hk, map_inv₀, inv_inv]

theorem valuation_eq_zpow_of_ine_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) →
    ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  intro l _ Ω _ _ _ A hA c hc0 hc
  have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
  have hne : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hM : (Ideal.span {(l : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpr.irreducible
  have hP : (Ideal.span {(l : ℤ)}).IsPrime := hM.isPrime

  set B := A.comap (algebraMap ℚ Ω) with hB
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hloc : IsLocalization.AtPrime B (Ideal.span {(l : ℤ)}) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro s
      have hs' := hs0 s
      have hsq : ((s : ℤ) : ℚ) ≠ 0 := by
        have : (s : ℤ) ≠ 0 := fun h0 => hs' (h0 ▸ dvd_zero _)
        exact_mod_cast this
      have hinv : ((s : ℤ) : ℚ)⁻¹ ∈ B := by
        rw [hB, ValuationSubring.mem_comap, ← A.valuation_le_one_iff, map_inv₀, map_intCast, map_inv₀,
          valuation_intCast_eq_one_of_not_dvd hA _ hs', inv_one]
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      simp [hsq]
    · intro z
      have hz : A.valuation (algebraMap ℚ Ω (z : ℚ)) ≤ 1 :=
        (A.valuation_le_one_iff _).2 (ValuationSubring.mem_comap.1 z.2)
      have hden := not_dvd_den_of_valuation_le_one hA _ hz
      refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ),
        Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, eq_intCast, SubringClass.coe_intCast, Int.cast_natCast]
      exact Rat.mul_den_eq_num _
    · intro x y hxy
      refine ⟨1, ?_⟩
      have hq : (x : ℚ) = y := by
        have := congrArg (fun b : B => (b : ℚ)) hxy
        simpa using this
      simp only [OneMemClass.coe_one, one_mul]
      exact_mod_cast hq
  have : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hne B
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have : Finite (ℤ ⧸ Ideal.span {(l : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod l).symm.toEquiv
  have : Finite (ResidueField B) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {(l : ℤ)}) B).toEquiv
  have hAb : IsAbove B ℚ A.toSubring := isAbove_of_overL hA B
  have hirr : Irreducible (algebraMap ℤ B l) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(l : ℤ)}) B, Ideal.map_span,
      Set.image_singleton]

  have hs : ∀ σ ∈ inertia ℚ A, σ ∈ Ine (F := ℚ) A := by
    intro σ hσ
    rw [mem_Ine]
    unfold inertia at hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
    refine ⟨τ.2, fun x hx => ?_⟩
    set a : A := ⟨x, (A.valuation_le_one_iff x).1 hx⟩
    have hfix : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := by
      have := congrArg (fun f => f (IsLocalRing.residue A a)) (MonoidHom.mem_ker.1 hτ)
      simpa using this
    have h0 : IsLocalRing.residue A (τ • a - a) = 0 := by
      rw [map_sub, IsLocalRing.ResidueField.residue_smul, hfix, sub_self]
    have hm : τ • a - a ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq_zero_iff_mem.1 h0
    exact (A.valuation_lt_one_iff _).1 hm
  have hfixc : c ∈ IntermediateField.fixedField (inertia ℚ A) :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hc σ (hs σ hσ)
  obtain ⟨k, hk⟩ := valuation_eq_zpow_of_fixed A hAb hirr hc0 hfixc
  refine ⟨k, ?_⟩
  rw [hk]
  simp

end GlobalTheory.InertiaFixedValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralIffNormLeOne
section
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

noncomputable section

namespace GlobalTheory.KZ.AutoPin

variable {l : ℕ} [Fact l.Prime]

def compPow (l : ℕ) [Fact l.Prime] (B : PowerSeries (Qbar l)) : PowerSeries (Qbar l) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), B.coeff k * ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_l_pos : 0 < ‖((l : ℕ) : Qbar l)‖ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)

theorem norm_lpow_anti {k n : ℕ} (h : k ≤ n) : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_l_lt_one.le h

theorem cg_trans {n : ℕ} {a b d : Qbar l} (h1 : Cg n a b) (h2 : Cg n b d) : Cg n a d := by
  unfold Cg at *
  calc ‖a - d‖ = ‖(a - b) + (b - d)‖ := by ring_nf
    _ ≤ max ‖a - b‖ ‖b - d‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h1 h2

theorem cg_mono {k n : ℕ} {a b : Qbar l} (h : Cg n a b) (hk : k ≤ n) : Cg k a b :=
  le_trans h (norm_lpow_anti hk)

theorem cg_mul {n : ℕ} {x a b : Qbar l} (hx : ‖x‖ ≤ 1) (h : Cg n a b) : Cg n (x * a) (x * b) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hx) h

theorem norm_tval_le (B : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) (hB : ∀ n, ‖B.coeff n‖ ≤ 1) (hz : ‖z - 1‖ ≤ 1) :
    ‖tval B N z‖ ≤ 1 := by
  unfold tval
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (hB n) (by positivity) (pow_le_one₀ (norm_nonneg _) hz)

theorem tval_sub (P Q : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : tval (P - Q) N z = tval P N z - tval Q N z := by
  unfold tval; rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun n _ => ?_; simp [sub_mul]

theorem tval_smul (x : Qbar l) (P : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : tval (x • P) N z = x * tval P N z := by
  unfold tval; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_; simp [mul_assoc]

theorem isIntegral_iff_norm_le_one (x : Qbar l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  (isIntegral_iff_norm_le_one x).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem intCast_mem (c : Coef l) (n : ℤ) : ((n : ℤ) : Qbar l) ∈ c.O := by
  have : ((n : ℤ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (n : ℤ_[l]) := by simp
  rw [this]; exact c.O.algebraMap_mem _

theorem polyPow_coeff_int (k n : ℕ) : ∃ t : ℤ,
    ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n = (t : Qbar l) := by
  refine ⟨((((Polynomial.X + 1) ^ l - 1 : Polynomial ℤ)) ^ k).coeff n, ?_⟩
  have : (((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k =
      Polynomial.map (Int.castRingHom (Qbar l)) ((((Polynomial.X + 1) ^ l - 1 : Polynomial ℤ)) ^ k) := by
    simp [Polynomial.map_pow, Polynomial.map_sub]
  rw [this, Polynomial.coeff_map]; rfl

theorem compPow_coeff_mem (c : Coef l) (B : PowerSeries (Qbar l)) (hB : ∀ n, B.coeff n ∈ c.O) (n : ℕ) :
    (compPow l B).coeff n ∈ c.O := by
  unfold compPow
  rw [PowerSeries.coeff_mk]
  refine sum_mem fun k _ => mul_mem (hB k) ?_
  obtain ⟨t, ht⟩ := polyPow_coeff_int (l := l) k n
  rw [ht]; exact intCast_mem c t

end GlobalTheory.KZ.AutoPin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBActSgDDiamIff
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem isDiam_sgD_of_coprime {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := Nat.coprime_zero_right d |>.1 hd
    subst h1
    refine Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
    · simp [en]
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem isDiam_mul {N l a d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l a s) (ht : IsDiam N l d t) :
    IsDiam N l (d * a) (s * t) := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  refine ⟨Subgroup.mul_mem _ hs0 ht0, ?_⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hs0).1
  simp only [en] at hsd htd ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [hsN, hsd, htd]
  ring

end GlobalTheory.KZ

theorem GlobalTheory.KZ.isThB_act_sgD_diam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w a d : ℕ), a.Coprime N → d.Coprime N →
    ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b)) φ ↔
    IsThB X A N l n (X.act l (sgD N l (d * a) : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l hl n w a d ha hd b hb φ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hsa := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 ha
  have hsd := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 hd
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have e : X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b) =
      X.act l ((sgD N l a * sgD N l d : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
    rw [Matrix.SpecialLinearGroup.coe_mul, GlobalTheory.KZ.Tower.diam,
      GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b]
  rw [e]
  exact _root_.GlobalTheory.KZ.isThB_act_isDiam_iff Ω ε X A N l n w (d * a) b hb _ (GlobalTheory.KZ.isDiam_mul hsa hsd) φ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
section
noncomputable section

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.RecOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def fixA (A : ValuationSubring Ω) : Subring A where
  carrier := {a | ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a}
  one_mem' := fun s _ => by simp
  mul_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
    rw [map_mul, ha s hs, hb s hs]
  zero_mem' := fun s _ => by simp
  add_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
    rw [map_add (f := _), ha s hs, hb s hs]
  neg_mem' := fun {a} ha s hs => by
    show s (-(a : Ω)) = -(a : Ω)
    rw [map_neg, ha s hs]

theorem mem_fixA {A : ValuationSubring Ω} {a : A} : a ∈ fixA A ↔ ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a := Iff.rfl

abbrev dA (A : ValuationSubring Ω) : Derivation (fixA A) A (KaehlerDifferential (fixA A) A) :=
  KaehlerDifferential.D (fixA A) A

def cycAlg (l : ℕ) (A : ValuationSubring Ω) : Subalgebra (fixA A) A :=
  Algebra.adjoin (fixA A) {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}

theorem mem_cycAlg_of_pow {l : ℕ} {A : ValuationSubring Ω} {z : A} {n : ℕ} (h : z ^ (l ^ n) = 1) :
    z ∈ cycAlg l A := Algebra.subset_adjoin ⟨n, h⟩

def ineCyc (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) : Subgroup (G ℚ Ω) :=
  Ine (F := ℚ) A ⊓ (cycZ ℚ Ω l).ker

theorem mem_ineCyc {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {s : G ℚ Ω} :
    s ∈ ineCyc l A ↔ s ∈ Ine (F := ℚ) A ∧ cycZ ℚ Ω l s = 1 := Iff.rfl

abbrev FracA (A : ValuationSubring Ω) : Type := Ω ⧸ LinearMap.range (Algebra.linearMap A Ω)


omit [Algebra ℚ Ω] in
theorem mem_of_pow_mem (A : ValuationSubring Ω) {x : Ω} {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ∈ A) : x ∈ A := by
  rw [← A.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  by_contra hx
  push_neg at hx
  exact absurd h (not_le.2 (one_lt_pow' hx hn))

end GlobalTheory.RecOne
end
end

