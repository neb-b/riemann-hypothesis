module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0063

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumTriv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pKumTriv :
    UpperTheory.Kd.C7.SKumTriv := by
  intro l _ _ Ω _ _ _ A _ ζ hζ m n hnm u hu h
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
    exact ⟨⟨ζ i, (hζ i).1⟩, inferInstance⟩
  have hpos : 0 < l ^ n := pow_pos hp.pos n
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq u hpos
  refine ⟨v, hv, fun s hs => ?_⟩
  obtain ⟨w, hw, hsw⟩ := h s hs
  rw [ZMod.val_zero, pow_zero, one_mul] at hsw
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (v / w) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  have hc : cycMod ℚ Ω l m s = 1 := (Subgroup.mem_inf.1 hs).2
  have h2 : s (v / w) = v / w := fix_of_cycMod hnm hc h1
  have e : v = v / w * w := by field_simp
  calc s v = s (v / w * w) := by rw [← e]
    _ = v / w * w := by rw [map_mul, h2, hsw]
    _ = v := e.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PConj
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

theorem pConj : SConj := by
  intro l _ _ Ω _ _ _ A _ c Z hZ m s hs t ht
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hti : t⁻¹ ∈ Ine (F := ℚ) A := inv_mem ht
  have h1I : (1 : G ℚ Ω) ∈ Ine (F := ℚ) A := one_mem _
  refine ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hsI) hti, ?_⟩, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · have h0 : Z m 1 x = 0 := by
      have h := hZ.coc m 1 h1I 1 h1I x
      rw [mul_one, map_one, inv_one, mul_one] at h
      linear_combination -h
    have h2 := hZ.coc m t ht t⁻¹ hti x
    rw [mul_inv_cancel, h0] at h2
    have h3 := hZ.coc m t ht (s * t⁻¹) (mul_mem hsI hti) x
    have h4 := hZ.coc m s hsI t⁻¹ hti (x * (cycMod ℚ Ω l m t)⁻¹)
    rw [hsk, inv_one, mul_one] at h4
    rw [mul_assoc, h3, h4]
    linear_combination -h2

end UpperTheory.Kd.C7
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PEvHom
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem term_le {R K : Type} [CommRing R] [NormedField K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K)
    (h : PowerSeries R) (i : ℕ) : ‖f (h.coeff i) * t ^ i‖ ≤ ‖t‖ ^ i := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (hf _)

private theorem summ {R K : Type} [CommRing R] [NormedField K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K) (ht : ‖t‖ < 1)
    (h : PowerSeries R) : Summable fun i => ‖f (h.coeff i) * t ^ i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_le f hf t h)
    (summable_geometric_of_lt_one (norm_nonneg _) ht)

private theorem exE {R K : Type} [CommRing R] [NormedField K] [CompleteSpace K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1)
    (t : K) (ht : ‖t‖ < 1) : ∃ E : PowerSeries R →+* K, ∀ h, E h = ∑' i, f (h.coeff i) * t ^ i := by
  refine ⟨{ toFun := fun h => ∑' i, f (h.coeff i) * t ^ i
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩
  · rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [PowerSeries.coeff_one, hb]
  · intro a b
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summ f hf t ht a) (summ f hf t ht b)]
    refine tsum_congr fun n => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_mul, pow_add]; ring
  · simp
  · intro a b
    rw [← Summable.tsum_add (summ f hf t ht a).of_norm (summ f hf t ht b).of_norm]
    refine tsum_congr fun n => ?_
    rw [map_add (f := _), map_add (f := _), add_mul]

private theorem tail {R K : Type} [CommRing R] [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K) (ht : ‖t‖ < 1) (h : PowerSeries R) (N : ℕ) :
    ‖(∑' i, f (h.coeff i) * t ^ i) - ∑ i ∈ Finset.range N, f (h.coeff i) * t ^ i‖ ≤ ‖t‖ ^ N := by
  rw [← (summ f hf t ht h).of_norm.sum_add_tsum_nat_add N, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
  exact (term_le f hf t h _).trans (pow_le_pow_of_le_one (norm_nonneg _) ht.le (by omega))

private theorem rootb {K : Type} [NormedField K] [IsUltrametricDist K] (l m : ℕ) (hl : l.Prime) (h2 : l ≠ 2)
    (z : K) (hz : z ^ l ^ m = 1) : ‖z - 1‖ ^ l ^ m ≤ ‖(l : K)‖ :=
  _root_.UpperTheory.Reformulated.B.Qh18.rootb l m hl h2 z hz

theorem UpperTheory.Kd.C7.pEvHom :
    UpperTheory.Kd.C7.SEvHom := by
  intro l hl h2 Ω _ _ _ A _ j Φ m hm z hz
  have hb := rootb l m hl.out h2 z hz.pow_eq_one
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have ht : ‖z - 1‖ < 1 := by
    by_contra hc
    exact absurd (hb.trans_lt hl1) (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  obtain ⟨E, hE⟩ := exE Φ.jh Φ.jh_le (z - 1) ht
  have hC : ∀ x, E (PowerSeries.C x) = Φ.jh x := by
    intro x
    rw [hE, tsum_eq_single 0]
    · simp
    · intro b hb; simp [PowerSeries.coeff_C, hb]
  have hX : E (1 + PowerSeries.X) = z := by
    rw [map_add (f := _), map_one, hE, tsum_eq_single 1]
    · simp
    · intro b hb; simp [PowerSeries.coeff_X, hb]
  have hcyc : E (GlobalTheory.Col.cyc Φ.R l m) = 0 := by
    have : E.comp PowerSeries.C = Φ.jh := RingHom.ext hC
    rw [GlobalTheory.Col.cyc, Polynomial.hom_eval₂, this, hX, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hz.isRoot_cyclotomic (pow_pos hl.out.pos m)
  refine ⟨Ideal.Quotient.lift _ E (fun a ha => ?_), fun y => ?_, hC, hX, fun h => ?_⟩
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hcyc, mul_zero]
  · obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := tail Φ.jh Φ.jh_le (z - 1) ht h 0
    rw [Ideal.Quotient.lift_mk, hE]
    simpa using this
  · rw [Ideal.Quotient.lift_mk, hE]
    refine (tail Φ.jh Φ.jh_le (z - 1) ht h _).trans ?_
    have hle : l ^ m * m ≤ l ^ (3 * m) := by
      rw [show 3 * m = m + 2 * m by ring, pow_add]
      exact Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.lt_pow_self hl.out.one_lt).le)
    refine (pow_le_pow_of_le_one (norm_nonneg _) ht.le hle).trans ?_
    rw [pow_mul, norm_pow]
    exact pow_le_pow_left₀ (by positivity) hb m
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PowCompPow
section
noncomputable section

open GlobalTheory.Col

namespace UpperTheory.Kd.C7

private theorem cyc_charP (S : Type) [CommRing S] (p : ℕ) [hp : Fact p.Prime] [CharP S p] (j : ℕ) :
    cyc S p (j + 1) = PowerSeries.X ^ (p ^ (j + 1) - p ^ j) := by
  have h := Polynomial.cyclotomic_mul_prime_pow_eq S (p := p) (m := 1) (by simpa using hp.out.one_lt.ne') (k := j + 1) (Nat.succ_pos j)
  rw [mul_one, Polynomial.cyclotomic_one] at h
  rw [cyc, h, Polynomial.eval₂_pow]
  simp

private theorem dvd_of_map {R : Type} [CommRing R] (p : ℕ) (h : PowerSeries R)
    (H : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) h = 0) :
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) * h' := by
  have : ∀ k, ∃ y : R, y * p = PowerSeries.coeff k h := by
    intro k
    have := congrArg (PowerSeries.coeff k) H
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this
    exact Ideal.mem_span_singleton'.1 this
  choose y hy using this
  refine ⟨PowerSeries.mk y, ?_⟩
  ext k
  rw [← map_natCast (PowerSeries.C (R := R)), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hy, mul_comm]

private theorem step {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime] (hpr : Prime (p : R))
    (h : PowerSeries R) (c m₀ : ℕ)
    (H : ∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b) :
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) * h' ∧ ∀ m, m₀ + c + 1 ≤ m →
      ∃ a b : PowerSeries R, h' = (p : PowerSeries R) ^ (m - (c + 1)) * a + cyc R p m * b := by
  set π := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hπ
  haveI : Nontrivial (R ⧸ Ideal.span {(p : R)}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact hpr.not_isUnit)
  have hp0 : ((p : ℕ) : R ⧸ Ideal.span {(p : R)}) = 0 := by
    rw [← map_natCast π]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0
  have hp1 : ((p : ℕ) : PowerSeries (R ⧸ Ideal.span {(p : R)})) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := R ⧸ Ideal.span {(p : R)})), hp0, map_zero]
  have key : ∀ j, c ≤ j → ∀ a b : PowerSeries R, h = (p : PowerSeries R) ^ (j + 1 - c) * a + cyc R p (j + 1) * b →
      PowerSeries.map π h = PowerSeries.X ^ (p ^ (j + 1) - p ^ j) * PowerSeries.map π b := by
    intro j hj a b hab
    rw [hab, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, hp1, zero_pow (by omega), zero_mul, zero_add,
      coeffMap_cyc, cyc_charP]
  have h0 : PowerSeries.map π h = 0 := by
    ext k
    obtain ⟨a, b, hab⟩ := H (m₀ + c + k + 1) (by omega)
    have h1 := key (m₀ + c + k) (by omega) a b hab
    have h2 : k < p ^ (m₀ + c + k + 1) - p ^ (m₀ + c + k) := by
      have h3 : m₀ + c + k < p ^ (m₀ + c + k) := Nat.lt_pow_self hp.out.one_lt
      have h4 : p ^ (m₀ + c + k) * 2 ≤ p ^ (m₀ + c + k + 1) := by
        rw [pow_succ]; exact Nat.mul_le_mul_left _ hp.out.two_le
      omega
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 ⟨_, h1⟩ k h2
  obtain ⟨h', hh'⟩ := dvd_of_map p h h0
  refine ⟨h', hh', fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a, b, hab⟩ := H (j + 1) (by omega)
  have h1 := key j (by omega) a b hab
  rw [h0] at h1
  have h2 : PowerSeries.map π b = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff (k + (p ^ (j + 1) - p ^ j))) h1
    rw [PowerSeries.coeff_X_pow_mul] at this
    simpa using this.symm
  obtain ⟨b', hb'⟩ := dvd_of_map p b h2
  refine ⟨a, b', ?_⟩
  have hne : ((p : ℕ) : PowerSeries R) ≠ 0 := by
    rw [← map_natCast (PowerSeries.C (R := R))]
    intro h3
    exact hpr.ne_zero (by simpa using congrArg (PowerSeries.coeff 0) h3)
  apply mul_left_cancel₀ hne
  have e : j + 1 - c = (j + 1 - (c + 1)) + 1 := by omega
  rw [← hh', hab, hb', e]
  ring

private theorem allDvd {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime] (hpr : Prime (p : R)) (n : ℕ) :
    ∀ (h : PowerSeries R) (c m₀ : ℕ),
    (∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b) →
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) ^ n * h' := by
  induction n with
  | zero => intro h _ _ _; exact ⟨h, by simp⟩
  | succ n ih =>
    intro h c m₀ H
    obtain ⟨h', e, H'⟩ := step p hpr h c m₀ H
    obtain ⟨h'', e'⟩ := ih h' (c + 1) (m₀ + c + 1) H'
    exact ⟨h'', by rw [e, e']; ring⟩

private theorem pow_comp_pow {R : Type} [CommRing R] (σ : R ≃+* R) (m : ℕ) (x : R) :
    ((σ : R →+* R) ^ m) ((((σ.symm : R ≃+* R) : R →+* R) ^ m) x) = x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (σ : R →+* R), pow_succ' ((σ.symm : R ≃+* R) : R →+* R)]
    simp only [RingHom.mul_def, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact ih x

theorem pUniq : SUniq := by
  intro R _ p hp σ hF h c m₀ H
  haveI := hF.dom
  haveI := hF.complete
  have H' : ∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b := by
    intro m hm
    have h1 := H m hm
    rw [LC, map_zero, sub_zero] at h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_natCast (ev R p m), ← map_pow, ← map_mul, eq_comm, Ideal.Quotient.eq] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hy
    have h2 := congrArg (PowerSeries.map ((σ : R →+* R) ^ m)) hb
    have h3 : PowerSeries.map ((σ : R →+* R) ^ m) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ m) h) = h := by
      ext k
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map, pow_comp_pow]
    rw [map_sub, h3, map_mul, map_mul, map_pow, map_natCast, coeffMap_cyc] at h2
    exact ⟨PowerSeries.map ((σ : R →+* R) ^ m) a, PowerSeries.map ((σ : R →+* R) ^ m) b, by linear_combination -h2⟩
  ext k
  rw [map_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : R)}) inferInstance _ fun n => ?_
  obtain ⟨h', e⟩ := allDvd p hF.prime n h c m₀ H'
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨PowerSeries.coeff k h', ?_⟩
  rw [e, ← map_natCast (PowerSeries.C (R := R)), ← map_pow, PowerSeries.coeff_C_mul, mul_comm]

end UpperTheory.Kd.C7
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

private theorem roots_pow {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : Roots l ζ) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, (h (n + d)).2, ih]

private theorem nat_le_one {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem add_le {l : ℕ} [Fact l.Prime] {a b : Qbar l} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)

theorem pPresMono : SPresMono := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z Z' m n n' P hn hZ hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hlp.pos i).ne'⟩
    infer_instance
  haveI : NeZero (l ^ n') := ⟨(pow_pos hlp.pos n').ne'⟩
  refine ⟨(hζ n').1, hn.trans h2, h3, h4, fun s hs hc _ => ?_⟩
  obtain ⟨k, hk, hcg⟩ := h5 s hs hc (fix_of_cycMod h2 hc h1.pow_eq_one)
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hk i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm d n', hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, roots_pow hζ, ZMod.val_natCast]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n'), pow_add, pow_mul, (hζ n').1.pow_eq_one, one_pow, one_mul]
  · have hz := hZ s ⟨hs, hc⟩
    unfold Cg at hz hcg ⊢
    have e1 : ‖Z m s 1 - ∑ i, β.val i * (((k i).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine hcg.trans ?_
      rw [pow_add, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      exact_mod_cast nat_le_one (l := l) (l ^ d)
    have e2 : ‖∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ 1 := by
      refine Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ 1) (fun a b => add_le) (by simp) (fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_one₀ (h4 i) (norm_nonneg _) (nat_le_one _)
    have e3 : ‖((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) e2
    rw [norm_sub_rev] at hz
    have e4 : ∑ i, β.val i * (((k i).val : ℕ) : Qbar l) =
        ((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l)) +
        ∑ i, β.val i * (((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZMod.val_natCast]
      conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n')]
      push_cast
      ring
    have := add_le (add_le hz e1) e3
    rw [e4] at this
    convert this using 2
    ring

end UpperTheory.Kd.C7
end
end

