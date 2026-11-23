module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwistedKernelFixed
section
namespace UpperTheory.Reformulated.B.TwistedKernelFixed

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

theorem aux2 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) {a b : V}
    (ha : a ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v})
    (hb : b ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v}) (h : H) :
    ρ h (a + b) = (χ h : k) • (a + b) := by
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem aux3 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) (h : H) :
    ρ h (0 : V) = (χ h : k) • (0 : V) := by
  rw [map_zero, smul_zero]

theorem aux4 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) (c : k) {v : V}
    (hv : v ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v}) (h : H) :
    ρ h (c • v) = (χ h : k) • c • v := by
  rw [map_smul, hv h, smul_comm]

noncomputable def eig {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) : Submodule k V where
  carrier := {v : V | ∀ h : H, ρ h v = (χ h : k) • v}
  add_mem' := @aux2 k G V _ _ _ _ ρ H χ
  zero_mem' := aux3 ρ H χ
  smul_mem' := aux4 ρ H χ

noncomputable def fixed {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : Submodule k V :=
  eig ρ H 1

noncomputable def twKer {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w : V | ∃ (n : N) (v : V), w = ρ n v - (ψ n : k) • v}

private theorem sum_shift {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : H →* (V →ₗ[ℂ] V)) (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)] (u : V)
    (hu : ∀ k ∈ K, ρ k u = u) (n : H) :
    ∑ q : H ⧸ K, ρ q.out (ρ n u) = ∑ q : H ⧸ K, ρ q.out u := by
  refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ K)) _ _ fun q => ?_
  have h1 : ((q.out * n : H) : H ⧸ K) = (((q * (n : H ⧸ K)).out : H) : H ⧸ K) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have h2 := hu _ (QuotientGroup.eq.mp h1)
  have h3 : (q * (n : H ⧸ K)).out = q.out * n * ((q.out * n)⁻¹ * (q * (n : H ⧸ K)).out) := by
    rw [mul_inv_cancel_left]
  rw [Equiv.coe_mulRight, h3, map_mul, Module.End.mul_apply, h2, map_mul, Module.End.mul_apply]

theorem eq_zero_of_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} [TopologicalSpace G] [IsTopologicalGroup G] (hs : IsSmooth π)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : v ∈ fixed π H)
    (hw : v ∈ twKer π H (1 : H →* ℂˣ)) : v = 0 := by
  classical
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have key : ∀ w ∈ twKer π H (1 : H →* ℂˣ),
      ∃ K : Subgroup H, K.FiniteIndex ∧ ∀ (L : Subgroup H) [L.Normal] [Fintype (H ⧸ L)], L ≤ K →
        ∑ q : H ⧸ L, π (q.out : H) w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, u, rfl⟩ := hx
      let K : Subgroup H :=
        { carrier := {h | π (h : G) u = u}
          mul_mem' := fun {a b} ha hb => by
            have ha' : π (a : G) u = u := ha
            have hb' : π (b : G) u = u := hb
            show π ((a : G) * b) u = u
            rw [map_mul, Module.End.mul_apply, hb', ha']
          one_mem' := by
            show π (1 : G) u = u
            rw [map_one, Module.End.one_apply]
          inv_mem' := fun {a} ha => by
            have ha' : π (a : G) u = u := ha
            show π ((a : G)⁻¹) u = u
            conv_lhs => rw [← ha']
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      have hK : IsOpen (K : Set H) := (hs u).preimage continuous_subtype_val
      have := Subgroup.quotient_finite_of_isOpen K hK
      refine ⟨K, Subgroup.finiteIndex_of_finite_quotient, fun L _ _ hL => ?_⟩
      have := sum_shift (π.comp H.subtype) L u (fun k hk => hL hk) n
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr this
    | zero => exact ⟨⊤, inferInstance, fun L _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, h₁, hx⟩ := hx
      obtain ⟨K₂, h₂, hy⟩ := hy
      refine ⟨K₁ ⊓ K₂, inferInstance, fun L _ _ hL => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [hx L (hL.trans inf_le_left), hy L (hL.trans inf_le_right), add_zero]
    | smul c x _ hx =>
      obtain ⟨K, h, hx⟩ := hx
      refine ⟨K, h, fun L _ _ hL => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, hx L hL, smul_zero]
  obtain ⟨K, hK, h⟩ := key v hw
  have : Fintype (H ⧸ K.normalCore) := Fintype.ofFinite _
  have h0 := h K.normalCore K.normalCore_le
  have hv' : ∀ g : H, π (g : G) v = v := fun g => by
    have := hv g
    simpa using this
  simp only [hv', Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h0
  exact (smul_eq_zero.mp h0).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end UpperTheory.Reformulated.B.TwistedKernelFixed
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnipotentExponentialSurjective
section
private theorem exp_second_order {A : Type} [CommRing A] [Algebra ℚ A] {y : A}
    (hy : IsNilpotent y) : ∃ d : A, IsNilpotent.exp y = 1 + y + y ^ 2 * d := by
  obtain ⟨k, hk⟩ := hy
  have h2 : y ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  refine ⟨∑ i ∈ Finset.range k, (((i + 2).factorial : ℚ)⁻¹) • y ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have h : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ)⁻¹) • y ^ (i + 1 + 1)
      = y ^ 2 * ((((i + 2).factorial : ℚ)⁻¹) • y ^ i) := by
    intro i _
    rw [mul_smul_comm, ← pow_add, add_comm 2 i]
  rw [Finset.sum_congr rfl h]
  simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    pow_one, pow_zero]
  ring

private theorem exp_approx {A : Type} [CommRing A] [Algebra ℚ A] {n : A}
    (hn : IsNilpotent n) (k : ℕ) :
    ∃ x c : A, IsNilpotent x ∧ IsNilpotent.exp x = 1 + n + n ^ (k + 1) * c := by
  induction k with
  | zero => exact ⟨0, -1, IsNilpotent.zero, by rw [IsNilpotent.exp_zero]; ring⟩
  | succ k ih =>
    obtain ⟨x, c, hx, he⟩ := ih
    have hy : IsNilpotent (n * (-(n ^ k * c))) :=
      (Commute.all _ _).isNilpotent_mul_right hn
    obtain ⟨d, hd⟩ := exp_second_order hy
    refine ⟨x + n * (-(n ^ k * c)),
      -c - n ^ k * c ^ 2 + (1 + n + n ^ (k + 1) * c) * (n ^ k * c ^ 2 * d),
      (Commute.all _ _).isNilpotent_add hx hy, ?_⟩
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hx hy, he, hd]
    ring

theorem UpperTheory.Reformulated.B.UnipotentExponentialSurjective.ul_exp_onto :
    ∀ {A : Type} [inst : CommRing A] [inst_1 : Algebra ℚ A] {n : A},
    IsNilpotent n → ∃ (x : A), IsNilpotent x ∧ IsNilpotent.exp x = (1 : A) + n := by
  intro A _ _ n hn
  obtain ⟨k, hk⟩ := id hn
  obtain ⟨x, c, hx, he⟩ := exp_approx hn k
  exact ⟨x, hx, by rw [he, pow_succ, hk, zero_mul, zero_mul, add_zero]⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnipotentFundamentalDomain
section
theorem UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K],
    Module.finrank ℚ K ≤ (2 : ℕ) →
      ∀ (P Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        P ≠ Q →
          Ideal.under ℤ P.asIdeal = Ideal.under ℤ Q.asIdeal →
            (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion K P → WithZero (Multiplicative ℤ))
                (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) P.asIdeal) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion K P) =
              WithZero.exp (-1 : ℤ) := by
  intro K _ _ hn P Q hPQ hunder
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have hQm : Q.asIdeal.IsMaximal := Q.isMaximal
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (IsDedekindDomain.HeightOneSpectrum.ext h)
  have hIprime : (Ideal.under ℤ P.asIdeal).IsPrime := Ideal.IsPrime.under ℤ P.asIdeal
  have hNP0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have hNmem : ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    simpa [Ideal.under_def, Ideal.mem_comap] using this
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.under ℤ P.asIdeal)).principal
  have hg' : Ideal.under ℤ P.asIdeal = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [hg', Ideal.mem_span_singleton] at hNmem
    exact hNP0 (by simpa using hNmem)
  have hgprime : Prime g := by
    rw [hg'] at hIprime
    exact (Ideal.span_singleton_prime hg0).1 hIprime
  set p : ℕ := g.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hgprime
  have hpI : (p : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    rw [hg', Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.2 dvd_rfl
  have hpP : (p : NumberField.RingOfIntegers K) ∈ P.asIdeal := by
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hpQ : (p : NumberField.RingOfIntegers K) ∈ Q.asIdeal := by
    rw [hunder] at hpI
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hnorm : Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers K)}) =
      p ^ Module.finrank ℚ K := by
    have h : (p : NumberField.RingOfIntegers K) =
        algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) := by simp
    rw [Ideal.absNorm_span_singleton, h, Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast, NumberField.RingOfIntegers.rank]
  have hdvd : P.asIdeal * Q.asIdeal ∣ Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime (hPm.coprime_of_ne hQm hne)]
    exact le_inf ((Ideal.span_singleton_le_iff_mem _).2 hpP)
      ((Ideal.span_singleton_le_iff_mem _).2 hpQ)
  obtain ⟨J, hJ⟩ := hdvd
  have hprod : p ^ Module.finrank ℚ K =
      Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal * Ideal.absNorm J := by
    rw [← hnorm, hJ, map_mul, map_mul]
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_assoc]) : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_comm (Ideal.absNorm P.asIdeal), mul_assoc]) :
      Ideal.absNorm Q.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro_left _ hprod.symm : Ideal.absNorm J ∣ p ^ Module.finrank ℚ K)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at ha
    exact hPm.ne_top ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hb
    exact hQm.ne_top hb
  have hexp : Module.finrank ℚ K = a + b + c := by
    apply Nat.pow_right_injective hp.two_le
    simp only
    rw [hprod, ha, hb, hc, pow_add, pow_add]
  have ha1 : a = 1 := by omega
  have hc0 : c = 0 := by omega
  have hNP : Ideal.absNorm P.asIdeal = p := by rw [ha, ha1, pow_one]
  have hJtop : J = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, hc, hc0, pow_zero]
  have hspan : Ideal.span {(p : NumberField.RingOfIntegers K)} = P.asIdeal * Q.asIdeal := by
    rw [hJ, hJtop, Ideal.mul_top]
  have hp0 : (p : NumberField.RingOfIntegers K) ≠ 0 := by
    intro h
    rw [h] at hnorm
    rw [Set.singleton_zero, Ideal.span_zero, Ideal.absNorm_bot] at hnorm
    exact pow_ne_zero _ hp.ne_zero hnorm.symm
  have h1 : P.intValuation (p : NumberField.RingOfIntegers K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_one]
    exact Dvd.intro _ rfl
  have h2 : ¬ P.intValuation (p : NumberField.RingOfIntegers K) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_two]
    intro h
    have h3 : P.asIdeal ∣ Q.asIdeal := (mul_dvd_mul_iff_left P.ne_bot).1 h
    exact hne (hQm.eq_of_le hPm.ne_top (Ideal.dvd_iff_le.1 h3)).symm
  have hval : P.intValuation (p : NumberField.RingOfIntegers K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hp0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    omega
  rw [hNP]
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) P
    (p : NumberField.RingOfIntegers K)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval] at key
  simpa using key
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitBall
section
noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

private def UpperTheory.Reformulated.B.UnitBallLemmas.unitBall (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv F →
        (MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F = (1 : ℂ_[p]) →
          ∃ (G : MvPowerSeries σ ℂ_[p]), UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv G ∧ F * G = (1 : MvPowerSeries σ ℂ_[p]) := by
  intro p _ σ F hF h1
  let F' : MvPowerSeries σ (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) :=
    fun n => ⟨MvPowerSeries.coeff n F, hF n⟩
  have hmap : MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype F' = F := by
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  have hc : MvPowerSeries.constantCoeff F' = ((1 : (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p)ˣ) : UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) := by
    apply Subtype.ext
    exact h1
  refine ⟨MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype (MvPowerSeries.invOfUnit F' 1), ?_, ?_⟩
  · intro n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n (MvPowerSeries.invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, MvPowerSeries.mul_invOfUnit F' 1 hc, map_one]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitBallSubring
section
private def unitBallSubring (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem UpperTheory.Reformulated.B.Qh18.rootb :
    ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] (l m : ℕ),
    Nat.Prime l → l ≠ (2 : ℕ) → ∀ (z : K), z ^ l ^ m = (1 : K) → ‖z - (1 : K)‖ ^ l ^ m ≤ ‖(↑l : K)‖ := by
  intro K _ _ l m hl _ z hz
  have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hz
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 h
  have hzS : z ∈ unitBallSubring K := hz1.le
  have hx : z - 1 ∈ unitBallSubring K := sub_mem hzS (one_mem _)
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (⟨z - 1, hx⟩ : unitBallSubring K) 1 m
  have hr' := congrArg (Subtype.val) hr
  push_cast at hr'
  have hrn : ‖(r : K)‖ ≤ 1 := r.2
  have hxn : ‖z - 1‖ ≤ 1 := hx
  rw [sub_add_cancel, hz] at hr'
  have e : (z - 1) ^ l ^ m = -((l : K) * ((z - 1) * (r : K))) := by
    simp only [one_pow, mul_one] at hr'
    linear_combination (-1 : K) * hr'
  rw [← norm_pow, e, norm_neg, norm_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ hxn (norm_nonneg _) hrn)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryGroupStatement
section
noncomputable def UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

theorem UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ}
      {x y : Module.End ℂ V},
      x ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j → y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k → x * y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
  intro n V _ _ E j k x y hx hy
  have h : UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j * UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k ≤ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
    unfold UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨a, ⟨l1, hl1, rfl⟩, b, ⟨l2, hl2, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨l1 ++ l2, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp [List.map_append, List.prod_append]
  exact h (Submodule.mul_mem_mul hx hy)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnramifiedAntiInvariantLocal
section
open NumberField

theorem UpperTheory.unramified_anti_invariant_local :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      Module.finrank F E = 2 →
      Algebra.Unramified (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E) →
      ∀ (ξ : E), ξ ≠ 0 → σ ξ = -ξ →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        ∃ (a b : NumberField.RingOfIntegers E) (n : NumberField.RingOfIntegers F),
          n ∉ v.asIdeal ∧ σ (a : E) = -(a : E) ∧ (a : E) * (b : E) = algebraMap F E (n : F) := by
  intro F E _ _ _ _ _ σ hr hU ξ hξ hσ v
  have hne : σ ξ ≠ ξ := by
    intro h
    rw [hσ] at h
    exact hξ (by linear_combination (-1 / 2 : E) * h)
  have hfix : ∀ y : E, σ y = y → ∃ c : F, algebraMap F E c = y := by
    intro y hy
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := hy
      rw [h] at this
      exact Algebra.mem_bot.mp this
    · have : ξ ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      exact absurd this hne
  have hinv : ∀ y : E, σ (σ y) = y := by
    intro y
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)) with h | h
    · have : ξ ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by
        show σ (σ ξ) = ξ
        rw [hσ, map_neg, hσ, neg_neg]
      rw [h] at this
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp this
      exact absurd (by rw [← hc, AlgHom.commutes]) hne
    · have : y ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by rw [h]; trivial
      exact this
  let τ : 𝓞 E →ₐ[𝓞 F] 𝓞 E := RingOfIntegers.mapAlgHom σ
  have hτ : ∀ x : 𝓞 E, ((τ x : 𝓞 E) : E) = σ x := fun _ => rfl
  have := v.isMaximal
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hx : ∃ x : 𝓞 E, x - τ x ∉ w := by
    by_contra hcon
    push Not at hcon
    have heq : AlgHom.id (𝓞 F) (𝓞 E) = τ :=
      Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw.ne_top)
        (fun x => Ideal.Quotient.eq.mpr (hcon x))
    have hall : ∀ x : 𝓞 E, σ x = x := fun x => by rw [← hτ, ← heq]; rfl
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ξ
    apply hne
    rw [← hpq, map_div₀]
    exact congrArg₂ (· / ·) (hall p) (hall q)
  obtain ⟨x, hx⟩ := hx
  set a : 𝓞 E := x - τ x with ha
  have hσa : σ (a : E) = -(a : E) := by
    have : (a : E) = x - σ x := by rw [← hτ]; rfl
    rw [this, map_sub, hinv, neg_sub]
  obtain ⟨c, hc⟩ := hfix ((a : E) * a) (by rw [map_mul, hσa, neg_mul_neg])
  have hci : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (B := E) , hc]
    exact a.isIntegral_coe.mul a.isIntegral_coe
  refine ⟨a, a, ⟨c, hci⟩, ?_, hσa, hc.symm⟩
  intro hn
  have h1 := (Ideal.mem_of_liesOver w v.asIdeal _).mp hn
  have h2 : algebraMap (𝓞 F) (𝓞 E) ⟨c, hci⟩ = a * a := by
    apply RingOfIntegers.ext
    exact hc
  rw [h2] at h1
  exact hx ((hw.isPrime.mem_or_mem h1).elim id id)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpperTriangularMul
section
theorem UpperTheory.Reformulated.B.Qe38.upper_triangular_mul :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (U T : Matrix (Fin n) (Fin n) K),
    (∀ (i j : Fin n), j < i → U i j = (0 : K)) →
      (∀ (i j : Fin n), j < i → T i j = (0 : K)) → ∀ (i j : Fin n), j < i → (U * T) i j = (0 : K) := by
  intro K _ n U T hU hT i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with hk | hk
  · rw [hU i k hk, zero_mul]
  · rw [hT k j (lt_of_lt_of_le hij hk), mul_zero]
end

