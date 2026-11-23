module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Cases
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.cases :
    ∀ (h : Host) (t : ℕ), h.Big t → ∀ (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l e : ℕ, l.Prime → l ≠ 2 → 0 < e → e < t →
      (l ∉ Bchi h.chi → ¬ l ∣ orderOf ψ ∧ comp l ψ ^ 2 = 1 ∧ th0 l ψ = ψ ∧ kap l ψ = 1 ∧ (l - 1 ∣ 2 * e → chiP l ψ = ψ) ∧
        (h.CaseI l e ∨ h.CaseZ l e ψ ∨ h.CaseII l e ψ ∨ h.CaseIII l e ψ)) ∧
      (l ∈ Bchi h.chi → h.CaseII l e ψ ∨ h.CaseIV l e ψ ∨ h.CaseV l e) := by
  intro h t hbig O _ _ ψ hψ l e hl hl2 he het
  have hB := bchiFacts h t hbig
  have hC := hostComp h O ψ hψ
  refine ⟨fun hnB => ?_, fun hinB => ?_⟩
  · obtain ⟨_, hlo, hlq, _, _, _, _, hE⟩ := hB.2.2.2.2 l hl hl2 hnB
    have hCl := hC.2.2 l hl hl2
    have hord : ¬ l ∣ orderOf ψ := by
      intro hd
      have hd' := hd.trans hC.1
      rcases (Nat.Prime.dvd_mul hl).1 hd' with h2 | h2
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h2))
      · exact hlo h2
    have hP := (partOrd _ l hl ψ hC.2.1).2.2.2.2.2.1 hord
    have hth : th0 l ψ = ψ := hP.2
    have hchi : l - 1 ∣ 2 * e → chiP l ψ = ψ := by
      intro hdiv
      have hc1 : comp l ψ = 1 := hCl.2.2.2 (hE e he het hdiv).2.2
      show th0 l ψ * (comp l (th0 l ψ))⁻¹ = ψ
      rw [hth, hc1, inv_one, mul_one]
    refine ⟨hord, hCl.2.2.1 hlq, hth, hP.1, hchi, ?_⟩
    by_cases hdiv : l - 1 ∣ 2 * e
    · by_cases h1 : ψ = 1
      · exact Or.inr (Or.inl ⟨hnB, hdiv, h1⟩)
      · by_cases hodd : Odd (orderOf ψ)
        · exact Or.inr (Or.inr (Or.inr ⟨hnB, hdiv, hodd, h1⟩))
        · refine Or.inr (Or.inr (Or.inl ⟨(hE e he het hdiv).1, ?_, Or.inr hdiv⟩))
          show Even (orderOf (chiP l ψ))
          rw [hchi hdiv]
          exact Nat.not_odd_iff_even.mp hodd
    · exact Or.inl ⟨hnB, hdiv⟩
  · by_cases he1 : e = 1
    · exact Or.inr (Or.inr ⟨hinB, he1⟩)
    · have h2e : 2 ≤ e := by omega
      by_cases hev : Even (orderOf (chiP l ψ))
      · exact Or.inl ⟨h2e, hev, Or.inl hinB⟩
      · exact Or.inr (Or.inl ⟨hinB, h2e, Nat.not_even_iff_odd.mp hev⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostSb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem kap_pow {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (hψ : 0 < orderOf ψ)
    (l : ℕ) (hl : l.Prime) : ∃ s, kap l ψ ^ l ^ s = 1 := by
  refine ⟨(orderOf ψ).factorization l, ?_⟩
  rw [← (partOrd _ l hl ψ hψ).1]
  exact pow_orderOf_eq_one _

private theorem comp_kap_iff {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N)
    (hψ : 0 < orderOf ψ) (l : ℕ) (hl : l.Prime) (p : ℕ) (hp : p.Prime) :
    comp p (kap l ψ) = 1 ↔ ¬ l ∣ orderOf (comp p ψ) := by
  obtain ⟨h1, -, h3, -⟩ := partOrd _ l hl ψ hψ
  obtain ⟨-, hmul, -, -, -, hsub, -⟩ := compAlg O N p hp
  have hsplit : comp p ψ = comp p (th0 l ψ) * comp p (kap l ψ) := by
    rw [← hmul, dirichletPrimeToLPart_mul_lPowerPart]
  have ha : ¬ l ∣ orderOf (comp p (th0 l ψ)) := fun hd => h3 (hd.trans (hsub _).2.1)
  have hb : orderOf (comp p (kap l ψ)) ∣ l ^ (orderOf ψ).factorization l := by
    rw [← h1]; exact (hsub _).2.1
  have hcop : (orderOf (comp p (th0 l ψ))).Coprime (orderOf (comp p (kap l ψ))) := by
    refine Nat.Coprime.coprime_dvd_right hb ?_
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 ha).symm
  rw [hsplit, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hl.dvd_mul]
  simp only [ha, false_or]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl).1 hb
  constructor
  · intro h1' hd
    rw [h1', orderOf_one] at hd
    exact hl.ne_one (Nat.dvd_one.1 hd)
  · intro hd
    rw [← orderOf_eq_one_iff, hi]
    rcases i with _ | i
    · exact pow_zero l
    · exfalso
      apply hd
      rw [hi]
      exact dvd_pow_self l (Nat.succ_ne_zero i)

private theorem ordProj_N (h : Host) (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hq : p ∣ h.q) :
    h.N.factorization p = h.q.factorization p := by
  obtain ⟨hq1, -, hd, -, hcop⟩ := h.pair
  have hq0 : h.q ≠ 0 := h.chi.ne.out
  have hqd0 : h.q1 * h.d ≠ 0 := mul_ne_zero hq1.ne_zero hd.ne_zero
  have h20 : (2 : ℕ) ^ (h.ex + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hl0 : (2 ^ (h.ex + 2)).lcm h.q ≠ 0 := Nat.lcm_ne_zero h20 hq0
  have hnd : ¬ p ∣ h.q1 * h.d := fun hd' =>
    hp.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd' hcop) hq)
  have h2nd : ¬ p ∣ 2 ^ (h.ex + 2) := fun h' =>
    h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
  show ((2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d)).factorization p = _
  rw [Nat.factorization_mul hl0 hqd0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd,
    add_zero, Nat.factorization_lcm h20 hq0, Finsupp.sup_apply, Nat.factorization_eq_zero_of_not_dvd h2nd]
  simp

theorem UpperTheory.V.HV.hostSb :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 →
      (∀ p ∈ Sb l ψ, p.Prime ∧ p ≠ 2 ∧ p ≠ l ∧ p ∣ h.q ∧ p ≡ 1 [MOD l]) ∧ (kap l ψ).conductor ∣ h.q ∧ comp 2 (kap l ψ) = 1 ∧
      (∀ p, p.Prime → p ≠ l → (p ∈ Sb l ψ ↔ l ∣ orderOf (comp p ψ))) ∧ ∀ v ∈ Tb l ψ, v ∣ l * h.q := by
  intro h O _ _ ψ hc l hl hl2
  haveI : NeZero h.N := ⟨h.N_pos.ne'⟩
  obtain ⟨-, hψ, hcomp⟩ := hostComp h O ψ hc
  obtain ⟨s, hs⟩ := kap_pow ψ hψ l hl
  have hlodd : ¬ l ∣ 2 := fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 hd)
  have hc2 : comp 2 (kap l ψ) = 1 := by
    obtain ⟨-, ⟨k, hk⟩, -⟩ := compOrd O h.N (kap l ψ) 2 Nat.prime_two
    obtain ⟨-, -, -, -, -, hsub, -⟩ := compAlg O h.N 2 Nat.prime_two
    have hdv : orderOf (comp 2 (kap l ψ)) ∣ l ^ s :=
      ((hsub _).2.1).trans (orderOf_dvd_of_pow_eq_one hs)
    rw [← orderOf_eq_one_iff, hk]
    rcases k with _ | k
    · exact pow_zero 2
    · exfalso
      rw [hk] at hdv
      have h2 : 2 ∣ l := Nat.prime_two.dvd_of_dvd_pow ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdv)
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).1 h2).symm
  have key : ∀ p, p.Prime → comp p (kap l ψ) ≠ 1 → p ≠ 2 ∧ p ∣ h.q := by
    intro p hp hne
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hne hc2
    refine ⟨hp2, ?_⟩
    by_contra hq
    obtain ⟨-, -, hsq, -⟩ := hcomp p hp hp2
    have h2 : orderOf (comp p ψ) ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq hq)
    exact hne ((comp_kap_iff ψ hψ l hl p hp).2 (fun hd => hlodd (hd.trans h2)))
  have hSb : ∀ p, p ∈ Sb l ψ ↔ p.Prime ∧ p ∣ h.N ∧ p ≠ l ∧ comp p (kap l ψ) ≠ 1 := by
    intro p
    simp only [Sb, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hd, -⟩, h1, h2⟩
      exact ⟨hp, hd, h1, h2⟩
    · rintro ⟨hp, hd, h1, h2⟩
      exact ⟨⟨hp, hd, h.N_pos.ne'⟩, h1, h2⟩
  refine ⟨?_, ?_, hc2, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpp, -, hpl, hne⟩ := (hSb p).1 hp
    obtain ⟨hp2, hpq⟩ := key p hpp hne
    exact ⟨hpp, hp2, hpl, hpq, ((compOrd O h.N (kap l ψ) p hpp).2.2.2 l s hl (Ne.symm hpl) hs hne).1⟩
  · obtain ⟨-, -, -, -, -, hall⟩ := compCond O h.N (kap l ψ) 2 Nat.prime_two
    rw [hall h.q h.q_dvd]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨hcd, hiff, -⟩ := compCond O h.N (kap l ψ) p hpp
    rw [hcd]
    by_cases hne : comp p (kap l ψ) = 1
    · rw [Nat.factorization_eq_zero_of_not_dvd (hiff.1 hne), pow_zero]
      exact one_dvd _
    · obtain ⟨hp2, hpq⟩ := key p hpp hne
      have hcl := DirichletCharacter.conductor_dvd_level (kap l ψ)
      have hc0 : (kap l ψ).conductor ≠ 0 := fun h0 => h.N_pos.ne' (Nat.eq_zero_of_zero_dvd (h0 ▸ hcl))
      have hle : (kap l ψ).conductor.factorization p ≤ h.q.factorization p := by
        rw [← ordProj_N h p hpp hp2 hpq]
        exact (Nat.factorization_le_iff_dvd hc0 h.N_pos.ne').2 hcl p
      exact (pow_dvd_pow p hle).trans (Nat.ordProj_dvd h.q p)
  · intro p hp hpl
    rw [hSb p]
    constructor
    · rintro ⟨-, -, -, hne⟩
      by_contra hd
      exact hne ((comp_kap_iff ψ hψ l hl p hp).2 hd)
    · intro hd
      refine ⟨hp, ?_, hpl, fun h1 => (comp_kap_iff ψ hψ l hl p hp).1 h1 hd⟩
      by_contra hN
      obtain ⟨-, -, -, -, -, hsub, -⟩ := compAlg O h.N p hp
      rw [(hsub ψ).2.2.1 hN, orderOf_one] at hd
      exact hl.ne_one (Nat.dvd_one.1 hd)
  · intro v hv
    simp only [Tb, Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact dvd_mul_right _ _
    · obtain ⟨hvp, -, -, hne⟩ := (hSb v).1 hv
      exact dvd_mul_of_dvd_right (key v hvp hne).2 _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrdProjNDvd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ordProj_N_dvd (h : Host) (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hq : p ∣ h.q) : ordProj[p] h.N ∣ h.q := by
  obtain ⟨hq1, _, hd, _, hcop⟩ := h.pair
  have hq0 : h.q ≠ 0 := h.chi.ne.out
  have hqd : ¬ p ∣ h.q1 * h.d := fun hpd =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpd hcop) hq)
  have hL0 : (2 ^ (h.ex + 2)).lcm h.q ≠ 0 := Nat.lcm_ne_zero (pow_ne_zero _ two_ne_zero) hq0
  have hM0 : h.q1 * h.d ≠ 0 := mul_ne_zero hq1.ne_zero hd.ne_zero
  have hlcm : ((2 ^ (h.ex + 2)).lcm h.q).factorization p = h.q.factorization p := by
    simp [Nat.factorization_lcm (pow_ne_zero _ two_ne_zero) hq0, Nat.factorization_pow,
      Nat.prime_two.factorization, Finsupp.single_apply, Ne.symm h2]
  show p ^ (Nat.factorization ((2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d))) p ∣ h.q
  rw [Nat.factorization_mul hL0 hM0, Finsupp.add_apply, hlcm,
    Nat.factorization_eq_zero_of_not_dvd hqd, add_zero]
  exact Nat.ordProj_dvd _ _

private theorem rem_comp {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) :
    comp r (χ * (comp r χ)⁻¹) = 1 ∧ (∀ p, p.Prime → p ≠ r → comp p (χ * (comp r χ)⁻¹) = comp p χ) ∧
      orderOf (χ * (comp r χ)⁻¹) ∣ orderOf χ := by
  have hA := compAlg O N r hr
  refine ⟨?_, fun p hp hpr => ?_, ?_⟩
  · rw [hA.2.1, hA.2.2.2.1, (hA.2.2.2.2.2.1 χ).1, mul_inv_cancel]
  · have hB := compAlg O N p hp
    rw [hB.2.1, hB.2.2.2.1, (hB.2.2.2.2.2.1 χ).2.2.2 r hr (Ne.symm hpr), inv_one, mul_one]
  · rw [orderOf_dvd_iff_pow_eq_one, mul_pow, inv_pow, pow_orderOf_eq_one,
      orderOf_dvd_iff_pow_eq_one.mp (hA.2.2.2.2.2.1 χ).2.1, inv_one, mul_one]

theorem UpperTheory.V.HV.hostTh1 :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 →
      comp 2 (th0 l ψ) = psi2 ψ ∧ th0 l ψ = psi2 ψ * th1 l ψ ∧ orderOf (th1 l ψ) ∣ 2 * h.o ∧ ¬ l ∣ orderOf (th1 l ψ) ∧
      Odd (th1 l ψ).conductor ∧ (th1 l ψ ^ 2).conductor ∣ h.q ∧ comp 2 (chiP l ψ) = psi2 ψ ∧ comp l (chiP l ψ) = 1 ∧
      ¬ l ∣ orderOf (chiP l ψ) ∧ (∀ r, r.Prime → r ≠ l → comp r (chiP l ψ) = comp r (th0 l ψ)) ∧
      ∀ r, r.Prime → r ≠ 2 → orderOf (comp r (th0 l ψ)) ∣ 2 * h.o := by
  intro h O _ _ ψ hψ l hl hl2
  have hC := hostComp h O ψ hψ
  have hpos := hC.2.1
  have hPO := partOrd _ l hl ψ hpos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ψ ^ n = th0 l ψ := by
    have hz : lPrime l ψ ∈ Subgroup.zpowers ψ := hPO.2.2.2.2.1
    rw [← (orderOf_pos_iff.mp hpos).mem_powers_iff_mem_zpowers] at hz
    exact (Submonoid.mem_powers_iff _ _).mp hz
  have hcθ : ∀ r, r.Prime → comp r (th0 l ψ) = comp r ψ ^ n := fun r hr => by
    rw [← hn, (compAlg O h.N r hr).2.2.2.2.1]
  have h11 : ∀ r, r.Prime → r ≠ 2 → orderOf (comp r (th0 l ψ)) ∣ 2 * h.o := fun r hr hr2 => by
    rw [hcθ r hr]
    exact (orderOf_pow_dvd n).trans (hC.2.2 r hr hr2).1
  have hκ : comp 2 (kap l ψ) = 1 := by
    obtain ⟨a, ha⟩ := (compOrd O h.N (kap l ψ) 2 Nat.prime_two).2.1
    have hdk : orderOf (comp 2 (kap l ψ)) ∣ l ^ (orderOf ψ).factorization l := by
      rw [← hPO.1]
      exact ((compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.1 (kap l ψ)).2.1
    rw [← orderOf_eq_one_iff, ha]
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero]
    · exfalso
      rw [ha] at hdk
      have h2l := (dvd_pow_self 2 h0.ne').trans hdk
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).1 (Nat.prime_two.dvd_of_dvd_pow h2l)).symm
  have h1 : comp 2 (th0 l ψ) = psi2 ψ := by
    show comp 2 (th0 l ψ) = comp 2 ψ
    conv_rhs => rw [← dirichletPrimeToLPart_mul_lPowerPart l ψ]
    rw [(compAlg O h.N 2 Nat.prime_two).2.1, hκ, mul_one]
  have hR2 := rem_comp (th0 l ψ) 2 Nat.prime_two
  have hRl := rem_comp (th0 l ψ) l hl
  have hth1 : th1 l ψ = th0 l ψ * (comp 2 (th0 l ψ))⁻¹ := rfl
  have hchi : chiP l ψ = th0 l ψ * (comp l (th0 l ψ))⁻¹ := rfl
  have hc2 : comp 2 (th1 l ψ) = 1 := by
    rw [hth1]
    exact hR2.1
  have hcp : ∀ p, p.Prime → p ≠ 2 → comp p (th1 l ψ) = comp p (th0 l ψ) := fun p hp hp2 => by
    rw [hth1]
    exact hR2.2.1 p hp hp2
  have hnlθ : ¬ l ∣ orderOf (th0 l ψ) := hPO.2.2.1
  have hNpf : ∀ p ∈ h.N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  refine ⟨h1, ?_, ?_, fun hd => hnlθ (hd.trans (by rw [hth1]; exact hR2.2.2)), ?_, ?_, ?_, ?_,
    fun hd => hnlθ (hd.trans (by rw [hchi]; exact hRl.2.2)), fun r hr hrl => ?_, h11⟩
  · rw [hth1, h1, mul_comm, inv_mul_cancel_right]
  · apply orderOf_dvd_of_pow_eq_one
    apply (compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.2.2
    intro p hp
    by_cases hp2 : p = 2
    · subst hp2
      rw [hc2, one_pow]
    · rw [hcp p (hNpf p hp) hp2]
      exact orderOf_dvd_iff_pow_eq_one.mp (h11 p (hNpf p hp) hp2)
  · rw [hth1, (compCond O h.N (th0 l ψ) 2 Nat.prime_two).2.2.1]
    exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (th0 l ψ).conductor_ne_zero)
  · rw [(compCond O h.N (th1 l ψ ^ 2) 2 Nat.prime_two).2.2.2.2.2 h.q h.q_dvd]
    intro p hp
    have hpp := hNpf p hp
    by_cases hp2 : p = 2
    · subst hp2
      rw [(compAlg O h.N 2 Nat.prime_two).2.2.2.2.1, hc2, one_pow, DirichletCharacter.conductor_one]
      exact one_dvd _
    · by_cases hpq : p ∣ h.q
      · rw [(compCond O h.N (th1 l ψ ^ 2) p hpp).1]
        refine dvd_trans ?_ (ordProj_N_dvd h p hpp hp2 hpq)
        apply Nat.pow_dvd_pow
        exact (Nat.factorization_le_iff_dvd (th1 l ψ ^ 2).conductor_ne_zero (NeZero.ne h.N)).mpr
          (DirichletCharacter.conductor_dvd_level _) p
      · rw [(compAlg O h.N p hpp).2.2.2.2.1, hcp p hpp hp2, hcθ p hpp, ← pow_mul, mul_comm n 2, pow_mul,
          (hC.2.2 p hpp hp2).2.2.1 hpq, one_pow, DirichletCharacter.conductor_one]
        exact one_dvd _
  · rw [hchi, hRl.2.1 2 Nat.prime_two (Ne.symm hl2), h1]
  · rw [hchi]
    exact hRl.1
  · rw [hchi]
    exact hRl.2.1 r hr hrl
end

