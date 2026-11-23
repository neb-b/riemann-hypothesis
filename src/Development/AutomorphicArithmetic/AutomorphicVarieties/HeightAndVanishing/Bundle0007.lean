module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CmDatumCharTwoAdicOrderBounds
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem arith (l a o : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (ho : 0 < o) (ha : a ∣ 2 * o) (hla : ¬ l ∣ a) :
    0 < orderOf (l : ZMod (Nat.lcm 4 a)) ∧ 2 ≤ (l ^ orderOf (l : ZMod (Nat.lcm 4 a)) - 1).factorization 2 ∧
      2 ^ (l ^ orderOf (l : ZMod (Nat.lcm 4 a)) - 1).factorization 2 < l ^ Nat.totient (4 * o) := by
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    omega
  set M := Nat.lcm 4 a with hM
  have hMdvd : M ∣ 4 * o :=
    Nat.lcm_dvd (Dvd.intro o rfl) (ha.trans (Nat.mul_dvd_mul_right (by norm_num : 2 ∣ 4) o))
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0] at hMdvd
      have := Nat.eq_zero_of_zero_dvd hMdvd
      omega
    · exact h0
  have hcop : l.Coprime M := by
    rw [hl.coprime_iff_not_dvd]
    intro hdvd
    have h4a : l ∣ 4 * a := hdvd.trans (Nat.lcm_dvd (dvd_mul_right 4 a) (dvd_mul_left a 4))
    rcases (Nat.Prime.dvd_mul hl).mp h4a with h4 | ha'
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
        (hl.dvd_of_dvd_pow (show l ∣ 2 ^ 2 by simpa using h4)))
    · exact hla ha'
  have hpow : (l : ZMod M) ^ Nat.totient M = 1 := by
    have h1 := Nat.ModEq.pow_totient hcop
    have h2 : ((l ^ Nat.totient M : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    simpa using h2
  have htot : 0 < Nat.totient M := Nat.totient_pos.2 hMpos
  have hfpos : 0 < orderOf (l : ZMod M) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, htot, hpow⟩)
  set f := orderOf (l : ZMod M) with hf
  have hlf : (l : ZMod M) ^ f = 1 := pow_orderOf_eq_one _
  have hmod : l ^ f ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact hlf
  have h4 : 4 ∣ l ^ f - 1 := by
    have hM4 : 4 ∣ M := Nat.dvd_lcm_left 4 a
    exact hM4.trans ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp hmod.symm)
  have hne : l ^ f - 1 ≠ 0 := by
    have : l ≤ l ^ f := Nat.le_self_pow (by omega) l
    omega
  have hv : 2 ≤ (l ^ f - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp (by simpa using h4)
  have hfle : f ≤ Nat.totient (4 * o) := by
    have h1 : f ∣ Nat.totient M := orderOf_dvd_of_pow_eq_one hpow
    have h2 : Nat.totient M ∣ Nat.totient (4 * o) := Nat.totient_dvd_of_dvd hMdvd
    exact Nat.le_of_dvd (Nat.totient_pos.2 (by omega)) (h1.trans h2)
  refine ⟨hfpos, hv, ?_⟩
  calc 2 ^ (l ^ f - 1).factorization 2 ≤ l ^ f - 1 := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd _ _)
    _ < l ^ f := by omega
    _ ≤ l ^ Nat.totient (4 * o) := Nat.pow_le_pow_right (by omega) hfle

theorem UpperTheory.V.HV.cmDatum_char_two_adic_order_bounds :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 →
      0 < f0 l ψ ∧ 2 ≤ n0 l ψ ∧ 2 ^ n0 l ψ < l ^ Nat.totient (4 * h.o) ∧ h.R1 l ψ ≤ 16 * h.o * (l * h.q) ^ 2 * l ^ (2 * Nat.totient (4 * h.o)) ∧
      (h.R1 l ψ ≤ 2 ^ c2 ψ → 12 ≤ c2 ψ ∧ ∀ v ∈ Tb l ψ, 8 * h.o * v ^ 2 < 2 ^ c2 ψ) := by
  intro h O _ _ ψ hψ l hl hl2
  have ho : 0 < h.o := by
    haveI := h.chi.ne
    exact orderOf_pos _
  have hq : 0 < h.q := Nat.pos_of_neZero h.q
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    omega
  have hlq : 0 < l * h.q := Nat.mul_pos (by omega) hq
  obtain ⟨-, -, ha, hla, -⟩ := hostTh1 h O ψ hψ l hl hl2
  obtain ⟨hf, hn, hlt⟩ := arith l (orderOf (th1 l ψ)) h.o hl hl2 ho ha hla
  have hn' : 2 ≤ n0 l ψ := hn
  have hlt' : 2 ^ n0 l ψ < l ^ Nat.totient (4 * h.o) := hlt
  have hR1 : h.R1 l ψ = 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := rfl
  have hR : h.R1 l ψ ≤ 16 * h.o * (l * h.q) ^ 2 * l ^ (2 * Nat.totient (4 * h.o)) := by
    rw [hR1]
    apply Nat.mul_le_mul_left
    calc 4 ^ n0 l ψ = (2 ^ n0 l ψ) ^ 2 := by
          rw [← pow_mul', pow_mul]
          norm_num
      _ ≤ (l ^ Nat.totient (4 * h.o)) ^ 2 := Nat.pow_le_pow_left hlt'.le 2
      _ = l ^ (2 * Nat.totient (4 * h.o)) := (pow_mul' l 2 _).symm
  refine ⟨hf, hn', hlt', hR, fun hc => ?_⟩
  have hpos : 0 < h.o * (l * h.q) ^ 2 := Nat.mul_pos ho (pow_pos hlq 2)
  have h4 : 16 ≤ 4 ^ n0 l ψ := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n0 l ψ := Nat.pow_le_pow_right (by norm_num) hn'
  constructor
  · have h9 : 9 ≤ (l * h.q) ^ 2 := by
      have h3 : 3 ≤ l * h.q := le_trans hl3 (Nat.le_mul_of_pos_right l hq)
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ (l * h.q) ^ 2 := Nat.pow_le_pow_left h3 2
    have hbig : 2 ^ 11 < 2 ^ c2 ψ := by
      calc 2 ^ 11 < 16 * 1 * 9 * 16 := by norm_num
        _ ≤ 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (show 1 ≤ h.o from ho)) h9) h4
        _ = h.R1 l ψ := hR1.symm
        _ ≤ 2 ^ c2 ψ := hc
    by_contra hlt2
    have hle : 2 ^ c2 ψ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro v hv
    have hvd : v ∣ l * h.q := (hostSb h O ψ hψ l hl hl2).2.2.2.2 v hv
    have hvle : v ≤ l * h.q := Nat.le_of_dvd hlq hvd
    have h8 : 8 < 16 * 4 ^ n0 l ψ := by omega
    calc 8 * h.o * v ^ 2 ≤ 8 * h.o * (l * h.q) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvle 2)
      _ = (h.o * (l * h.q) ^ 2) * 8 := by ring
      _ < (h.o * (l * h.q) ^ 2) * (16 * 4 ^ n0 l ψ) := Nat.mul_lt_mul_of_pos_left h8 hpos
      _ = 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := by ring
      _ = h.R1 l ψ := hR1.symm
      _ ≤ 2 ^ c2 ψ := hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem eq_one_of_odd {Γ : Type} [Monoid Γ] {x : Γ} {k m : ℕ} (h1 : orderOf x ∣ 2 ^ k) (h2 : orderOf x ∣ m)
    (hm : Odd m) : x = 1 := by
  have hc : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h3 : orderOf x ∣ Nat.gcd (2 ^ k) m := Nat.dvd_gcd h1 h2
  rw [hc.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

private theorem cond_dvd (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N) (hψ : h.IsChar ψ)
    (h2 : comp 2 ψ = 1) (ho : ∀ p, p.Prime → p = h.q1 ∨ p = h.d → ∃ m, Odd m ∧ orderOf (comp p ψ) ∣ m) :
    ψ.conductor ∣ h.q := by
  have hN : h.N ≠ 0 := NeZero.ne _
  obtain ⟨-, -, -, -, -, hpf, hpow, hq1, hd, -⟩ := hostIndex h
  rw [(compCond O h.N ψ 2 Nat.prime_two).2.2.2.2.2 h.q h.q_dvd]
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpN : p ∣ h.N := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨hcond, hone, -⟩ := compCond O h.N ψ p hpp
  have c1 : comp p ψ = 1 → (comp p ψ).conductor = 1 := fun e => by
    rw [hcond, Nat.factorization_eq_zero_of_not_dvd (hone.mp e), pow_zero]
  by_cases h2p : p = 2
  · subst h2p
    rw [c1 h2]
    exact one_dvd _
  have hf : ψ.conductor.factorization p ≤ h.N.factorization p :=
    (Nat.factorization_le_iff_dvd ψ.conductor_ne_zero hN).mpr ψ.conductor_dvd_level p
  have hdvdp : (comp p ψ).conductor ∣ p ^ h.N.factorization p := by
    rw [hcond]
    exact Nat.pow_dvd_pow p hf
  have key : p = h.q1 ∨ p = h.d → (comp p ψ).conductor ∣ h.q := by
    intro hpe
    have hpp1 : p ^ h.N.factorization p = p := by
      rcases hpe with rfl | rfl
      exacts [hq1, hd]
    rw [hpp1] at hdvdp
    by_cases hpq : p ∣ h.q
    · exact hdvdp.trans hpq
    · obtain ⟨m, hm, hmd⟩ := ho p hpp hpe
      have hsq : comp p ψ ^ 2 = 1 := ((hostComp h O ψ hψ).2.2 p hpp h2p).2.2.1 hpq
      have e : comp p ψ = 1 :=
        eq_one_of_odd (k := 1) (by simpa using orderOf_dvd_of_pow_eq_one hsq) hmd hm
      rw [c1 e]
      exact one_dvd _
  by_cases hpe : p = h.q1 ∨ p = h.d
  · exact key hpe
  push_neg at hpe
  rcases (hpf p hpp).mp hpN with h2' | hpq | hq1' | hd'
  · exact absurd h2' h2p
  · rw [hpow p hpp h2p hpe.1 hpe.2] at hdvdp
    exact hdvdp.trans (Nat.ordProj_dvd _ _)
  · exact absurd hq1' hpe.1
  · exact absurd hd' hpe.2

private theorem comp_two_eq_one (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N)
    (ho : Odd (orderOf ψ)) : comp 2 ψ = 1 := by
  obtain ⟨k, hk⟩ := (compOrd O N ψ 2 Nat.prime_two).2.1
  have hd : orderOf (comp 2 ψ) ∣ orderOf ψ := ((compAlg O N 2 Nat.prime_two).2.2.2.2.2.1 ψ).2.1
  exact eq_one_of_odd (k := k) (hk ▸ dvd_refl _) hd ho

theorem UpperTheory.V.HV.hostOdd :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ →
      (Odd (orderOf ψ) → orderOf ψ ∣ ordCompl[2] h.o ∧ psi2 ψ = 1 ∧ c2 ψ = 0 ∧ Odd ψ.conductor ∧ ψ.conductor ∣ h.q) ∧
      ∀ l, l.Prime → l ≠ 2 → l ≠ h.q1 → l ≠ h.d → Odd (orderOf (chiP l ψ)) → ψ.conductor ∣ h.q ∧ psi2 ψ = 1 := by
  intro h O _ _ ψ hψ
  obtain ⟨hord, hpos, -⟩ := hostComp h O ψ hψ
  refine ⟨fun hodd => ?_, fun l hl hl2 hlq1 hld hodd => ?_⟩
  · have h2 : comp 2 ψ = 1 := comp_two_eq_one O h.N ψ hodd
    have hcd : ψ.conductor ∣ h.q := cond_dvd h O ψ hψ h2
      (fun p hp _ => ⟨orderOf ψ, hodd, ((compAlg O h.N p hp).2.2.2.2.2.1 ψ).2.1⟩)
    obtain ⟨hc2eq, hone2, -⟩ := compCond O h.N ψ 2 Nat.prime_two
    have hnd : ¬ 2 ∣ ψ.conductor := hone2.mp h2
    refine ⟨?_, h2, ?_, ?_, hcd⟩
    · have hco : Nat.Coprime (orderOf ψ) (2 ^ (h.ex + 1)) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
      have hdo : orderOf ψ ∣ h.o := hco.dvd_of_dvd_mul_left hord
      exact Nat.dvd_ordCompl_of_dvd_not_dvd hdo (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])
    · show (comp 2 ψ).conductor.factorization 2 = 0
      rw [hc2eq, Nat.factorization_eq_zero_of_not_dvd hnd]
      simp
    · rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
  · obtain ⟨-, -, -, -, -, -, hc2chi, -, -, hcomp_eq, -⟩ := hostTh1 h O ψ hψ l hl hl2
    have hpsi : psi2 ψ = 1 := by
      rw [← hc2chi]
      exact comp_two_eq_one O h.N _ hodd
    refine ⟨cond_dvd h O ψ hψ hpsi ?_, hpsi⟩
    intro p hp hpe
    have hpl : p ≠ l := by
      rcases hpe with rfl | rfl
      exacts [hlq1.symm, hld.symm]
    obtain ⟨hkap, -⟩ := partOrd _ l hl ψ hpos
    refine ⟨orderOf (chiP l ψ) * l ^ (orderOf ψ).factorization l,
      Odd.mul hodd (Odd.pow (hl.odd_of_ne_two hl2)), ?_⟩
    have e : comp p ψ = comp p (th0 l ψ) * comp p (kap l ψ) := by
      rw [← (compAlg O h.N p hp).2.1, dirichletPrimeToLPart_mul_lPowerPart]
    rw [e]
    refine (Commute.all _ _).orderOf_mul_dvd_mul_orderOf.trans (Nat.mul_dvd_mul ?_ ?_)
    · rw [← hcomp_eq p hp hpl]
      exact ((compAlg O h.N p hp).2.2.2.2.2.1 _).2.1
    · have hk := ((compAlg O h.N p hp).2.2.2.2.2.1 (kap l ψ)).2.1
      rw [show kap l ψ = lPart l ψ from rfl, hkap] at hk
      exact hk
end

