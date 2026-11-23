module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem pow_eq_self_of_sq {M : Type} [Monoid M] {x : M} {n j : ℕ} (h2 : x ^ 2 = 1) (hn : x ^ n = 1)
    (hj : j.Coprime n) : x ^ j = x := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h3 : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hn
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · rw [orderOf_eq_one_iff] at h
    simp [h]
  · have h2n : 2 ∣ n := h ▸ h3
    have hodd : ¬ 2 ∣ j := fun h2j =>
      absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2j hj) h2n) (by norm_num)
    obtain ⟨k, hk⟩ := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]

theorem UpperTheory.V.HV.gdFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] (l : ℕ) [Fact l.Prime] (e : ℕ) (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N]
      (ψ : DirichletCharacter O N), GD Ω K l e ψ → 5 ≤ l ∧ th0 l ψ = ψ ∧ kap l ψ = 1 ∧ chiP l ψ * comp l ψ = ψ ∧ comp l (chiP l ψ) = 1 ∧
        ¬ l ∣ orderOf (chiP l ψ) ∧ (comp l ψ ≠ 1 → l ∣ N ∧ (comp l ψ).conductor = l) ∧
        ∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker → GD Ω K l e ψ' ∧ comp l ψ' = comp l ψ := by
  intro Ω _ _ _ K _ _ _ l _ e O _ _ N _ ψ hG
  have hl : l.Prime := Fact.out
  have hpos : 0 < orderOf ψ := by
    rw [← (orbFacts O N ψ).1]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hA := compAlg O N l hl
  have hcc : comp l (comp l ψ) = comp l ψ := (hA.2.2.2.2.2.1 ψ).1
  have hcd : ∀ χ : DirichletCharacter O N, orderOf (comp l χ) ∣ orderOf χ :=
    fun χ => (hA.2.2.2.2.2.1 χ).2.1
  have hP := (partOrd _ l hl ψ hpos).2.2.2.2.2.1 hG.ord
  have hth : th0 l ψ = ψ := hP.2
  have hkap : kap l ψ = 1 := hP.1
  have hchi : chiP l ψ = ψ * (comp l ψ)⁻¹ := by
    show th0 l ψ * (comp l (th0 l ψ))⁻¹ = _
    rw [hth]
  have hcn : comp l ψ ^ orderOf ψ = 1 := orderOf_dvd_iff_pow_eq_one.mp (hcd ψ)
  have hcchi : comp l (chiP l ψ) = 1 := by
    rw [hchi, hA.2.1, hA.2.2.2.1, hcc, mul_inv_cancel]
  have hchid : orderOf (chiP l ψ) ∣ orderOf ψ := by
    rw [orderOf_dvd_iff_pow_eq_one, hchi, mul_pow, inv_pow, pow_orderOf_eq_one, hcn, inv_one, mul_one]
  refine ⟨?_, hth, hkap, ?_, hcchi, fun h => hG.ord (h.trans hchid), ?_, ?_⟩
  · by_contra h
    have h2 := hl.two_le
    have g := hG.gen
    have lo := hG.l_odd
    interval_cases l
    · exact lo rfl
    · exact g (dvd_mul_right 2 e)
    · norm_num at hl
  · rw [hchi, inv_mul_cancel_right]
  · intro hne
    refine ⟨?_, ?_⟩
    · by_contra hN
      exact hne ((hA.2.2.2.2.2.1 ψ).2.2.1 hN)
    · have hO := (compOrd O N (comp l ψ) l hl).2.2.2 2 1 Nat.prime_two (Ne.symm hG.l_odd)
        (by rw [pow_one]; exact hG.ine) (by rwa [hcc])
      rw [hcc] at hO
      exact hO.2
  · intro ψ' hker
    obtain ⟨j, hj, rfl⟩ := ((orbFacts O N ψ).2.2.1 ψ').1 hker
    have hcj : comp l (ψ ^ j) = comp l ψ := by
      rw [hA.2.2.2.2.1]
      exact pow_eq_self_of_sq hG.ine hcn hj
    refine ⟨?_, hcj⟩
    have hord : orderOf (ψ ^ j) = orderOf ψ := Nat.Coprime.orderOf_pow hj.symm
    have hP' : ¬ l ∣ orderOf (ψ ^ j) := by
      rw [hord]
      exact hG.ord
    have hth' : th0 l (ψ ^ j) = ψ ^ j :=
      ((partOrd _ l hl (ψ ^ j) (hord ▸ hpos)).2.2.2.2.2.1 hP').2
    have hchi' : chiP l (ψ ^ j) = chiP l ψ ^ j := by
      show th0 l (ψ ^ j) * (comp l (th0 l (ψ ^ j)))⁻¹ = _
      rw [hth', hcj, hchi, mul_pow, inv_pow, pow_eq_self_of_sq hG.ine hcn hj]
    have hkc : (MulChar.toUnitHom (chiP l (ψ ^ j))).ker = (MulChar.toUnitHom (chiP l ψ)).ker :=
      ((orbFacts O N (chiP l ψ)).2.2.1 _).2 ⟨j, Nat.Coprime.coprime_dvd_right hchid hj, hchi'⟩
    have hpow : ∀ (χ : DirichletCharacter O N) (k : ℕ), (χ ^ k) (-1) = χ (-1) ^ k := by
      intro χ k
      have h := MulChar.pow_apply_coe χ k (-1)
      rwa [Units.val_neg, Units.val_one] at h
    have h1 : (1 : DirichletCharacter O N) (-1) = 1 := by
      have h := MulChar.one_apply_coe (R' := O) (-1 : (ZMod N)ˣ)
      rwa [Units.val_neg, Units.val_one] at h
    have hpar : PsiEven e (ψ ^ j) := by
      show (ψ ^ j) (-1) = (-1) ^ e
      have hx2 : ψ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
      have hxn : ψ (-1) ^ orderOf ψ = 1 := by rw [← hpow, pow_orderOf_eq_one, h1]
      rw [hpow, pow_eq_self_of_sq hx2 hxn hj]
      exact hG.par
    have hk : (Chr.dirG ℚ Ω (chiP l (ψ ^ j))).ker = (Chr.dirG ℚ Ω (chiP l ψ)).ker := by
      unfold Chr.dirG
      rw [← MonoidHom.comap_ker, ← MonoidHom.comap_ker, hkc]
    exact
      { l_odd := hG.l_odd, e_pos := hG.e_pos, N_even := hG.N_even, ord := hP',
        ine := by rw [hcj]; exact hG.ine, par := hpar, quad := hG.quad, imag := hG.imag,
        l_cop := hG.l_cop, cop := hG.cop, eta := by rw [hk]; exact hG.eta, gen := hG.gen }
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem pow_eq_one_of {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (m : ℕ)
    (H : ∀ u : (ZMod N)ˣ, χ.toUnitHom u ^ m = 1) : χ ^ m = 1 := by
  refine MulChar.ext fun u => ?_
  have hu := congrArg Units.val (H u)
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one] at hu
  rw [MulChar.pow_apply_coe, hu, MulChar.one_apply_coe]

private theorem unitHom_pow_orderOf {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    χ.toUnitHom u ^ orderOf χ = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
    MulChar.one_apply_coe, Units.val_one]

theorem UpperTheory.V.HV.hostComp :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ →
      orderOf ψ ∣ 2 ^ (h.ex + 1) * h.o ∧ 0 < orderOf ψ ∧ ∀ r, r.Prime → r ≠ 2 →
        orderOf (comp r ψ) ∣ 2 * h.o ∧ (r ∣ h.q → orderOf (comp r ψ) ∣ h.o) ∧ (¬ r ∣ h.q → comp r ψ ^ 2 = 1) ∧ (¬ r ∣ h.N → comp r ψ = 1) := by
  intro h O _ _ ψ hψ
  have hI := hostIndex h
  have ho : 0 < h.o := hI.2.2.2.1
  have hmemK : ∀ x ∈ h.H, ψ.toUnitHom x = 1 := fun x hx => MonoidHom.mem_ker.mp (hψ hx)
  have hA : ψ ^ (2 ^ (h.ex + 1) * h.o) = 1 :=
    pow_eq_one_of ψ _ (fun u => by
      rw [← map_pow]
      exact hmemK _ (hI.2.2.2.2.2.2.2.2.2 u))
  refine ⟨orderOf_dvd_of_pow_eq_one hA,
    Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hA) (Nat.mul_pos (pow_pos two_pos _) ho), ?_⟩
  intro r hr hr2
  have facts := projFacts h.N r hr
  have hca := compAlg O h.N r hr
  have cu : ∀ u, (comp r ψ).toUnitHom u = ψ.toUnitHom (proj r h.N u) := hca.1 ψ
  have off : ∀ (M : ℕ) (hM : M ∣ h.N), ¬ r ∣ M → ∀ u, ZMod.unitsMap hM (proj r h.N u) = 1 :=
    facts.2.2.2.2.2.2.2.1
  have n2 : ¬ r ∣ 2 ^ (h.ex + 2) := fun hd =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  have sq : ¬ r ∣ h.q → comp r ψ ^ 2 = 1 := by
    intro hq
    refine pow_eq_one_of _ 2 (fun u => ?_)
    rw [cu, ← map_pow]
    apply hmemK
    simp only [Host.H, Subgroup.mem_inf]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.two_pow_dvd h) n2 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.q_dvd h) hq u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow]
      exact ⟨_, rfl⟩
    · rw [Subgroup.mem_comap, map_pow]
      exact ⟨_, rfl⟩
  have hcop := h.pair.2.2.2.2
  have dq : r ∣ h.q → comp r ψ ^ h.o = 1 := by
    intro hq
    have nq1 : ¬ r ∣ h.q1 := fun hd =>
      hr.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_of_dvd_left hd _) hcop) hq)
    have nd : ¬ r ∣ h.d := fun hd =>
      hr.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_of_dvd_right hd _) hcop) hq)
    refine pow_eq_one_of _ h.o (fun u => ?_)
    rw [cu, ← map_pow]
    apply hmemK
    simp only [Host.H, Subgroup.mem_inf]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.two_pow_dvd h) n2 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, MonoidHom.mem_ker, map_pow, map_pow]
      exact unitHom_pow_orderOf _ _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.host_q1_dvd_N h) nq1 u, one_pow]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_comap, map_pow, off _ (Host.d_dvd h) nd u, one_pow]
      exact Subgroup.one_mem _
  refine ⟨?_, fun hq => orderOf_dvd_of_pow_eq_one (dq hq), sq, (hca.2.2.2.2.2.1 ψ).2.2.1⟩
  by_cases hq : r ∣ h.q
  · exact (orderOf_dvd_of_pow_eq_one (dq hq)).trans (dvd_mul_left _ _)
  · exact (orderOf_dvd_of_pow_eq_one (sq hq)).trans (dvd_mul_right _ _)
end

