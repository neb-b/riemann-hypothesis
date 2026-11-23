module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0003
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem index_inf_dvd_index_mul_index_of_commGroup {G : Type*} [CommGroup G] (A B : Subgroup G) :
    (A ⊓ B).index ∣ A.index * B.index := by
  have h := Subgroup.relIndex_inf_mul_relIndex A B ⊤
  rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
  rw [← h]
  exact Nat.mul_dvd_mul_right (Subgroup.relIndex_dvd_index_of_normal _ _) _

private theorem index_comap_dvd_index_of_commGroup {G G' : Type*} [CommGroup G] [Group G'] (A : Subgroup G) (f : G' →* G) :
    (A.comap f).index ∣ A.index := by
  rw [Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

private theorem index_range_sq_units_zmod_prime_dvd_two (p : ℕ) (hp : p.Prime) :
    ((powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range).index ∣ 2 := by
  haveI := Fact.mk hp
  set S := (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range
  haveI : IsCyclic ((ZMod p)ˣ ⧸ S) :=
    isCyclic_of_surjective (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
  have hcard : Nat.card ((ZMod p)ˣ ⧸ S) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
  exact hcard

private theorem index_zpowers_neg_one_units_zmod_two_pow_dvd (e : ℕ) :
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)).index ∣ 2 ^ e := by
  have h4 : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Fact (1 < 2 ^ (e + 2)) := ⟨by omega⟩
  have h := Subgroup.index_mul_card (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one,
    ZMod.ringChar_zmod_n, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_two, if_neg (by omega)] at h
  have h' : 2 ^ (e + 1) * (2 - 1) = 2 ^ e * 2 := by ring
  rw [h'] at h
  rw [Nat.eq_of_mul_eq_mul_right (by norm_num) h]

private theorem index_ker_toUnitHom_dvd_orderOf_dirichletCharacter (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) :
    (MulChar.toUnitHom χ).ker.index ∣ orderOf χ := by
  rw [Subgroup.index_ker]
  haveI : IsCyclic (MulChar.toUnitHom χ).range := inferInstance
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  obtain ⟨_, u, rfl⟩ := x
  apply Subtype.ext
  apply Units.ext
  have ho : orderOf χ ≠ 0 := (orderOf_pos χ).ne'
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom,
    OneMemClass.coe_one, Units.val_one]
  rw [← MulChar.pow_apply' χ ho, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem orderOf_dirichletCharacter_le_level (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) : orderOf χ ≤ n := by
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have h1 : χ ^ n.totient = 1 := by
    ext u
    rw [MulChar.pow_apply' χ hpos.ne', ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
      Units.val_one, map_one, MulChar.one_apply_coe]
  exact (Nat.le_of_dvd hpos (orderOf_dvd_of_pow_eq_one h1)).trans (Nat.totient_le n)

theorem UpperTheory.V.HV.hostIndex :
    ∀ h : Host, h.H.index ∣ 2 ^ (h.ex + 2) * h.o ∧ h.H.index ≤ h.N ∧ 16 ∣ h.N ∧ 0 < h.o ∧ h.o ≤ h.q ∧
      (∀ p, p.Prime → (p ∣ h.N ↔ p = 2 ∨ p ∣ h.q ∨ p = h.q1 ∨ p = h.d)) ∧
      (∀ p, p.Prime → p ≠ 2 → p ≠ h.q1 → p ≠ h.d → ordProj[p] h.N = ordProj[p] h.q) ∧ ordProj[h.q1] h.N = h.q1 ∧ ordProj[h.d] h.N = h.d ∧
      ∀ u : (ZMod h.N)ˣ, u ^ (2 ^ (h.ex + 1) * h.o) ∈ h.H := by
  intro h
  obtain ⟨hq1, hq1m, hd, hdm, hcop⟩ := h.pair
  haveI := h.chi.ne
  have hq0 : h.q ≠ 0 := NeZero.ne _
  have hq12 : h.q1 ≠ 2 := by intro e; omega
  have hd2 : h.d ≠ 2 := by intro e; omega
  have hq1d : h.q1 ≠ h.d := by intro e; omega
  have cq1 : ¬ h.q1 ∣ h.q := fun hdv => hq1.one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hcop) hdv)
  have cd : ¬ h.d ∣ h.q := fun hdv => hd.one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop) hdv)
  have hN : h.N = (2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d) := rfl
  have hN0 : h.N ≠ 0 := by
    rw [hN]
    exact Nat.mul_ne_zero (Nat.lcm_ne_zero (by positivity) hq0) (Nat.mul_ne_zero hq1.ne_zero hd.ne_zero)
  haveI : NeZero h.N := ⟨hN0⟩
  have hfac : ∀ p, p.Prime → h.N.factorization p =
      max ((h.ex + 2) * (if p = 2 then 1 else 0)) (h.q.factorization p) +
        ((if p = h.q1 then 1 else 0) + (if p = h.d then 1 else 0)) := by
    intro p hp
    rw [hN, Nat.factorization_mul (Nat.lcm_ne_zero (by positivity) hq0)
        (Nat.mul_ne_zero hq1.ne_zero hd.ne_zero),
      Nat.factorization_lcm (by positivity) hq0, Nat.factorization_mul hq1.ne_zero hd.ne_zero,
      Nat.factorization_pow, Nat.prime_two.factorization, hq1.factorization, hd.factorization]
    simp [Finsupp.single_apply, eq_comm]
    split_ifs <;> simp
  have fq1 : h.q.factorization h.q1 = 0 := Nat.factorization_eq_zero_of_not_dvd cq1
  have fd : h.q.factorization h.d = 0 := Nat.factorization_eq_zero_of_not_dvd cd
  have hdiv : h.H.index ∣ 2 ^ (h.ex + 2) * h.o := by
    have i1 := index_comap_dvd_index_of_commGroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (h.ex + 2)))ˣ))
      (ZMod.unitsMap (Host.two_pow_dvd h))
    have i2 := index_comap_dvd_index_of_commGroup (MulChar.toUnitHom h.chi.χ).ker (ZMod.unitsMap (Host.q_dvd h))
    have i3 := index_comap_dvd_index_of_commGroup (powMonoidHom 2 : (ZMod h.q1)ˣ →* (ZMod h.q1)ˣ).range
      (ZMod.unitsMap (Host.host_q1_dvd_N h))
    have i4 := index_comap_dvd_index_of_commGroup (powMonoidHom 2 : (ZMod h.d)ˣ →* (ZMod h.d)ˣ).range
      (ZMod.unitsMap (Host.d_dvd h))
    have j1 := i1.trans (index_zpowers_neg_one_units_zmod_two_pow_dvd h.ex)
    have j2 := i2.trans (index_ker_toUnitHom_dvd_orderOf_dirichletCharacter h.chi.N h.chi.χ)
    have j3 := i3.trans (index_range_sq_units_zmod_prime_dvd_two h.q1 hq1)
    have j4 := i4.trans (index_range_sq_units_zmod_prime_dvd_two h.d hd)
    have k := ((((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul_right
      ((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul_right
        ((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul j1 j2)) _)) _))).trans
      (Nat.mul_dvd_mul (Nat.mul_dvd_mul (dvd_refl _) j3) j4))
    have e : 2 ^ h.ex * orderOf h.chi.χ * 2 * 2 = 2 ^ (h.ex + 2) * h.o := by
      simp only [Host.o, ordC]
      ring
    rw [← e]
    exact k
  refine ⟨hdiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : h.H.index ∣ h.N.totient := by
      have := Subgroup.index_dvd_card h.H
      rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at this
    exact (Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)) hc).trans (Nat.totient_le _)
  · rw [hN]
    exact (Nat.pow_dvd_pow 2 (by have := h.two_le; omega : 4 ≤ h.ex + 2)).trans
      ((Nat.dvd_lcm_left _ _).trans (dvd_mul_right _ _))
  · exact orderOf_pos _
  · exact orderOf_dirichletCharacter_le_level _ _
  · intro p hp
    rw [hp.dvd_iff_one_le_factorization hN0, hp.dvd_iff_one_le_factorization hq0, hfac p hp]
    by_cases e2 : p = 2 <;> by_cases e3 : p = h.q1 <;> by_cases e4 : p = h.d <;>
      simp [e2, e3, e4] <;> omega
  · intro p hp h2 h3 h4
    rw [hfac p hp]
    simp [h2, h3, h4]
  · rw [hfac _ hq1, fq1]
    simp [hq12, hq1d]
  · rw [hfac _ hd, fd]
    simp [hd2, hq1d.symm]
  · intro u
    have sq : ∀ (n : ℕ) (w : (ZMod n)ˣ),
        w ^ (2 ^ (h.ex + 1) * h.o) ∈ (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
      intro n w
      refine ⟨w ^ (2 ^ h.ex * h.o), ?_⟩
      rw [powMonoidHom_apply, ← pow_mul]
      congr 1
      ring
    simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap, map_pow]
    refine ⟨⟨⟨?_, ?_⟩, sq _ _⟩, sq _ _⟩
    · have ht : (2 ^ (h.ex + 2)).totient = 2 ^ (h.ex + 1) := by
        rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp
      rw [pow_mul, ← ht, ZMod.pow_totient, one_pow]
      exact Subgroup.one_mem _
    · rw [MonoidHom.mem_ker, map_pow]
      have h1 : (MulChar.toUnitHom h.chi.χ) (ZMod.unitsMap (Host.q_dvd h) u) ^ h.o = 1 := by
        apply Units.ext
        have ho : orderOf h.chi.χ ≠ 0 := (orderOf_pos _).ne'
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one]
        simp only [Host.o, ordC]
        rw [← MulChar.pow_apply' _ ho, pow_orderOf_eq_one, MulChar.one_apply_coe]
      rw [mul_comm, pow_mul, h1, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.IvField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) (m : ℕ) [NeZero m] (h : ψ.conductor ∣ m) :
    (Chr.cls ℚ Ω m).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  obtain ⟨hd, χ₀, hχ⟩ := ψ.factorsThrough_conductor
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have e1 := (Chr.clsFacts ℚ Ω N).2.1 ψ.conductor hd
  have e2 := (Chr.clsFacts ℚ Ω m).2.1 ψ.conductor h
  have hc : Chr.cls ℚ Ω ψ.conductor σ = 1 := by
    rw [← e2, MonoidHom.comp_apply, hσ, map_one]
  have hu : ∀ u : (ZMod N)ˣ, MulChar.toUnitHom ψ u = MulChar.toUnitHom χ₀ (ZMod.unitsMap hd u) := by
    intro u
    apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom]
    conv_lhs => rw [hχ]
    rw [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  unfold Chr.dirG
  rw [MonoidHom.comp_apply, hu, ← MonoidHom.comp_apply (ZMod.unitsMap hd), e1, hc, map_one]

theorem UpperTheory.V.HV.ivField :
    ∀ (χ : PChar) (l : ℕ) [Fact l.Prime] (j : ℕ), l ≠ 2 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω],
      ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁) (_ : Algebra L₁ Ω)
        (_ : IsAlgClosure L₁ Ω) (_ : IsAbelianGalois ℚ L₁), IsAbField (Lchi χ l) L₀ ∧ IsLayer l j L₀ L₁ ∧ Module.finrank ℚ L₁ ≤ l * χ.N * l ^ j ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.conductor ∣ χ.N → galOf ℚ L₁ Ω ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro χ l _ j hl2 Ω _ _ _
  haveI := χ.ne
  have hlp : l.Prime := Fact.out
  have hAm : (Lchi χ l).m = l * χ.N := by
    simp only [Lchi, AbF.cyc]
    exact max_eq_left (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hlp.ne_zero (NeZero.ne _)))
  have hldvd : l ∣ (Lchi χ l).m := by rw [hAm]; exact dvd_mul_right l _
  obtain ⟨L₀, i0, i1, hab, hdeg⟩ := exists_numberField_isAbField_finrank_eq_deg (Lchi χ l)
  have hmu : (Lchi χ l).HasMu l := by
    refine ⟨hldvd, ?_⟩
    rintro a ⟨u, hu, hua⟩
    have hu1 : u = 1 := (Subgroup.mem_bot).mp hu
    rw [hu1, Units.val_one] at hua
    have h2 : ((a : ℕ) : ZMod (Lchi χ l).m) = ((1 : ℕ) : ZMod (Lchi χ l).m) := by
      rw [Nat.cast_one]; exact hua.symm
    exact Nat.ModEq.of_dvd hldvd ((ZMod.natCast_eq_natCast_iff _ _ _).mp h2)
  obtain ⟨z, hz⟩ := (abelianField_hasMu_iff_exists_primitiveRoot (Lchi χ l) l hlp hl2 L₀ hab).mp hmu
  obtain ⟨L₁, i2, i3, i4, hlay⟩ := exists_cyclotomic_layer_of_primitiveRoot l j hlp hl2 L₀ ⟨z, hz⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra L₁ Ω := (IsAlgClosed.lift (R := ℚ) (S := L₁) (M := Ω)).toRingHom.toAlgebra
  letI : Algebra L₀ Ω := ((algebraMap L₁ Ω).comp (algebraMap L₀ L₁)).toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower ℚ L₁ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L₀ L₁ := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI hcl : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) L₁⟩
  obtain ⟨N', hN', H, hlev⟩ := Chr.layerLevel (Lchi χ l) l j hlp L₀ L₁ hab hlay
  obtain ⟨habel, -, -⟩ := Chr.levGal L₁ N' H hlev
  have hlev0 := Chr.abLevel.1 (Lchi χ l) L₀ hab
  have hgal0 := ((Chr.levGal L₀ _ _ hlev0).2.2 Ω).1
  refine ⟨L₀, i0, i1, L₁, i2, i3, i4, inferInstance, hcl, habel, hab, hlay, ?_, ?_⟩
  · rw [← Module.finrank_mul_finrank ℚ L₀ L₁, hdeg, hlay.2]
    apply Nat.mul_le_mul_right
    rw [AbF.deg]
    show (⊥ : Subgroup (ZMod (Lchi χ l).m)ˣ).index ≤ l * χ.N
    rw [Subgroup.index_bot, ← hAm]
    haveI : NeZero (Lchi χ l).m := ⟨(AbF.pos _).ne'⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  · intro O _ _ N _ ψ hψ
    calc galOf ℚ L₁ Ω ≤ galOf ℚ L₀ Ω := galOf_le ℚ L₀ Ω L₁
      _ = Chr.levH ℚ Ω (Lchi χ l).H := hgal0
      _ ≤ (Chr.dirG ℚ Ω ψ).ker := by
        rw [Chr.levH]
        show Subgroup.comap _ ⊥ ≤ _
        rw [MonoidHom.comap_bot]
        exact ker_le Ω ψ _ (hψ.trans (hAm ▸ dvd_mul_left _ _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LossLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.lossLe :
    ∀ l N n e : ℕ, l.Prime → l ≠ 2 → 2 ≤ N → n ≤ N → 1 ≤ e → lossAll l N n e ≤ (N * e) ^ 6 ∧ LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
  intro l N n e hl hl2 hN hn he
  have hfac : ∀ (p m : ℕ), m.factorization p ≤ m := by
    intro p m
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · exact (Nat.factorization_lt p h0.ne').le
  have hnu : LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
    unfold LDataCardLeFinrank.nuBound
    have a1 := hfac l N
    have a2 := hfac l e
    split_ifs
    · have : max (N.factorization l) 1 ≤ N.factorization l + 1 := max_le (by omega) (by omega)
      nlinarith
    · exact Nat.zero_le _
  have hk : N.primeFactors.card ≤ N := by
    calc N.primeFactors.card ≤ (Finset.Icc 1 N).card := by
          apply Finset.card_le_card
          intro p hp
          have hp' := Nat.mem_primeFactors.mp hp
          simp only [Finset.mem_Icc]
          exact ⟨hp'.1.one_lt.le, Nat.le_of_dvd (by omega) hp'.2.1⟩
      _ = N := by simp
  have hv : n.factorization l ≤ N := (hfac l n).trans hn
  refine ⟨?_, hnu⟩
  set M := N * e with hM
  have hNM : N ≤ M := Nat.le_mul_of_pos_right N he
  have hM2 : 2 ≤ M := hN.trans hNM
  have hnuM : LDataCardLeFinrank.nuBound l N e ≤ 2 * M := by rw [hM, ← mul_assoc]; exact hnu
  unfold lossAll Chr.loss
  have b1 : (n + n ^ 2) * LDataCardLeFinrank.nuBound l N e ≤ (M + M ^ 2) * (2 * M) := by
    apply Nat.mul_le_mul _ hnuM
    have : n ≤ M := hn.trans hNM
    have : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have b2 : N.primeFactors.card * (n * n.factorization l) ≤ M * (M * M) :=
    Nat.mul_le_mul (hk.trans hNM) (Nat.mul_le_mul (hn.trans hNM) (hv.trans hNM))
  have b3 : N.primeFactors.card * n.factorization l ≤ M * M :=
    Nat.mul_le_mul (hk.trans hNM) (hv.trans hNM)
  have hM3 : 8 ≤ M ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ M ^ 3 := Nat.pow_le_pow_left hM2 3
  have b4 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M ≤ M ^ 6 := by
    have e6 : M ^ 6 = M ^ 3 * M ^ 3 := by ring
    have : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M = 2 * M ^ 2 + 3 * M ^ 3 + M ^ 2 := by ring
    rw [h1, e6]
    nlinarith
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orb_gen {G O : Type} [CommGroup G] [Finite G] [CommRing O] [IsDomain O] (f : G →* Oˣ) :
    IsCyclic (G ⧸ f.ker) ∧ ∃ g : G, (∀ x, ∃ a : ℕ, f x = f g ^ a) ∧ f.ker.index = orderOf (f g) := by
  have hfin : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hc : IsCyclic f.range := isCyclic_subgroup_units f.range
  refine ⟨isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange f).symm
    (QuotientGroup.quotientKerEquivRange f).symm.surjective, ?_⟩
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := hc.exists_monoid_generator
  refine ⟨g, fun x => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hg ⟨f x, x, rfl⟩
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  · rw [Subgroup.index_ker, ← orderOf_eq_card_of_forall_mem_powers hg, ← Subgroup.orderOf_coe]

theorem UpperTheory.V.HV.orbFacts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.toUnitHom.ker.index = orderOf ψ ∧ IsCyclic ((ZMod N)ˣ ⧸ ψ.toUnitHom.ker) ∧
      (∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker ↔ ∃ j : ℕ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j) ∧
      {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker}.ncard = Nat.totient (orderOf ψ) := by
  intro O _ _ N _ ψ
  obtain ⟨hc, g, hg, hidx⟩ := orb_gen ψ.toUnitHom
  have hpow : ∀ (χ : DirichletCharacter O N) (k : ℕ) (x : (ZMod N)ˣ),
      (χ ^ k).toUnitHom x = χ.toUnitHom x ^ k := by
    intro χ k x
    ext
    simp [MulChar.pow_apply_coe]
  have hext : ∀ χ χ' : DirichletCharacter O N, (∀ x, χ.toUnitHom x = χ'.toUnitHom x) → χ = χ' := by
    intro χ χ' h
    ext x
    simpa using congrArg Units.val (h x)
  have hone : ∀ x, (1 : DirichletCharacter O N).toUnitHom x = 1 := by
    intro x
    ext
    simp
  have hord : orderOf ψ = orderOf (ψ.toUnitHom g) := by
    rw [orderOf_eq_orderOf_iff]
    intro k
    constructor
    · intro h
      rw [← hpow, h, hone]
    · intro h
      apply hext
      intro x
      obtain ⟨a, ha⟩ := hg x
      rw [hpow, hone, ha, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  have hpos : 0 < orderOf (ψ.toUnitHom g) :=
    (ψ.toUnitHom.isOfFinOrder (isOfFinOrder_of_finite g)).orderOf_pos
  have hfwd : ∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker →
      ∃ j < orderOf ψ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j := by
    intro ψ' h
    have hm : ∀ x, ψ'.toUnitHom x = 1 ↔ ψ.toUnitHom x = 1 := fun x => by
      rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, h]
    have ho : orderOf (ψ'.toUnitHom g) = orderOf (ψ.toUnitHom g) := by
      rw [orderOf_eq_orderOf_iff]
      intro k
      rw [← map_pow, ← map_pow, hm]
    have h1 := IsPrimitiveRoot.orderOf (ψ.toUnitHom g)
    have h2 := IsPrimitiveRoot.orderOf (ψ'.toUnitHom g)
    rw [ho] at h2
    haveI : NeZero (orderOf (ψ.toUnitHom g)) := ⟨hpos.ne'⟩
    obtain ⟨j, hj, hcop, hjj⟩ := (h1.isPrimitiveRoot_iff').1 h2
    refine ⟨j, hord ▸ hj, hord ▸ hcop, hext _ _ fun x => ?_⟩
    obtain ⟨a, ha⟩ := hg x
    have h3 : ψ.toUnitHom (x / g ^ a) = 1 := by rw [map_div, map_pow, ha, div_self']
    have h4 := (hm _).2 h3
    rw [map_div, map_pow, div_eq_one] at h4
    rw [hpow, h4, ha, ← hjj, ← pow_mul, ← pow_mul, mul_comm]
  have hbwd : ∀ j : ℕ, j.Coprime (orderOf ψ) → (ψ ^ j).toUnitHom.ker = ψ.toUnitHom.ker := by
    intro j hj
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hpow]
    constructor
    · intro h
      have h2 : ψ.toUnitHom x ^ orderOf ψ = 1 := by rw [← hpow, pow_orderOf_eq_one, hone]
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one h2)
      rw [hj.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    · intro h
      rw [h, one_pow]
  refine ⟨hidx.trans hord.symm, hc, fun ψ' => ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨j, -, hj⟩ := hfwd ψ' h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact hbwd j hj
  · have hset : {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker} =
        (fun j : ℕ => ψ ^ j) ''
          ((Finset.range (orderOf ψ)).filter (fun a => (orderOf ψ).Coprime a) : Finset ℕ) := by
      ext ψ'
      constructor
      · intro h
        obtain ⟨j, hj, hcop, rfl⟩ := hfwd ψ' h
        exact ⟨j, by simpa using ⟨hj, hcop.symm⟩, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
        exact hbwd j hj'.2.symm
    rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset, Nat.totient_eq_card_coprime]
    refine pow_injOn_Iio_orderOf.mono fun j hj => ?_
    have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
    exact hj'.1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbSum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_eq_bot_of_orderOf {Q : Type} [CommGroup Q] [Finite Q] (χ : Q →* ℂˣ)
    (h : orderOf χ = Nat.card Q) : χ.ker = ⊥ := by
  have h1 : χ ^ χ.ker.index = 1 := by
    ext x
    have : x ^ χ.ker.index ∈ χ.ker := Subgroup.pow_index_mem _ _
    rw [MonoidHom.mem_ker, map_pow] at this
    simp [MonoidHom.pow_apply, this]
  have h2 : Nat.card Q ∣ χ.ker.index := h ▸ orderOf_dvd_of_pow_eq_one h1
  have h3 : χ.ker.index = Nat.card Q := Nat.dvd_antisymm (Subgroup.index_dvd_card _) h2
  have h4 := Subgroup.card_mul_index χ.ker
  rw [h3] at h4
  have h5 : Nat.card χ.ker = 1 := by
    have hp : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hp (by rw [h4, one_mul])
  exact Subgroup.card_eq_one.1 h5

open Classical in
private theorem totient_le_card_ker {Γ : Type} [CommGroup Γ] [Finite Γ] [Fintype (Γ →* ℂˣ)] (H : Subgroup Γ)
    (hH : IsCyclic (Γ ⧸ H)) :
    Nat.totient H.index ≤ (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card := by
  haveI : NeZero (Monoid.exponent (Γ ⧸ H)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Γ ⧸ H) ℂ
  haveI : Finite ((Γ ⧸ H) →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype ((Γ ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  haveI : IsCyclic ((Γ ⧸ H) →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  have hc : Fintype.card ((Γ ⧸ H) →* ℂˣ) = H.index := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]; rfl
  rw [← IsCyclic.card_orderOf_eq_totient (α := (Γ ⧸ H) →* ℂˣ) (d := H.index) (hc ▸ dvd_rfl)]
  refine Finset.card_le_card_of_injOn (fun χ => χ.comp (QuotientGroup.mk' H)) ?_ ?_
  · intro χ hχ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hχ ⊢
    have := ker_eq_bot_of_orderOf χ hχ
    rw [← MonoidHom.comap_ker, this, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · intro a _ b _ hab
    exact QuotientGroup.monoidHom_ext _ hab

theorem UpperTheory.V.HV.orbSum :
    ∀ (Γ : Type) [CommGroup Γ] [Finite Γ] (T : Finset (Subgroup Γ)), (∀ H ∈ T, IsCyclic (Γ ⧸ H)) → ∑ H ∈ T, Nat.totient H.index ≤ Nat.card Γ := by
  intro Γ _ _ T hT
  classical
  haveI : NeZero (Monoid.exponent Γ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Γ ℂ
  haveI : Finite (Γ →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype (Γ →* ℂˣ) := Fintype.ofFinite _
  calc ∑ H ∈ T, Nat.totient H.index
      ≤ ∑ H ∈ T, (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card :=
        Finset.sum_le_sum fun H hH => by convert totient_le_card_ker H (hT H hH)
    _ = (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker ∈ T).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ Fintype.card (Γ →* ℂˣ) := Finset.card_le_univ _
    _ = Nat.card Γ := by rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]
end

