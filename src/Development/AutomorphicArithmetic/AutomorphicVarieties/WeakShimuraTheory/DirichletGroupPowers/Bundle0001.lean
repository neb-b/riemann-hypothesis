module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ClsIndep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem crt_unit (M N : ℕ) [NeZero M] [NeZero N] (h : M.Coprime N) (a : (ZMod M)ˣ) :
    ∃ u : (ZMod (M * N))ˣ, ZMod.unitsMap (Nat.dvd_mul_right M N) u = a ∧
      ZMod.unitsMap (Nat.dvd_mul_left N M) u = 1 := by
  set e := ZMod.chineseRemainder h
  have h1 : ZMod.castHom (Nat.dvd_mul_right M N) (ZMod M) = (RingHom.fst _ _).comp e.toRingHom :=
    Subsingleton.elim _ _
  have h2 : ZMod.castHom (Nat.dvd_mul_left N M) (ZMod N) = (RingHom.snd _ _).comp e.toRingHom :=
    Subsingleton.elim _ _
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (MulEquiv.prodUnits.symm (a, 1)), ?_, ?_⟩
  · ext
    rw [ZMod.unitsMap_def, h1]
    simp [MulEquiv.prodUnits]
  · ext
    rw [ZMod.unitsMap_def, h2]
    simp [MulEquiv.prodUnits]

theorem UpperTheory.V.Ws.large₂.clsIndep :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M N : ℕ) [NeZero M] [NeZero N], M.Coprime N → ∀ a : (ZMod M)ˣ,
      ∃ g : G ℚ Ω, Chr.cls ℚ Ω M g = a ∧ ∀ (N' : ℕ) [NeZero N'], N' ∣ N → Chr.cls ℚ Ω N' g = 1 := by
  intro Ω _ _ _ M N _ _ hMN a
  obtain ⟨u, hu1, hu2⟩ := crt_unit M N hMN a
  obtain ⟨g, hg⟩ := (UpperTheory.V.Chr.clsOnto Ω (M * N)).1 u
  have hres := (UpperTheory.V.Chr.clsFacts ℚ Ω (M * N)).2.1
  refine ⟨g, ?_, ?_⟩
  · rw [← hres M (Nat.dvd_mul_right M N), MonoidHom.comp_apply, hg, hu1]
  · intro N' _ hN'
    rw [← hres N' (hN'.trans (Nat.dvd_mul_left N M)), MonoidHom.comp_apply, hg,
      ← ZMod.unitsMap_comp hN' (Nat.dvd_mul_left N M), MonoidHom.comp_apply, hu2, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.DirGPowOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem dirG_pow_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {m : ℕ} (h : χ ^ m = 1) : UpperTheory.V.Chr.dirG ℚ Ω χ ^ m = 1 := by
  ext g
  have hg := congrArg (fun ψ : DirichletCharacter O N => ψ ((UpperTheory.V.Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N)) h
  simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hg
  simp [UpperTheory.V.Chr.dirG, hg]

private theorem dirG_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ} (hA : A.valuation (v : Ω) < 1) (hN : v.Coprime N)
    {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) : UpperTheory.V.Chr.dirG ℚ Ω χ g = 1 := by
  have hnot : ¬ A.valuation (N : Ω) < 1 := by
    intro hNv
    have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one (⟨z, by simp⟩ : A)
    have hgcd := Nat.gcd_eq_gcd_ab v N
    rw [hN] at hgcd
    have h1 : ((1 : ℤ) : Ω) = (v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω) := by
      exact_mod_cast hgcd
    have hlt : A.valuation ((v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hA (hint _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hNv (hint _)
    rw [← h1] at hlt
    simp at hlt
  have hker := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 A hnot hg
  rw [MonoidHom.mem_ker] at hker
  simp [UpperTheory.V.Chr.dirG, hker]

private theorem not_dvd_card {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (φ : Γ →* Oˣ) {m l : ℕ} [Fact l.Prime]
    (hm : m ≠ 0) (hl : l.Coprime m) (h : φ ^ m = 1) (H : Subgroup Γ) : ¬ l ∣ Nat.card (H.map φ) := by
  intro hdvd
  haveI : NeZero m := ⟨hm⟩
  have hle : H.map φ ≤ rootsOfUnity m O := by
    rintro _ ⟨x, -, rfl⟩
    rw [mem_rootsOfUnity]
    have := congrArg (fun f => f x) h
    simpa [MonoidHom.pow_apply] using this
  haveI : Finite (H.map φ) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H.map φ) l hdvd
  have hym : orderOf y ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    obtain ⟨x, -, hx⟩ := y.2
    apply Subtype.ext
    have := congrArg (fun f => f x) h
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    simp [← hx, this]
  rw [hy] at hym
  have := Nat.Coprime.eq_one_of_dvd hl hym
  exact (Fact.out : l.Prime).one_lt.ne' this

theorem UpperTheory.V.Ws.large₂.host3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → 5 ≤ l ∧ l - 1 ∣ 2 * D.e ∧ D.Sb = ∅ ∧ (∃ m : ℕ, Odd m ∧ l.Coprime m ∧ D.ψ ^ m = 1) ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.ξ.ker ⊓ D.ψ.ker := by
  intro Ω _ _ _ l _ c D h3
  obtain ⟨hG, h, t, e, ψ, hBig, he0, het, hX, hIII, hA⟩ := h3
  obtain ⟨he, hψ, hS, hx⟩ := hA
  obtain ⟨_, ξ', ξ₀, -, -, -, hξ⟩ := hx
  obtain ⟨hlB, hle, hodd, -⟩ := hIII
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := hG.l_odd
  obtain ⟨-, -, -, -, hB⟩ := bchiFacts h t hBig
  obtain ⟨h5, hno, -, -, -, hl1, -, hfin⟩ := hB l hlp hl2 hlB
  have hlN : ¬ l ∣ h.N := (hfin e he0 het hle).2.2
  have hchar := ((Host.mem_X h).1 hX).1
  have hdo := ((hostOdd h c.O ψ hchar).1 hodd).1
  have hcop : l.Coprime (orderOf ψ) := by
    rw [Nat.Prime.coprime_iff_not_dvd hlp]
    intro hd
    exact hno (hd.trans (hdo.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ _))))
  have hpow : D.ψ ^ orderOf ψ = 1 := by
    rw [hψ]; exact dirG_pow_one ψ (pow_orderOf_eq_one ψ)
  have hm0 : orderOf ψ ≠ 0 := by
    intro h0; rw [h0] at hodd; exact Nat.not_odd_zero hodd
  refine ⟨h5, he ▸ hle, ?_, ⟨orderOf ψ, hodd, hcop, hpow⟩, ?_⟩
  · rw [GradeZeroInterpolatingElement.Raw.Sb, Finset.filter_eq_empty_iff]
    rintro p - ⟨-, hd⟩
    exact not_dvd_card D.ψ hm0 hcop hpow _ hd
  · intro A hA g hg
    have hcN : l.Coprime h.N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
    have hc1 : l.Coprime (UpperTheory.V.pOne h.chi) :=
      (Nat.coprime_primes hlp (UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1).2 hl1
    have hc2 : l.Coprime (2 ^ h.nIII l ψ) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hlp Nat.prime_two).2 hl2)
    refine ⟨?_, ?_⟩
    · show g ∈ D.ξ.ker
      rw [MonoidHom.mem_ker, hξ, MonoidHom.mul_apply, dirG_unr ξ₀ hA hc1 hg, dirG_unr ξ' hA hc2 hg, mul_one]
    · show g ∈ D.ψ.ker
      rw [MonoidHom.mem_ker, hψ, dirG_unr ψ hA hcN hg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.EltTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem not_over_odd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (h2 : A.valuation ((2 : ℕ) : Ω) < 1) {n : ℕ}
    (hn : Odd n) : ¬ A.valuation (n : Ω) < 1 := by
  intro h
  obtain ⟨k, rfl⟩ := hn
  have h1 : A.valuation (((2 : ℕ) : Ω) * (k : Ω)) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le h2 ((A.valuation_le_one_iff _).2 (natCast_mem A k))
  have h3 := A.valuation.map_sub_lt h h1
  have e : ((2 * k + 1 : ℕ) : Ω) - ((2 : ℕ) : Ω) * (k : Ω) = 1 := by push_cast; ring
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

private theorem neg_mem_range (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ∈ (proj 2 (2 ^ n)).range := by
  rw [(projFacts (2 ^ n) 2 Nat.prime_two).2.2.2.2.2.1, MonoidHom.mem_ker]
  have e : ordCompl[2] (2 ^ n) = 1 := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same, Nat.div_self (by positivity)]
  have : Subsingleton (ZMod (ordCompl[2] (2 ^ n))) := by rw [e]; infer_instance
  exact Subsingleton.elim _ _

theorem UpperTheory.V.Ws.large₂.eltTwo :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → ∃ g ∈ D.Ip 2, D.ξ g = -1 ∧ D.ψ g = 1 ∧ D.om g = 1 := by
  rintro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, -, -, -, -, ⟨-, -, hodd, -⟩, -, hψ, -, hp, ξ', ξ₀, -, hξ', -, hξ⟩
  have hA := hG.pl_over 2 Nat.prime_two
  have hlo : Odd l := hl.out.odd_of_ne_two hG.l_odd
  have hpo : Odd (pOne h.chi) :=
    Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) (pK_pOne_prime_conditions h.chi).2.1.2.2)
  have hom : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hG.om_bar σ⟩
  have h1 : D.Ip 2 ≤ D.om.ker := ((omT Ω l c).2 D.om hom).2.2.2.2.2.1 _ (not_over_odd _ hA hlo)
  have h2 : D.Ip 2 ≤ (Chr.cls ℚ Ω (pOne h.chi)).ker :=
    (Chr.clsFacts ℚ Ω (pOne h.chi)).2.2.2.2 _ (not_over_odd _ hA hpo)
  obtain ⟨g, hg, hc⟩ : (-1 : (ZMod (2 ^ h.nIII l ψ))ˣ) ∈ (D.Ip 2).map (Chr.cls ℚ Ω (2 ^ h.nIII l ψ)) := by
    rw [(compIne Ω (2 ^ h.nIII l ψ) 2 Nat.prime_two _ hA).1]
    exact neg_mem_range _ _
  have h3 : D.ξ g = -1 := by
    have h4 : Chr.cls ℚ Ω (pOne h.chi) g = 1 := h2 hg
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, h4, hc, map_one, one_mul]
    ext1
    rw [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, hξ', Units.val_neg, Units.val_one]
  refine ⟨g ^ orderOf ψ, pow_mem hg _, by rw [map_pow, h3, hodd.neg_one_pow], ?_, h1 (pow_mem hg _)⟩
  rw [hψ, Chr.dirG, MonoidHom.comp_apply, map_pow, map_pow]
  ext1
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ImgRoots
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.large₂.imgRoots :
    ∀ {O : Type} [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (x : Oˣ), x ^ orderOf χ = 1 → ∃ b : (ZMod N)ˣ, χ.toUnitHom b = x := by
  intro O _ _ N _ χ x hx
  have hn : 0 < orderOf χ := orderOf_pos χ
  haveI : NeZero (orderOf χ) := ⟨hn.ne'⟩
  haveI : Finite χ.toUnitHom.range :=
    Finite.of_surjective χ.toUnitHom.rangeRestrict χ.toUnitHom.rangeRestrict_surjective
  have hle : χ.toUnitHom.range ≤ rootsOfUnity (orderOf χ) O := by
    rintro _ ⟨b, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' χ hn.ne', pow_orderOf_eq_one,
      MulChar.one_apply_coe, Units.val_one]
  have hcard : orderOf χ ≤ Nat.card χ.toUnitHom.range := by
    have hpos : 0 < Nat.card χ.toUnitHom.range := Nat.card_pos
    apply orderOf_le_of_pow_eq_one hpos
    refine MulChar.ext fun a => ?_
    rw [MulChar.pow_apply' χ hpos.ne', MulChar.one_apply_coe]
    have h1 := pow_card_eq_one' (G := χ.toUnitHom.range) (x := ⟨χ.toUnitHom a, a, rfl⟩)
    have h2 := congrArg (fun u : χ.toUnitHom.range => ((u : Oˣ) : O)) h1
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at h2
    rw [← MulChar.coe_toUnitHom]
    exact h2
  have heq : χ.toUnitHom.range = rootsOfUnity (orderOf χ) O :=
    Subgroup.eq_of_le_of_card_ge hle ((card_rootsOfUnity O (orderOf χ)).trans hcard)
  have hxmem : x ∈ rootsOfUnity (orderOf χ) O := (mem_rootsOfUnity _ _).2 hx
  rw [← heq] at hxmem
  obtain ⟨b, hb⟩ := hxmem
  exact ⟨b, hb⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.RedOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.large₂.redOne :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (m : ℕ), l.Coprime m → ∀ x : c.Oˣ, x ^ m = 1 → residue c.O (x : c.O) = 1 → x = 1 := by
  intro l _ c m hm x hx hres
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l c.O
  have hmu : IsUnit ((m : ℕ) : c.O) :=
    hunit m ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hm)
  have hgeom : (∑ i ∈ Finset.range m, (x : c.O) ^ i) * ((x : c.O) - 1) = 0 := by
    rw [geom_sum_mul, ← Units.val_pow_eq_pow_val, hx, Units.val_one, sub_self]
  have hsum : IsUnit (∑ i ∈ Finset.range m, (x : c.O) ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hr := hmu.map (residue c.O)
    rw [map_natCast] at hr
    exact hr.ne_zero
  have h0 : (x : c.O) - 1 = 0 := (hsum.mul_right_eq_zero).1 hgeom
  exact Units.ext (sub_eq_zero.1 h0)
end

