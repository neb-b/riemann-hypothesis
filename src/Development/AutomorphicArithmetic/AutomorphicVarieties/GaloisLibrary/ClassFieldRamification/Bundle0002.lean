module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Sylow
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.PhiLe
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.phiLe :
    ∀ (p : ℕ) [Fact p.Prime] (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ K : Subgroup P, IsCoatom K → K.Normal ∧ K.index = p ∧ phi p P ≤ K := by
  intro p _ P _ _ hP K hK
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK
  refine ⟨hN, ?_⟩
  have hQp : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hne : Nontrivial (P ⧸ K) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hK.1
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    have h1 : 1 < Nat.card (P ⧸ K) := Finite.one_lt_card
    rcases n with _ | n
    · rw [hn, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · rw [hn, pow_succ]
      exact dvd_mul_left _ _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ K) p hdvd
  have htop : Subgroup.zpowers x = ⊤ := by
    have h1 : K ≤ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      intro k hk
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
      exact one_mem _
    rcases hK.le_iff.mp h1 with h | h
    · rw [eq_top_iff]
      intro y _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have : g ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
        rw [h]
        exact Subgroup.mem_top g
      exact this
    · exfalso
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have : g ∈ (Subgroup.zpowers ((g : P ⧸ K))).comap (QuotientGroup.mk' K) :=
        Subgroup.mem_zpowers _
      rw [h] at this
      rw [(QuotientGroup.eq_one_iff g).mpr this, orderOf_one] at hx
      exact (Fact.out : p.Prime).one_lt.ne hx
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← Subgroup.card_top, ← htop, Nat.card_zpowers, hx]
  have hidx : K.index = p := by
    rw [Subgroup.index, hcard]
  refine ⟨hidx, ?_⟩
  have hcomm : ∀ a b : P ⧸ K, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top b
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self x m n).eq
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    show g ^ p ∈ K
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'
  · rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hcomm (a : P ⧸ K) (b : P ⧸ K), mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.SplitCyc
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.splitCyc :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ), p.Prime → (p : 𝓞 ℚ) ∈ v.asIdeal → ¬ p ∣ N → GroundTheory.Global.SplitsCompletely C v → p ≡ 1 [MOD N] := by
  intro N _ C _ _ _ v p hp hpv hpN hspl
  haveI := Fact.mk hp
  haveI := v.isMaximal
  have hspan : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hvZ : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    refine (hspan.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap, map_natCast]
    exact hpv
  haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hvZ.symm⟩
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun y => ⟨Rat.ringOfIntegersEquiv y, by
    have h : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) :=
      Subsingleton.elim _ _
    rw [← h]
    exact Rat.ringOfIntegersEquiv.symm_apply_apply y⟩
  have hv1 : v.asIdeal.inertiaDeg ℤ = 1 := by
    letI := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
    letI := Ideal.Quotient.field v.asIdeal
    rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) v.asIdeal,
      finrank_eq_one_iff_of_nonzero (1 : 𝓞 ℚ ⧸ v.asIdeal) one_ne_zero, eq_top_iff]
    rintro y -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hsurj y
    rw [Submodule.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Algebra.smul_def, mul_one]
    rfl
  obtain ⟨⟨P, hPp, hPl⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 C)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hs := hspl ⟨P, hPp, hPne⟩ hPl
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have ht := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P
  rw [hv1, one_mul, hs.2, IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p C P hpN] at ht
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact orderOf_eq_one_iff.mp ht
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnitsGen
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem mem_ker_iff {N d : ℕ} [NeZero N] (h : d ∣ N) (u : (ZMod N)ˣ) :
    u ∈ (ZMod.unitsMap h).ker ↔ (u : ZMod N).val ≡ 1 [MOD d] := by
  rw [MonoidHom.mem_ker, ZMod.unitsMap_def, Units.ext_iff, Units.coe_map, Units.val_one]
  simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

private theorem ker_le_sup {N g d e : ℕ} [NeZero N] (hg : g ∣ N) (hd : d ∣ N) (he : e ∣ N)
    (hgcd : Nat.gcd d e ∣ g) (hN : N ∣ d * e) :
    (ZMod.unitsMap hg).ker ≤ (ZMod.unitsMap hd).ker ⊔ (ZMod.unitsMap he).ker := by
  intro u hu
  rw [mem_ker_iff hg] at hu
  have hx1 : 1 ≡ (u : ZMod N).val [MOD Nat.gcd d e] := (Nat.ModEq.of_dvd hgcd hu).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hx1
  have hxN : (u : ZMod N).val.Coprime N := ZMod.val_coe_unit_coprime u
  have hkd : k.Coprime d := by
    unfold Nat.Coprime
    rw [hk1.gcd_eq]
    exact Nat.gcd_one_left d
  have hke : k.Coprime e := by
    unfold Nat.Coprime
    rw [hk2.gcd_eq]
    exact Nat.Coprime.coprime_dvd_right he hxN
  have hkN : k.Coprime N := Nat.Coprime.coprime_dvd_right hN (Nat.Coprime.mul_right hkd hke)
  have hvval : ((ZMod.unitOfCoprime k hkN : (ZMod N)ˣ) : ZMod N).val = k % N := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  have hv : ZMod.unitOfCoprime k hkN ∈ (ZMod.unitsMap hd).ker := by
    rw [mem_ker_iff hd, hvval]
    exact ((Nat.mod_modEq k N).of_dvd hd).trans hk1
  have key : ZMod.unitsMap he (ZMod.unitOfCoprime k hkN) = ZMod.unitsMap he u := by
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, Units.coe_map]
    simp only [MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.cast_eq_val]
    rw [hvval, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq k N).of_dvd he).trans hk2
  have hw : (ZMod.unitOfCoprime k hkN)⁻¹ * u ∈ (ZMod.unitsMap he).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, key, inv_mul_cancel]
  have hu' : u = ZMod.unitOfCoprime k hkN * ((ZMod.unitOfCoprime k hkN)⁻¹ * u) := by
    rw [mul_inv_cancel_left]
  rw [hu']
  exact Subgroup.mul_mem_sup hv hw

private theorem aux (N : ℕ) [NeZero N] (b : ℕ) : ∀ (a : ℕ) (ha : a ∣ N), a * b = N → a.Coprime b →
    (ZMod.unitsMap ha).ker ≤ ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits N p := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a ha hab hcop
  have hN0 : N ≠ 0 := NeZero.ne N
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [← hab, mul_zero])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [← hab, zero_mul])
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one] at hab
    subst hab
    intro u hu
    rw [mem_ker_iff ha] at hu
    have hu1 : u = 1 := by
      ext
      rw [Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod a), ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff]
      exact hu
    rw [hu1]
    exact one_mem _
  · obtain ⟨p, hp, hpb⟩ := Nat.exists_prime_and_dvd hb1
    have hpa : ¬ p ∣ a := by
      intro h
      have h1 := Nat.dvd_gcd h hpb
      rw [hcop.gcd_eq_one] at h1
      exact hp.ne_one (Nat.dvd_one.mp h1)
    have hbsplit := Nat.ordProj_mul_ordCompl_eq_self b p
    have hk0 : 0 < b.factorization p := hp.factorization_pos_of_dvd hb0 hpb
    have hb'pos : 0 < b / p ^ b.factorization p := Nat.ordCompl_pos p hb0
    have hpk : 2 ≤ p ^ b.factorization p := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hb'lt : b / p ^ b.factorization p < b := by
      have h2 : 2 * (b / p ^ b.factorization p) ≤ p ^ b.factorization p * (b / p ^ b.factorization p) :=
        Nat.mul_le_mul_right _ hpk
      omega
    have hb'dvd : b / p ^ b.factorization p ∣ b := Nat.ordCompl_dvd b p
    have hpb' : Nat.Coprime p (b / p ^ b.factorization p) := Nat.coprime_ordCompl hp hb0
    have ha'N : a * p ^ b.factorization p * (b / p ^ b.factorization p) = N := by
      rw [mul_assoc, hbsplit, hab]
    have ha'dvd : a * p ^ b.factorization p ∣ N := ⟨_, ha'N.symm⟩
    have ha'cop : (a * p ^ b.factorization p).Coprime (b / p ^ b.factorization p) :=
      Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right hb'dvd hcop) (Nat.Coprime.pow_left _ hpb')
    have IH := ih _ hb'lt (a * p ^ b.factorization p) ha'dvd ha'N ha'cop
    have hvN : N.factorization p = b.factorization p := by
      rw [← hab, Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]
    have hNsplit := Nat.ordProj_mul_ordCompl_eq_self N p
    have hcopE : (p ^ b.factorization p).Coprime (N / p ^ N.factorization p) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)
    have hgcd : Nat.gcd (a * p ^ b.factorization p) (N / p ^ N.factorization p) ∣ a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hcopE]
      exact Nat.gcd_dvd_left _ _
    have hNde : N ∣ (a * p ^ b.factorization p) * (N / p ^ N.factorization p) := by
      refine ⟨a, ?_⟩
      rw [← hvN, mul_assoc, hNsplit, mul_comm]
    have hstep := ker_le_sup ha ha'dvd (Nat.ordCompl_dvd N p) hgcd hNde
    refine hstep.trans (sup_le (IH.trans ?_) ?_)
    · exact iSup₂_le fun q hq =>
        le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) q
          (Nat.primeFactors_mono hb'dvd hb0 hq)
    · exact le_iSup₂ (f := fun q (_ : q ∈ b.primeFactors) => KStar.Ram.inertiaUnits N q) p
        (Nat.mem_primeFactors.2 ⟨hp, hpb, hb0⟩)

theorem UpperTheory.V.CF.unitsGen :
    ∀ (a b : ℕ) [NeZero (a * b)], a.Coprime b → (ZMod.unitsMap (dvd_mul_right a b)).ker ≤ ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p := by
  intro a b _ h
  exact aux (a * b) b a _ rfl h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.unramIff :
    (∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ), p.Prime → (UnramAt L p ↔ ∀ w : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ w.asIdeal → w.asIdeal.inertia Gal(L/ℚ) = ⊥)) ∧ (∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L)) ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime → UnramAt L p → UnramAt K p := by
  have h2 : ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime →
      (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L) := by
    intro L _ _ p hp
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hpZ]
    unfold UnramAt
    refine forall_congr' fun P => forall_congr' fun hP => ?_
    haveI := hP
    rw [Int.cast_natCast, Ideal.ramificationIdx_eq_one_iff]
  refine ⟨?_, h2, ?_⟩
  · intro L _ _ _ p hp
    unfold UnramAt
    constructor
    · intro h w hw
      haveI := w.isPrime
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
      exact h w.asIdeal w.isPrime hw
    · intro h P hP hpP
      haveI := hP
      have hne : P ≠ ⊥ := by
        intro hb
        rw [hb, Ideal.mem_bot] at hpP
        exact hp.ne_zero (by exact_mod_cast hpP)
      have hw := h ⟨P, hP, hne⟩ hpP
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (P.under ℤ) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P Gal(L/ℚ)] at hw
      exact hw
  · intro K L _ _ _ _ _ p hp hL
    exact (h2 K p hp).2 fun hd => (h2 L p hp).1 hL (hd.trans (NumberField.discr_dvd_discr K L))
end

