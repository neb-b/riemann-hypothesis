module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith
public import Formalism.DirichletDensity.DirichletDensityProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.ArtLSpec
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem exists_unit {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ l [MOD ordCompl[l] N] ∧ (u : ZMod N).val ≡ 1 [MOD ordProj[l] N] := by
  have hcl : Nat.Coprime l (ordCompl[l] N) := Nat.coprime_ordCompl hl hN
  have hcop : Nat.Coprime (ordCompl[l] N) (ordProj[l] N) := (Nat.Coprime.pow_left _ hcl).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop l 1
  have hc1 : Nat.Coprime k (ordCompl[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk1]
    exact hcl
  have hc2 : Nat.Coprime k (ordProj[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk2]
    simp
  have hco : Nat.Coprime k N := by
    have h := Nat.Coprime.mul_right hc2 hc1
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at h
  refine ⟨ZMod.unitOfCoprime k hco, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordCompl_dvd N l)).trans hk1
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordProj_dvd N l)).trans hk2

private theorem unit_unique {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) {u v : (ZMod N)ˣ}
    (h1 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordCompl[l] N])
    (h2 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordProj[l] N]) : u = v := by
  have hcop : Nat.Coprime (ordProj[l] N) (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  haveI : NeZero N := ⟨hN⟩
  apply Units.ext
  apply ZMod.val_injective
  have hu := ZMod.val_lt (u : ZMod N)
  have hv := ZMod.val_lt (v : ZMod N)
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h

private theorem val_iff {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod N)ˣ) (a : ℕ) :
    (u : ZMod N).val ≡ a [MOD f] ↔ ((ZMod.unitsMap hf u : (ZMod f)ˣ) : ZMod f) = (a : ZMod f) := by
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]

theorem UpperTheory.HF.artL_spec :
    ∀ {φ : Frame} (H : HostRaw φ) {l : ℕ}, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] ∧ H.artL l = H.art u) ∧ (∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] → (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l) ∧ ∀ g : φ.GG, g ∈ H.decG l ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
  intro φ H l hl
  haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hex := exists_unit hN hl
  have hart : H.artL l = H.art hex.choose := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.artL
    rw [dite_eq_left hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  have part2 : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] →
      (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l := by
    intro u hu1 hu2
    rw [hart, unit_unique hN hl (hu1.trans hc1.symm) (hu2.trans hc2.symm)]
  refine ⟨⟨hex.choose, hc1, hc2, hart⟩, part2, ?_⟩
  have hA : ordCompl[l] H.condN ∣ H.condN := Nat.ordCompl_dvd _ _
  haveI : NeZero (ordCompl[l] H.condN) :=
    ⟨fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hA))⟩
  obtain ⟨lA, hlA⟩ : ∃ w : (ZMod (ordCompl[l] H.condN))ˣ, (w : ZMod (ordCompl[l] H.condN)) = (l : ZMod _) :=
    ⟨ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl hN), ZMod.coe_unitOfCoprime _ _⟩
  have key : ∀ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ↔ ZMod.unitsMap hA u = lA ^ k := by
    intro u k
    rw [val_iff hA u (l ^ k), Units.ext_iff, Units.val_pow_eq_pow_val, hlA, Nat.cast_pow]
  let T : Subgroup φ.GG := ((Subgroup.zpowers lA).comap (ZMod.unitsMap hA)).map H.art
  have memT : ∀ g, g ∈ T ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
    intro g
    simp only [T, Subgroup.mem_map, Subgroup.mem_comap, ← mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff]
    constructor
    · rintro ⟨u, ⟨k, hk⟩, rfl⟩
      exact ⟨u, k, (key u k).mpr hk.symm, rfl⟩
    · rintro ⟨u, k, hk, rfl⟩
      exact ⟨u, ⟨k, ((key u k).mp hk).symm⟩, rfl⟩
  have hle1 : UpperTheory.HF.Formalism.HC.HostRaw.decG H l ≤ T := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l g).mp hg
      exact (memT _).mpr ⟨u, 0, by simpa using hu, rfl⟩
    · rw [Subgroup.zpowers_le, hart]
      exact (memT _).mpr ⟨hex.choose, 1, by simpa using hc1, rfl⟩
  have hu1 : ZMod.unitsMap hA hex.choose = lA := by
    have h := (key hex.choose 1).mp (by simpa using hc1)
    simpa using h
  have hle2 : T ≤ UpperTheory.HF.Formalism.HC.HostRaw.decG H l := by
    intro g hg
    obtain ⟨u, k, hk, rfl⟩ := (memT g).mp hg
    have hw : ((u * (hex.choose ^ k)⁻¹ : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1
        [MOD ordCompl[l] H.condN] := by
      have h := (key (u * (hex.choose ^ k)⁻¹) 0).mpr
        (by rw [map_mul, map_inv, map_pow, hu1, (key u k).mp hk]; simp)
      simpa using h
    have hmem : H.art (u * (hex.choose ^ k)⁻¹) ∈ UpperTheory.HF.Formalism.HC.HostRaw.inertG H l :=
      (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l _).mpr ⟨_, hw, rfl⟩
    have heq : H.art u = H.art (u * (hex.choose ^ k)⁻¹) * H.artL l ^ k := by
      rw [hart, map_mul, map_inv, map_pow, inv_mul_cancel_right]
    rw [heq]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
  intro g
  rw [show UpperTheory.HF.Formalism.HC.HostRaw.decG H l = T from le_antisymm hle1 hle2]
  exact memT g
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.CardImgOneDvd
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem card_map_dvd {G G' : Type*} [Group G] [Group G'] (a : G →* G') {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (B.map a) ∣ Nat.card (A.map a) * A.relIndex B := by
  have hAB : A.map a ≤ B.map a := Subgroup.map_mono h
  have hc : Nat.card (B.map a) = Nat.card (A.map a) * (A.map a).relIndex (B.map a) := by
    rw [Subgroup.relIndex, ← Subgroup.card_mul_index ((A.map a).subgroupOf (B.map a))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hc]
  apply mul_dvd_mul_left
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left B (Subgroup.le_comap_map a A)

private theorem index_unitsOne {φ : Frame} (H : HostRaw φ) {f : ℕ} (hf : f ∣ H.condN) :
    (H.unitsOne f).index = f.totient := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hf)
  have hg : Nat.gcd f H.condN = f := Nat.gcd_eq_left hf
  haveI : NeZero (Nat.gcd f H.condN) := ⟨by rw [hg]; exact hf0⟩
  unfold HostRaw.unitsOne
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hg]

theorem UpperTheory.HF.card_imgOne_dvd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ g → g ∣ H.condN → Nat.card (H.imgOne f) ∣ Nat.card (H.imgOne g) * (g.totient / f.totient) := by
  intro φ H f g hfg hg
  have hf : f ∣ H.condN := hfg.trans hg
  have hle : H.unitsOne g ≤ H.unitsOne f := by
    intro u hu
    rw [H.mem_unitsOne hg] at hu
    rw [H.mem_unitsOne hf]
    exact Nat.ModEq.of_dvd hfg hu
  have hd := card_map_dvd H.art hle
  have hidx := Subgroup.relIndex_mul_index hle
  rw [index_unitsOne H hf, index_unitsOne H hg] at hidx
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      subst h0
      exact H.condN_ne_zero (zero_dvd_iff.1 hf)
    · exact h0
  have htot : 0 < f.totient := Nat.totient_pos.2 hf0
  have hr : g.totient / f.totient = (H.unitsOne g).relIndex (H.unitsOne f) := by
    rw [← hidx, Nat.mul_div_cancel _ htot]
  rw [hr]
  exact hd
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK
section
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Polynomial

private theorem diffQuadK (K : Type) [Field K] [NumberField K] (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤)
    (hrank : Module.finrank ℚ K = 2) (β : 𝓞 K) (hβ : (β : K) = x) :
    discr K = -(d : ℤ) ∧ differentIdeal ℤ (𝓞 K) = span {β} := by
  have hdisc : discr K = -(d : ℤ) :=
    Formalism.HF.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj
      ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)
  refine ⟨hdisc, ?_⟩
  have hN : (differentIdeal ℤ (𝓞 K)).absNorm = d := by
    rw [absNorm_differentIdeal K, hdisc]; simp
  have hβ2 : β ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.ext
    have : ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2 := by push_cast; rfl
    rw [this, hβ, hx]
    push_cast; rfl
  have hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤ := by
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1
    rw [hadj] at h2
    show Algebra.adjoin ℚ {(β : K)} = ⊤
    rw [hβ, ← h2]
    rfl
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ))
    (by simp [hβ2])
  have h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K) := by
    have := congrArg (fun p => aeval β (derivative p)) hr
    simp only [derivative_X_pow, derivative_C, derivative_mul, map_add (f := _), map_mul,
      minpoly.aeval, zero_mul, add_zero] at this
    have e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r := by
      rw [← this]; simp [map_ofNat]
    rw [e]
    exact Ideal.mul_mem_right _ _ hmem
  have hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    have := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))
    rwa [hN] at this
  have hβmem : β ∈ differentIdeal ℤ (𝓞 K) := by
    have e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β) := by
      have h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1 := by
        have : d = 2 * (d / 2) + 1 := by omega
        exact_mod_cast this
      linear_combination (-β) * h
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)
  have hle : span {β} ≤ differentIdeal ℤ (𝓞 K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hβmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hNβ : (span {β}).absNorm ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]
    have : (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ)) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
    simp [Int.natAbs_pow]
  have hNβ' : (span {β}).absNorm = d := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) hNβ
  have hC1 : C.absNorm = 1 := by
    have := congrArg Ideal.absNorm hC
    rw [map_mul, hNβ', hN] at this
    exact Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)
  rw [Ideal.absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]

end

theorem UpperTheory.HF.discr_K :
    ∀ {φ : Frame} (H : HostAx φ), (discr H.K).natAbs = H.d ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = span {s} ∧ differentIdeal ℤ (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) * span {s} := by
  intro φ H
  let x : H.K := ⟨H.sqd, H.sqd_mem_K⟩
  have hx : x ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [x] using H.sqd_sq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast H.d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    have h' : IntermediateField.lift (@IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {x}) =
        IntermediateField.lift (⊤ : @IntermediateField ℚ H.K _ _ H.K.algebra') := by
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_singleton]
      rfl
    have key := IntermediateField.lift_injective H.K h'
    convert key <;> exact Subsingleton.elim _ _
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 H.K, (β : H.K) = x := ⟨⟨x, hint⟩, rfl⟩
  obtain ⟨hd, hK⟩ := diffQuadK H.K H.d H.d_prime H.d_mod_four x hx hadj H.finrank_K β hβ
  have hmap : (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) =
      span {algebraMap (𝓞 H.K) (𝓞 H.E) β} := by
    rw [hK, Ideal.map_span, Set.image_singleton]
  refine ⟨by rw [hd]; simp, algebraMap (𝓞 H.K) (𝓞 H.E) β, ?_, hmap, ?_⟩
  · show ((β : H.K) : H.E) = H.sqd
    rw [hβ]
  · rw [← hmap]
    exact differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H.K) (𝓞 H.E)
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec
section
open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

theorem UpperTheory.HF.frobG_spec :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔ H.galE σ = H.frobG p) ∧
      (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧ (((H.frobG p).1.1 : ℤˣ) : ℤ) = H.psAt p ∧
      (H.frobG p ∉ φ.Psi ↔ H.Inert p) ∧ (H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
      ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.frobG p).2 = hcl φ.e v := by
  intro φ H p hpr hnd
  have hp : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hpr.out).2 hnd
  have hodd : p % 2 = 1 := H.odd_of_coprime hp
  set u := ZMod.unitOfCoprime p hp with hu
  have hval : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hp
  have hF : H.frobG p = H.art u := H.frobG_of_coprime hp
  have hjac : (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p := by
    rw [hF, H.der.art_ch u, jacobi_neg_recip H.d_mod_four hodd]
    exact jacobi_congr (hval.of_dvd H.d_dvd_condN)
  have hne : jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by
    rw [← hjac]
    rcases Int.units_eq_one_or ((H.frobG p).1.2) with h | h <;> simp [h]
  have hpsi : H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1 := by
    rw [Frame.mem_Psi_iff, ← hjac]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Units.ext h
  refine ⟨?_, hjac, ?_, ?_, hpsi, ?_⟩
  · intro P _ _ σ
    rw [hF]
    exact H.frob_iff p hp P σ
  · rw [hF, H.psAt_of_coprime hp]
  · rw [hpsi]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.Inert
    constructor
    · intro h
      refine ⟨hpr.out, ?_⟩
      rcases hne with h1 | h1
      · exact absurd h1 h
      · exact h1
    · rintro ⟨-, h⟩
      rw [h]
      decide
  · have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.coprime_dvd_right H.tower_dvd_condN hp
    refine ⟨ZMod.unitOfCoprime p hc2, by simp, ?_⟩
    rw [hF]
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime]
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 (hval.of_dvd H.tower_dvd_condN)).symm
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.ImgOneGcd
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.imgOne_gcd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ H.condN → g ∣ H.condN → H.imgOne (Nat.gcd f g) = H.imgOne f ⊔ H.imgOne g := by
  intro φ H f g hf hg
  have hgcd : Nat.gcd f g ∣ H.condN := (Nat.gcd_dvd_left f g).trans hf
  apply le_antisymm
  · rintro x hx
    rw [H.mem_imgOne hgcd] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have key := Der.Rd.KK_gcd (N := H.condN) ((H.imgOne f ⊔ H.imgOne g).comap H.art) hf hg
      (fun v hv => Subgroup.mem_sup_left ((H.mem_imgOne hf _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      (fun v hv => Subgroup.mem_sup_right ((H.mem_imgOne hg _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      u (Der.Rd.mem_KK.2 hu)
    exact key
  · exact sup_le (H.imgOne_anti (Nat.gcd_dvd_left f g) hf) (H.imgOne_anti (Nat.gcd_dvd_right f g) hg)
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.LogPrimeIndep
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem UpperTheory.HF.log_prime_indep_fact (S : Finset ℕ) (u : ℕ → ℕ) (hS : ∀ l ∈ S, l.Prime)
    (p : ℕ) (hp : p ∈ S) : (∏ l ∈ S, l ^ u l).factorization p = u p := by
  rw [Nat.factorization_prod (fun l hl => pow_ne_zero _ (hS l hl).ne_zero), Finsupp.finsetSum_apply,
    Finset.sum_eq_single p]
  · rw [(hS p hp).factorization_pow]; simp
  · intro l hl hne
    rw [(hS l hl).factorization_pow]; simp [Finsupp.single_apply, hne]
  · intro h; exact absurd hp h

private theorem UpperTheory.HF.log_prime_indep_nat (S : Finset ℕ) (u v : ℕ → ℕ) (hS : ∀ l ∈ S, l.Prime)
    (h : ∑ l ∈ S, (u l : ℝ) * Real.log l = ∑ l ∈ S, (v l : ℝ) * Real.log l) :
    ∀ l ∈ S, u l = v l := by
  have key : ∀ w : ℕ → ℕ, ∑ l ∈ S, (w l : ℝ) * Real.log l
      = Real.log ((∏ l ∈ S, l ^ w l : ℕ) : ℝ) := by
    intro w
    push_cast
    rw [Real.log_prod (fun l hl => pow_ne_zero _ (by exact_mod_cast (hS l hl).ne_zero))]
    exact Finset.sum_congr rfl (fun l _ => (Real.log_pow _ _).symm)
  have pos : ∀ w : ℕ → ℕ, (0 : ℝ) < ((∏ l ∈ S, l ^ w l : ℕ) : ℝ) := by
    intro w
    exact_mod_cast Finset.prod_pos (fun l hl => pow_pos (hS l hl).pos _)
  rw [key u, key v] at h
  have h2 := Real.log_injOn_pos (Set.mem_Ioi.2 (pos u)) (Set.mem_Ioi.2 (pos v)) h
  have h3 : (∏ l ∈ S, l ^ u l) = ∏ l ∈ S, l ^ v l := by exact_mod_cast h2
  intro p hp
  rw [← UpperTheory.HF.log_prime_indep_fact S u hS p hp, ← UpperTheory.HF.log_prime_indep_fact S v hS p hp, h3]

private theorem UpperTheory.HF.log_prime_indep_int (S : Finset ℕ) (m : ℕ → ℤ) (hS : ∀ l ∈ S, l.Prime)
    (h : ∑ l ∈ S, (m l : ℝ) * Real.log l = 0) : ∀ l ∈ S, m l = 0 := by
  have h1 := UpperTheory.HF.log_prime_indep_nat S (fun l => (m l).toNat) (fun l => (-m l).toNat) hS (by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← sub_mul]
    congr 1
    have : (((m l).toNat : ℤ)) - ((-m l).toNat : ℤ) = m l := Int.toNat_sub_toNat_neg _
    exact_mod_cast this)
  intro l hl
  have := h1 l hl
  omega

theorem UpperTheory.HF.log_prime_indep :
    ∀ (S : Finset ℕ) (a b : ℕ → ℚ), (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (a l : ℝ) * Real.log l = ∑ l ∈ S, (b l : ℝ) * Real.log l → ∀ l ∈ S, a l = b l := by
  intro S a b hS h
  set D : ℕ := ∏ l ∈ S, (a l - b l).den with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun l _ => (a l - b l).den_nz)
  have hex : ∀ l, ∃ z : ℤ, l ∈ S → (z : ℚ) = (a l - b l) * D := by
    intro l
    by_cases hl : l ∈ S
    · obtain ⟨k, hk⟩ : (a l - b l).den ∣ D := Finset.dvd_prod_of_mem (fun l => (a l - b l).den) hl
      refine ⟨(a l - b l).num * k, fun _ => ?_⟩
      rw [hk]; push_cast
      rw [← mul_assoc, Rat.mul_den_eq_num]
    · exact ⟨0, fun h => absurd h hl⟩
  choose m hm using hex
  have h0 := UpperTheory.HF.log_prime_indep_int S m hS (by
    have : ∑ l ∈ S, (m l : ℝ) * Real.log l
        = (∑ l ∈ S, (a l : ℝ) * Real.log l - ∑ l ∈ S, (b l : ℝ) * Real.log l) * D := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have h1 : ((m l : ℚ) : ℝ) = (((a l - b l) * D : ℚ) : ℝ) := by rw [hm l hl]
      push_cast at h1
      rw [h1]; ring
    rw [this, h, sub_self, zero_mul])
  intro l hl
  have h1 := hm l hl
  rw [h0 l hl] at h1
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
  have : a l - b l = 0 := by
    rcases mul_eq_zero.1 (by simpa using h1.symm : (a l - b l) * (D : ℚ) = 0) with h | h
    · exact h
    · exact absurd h hDq
  exact sub_eq_zero.1 this
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.LogRdSum
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.log_rd_sum :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l ∧ Real.log H.rd = ∑ l ∈ H.condN.primeFactors, H.vdH l * Real.log l ∧ H.ram ⊆ H.condN.primeFactors ∧ 0 < H.rd := by
  intro φ H
  have hd : discr H.E ≠ 0 := discr_ne_zero H.E
  have hd' : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hd
  have habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpos : 0 < |(discr H.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have h1 : Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l := by
    unfold HostRaw.rd HostRaw.ram HostRaw.vdH
    rw [Real.log_rpow hpos, habs, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]
    rw [Nat.padicValNat_def]
    ring
  have h3 : H.ram ⊆ H.condN.primeFactors := by
    intro l hl
    have h := Nat.mem_primeFactors.1 hl
    exact Nat.mem_primeFactors.2 ⟨h.1, H.der.discr_primes.1 l h.1 (Int.natCast_dvd.2 h.2.1), H.condN_ne_zero⟩
  refine ⟨h1, ?_, h3, Real.rpow_pos_of_pos hpos _⟩
  rw [h1]
  refine Finset.sum_subset h3 fun l hl hn => ?_
  have hp := Nat.prime_of_mem_primeFactors hl
  have : ¬ l ∣ (discr H.E).natAbs := fun h => hn (Nat.mem_primeFactors.2 ⟨hp, h, hd'⟩)
  unfold HostRaw.vdH
  rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd this]
  simp
end

