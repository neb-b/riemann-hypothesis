module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
section
open UpperTheory.V.FW

private theorem card_dual (K A : Type) [Field K] [AddCommGroup A] [Module K A] [Finite A] :
    Nat.card (Module.Dual K A) = Nat.card A := by
  exact Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv

private theorem card_addHom_mod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    [Module (ZMod l) A] : Nat.card (A →+ ZMod l) = Nat.card A := by
  rw [← card_dual (ZMod l) A]
  exact Nat.card_congr
    { toFun := fun f => f.toZModLinearMap l
      invFun := fun g => g.toAddMonoidHom
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }

private theorem card_addHom_zmod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    (h : ∀ x : A, l • x = 0) : Nat.card (A →+ ZMod l) = Nat.card A :=
  @card_addHom_mod l _ A _ _ (AddCommGroup.zmodModule h)

theorem UpperTheory.V.FW.cardTors :
    ∀ (C : Type) [CommGroup C] [Finite C], (∀ n : ℕ, (powR (C := C) n).index = Nat.card (torK (C := C) n)) ∧ ∀ (l : ℕ) [Fact l.Prime], Nat.card (C →* Multiplicative (ZMod l)) = (powR (C := C) l).index := by
  intro C _ _
  refine ⟨fun n => ?_, fun l _ => ?_⟩
  · have h1 := Subgroup.card_mul_index (powR (C := C) n)
    have h2 := Subgroup.card_mul_index (torK (C := C) n)
    have h3 : (torK (C := C) n).index = Nat.card (powR (C := C) n) := Subgroup.index_ker _
    rw [h3] at h2
    have hpos : 0 < Nat.card (powR (C := C) n) := Nat.card_pos
    have h4 : Nat.card (powR (C := C) n) * (powR (C := C) n).index
        = Nat.card (powR (C := C) n) * Nat.card (torK (C := C) n) := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  · set N := powR (C := C) l
    have hle : ∀ f : C →* Multiplicative (ZMod l), N ≤ f.ker := by
      intro f x hx
      change x ∈ (powMonoidHom l : C →* C).range at hx
      rcases MonoidHom.mem_range.mp hx with ⟨c, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow]
    have e : (C ⧸ N →* Multiplicative (ZMod l)) ≃ (C →* Multiplicative (ZMod l)) :=
      { toFun := fun g => g.comp (QuotientGroup.mk' N)
        invFun := fun f => QuotientGroup.lift N f (hle f)
        left_inv := fun g => by
          apply QuotientGroup.monoidHom_ext
          ext
          rfl
        right_inv := fun f => by
          ext
          rfl }
    rw [← Nat.card_congr e, Nat.card_congr MonoidHom.toAdditiveLeft]
    have ht : ∀ x : Additive (C ⧸ N), l • x = 0 := by
      intro x
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N (Additive.toMul x)
      apply Additive.toMul.injective
      rw [toMul_nsmul, ← hc, toMul_zero, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow,
        QuotientGroup.eq_one_iff]
      change c ^ l ∈ (powMonoidHom l : C →* C).range
      exact MonoidHom.mem_range.mpr ⟨c, by simp [powMonoidHom_apply]⟩
    rw [card_addHom_zmod l (Additive (C ⧸ N)) ht]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CharPer
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.charPer :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) [NeZero (f * l ^ n)] (k : Type) [Field k] [CharP k l] (χ : (ZMod (f * l ^ n))ˣ →* kˣ) (s : ZMod (f * l ^ n)), f.Coprime l → 1 ≤ n → MulChar.ofUnitHom χ (s + ((f * l : ℕ) : ZMod (f * l ^ n))) = MulChar.ofUnitHom χ s := by
  intro l hl f n _ k _ _ χ s hf hn
  set M : ZMod (f * l ^ n) := ((f * l : ℕ) : ZMod (f * l ^ n)) with hM
  have hnil : IsNilpotent M := by
    refine ⟨n, ?_⟩
    rw [hM, ← Nat.cast_pow, CharP.cast_eq_zero_iff (ZMod (f * l ^ n)) (f * l ^ n), mul_pow]
    exact Nat.mul_dvd_mul_right (dvd_pow_self f (by omega)) _
  by_cases hs : IsUnit s
  swap
  · have hs' : ¬ IsUnit (s + M) := by
      intro h
      apply hs
      simpa using hnil.neg.isUnit_add_right_of_commute h (Commute.all _ _)
    rw [MulChar.map_nonunit _ hs, MulChar.map_nonunit _ hs']
  obtain ⟨u, rfl⟩ := hs
  set t : ℤ := ((((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)).val : ℕ) : ℤ) with ht
  set w : ZMod (f * l ^ n) := 1 + M * ((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)) with hw
  have hsplit : (u : ZMod (f * l ^ n)) + M = u * w := by
    rw [hw, mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one]
  have hwint : w = ((1 + (f : ℤ) * l * t : ℤ) : ZMod (f * l ^ n)) := by
    rw [hw, hM, ht]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hdvd : ((f * l ^ n : ℕ) : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
    have h1 : ((l : ℕ) : ℤ) ^ (n - 1 + 1) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 ^ (l ^ (n - 1)) :=
      dvd_sub_pow_of_dvd_sub (by simp only [add_sub_cancel_left]; exact ⟨f * t, by ring⟩) _
    rw [Nat.sub_add_cancel hn, one_pow] at h1
    have h2 : (f : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
      have := sub_dvd_pow_sub_pow (1 + (f : ℤ) * l * t) 1 (l ^ (n - 1))
      rw [one_pow] at this
      exact dvd_trans ⟨l * t, by ring⟩ this
    have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ n) := by
      have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right n hf)
      simpa using this
    push_cast
    exact hcop.mul_dvd h2 h1
  have hwpow : w ^ (l ^ (n - 1)) = 1 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    rw [hwint]
    push_cast at h0 ⊢
    linear_combination h0
  have hcw : MulChar.ofUnitHom χ w = 1 := by
    have hp : (MulChar.ofUnitHom χ w) ^ (l ^ (n - 1)) = 1 := by
      rw [← map_pow, hwpow, map_one]
    have : (MulChar.ofUnitHom χ w - 1) ^ (l ^ (n - 1)) = 0 := by
      rw [sub_pow_char_pow, hp, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero)).mp this)
  rw [hsplit, map_mul, hcw, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.DescZRetr
section
open UpperTheory.V.FW

private theorem UpperTheory.V.FW.descZ_retr (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    ∃ ϖ : k →+ ZMod l, ϖ 1 = 1 := by
  letI := ZMod.algebra k l
  have hinj : LinearMap.ker (LinearMap.toSpanSingleton (ZMod l) k 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one] at h
    exact (algebraMap (ZMod l) k).injective h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨g.toAddMonoidHom, ?_⟩
  have h1 := LinearMap.congr_fun hg 1
  simpa using h1

private theorem UpperTheory.V.FW.descZ_mul {k F G : Type} [CommRing k] [CommRing F] [CommGroup G] (ϖ : k →+ F)
    (u : MonoidAlgebra k G) (a : MonoidAlgebra ℤ G) :
    MonoidAlgebra.map ϖ (u * toK k G a) = MonoidAlgebra.map ϖ u * toK F G a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), mul_add, MonoidAlgebra.map_add (f := _), hx, hy, map_add (f := _), mul_add]
  | single g n =>
    ext h
    simp only [toK, MonoidAlgebra.mapRingHom_single, eq_intCast, MonoidAlgebra.coeff_map,
      Finsupp.mapRange_apply, MonoidAlgebra.mul_single_apply, AddMonoidHom.coe_coe]
    rw [← zsmul_eq_mul', map_zsmul, zsmul_eq_mul']

private theorem UpperTheory.V.FW.descZ_ker (l : ℕ) {G : Type} [CommGroup G] (y : MonoidAlgebra ℤ G)
    (hy : toK (ZMod l) G y = 0) : ∃ z, y = z * (l : MonoidAlgebra ℤ G) := by
  classical
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun n : ℤ => n / (l : ℤ)) (by simp) y.coeff), ?_⟩
  ext g
  have hg : (l : ℤ) ∣ y.coeff g := by
    have h0 := congrArg (fun w => w.coeff g) hy
    simp only [toK, MonoidAlgebra.coeff_mapRingHom, eq_intCast, MonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h0
    exact (CharP.intCast_eq_zero_iff (ZMod l) l _).mp h0
  rw [MonoidAlgebra.natCast_def, MonoidAlgebra.mul_single_apply, inv_one, mul_one,
    MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, Int.ediv_mul_cancel hg]

theorem UpperTheory.V.FW.descZ :
    ∀ (l : ℕ) [Fact l.Prime] (k G : Type) [Field k] [CharP k l] [CommGroup G] (x a b : MonoidAlgebra ℤ G), toK k G x ∈ Ideal.span {toK k G a, toK k G b} → x ∈ Ideal.span {a, b, (l : MonoidAlgebra ℤ G)} := by
  intro l _ k G _ _ _ x a b hx
  obtain ⟨ϖ, hϖ⟩ := descZ_retr l k
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hx
  have h1 : MonoidAlgebra.map ϖ (1 : MonoidAlgebra k G) = 1 := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.map_single, hϖ, MonoidAlgebra.one_def]
  have h2 := descZ_mul ϖ 1 x
  rw [one_mul, h1, one_mul, ← huv, MonoidAlgebra.map_add (f := _), descZ_mul, descZ_mul] at h2
  have hs : Function.Surjective (toK (ZMod l) G) :=
    MonoidAlgebra.map_surjective (Int.castRingHom (ZMod l) : ℤ →+ ZMod l) ZMod.intCast_surjective
  obtain ⟨u', hu⟩ := hs (MonoidAlgebra.map ϖ u)
  obtain ⟨v', hv⟩ := hs (MonoidAlgebra.map ϖ v)
  obtain ⟨z, hz⟩ := descZ_ker l (x - (u' * a + v' * b)) (by
    rw [map_sub, map_add (f := _), map_mul, map_mul, hu, hv, h2, sub_self])
  have hx' : x = u' * a + v' * b + z * (l : MonoidAlgebra ℤ G) := by rw [← hz]; ring
  rw [hx']
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FrobEig
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.frobEig :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) (k G A : Type) [Field k] [CharP k l] [CommGroup G] [CommRing A] [Algebra k A] (r : MonoidAlgebra k G →ₐ[k] A) (p : G →* G) (χ : G →* kˣ) (e : A) (θ : MonoidAlgebra k G), (∀ g, r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ l ^ a)) * e = ((χ g : k) ^ l ^ a) • e) → r θ ^ l ^ a * e = r (tw χ p θ) ^ l ^ a * e := by
  intro l _ a k G A _ _ _ _ _ r p χ e θ h
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  haveI : CharP A l := charP_of_injective_algebraMap (algebraMap k A).injective l
  set q := l ^ a with hq
  have frob_add : ∀ x y : A, (x + y) ^ q = x ^ q + y ^ q := fun x y => by
    rw [hq]
    exact add_pow_char_pow x y l a
  have hs : ∀ (x : G) (b : k), r (MonoidAlgebra.single x b) ^ q = b ^ q • r (MonoidAlgebra.of k G (x ^ q)) := by
    intro x b
    have e1 : MonoidAlgebra.single x b = b • MonoidAlgebra.of k G x := by
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
    rw [e1, map_smul, smul_pow, map_pow (MonoidAlgebra.of k G), map_pow r]
  induction θ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), frob_add, add_mul, hf, hg]
  | single g c =>
    rw [tw_single, hs, hs]
    have hg : g ^ q = (g * (p g)⁻¹) ^ q * (p g) ^ q := by
      rw [mul_pow, inv_pow, inv_mul_cancel_right]
    rw [hg, map_mul, map_mul, smul_mul_assoc, smul_mul_assoc,
      mul_comm (r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ q))), mul_assoc, h g, mul_smul_comm,
      smul_smul, mul_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GamGen
section
open UpperTheory.V.FW

private theorem padic_val_one_add_mul_pow_pow_sub_one (l : ℕ) (hl : l.Prime) (f : ℕ) (hf : f.Coprime l) (j : ℕ) :
    (l : ℤ) ^ (ee l + j) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 ∧
      ¬ (l : ℤ) ^ (ee l + j + 1) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hfl : ¬ (l : ℤ) ∣ (f : ℤ) := by
    intro hd
    have hd' : l ∣ f := Int.natCast_dvd_natCast.mp hd
    exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hf.symm hd')
  have hq : emultiplicity (l : ℤ) ((f : ℤ) * (l : ℤ) ^ ee l) = (ee l : ℕ∞) := by
    rw [emultiplicity_mul hp, emultiplicity_pow_self_of_prime hp, emultiplicity_eq_zero.mpr hfl,
      zero_add]
  have hx : ¬ (l : ℤ) ∣ 1 + (f : ℤ) * (l : ℤ) ^ ee l := by
    intro hd
    have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
    have h2 : (l : ℤ) ∣ (f : ℤ) * (l : ℤ) ^ ee l :=
      Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    have h3 : (l : ℤ) ∣ 1 := by
      have := dvd_sub hd h2
      simpa using this
    have h4 : l ∣ 1 := by exact_mod_cast h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h4)
  have key : emultiplicity (l : ℤ) ((1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1)
      = ((ee l + j : ℕ) : ℕ∞) := by
    by_cases h2 : l = 2
    · subst h2
      have e2 : ee 2 = 2 := by simp [ee]
      have h4 : (4 : ℤ) ∣ (1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) - 1 := by
        rw [e2]
        exact ⟨f, by push_cast; ring⟩
      have hx2 : ¬ (2 : ℤ) ∣ 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2 := by
        simpa using hx
      have := Int.two_pow_two_pow_sub_pow_two_pow (x := 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2)
        (y := 1) j h4 hx2
      rw [one_pow, add_sub_cancel_left] at this
      have hq2 : emultiplicity (2 : ℤ) ((f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) = (ee 2 : ℕ∞) := by
        simpa using hq
      rw [hq2] at this
      have : emultiplicity ((2 : ℕ) : ℤ) ((1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) ^ 2 ^ j - 1)
          = (ee 2 : ℕ∞) + j := by simpa using this
      rw [this]
      push_cast
      rfl
    · have hodd : Odd l := hl.odd_of_ne_two h2
      have e1 : ee l = 1 := by simp [ee, h2]
      have hxy : (l : ℤ) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) - 1 := by
        rw [add_sub_cancel_left]
        exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
      have := Int.emultiplicity_pow_sub_pow hl hodd hxy hx (l ^ j)
      rw [one_pow, add_sub_cancel_left, hq,
        emultiplicity_pow_self_of_prime (Nat.prime_iff.mp hl) j] at this
      rw [this]
      push_cast
      rfl
  constructor
  · rw [pow_dvd_iff_le_emultiplicity, key]
  · rw [pow_dvd_iff_le_emultiplicity, key]
    norm_cast
    omega

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.FW.gamGen :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (γ : (ZMod (f * l ^ n))ˣ), f.Coprime l → ee l ≤ n → (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l → (ZMod.unitsMap h).ker = Subgroup.zpowers γ ∧ γ ^ l ^ n = 1 := by
  intro l _ f n h γ hf hen hγ
  have hl : l.Prime := Fact.out
  obtain ⟨d, rfl⟩ : ∃ d, n = ee l + d := ⟨n - ee l, by omega⟩
  have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : l = 1 := by simpa [Nat.Coprime] using hf
    exact hl.one_lt.ne' this
  haveI : NeZero (f * l ^ (ee l + d)) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (f * l ^ ee l) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  set x : ℤ := 1 + (f : ℤ) * (l : ℤ) ^ ee l with hxdef
  have hγx : (γ : ZMod (f * l ^ (ee l + d))) = ((x : ℤ) : ZMod (f * l ^ (ee l + d))) := by
    rw [hγ, hxdef]
    push_cast
    ring
  have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ (ee l + d)) := by
    rw [← Int.natCast_pow, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ hf
  have hpow : ∀ m : ℕ, γ ^ m = 1 ↔ (l : ℤ) ^ (ee l + d) ∣ x ^ m - 1 := by
    intro m
    have hfdvd : (f : ℤ) ∣ x ^ m - 1 := by
      have h1 : x - 1 ∣ x ^ m - 1 ^ m := sub_dvd_pow_sub_pow x 1 m
      rw [one_pow] at h1
      refine dvd_trans ?_ h1
      rw [hxdef, add_sub_cancel_left]
      exact dvd_mul_right _ _
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, hγx, ← Int.cast_pow,
      ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    constructor
    · intro hd
      exact dvd_trans (dvd_mul_left _ _) hd
    · intro hd
      exact hcop.mul_dvd hfdvd hd
  have hord : orderOf γ = l ^ d := by
    rcases d with _ | d
    · rw [pow_zero, orderOf_eq_one_iff]
      have h1 : γ ^ (l ^ 0) = 1 := by
        rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf 0).1
      simpa using h1
    · apply orderOf_eq_prime_pow
      · rw [hpow, hxdef, ← Nat.add_assoc]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf d).2
      · rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf (d + 1)).1
  set K := (ZMod.unitsMap h).ker with hK
  have c1 : Nat.card (ZMod (f * l ^ (ee l + d)))ˣ = (f * l ^ (ee l + d)).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have c2 : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcardK : Nat.card K = l ^ d := by
    have a := Subgroup.card_mul_index K
    rw [hK, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective h),
      Subgroup.card_top, c1, c2,
      Nat.totient_mul (Nat.Coprime.pow_right _ hf), Nat.totient_mul (Nat.Coprime.pow_right _ hf),
      Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)] at a
    have hpos : 0 < f.totient * (l ^ (ee l - 1) * (l - 1)) := by
      have h1 := hl.one_lt
      have h2 := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hf0)
      exact Nat.mul_pos h2 (Nat.mul_pos (pow_pos hl.pos _) (by omega))
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hK, a]
    have : ee l + d - 1 = (ee l - 1) + d := by omega
    rw [this, pow_add]
    ring
  have hmem : γ ∈ K := by
    rw [hK, MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, Units.val_one,
      MonoidHom.coe_coe, hγ, map_add, map_one, map_mul, map_pow, map_natCast, map_natCast]
    have h0 : ((f * l ^ ee l : ℕ) : ZMod (f * l ^ ee l)) = 0 := ZMod.natCast_self _
    push_cast at h0
    rw [h0, add_zero]
  have hle : Subgroup.zpowers γ ≤ K := (Subgroup.zpowers_le).mpr hmem
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle ?_).symm, ?_⟩
  · rw [Nat.card_zpowers, hord, hcardK]
  · rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact pow_dvd_pow l (by omega)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcDiff
section
open UpperTheory.V.FW

private theorem norm_index_count_bound (M a c : ℕ) :
    (((a + c) / M : ℕ) : ℤ) = ((a / M : ℕ) : ℤ) +
      ∑ j ∈ Finset.range c, if (j : ZMod M) = ((a + c : ℕ) : ZMod M) then 1 else 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have e : a + (c + 1) = (a + c) + 1 := by omega
    have h1 : ∀ j : ℕ, (((j + 1 : ℕ) : ZMod M) = (((a + c + 1 : ℕ)) : ZMod M)) ↔
        ((j : ZMod M) = ((a + c : ℕ) : ZMod M)) := by
      intro j
      push_cast
      exact add_left_inj 1
    have h2 : ((0 : ℕ) : ZMod M) = ((a + c + 1 : ℕ) : ZMod M) ↔ M ∣ a + c + 1 := by
      rw [Nat.cast_zero, eq_comm]
      exact CharP.cast_eq_zero_iff (ZMod M) M _
    rw [e, Nat.succ_div, Finset.sum_range_succ']
    simp only [h1, h2]
    rw [Nat.cast_add, ih]
    split_ifs <;> push_cast <;> ring

theorem UpperTheory.V.FW.gcDiff :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → gc M c s - gc M c (s - c) = (∑ j ∈ Finset.range c, if (j : ZMod M) = s then 1 else 0) - if s = 0 then (c : ℤ) else 0 := by
  intro M c _ s hc
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hinv : (c : ZMod M)⁻¹ * (c : ZMod M) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one c hc
  have hts : (c : ZMod M)⁻¹ * (s - c) = (c : ZMod M)⁻¹ * s - 1 := by
    rw [mul_sub, hinv]
  unfold UpperTheory.V.FW.gc
  rw [hts]
  set t : ZMod M := (c : ZMod M)⁻¹ * s with ht
  have hs : s = (c : ZMod M) * t := by
    rw [ht, ← mul_assoc, ZMod.coe_mul_inv_eq_one c hc, one_mul]
  set w := (t - 1).val with hw
  have htw : t = ((w + 1 : ℕ) : ZMod M) := by
    rw [Nat.cast_add, Nat.cast_one, hw, ZMod.natCast_zmod_val]
    ring
  have key := norm_index_count_bound M (c * w) c
  have hcast : ((c * w + c : ℕ) : ZMod M) = s := by
    rw [hs, htw]
    push_cast
    ring
  rw [hcast] at key
  rcases Nat.lt_or_ge (w + 1) M with h | h
  · have hvt : t.val = w + 1 := by
      rw [htw, ZMod.val_natCast, Nat.mod_eq_of_lt h]
    have hs0 : s ≠ 0 := by
      intro h0
      have t0 : t = 0 := by rw [ht, h0, mul_zero]
      rw [t0, ZMod.val_zero] at hvt
      omega
    rw [hvt, if_neg hs0, sub_zero]
    have e : c * (w + 1) = c * w + c := by ring
    rw [e, key]
    ring
  · have hwe : w + 1 = M := by
      have := ZMod.val_lt (t - 1)
      omega
    have ht0 : t = 0 := by rw [htw, hwe, ZMod.natCast_self]
    have hs0 : s = 0 := by rw [hs, ht0, mul_zero]
    rw [ht0, ZMod.val_zero, if_pos hs0]
    have e : c * w + c = c * M := by rw [← hwe]; ring
    rw [e, Nat.mul_div_cancel _ hM] at key
    simp only [mul_zero, Nat.zero_div, Nat.cast_zero]
    linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HalfSum
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.halfSum :
    ∀ (α k : Type) [AddCommMonoid k] (σ : α → α) (H H' : Finset α) (g : α → k), (∀ x, σ (σ x) = x) → (∀ x, g (σ x) = g x) → (∀ x ∈ H, σ x ∉ H) → (∀ x ∈ H', σ x ∉ H') → (∀ x ∈ H, x ∈ H' ∨ σ x ∈ H') → (∀ x ∈ H', x ∈ H ∨ σ x ∈ H) → ∑ x ∈ H, g x = ∑ x ∈ H', g x := by
  classical
  intro α k _ σ H H' g hσ hg hH hH' hHH' hH'H
  refine Finset.sum_bij' (fun x _ => if x ∈ H' then x else σ x) (fun y _ => if y ∈ H then y else σ y)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp only [h, if_false]
      exact (hHH' x hx).resolve_left h
  · intro y hy
    by_cases h : y ∈ H
    · simp [h]
    · simp only [h, if_false]
      exact (hH'H y hy).resolve_left h
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h, hx]
    · simp [h, hH x hx, hσ]
  · intro y hy
    by_cases h : y ∈ H
    · simp [h, hy]
    · simp [h, hH' y hy, hσ]
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp [h, hg]
end

