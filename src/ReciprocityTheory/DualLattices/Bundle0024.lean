module

public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.DualLattices.Bundle0005
public import ReciprocityTheory.DualLattices.Bundle0011
public import ReciprocityTheory.DualLattices.HeightFunctionalStatementOfPairingProperties
public import ReciprocityTheory.DualLattices.Bundle0002
public import ReciprocityTheory.DualLattices.Bundle0010
public import ReciprocityTheory.DualLattices.Bundle0022
public import ReciprocityTheory.DualLattices.Bundle0020
public import ReciprocityTheory.DualLattices.Bundle0001
public import ReciprocityTheory.DualLattices.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.EmbeddingSeparatingGroup
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem embeddingSeparatingGroup : EmbeddingSeparatingGroupStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U
  have hv : v.Integers R := hS.integers
  have hpv : v (algebraMap R C (p : R)) < 1 := hS.p_lt
  have hp : p.Prime := Fact.out

  have hvnat : ∀ n : ℕ, ¬ p ∣ n → v (algebraMap R C (n : R)) = 1 := by
    intro n hn
    by_contra hne
    have hlt : v (algebraMap R C (n : R)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hne
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
    have h1 : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
    have h2 : (p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R) = 1 := by
      have := congrArg (fun z : ℤ => (z : R)) h1
      push_cast at this
      exact this
    have h3 : v (algebraMap R C ((p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R))) < 1 := by
      rw [map_add (f := _)]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hpv
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hlt
    rw [h2, map_one, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  have hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : R) := by
    intro n hn
    have hn0 : (n : C) ≠ 0 := by
      have : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
      exact_mod_cast this
    exact hv.isUnit_of_one (isUnit_iff_ne_zero.2 (by rw [map_natCast]; exact hn0)) (hvnat n hn)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have heig : ∀ a j, (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j = U.sg j a • U.εT j := U.εT_eig
  have hres1 : FrobeniusGroupField.res hv 1 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 1).2 (by simp)

  have hex : ∀ t : Option (Fin U.m × Fin U.m × Bool), ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧
      H.ρ b ^ m = 1 ∧
      (match t with
        | none => ∀ j, U.εT j ≠ 0 → v (algebraMap R C (U.sg j b - 1)) = 1
        | some (i, k, e) => U.εT i ≠ 0 → U.εT k ≠ 0 → cond e (k ≠ U.φ i) (i ≠ k) →
            FrobeniusGroupField.res hv (U.sg k b) ≠ FrobeniusGroupField.res hv (U.sg i b) ^ p ^ e.toNat) := by
    intro t
    rcases t with _ | ⟨i, k, e⟩
    · obtain ⟨b, m, s, hm, hmp, hbm, hb⟩ := FrobeniusGroupField.seed p hv hpv H.ρ U.εT U.sg heig 0 2
      refine ⟨b, m, hm, hmp, hbm, ?_⟩
      intro j hj
      have h2 : FrobeniusGroupField.res hv (U.sg j 0 + ((2 : ℤ) : R)) = FrobeniusGroupField.res hv 2 := by simp
      have hr2 : FrobeniusGroupField.res hv 2 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 2).2 (by simpa using hvnat 2 hp2')
      have hfer : ∀ s : ℕ, FrobeniusGroupField.res hv 2 ^ p ^ s = FrobeniusGroupField.res hv 2 := by
        intro s
        induction s with
        | zero => simp
        | succ s ih =>
          have hf := FrobeniusGroupField.fermat p hv hpv (2 : ℤ_[p])
          rw [map_ofNat] at hf
          rw [pow_succ, pow_mul, ih, hf]
      have hbj := hb j hj (by rw [h2]; exact hr2)
      rw [h2, hfer] at hbj
      apply (FrobeniusGroupField.res_ne_zero hv _).1
      rw [map_sub, hbj, map_one]
      have h21 : FrobeniusGroupField.res hv 2 - 1 = FrobeniusGroupField.res hv 1 := by
        rw [← map_one (FrobeniusGroupField.res hv), ← map_sub]
        norm_num
      rw [h21]
      exact hres1
    · by_cases hall : U.εT i ≠ 0 ∧ U.εT k ≠ 0 ∧ cond e (k ≠ U.φ i) (i ≠ k)
      · obtain ⟨hi, hk, hik⟩ := hall
        have ha : ∃ a, FrobeniusGroupField.res hv (U.sg k a) ≠ FrobeniusGroupField.res hv (U.sg i a) ^ p ^ e.toNat := by
          cases e
          · simp only [cond_false, Bool.toNat_false, pow_zero, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct i k hik
            refine ⟨a, fun heq => ?_⟩
            have h0 : FrobeniusGroupField.res hv (U.sg i a - U.sg k a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
          · simp only [cond_true, Bool.toNat_true, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct k (U.φ i) hik
            refine ⟨a, ?_⟩
            have hfr : FrobeniusGroupField.res hv (U.sg (U.φ i) a) = FrobeniusGroupField.res hv (U.sg i a) ^ p := by
              have h0 := (FrobeniusGroupField.res_eq_zero hv _).2 (U.frob i a)
              rw [map_sub, map_pow, sub_eq_zero] at h0
              exact h0
            rw [← hfr]
            intro heq
            have h0 : FrobeniusGroupField.res hv (U.sg k a - U.sg (U.φ i) a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
        obtain ⟨a, ha⟩ := ha
        obtain ⟨b, m, hm, hmp, hbm, hb⟩ :=
          FrobeniusGroupField.pair p hp2 hv hpv H.ρ U.εT U.sg heig a e.toNat i k hi hk ha
        exact ⟨b, m, hm, hmp, hbm, fun _ _ _ => hb⟩
      · exact ⟨1, 1, one_pos, hp.not_dvd_one, by simp, fun hi hk hik => absurd ⟨hi, hk, hik⟩ hall⟩
  choose b m0 hm0 hmp0 hbm0 hQ using hex

  let m : Option (Fin U.m × Fin U.m × Bool) → ℕ := fun t => 2 * m0 t
  have hm : ∀ t, 0 < m t := fun t => by
    have := hm0 t
    show 0 < 2 * m0 t
    omega
  have hmp : ∀ t, ¬ p ∣ m t := fun t h => ((Nat.Prime.dvd_mul hp).1 h).elim hp2' (hmp0 t)
  have hbm : ∀ t, H.ρ (b t) ^ m t = 1 := fun t => by
    show H.ρ (b t) ^ (2 * m0 t) = 1
    rw [mul_comm, pow_mul, hbm0 t, one_pow]
  haveI : ∀ t, NeZero (m t) := fun t => ⟨(hm t).ne'⟩
  have hone : ∀ t, (1 : ZMod (m t)).val = 1 := fun t => by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by have := hm0 t; show 1 < 2 * m0 t; omega)
  let G := ∀ t : Option (Fin U.m × Fin U.m × Bool), Multiplicative (ZMod (m t))
  let β : G → O := fun γ => ∏ t, b t ^ (Multiplicative.toAdd (γ t)).val
  have key : ∀ (s : Finset (Option (Fin U.m × Fin U.m × Bool)))
      (n : Option (Fin U.m × Fin U.m × Bool) → ℕ),
      H.ρ (∏ t ∈ s, b t ^ n t) = H.ρ (∏ t ∈ s, b t ^ (n t % m t)) := by
    intro s n
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, map_mul, ih, map_pow, map_pow,
      ← pow_eq_pow_mod _ (hbm a)]
  have hmul : ∀ γ γ' : G, H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ') := by
    intro γ γ'
    have e1 : β (γ * γ') = ∏ t, b t ^ (((Multiplicative.toAdd (γ t)).val +
        (Multiplicative.toAdd (γ' t)).val) % m t) := by
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Pi.mul_apply, toAdd_mul, ZMod.val_add]
    have k2 := key Finset.univ
      (fun t => (Multiplicative.toAdd (γ t)).val + (Multiplicative.toAdd (γ' t)).val)
    beta_reduce at k2
    rw [e1, ← k2, ← map_mul]
    congr 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => pow_add _ _ _
  have h1 : H.ρ (β 1) = 1 := by
    have hb1 : β 1 = 1 := by
      refine (Finset.prod_congr rfl fun t _ => ?_).trans Finset.prod_const_one
      show b t ^ (Multiplicative.toAdd ((1 : G) t)).val = 1
      rw [Pi.one_apply, toAdd_one, ZMod.val_zero, pow_zero]
    rw [hb1, map_one]
  have hcard : IsUnit (Fintype.card G : R) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun t _ => ?_
    have hc : Fintype.card (Multiplicative (ZMod (m t))) = m t := by simp
    rw [hc]
    exact hunit _ (hmp t)
  let gen : Option (Fin U.m × Fin U.m × Bool) → G := fun t =>
    Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t)))
  have hgen : ∀ t, β (gen t) = b t := by
    intro t
    show ∏ u, b u ^ (Multiplicative.toAdd
      (Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t))) u)).val
      = b t
    rw [Finset.prod_eq_single t]
    · rw [Pi.mulSingle_eq_same, toAdd_ofAdd, hone, pow_one]
    · intro u _ hu
      rw [Pi.mulSingle_eq_of_ne hu, toAdd_one, ZMod.val_zero, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  have hsep' : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      FrobeniusGroupField.res hv (U.sg k (b (some (i, k, false)))) ≠ FrobeniusGroupField.res hv (U.sg i (b (some (i, k, false)))) := by
    intro i k hi hk hik
    have hq := hQ (some (i, k, false)) hi hk (by simpa using hik)
    simpa using hq
  have hsepψ : ∀ j k, U.εT j ≠ 0 → U.εT k ≠ 0 → j ≠ k → ∃ γ : G, U.sg j (β γ) ≠ U.sg k (β γ) := by
    intro j k hj hk hjk
    refine ⟨gen (some (j, k, false)), ?_⟩
    rw [hgen]
    intro heq
    exact hsep' j k hj hk hjk (by rw [heq])
  refine ⟨G, inferInstance, inferInstance, β, hmul, h1, hcard, ?_, ?_, ?_⟩
  · intro i γ hi
    obtain ⟨j, hj, hψ⟩ := FrobeniusGroupField.proj p hv hpv hcard (fun γ => H.ρ (β γ)) hmul h1 U.εT U.εT_orth
      U.εT_sum (fun j γ => U.sg j (β γ)) (fun j γ => U.εT_eig (β γ) j)
      (fun j k hj hk hjk => hsepψ j k hj hk hjk) i hi
    have hjφ : j = U.φ i := by
      by_contra hne
      have hq := hQ (some (i, j, true)) hi hj (by simpa using hne)
      simp only [Bool.toNat_true, pow_one] at hq
      have h2 := hψ (gen (some (i, j, true)))
      simp only [hgen] at h2
      exact hq (by rw [h2, map_pow])
    rw [← hjφ]
    exact hψ γ
  · intro i k hi hk hik
    refine ⟨gen (some (i, k, false)), ?_⟩
    rw [hgen]
    apply (FrobeniusGroupField.res_ne_zero hv _).1
    rw [map_sub, sub_ne_zero]
    exact (hsep' i k hi hk hik).symm
  · intro i hi
    exact ⟨gen none, by rw [hgen]; exact hQ none i hi⟩

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.IsHeightUnique
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

lemma lhom_ext {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)

lemma isHeight_map (hB1 : PairingPropertiesStatement B) {R S : LAlg R₀} (Dp : DualPair R) (Dq : DualPair S)
    (g : LHom R S) (f : LHom Dp.D Dq.D) (hfπ : ∀ x, Dq.π.1 (f.1 x) = g.1 (Dp.π.1 x))
    (hfσ : ∀ x, f.1 (Dp.σ.1 x) = Dq.σ.1 (g.1 x)) (hfη : f.1 Dp.η = Dq.η) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (H : B.IsHeight Dp N y h) :
    B.IsHeight Dq N (B.map g y) (g.1.toLinearMap ∘ₗ h) := by
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨Units.map (f.1 : (Dp.D : Type u) →* Dq.D) z, ?_, ?_⟩
  · have h1 := hnat _ _ f N _ _ z hz
    have hf : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dq.π.ker := by
      intro a ha
      rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
      change Dq.π.1 (f.1 a) = 0
      rw [hfπ, ha, map_zero]
    have e1 : B.map f (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = B.tg Dq.π Dq.sqZero (v ⊗ₜ Dq.ηk) := by
      rw [← B.tg_nat Dp.π Dq.π Dp.sqZero Dq.sqZero f hf, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext hfη
    have e2 : B.map f (B.map Dp.σ y) = B.map Dq.σ (B.map g y) := by
      have hc : f.comp Dp.σ = Dq.σ.comp g := lhom_ext fun x => hfσ x
      rw [← B.map_comp, ← B.map_comp, hc]
    rw [e1, e2] at h1
    exact h1
  · simp only [Units.coe_map, MonoidHom.coe_coe, hze, map_add (f := _), map_one, map_mul, hfσ, hfη]
    rfl

lemma nsmul_tg_eta {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0) (v : B.gg) :
    N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by
  rw [← map_nsmul, ← tmul_smul]
  have : N • Dp.ηk = 0 := by
    apply Subtype.ext
    change N • Dp.η = 0
    rw [nsmul_eq_mul, ← map_natCast Dp.σ.1, hN, map_zero, zero_mul]
  rw [this, tmul_zero, map_zero]

lemma isHeight_mul_p (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N p : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : (N * p) • y = 0) (h : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp (N * p) y h) : B.IsHeight Dp N (p • y) h := by
  obtain ⟨-, -, -, -, -, -, -, hNp⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨z, ?_, hze⟩
  have h1 := hNp _ N p _ _ z (B.nsmul_tg_eta Dp N hN v) (by rw [← map_nsmul, hy, map_zero]) hz
  rwa [← map_nsmul] at h1

lemma isHeight_unique (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (h h' : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y h') : h = h' :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).unique H H'

lemma isHeight_exists (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) :
    ∃ h, B.IsHeight Dp N y h :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).exists

lemma isHeight_add (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y y' : B.G R} {h h' : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') :=
  (heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.2 y y' h h' H H'

lemma isHeight_zero (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) : B.IsHeight Dp N 0 0 := by
  obtain ⟨h, hh⟩ := B.isHeight_exists hB1 Dp N hN 0 (smul_zero N)
  have h2 := B.isHeight_add hB1 Dp N hN hh hh
  rw [add_zero] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ hh h2
  have h4 : h = 0 := by
    have := congrArg (fun k => k - h) h3
    simpa using this.symm
  rwa [h4] at hh

lemma isHeight_neg (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) : B.IsHeight Dp N (-y) (-h) := by
  obtain ⟨h', hh'⟩ := B.isHeight_exists hB1 Dp N hN (-y) (by rw [smul_neg, hy, neg_zero])
  have h2 := B.isHeight_add hB1 Dp N hN H hh'
  rw [add_neg_cancel] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ h2 (B.isHeight_zero hB1 Dp N hN)
  have h4 : h' = -h := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
  rwa [h4] at hh'

lemma isHeight_zsmul (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (k : ℤ) : B.IsHeight Dp N (k • y) (k • h) := by
  have hnat : ∀ m : ℕ, B.IsHeight Dp N (m • y) (m • h) := by
    intro m
    induction m with
    | zero => simpa using B.isHeight_zero hB1 Dp N hN
    | succ m ih => rw [succ_nsmul, succ_nsmul]; exact B.isHeight_add hB1 Dp N hN ih H
  rcases k with m | m
  · simpa using hnat m
  · have hm : N • ((m + 1) • y) = 0 := by rw [smul_comm, hy, smul_zero]
    have := B.isHeight_neg hB1 Dp N hN hm (hnat (m + 1))
    simpa [negSucc_zsmul] using this

lemma isHeight_sum (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {ι : Type} (s : Finset ι) (y : ι → B.G R) (hy : ∀ i, N • y i = 0)
    (h : ι → B.gg →ₗ[R₀] (R : Type u)) (H : ∀ i, B.IsHeight Dp N (y i) (h i)) :
    B.IsHeight Dp N (∑ i ∈ s, y i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using B.isHeight_zero hB1 Dp N hN
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact B.isHeight_add hB1 Dp N hN (H a) ih

end BX

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatementHolds
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def uR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R :=
  (hv.exists_of_le_one (D.u_int j y)).choose

theorem uR_spec (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    algebraMap R C (uR hv D j y) = D.u j y :=
  (hv.exists_of_le_one (D.u_int j y)).choose_spec

def MuR (hv : v.Integers R) (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) R :=
  Matrix.of fun y α => ∏ j, uR hv D j y ^ (α j).val

theorem det_map' {S : Type} [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (M.map f).det = f M.det := by
  exact (f.map_det M).symm

theorem mem_max_of_lt (hv : v.Integers R) [IsLocalRing R] {x : R} (hx : v (algebraMap R C x) < 1) :
    x ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  rw [hv.isUnit_iff_valuation_eq_one.mp hu] at hx
  exact lt_irrefl _ hx

theorem residue_p (hv : v.Integers R) [IsLocalRing R] (hp1 : v (algebraMap R C (p : R)) < 1) :
    ((p : ℕ) : IsLocalRing.ResidueField R) = 0 := by
  rw [← map_natCast (IsLocalRing.residue R) p, IsLocalRing.residue_eq_zero_iff]
  exact mem_max_of_lt hv hp1

theorem residue_uR (hv : v.Integers R) [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    IsLocalRing.residue R (uR hv D j y) = lam (D.Λ.map (IsLocalRing.residue R)) j y := by
  have h := D.u_cong j y
  rw [← uR_spec hv D j y, ← map_sub] at h
  have hm := mem_max_of_lt hv h
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
  rw [hm, lam]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_natCast, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xc, ZMod.castHom_apply, ZMod.natCast_val]

theorem isUnit_det_MuR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1)
    (D : Lifts H U X) : IsUnit (MuR hv D).det := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hlt : ∀ x : R, x ∈ nonunits R → v (algebraMap R C x) < 1 := fun x hx =>
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_iff_valuation_eq_one.mpr h)
  letI : IsLocalRing R := IsLocalRing.of_nonunits_add fun a b ha hb hu => by
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hu
    have h2 : v (algebraMap R C (a + b)) < 1 := by
      rw [map_add (f := _)]; exact v.map_add_lt (hlt a ha) (hlt b hb)
    rw [h1] at h2
    exact lt_irrefl _ h2
  haveI : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (residue_p hv hp1)
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hM : (IsLocalRing.residue R).mapMatrix (MuR hv D) =
      Matrix.of fun (x α : Nb p g) => monF (p := p) (D.Λ.map (IsLocalRing.residue R)) α x := by
    ext y α
    simp [MuR, monF, residue_uR hv D]
  rw [hM]
  refine det_monF_ne_zero _ ?_
  rw [det_map']
  exact D.Λ_det.map _

theorem valM_eq (hv : v.Integers R) (D : Lifts H U X) :
    valM D = (MuR hv D).map (algebraMap R C) *
      Matrix.diagonal fun α : Nb p g => algebraMap R C (∏ j, D.ε j ^ (α j).val) := by
  ext y α
  simp only [valM, monX, xL, MuR, Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply,
    map_prod, map_pow, uR_spec, mul_pow, Finset.prod_mul_distrib]
  ring

theorem det_valM_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X) :
    (valM D).det ≠ 0 := by
  rw [valM_eq hv D, Matrix.det_mul, det_map', Matrix.det_diagonal]
  refine mul_ne_zero ((isUnit_det_MuR hv hp1 D).map (algebraMap R C)).ne_zero ?_
  refine Finset.prod_ne_zero_iff.mpr fun α _ => ?_
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [map_pow]
  exact pow_ne_zero _ ((map_ne_zero_iff _ hv.hom_inj).mpr (D.ε_ne j))

end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

namespace ReciprocityTheory.PGsh.Up

theorem liftMonomialDeterminantStatement_holds : LiftMonomialDeterminantStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X D
  exact FrobeniusValuationMatrix.det_valM_ne hS.integers hS.p_lt D

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ThmAFull
section
noncomputable section

open TensorProduct Matrix

namespace ReciprocityTheory.PGsh

variable {R₀ : Type} [CommRing R₀]

private lemma ev_expand (B : BX R₀) {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (h : B.gg →ₗ[R₀] (O : Type)) (b : B.gg ⊗[R₀] (O : Type)) :
    B.ev h b = ∑ a, h (gb a) * B.ev (Algebra.linearMap R₀ (O : Type) ∘ₗ gb.coord a) b := by
  induction b using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul x r =>
    simp only [BX.ev, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Algebra.linearMap_apply, Module.Basis.coord_apply]
    conv_lhs => rw [← gb.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Algebra.smul_def]
    ring
  | add a b ha hb =>
    simp only [BX.ev, map_add (f := _)] at *
    rw [ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

end ReciprocityTheory.PGsh
end
end

