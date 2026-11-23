module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.SelfDualLatticesOneOrbit
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymVarInlFst
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MemIntPolOfCoeff
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyMinorDvd
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem key_pow_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u v : Fin (k + 1) → A) (M N' N : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hv0 : w ∣ v 0) :
    w ∣ ∑ a, (∑ b, u b * M b a) ^ (p ^ e) * (∑ b', v b' * N a b') := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hu0 : ∀ b, b ≠ 0 → φ (u b) = 0 := fun b hb => (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hu b hb)
  have hv0' : φ (v 0) = 0 := (Ideal.Quotient.eq_zero_iff_dvd w _).mpr hv0
  have hrow : ∀ a, φ (∑ b, u b * M b a) = φ (u 0) * φ (M 0 a) := by
    intro a
    have hz : ∀ i : Fin k, φ (u i.succ) = 0 := fun i => hu0 _ (Fin.succ_ne_zero _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add (f := _), map_mul, hp0, zero_mul, add_zero]
  have hδ : ∀ b', ∑ a, φ (N' 0 a) * φ (N a b') = if (0 : Fin (k + 1)) = b' then 1 else 0 := by
    intro b'
    have h := congrArg φ (hinv 0 b')
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp_rw [map_mul] at h
    rw [h]
    split_ifs <;> simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_mul, map_pow, hrow, mul_pow, hpow, map_sum, map_mul]
  have e : ∑ a, φ (u 0) ^ (p ^ e) * φ (N' 0 a) * ∑ b', φ (v b') * φ (N a b') =
      φ (u 0) ^ (p ^ e) * ∑ b', φ (v b') * ∑ a, φ (N' 0 a) * φ (N a b') := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  simp_rw [hδ]
  simp [hv0']

theorem sigPow_mod' (p f : ℕ) [Fact p.Prime] (s : ℤ) : sigPow p f s = sigPow p f (s % (f : ℤ)) := by
  unfold sigPow
  rw [Int.emod_emod]

theorem segPos_val (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    (((segPos X.TT j i).val : ℕ) : ℤ) = (((segStart X.TT j).val : ℤ) + ((segDists X.TT j).get i : ℤ)) % (X.n' : ℤ) := by
  simp only [segPos, posAdd]
  push_cast
  rfl

theorem kS_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let y : X.TT × Bool := (topOdd X j i, false)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let v : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 y b) * MvPolynomial.X (y, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  let N : Fin (X.m + 1) → Fin (X.m + 1) → A := fun a b => C (psiO X.p X.n' O s1 (g a b))

  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) =
      MvPolynomial.map (algebraMap O (KK O)) (∑ a, (∑ b, u b * M b a) ^ (X.p ^ d) * (∑ b', v b' * N a b')) := by
    unfold kSkey
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs a rfl,
      liftSubst_X_cov X.p X.n' O S.w (hhLetters X.TT) 1 g y a rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, v, M, N, map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl

  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this

  have hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0 := by
    intro b b'
    have h1 : ∑ a, N' b a * N a b' = C (psiO X.p X.n' O s1 ((g⁻¹ * g) b b')) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [N', N, ← map_mul, ← map_sum, Matrix.mul_apply]
    rw [h1, Matrix.nonsing_inv_mul g hg, Matrix.one_apply]
    split_ifs <;> simp
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hv0 : (C S.w : A) ∣ v 0 := by
    have : dW O S.w (hhLetters X.TT) 1 y (0 : Fin (X.m + 1)) = S.w := by simp [dW, hhLetters, y]
    exact ⟨MvPolynomial.X (y, 0), by simp only [v, this]⟩
  obtain ⟨Q, hQ⟩ := key_pow_dvd X.p hp (C S.w : A) hw X.m d u v M N' N hMN hinv hu hv0
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

theorem key_minor_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u u' : Fin (k + 1) → A) (M N' : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hu' : ∀ b, b ≠ 0 → w ∣ u' b) (c : Fin (k + 1)) :
    w ∣ (∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (p ^ e) - (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (p ^ e) := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hrow : ∀ (x : Fin (k + 1) → A) (Q : Fin (k + 1) → Fin (k + 1) → A), (∀ b, b ≠ 0 → w ∣ x b) →
      ∀ a, φ (∑ b, x b * Q b a) = φ (x 0) * φ (Q 0 a) := by
    intro x Q hx a
    have hz : ∀ i : Fin k, φ (x i.succ) = 0 := fun i =>
      (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hx _ (Fin.succ_ne_zero _))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add (f := _), map_mul, hp0, zero_mul, add_zero]
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, hrow u' N' hu' c, hrow u M hu 0, hrow u' N' hu' 0,
    hrow u M hu c, mul_pow, mul_pow, hpow 0, hpow c]
  ring

theorem kW_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (c : Fin (X.m + 1)) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let z : X.TT × Bool := (topOdd X j i, true)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let u' : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 z b) * MvPolynomial.X (z, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) =
      MvPolynomial.map (algebraMap O (KK O)) ((∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (X.p ^ d) -
        (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (X.p ^ d)) := by
    unfold kWkey
    simp only [map_sub, map_mul, map_pow]
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z c rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs c rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, u', M, N', map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl
  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hu' : ∀ b, b ≠ 0 → (C S.w : A) ∣ u' b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 z b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, z, this]
    exact ⟨MvPolynomial.X (z, b), by simp only [u', this]⟩
  obtain ⟨Q, hQ⟩ := key_minor_dvd X.p hp (C S.w : A) hw X.m d u u' M N' hMN hu hu' c
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

theorem key3Ord : CoarseMultiplicityOrderBound := by
  intro X _ O _ _ _ _ S hsq hD j i g hg
  exact ⟨kS_ord X O S hsq hD j i g hg, fun c => kW_ord X O S hsq hD j i g hg c.succ⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LeadingExponentHomogeneous
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem nat_split {O : Type} [CommRing O] [IsLocalRing O] {p : ℕ} (hp : p.Prime) (hpO : ¬ IsUnit (p : O)) {n : ℕ}
    (hn : n ≠ 0) : ∃ u : Oˣ, (n : O) = (p : O) ^ (n.factorization p) * u := by
  have hcop : Nat.Coprime (ordCompl[p] n) p := (Nat.coprime_ordCompl hp hn).symm
  have hunit : IsUnit ((ordCompl[p] n : ℕ) : O) := by
    by_contra hu
    have h1 := Nat.gcd_eq_gcd_ab (ordCompl[p] n) p
    rw [hcop] at h1
    have h2 : (1 : O) = ((ordCompl[p] n : ℕ) : O) * ((Nat.gcdA (ordCompl[p] n) p : ℤ) : O) +
        (p : O) * ((Nat.gcdB (ordCompl[p] n) p : ℤ) : O) := by
      have := congrArg (Int.cast : ℤ → O) h1
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_one, Int.cast_one] at this
      exact this
    have hm1 : ((ordCompl[p] n : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := hu
    have hm2 : (p : O) ∈ IsLocalRing.maximalIdeal O := hpO
    have h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm1) (Ideal.mul_mem_right _ _ hm2)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, ← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]

theorem kap_transport {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} (hp : p.Prime) {w : O}
    (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (E D : ℕ)
    (hlo : B.factorization p ≤ E + A.factorization p) (hhi : E + A.factorization p ≤ D + B.factorization p) :
    ∃ κ : O, κ ≠ 0 ∧ vLEO p κ (D : ℝ) ∧ (p : O) ^ E * (A : O) = κ * (B : O) := by
  have hpO := p_not_unit hw h2
  obtain ⟨uA, huA⟩ := nat_split hp hpO hA
  obtain ⟨uB, huB⟩ := nat_split hp hpO hB
  have hp0 : (p : O) ≠ 0 := by rw [← h2]; exact pow_ne_zero _ hw.ne_zero
  set n := E + A.factorization p - B.factorization p with hn
  have h1 : (p : O) ^ n ≠ 0 := pow_ne_zero _ hp0
  have hκ : (p : O) ^ n * uA * ((uB⁻¹ : Oˣ) : O) ≠ 0 := mul_ne_zero (mul_ne_zero h1 uA.ne_zero) (Units.ne_zero _)
  refine ⟨(p : O) ^ n * uA * ((uB⁻¹ : Oˣ) : O), hκ, ?_, ?_⟩
  · rw [vLEO_iff hw h2 hκ, dvr_order_mul (mul_ne_zero h1 uA.ne_zero) (Units.ne_zero _), dvr_order_mul h1 uA.ne_zero,
      dvr_order_pow hp0, dvr_order_unit_eq_zero uA.isUnit, dvr_order_unit_eq_zero (Units.isUnit _)]
    have hv : dvrOrderNat (p : O) = 2 := by rw [← h2, dvr_order_pow hw.ne_zero, nv_irr hw]
    rw [hv]
    have : (n : ℝ) ≤ D := by exact_mod_cast (by omega : n ≤ D)
    push_cast
    linarith
  · rw [huA, huB]
    have hu : ((uB⁻¹ : Oˣ) : O) * uB = 1 := by simp
    have hpw : (p : O) ^ E * (p : O) ^ A.factorization p = (p : O) ^ n * (p : O) ^ B.factorization p := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    linear_combination (uA : O) * hpw - ((p : O) ^ n * (p : O) ^ B.factorization p * uA) * hu

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def lvW (ℓ : ℕ) : BV C0 CE1 CE2 X j → ℕ := fun v => if symLev X.p C0 CE1 CE2 X j v = ℓ then 1 else 0

def lvL (ℓ : ℕ) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if symLev X.p C0 CE1 CE2 X j (Sum.inl (a, 0)) = ℓ then 1 else 0

theorem lev_balanced (ℓ : ℕ) : Balanced X.m (X.seg C0 CE1 CE2 j) (lvW C0 CE1 CE2 X j ℓ) (lvL C0 CE1 CE2 X j ℓ) := by
  refine ⟨fun a c => rfl, ?_, ?_⟩
  · intro l
    have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have e0 : finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) =
        Fin.castSucc (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l).val, by omega⟩ : Fin (2 * segS X.TT j + 1)) :=
      Fin.ext (Nat.min_eq_left (by omega))
    have e1 : finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) =
        Fin.castSucc (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l).val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) :=
      Fin.ext (Nat.min_eq_left (by omega))
    unfold lvW lvL
    rw [sl_Z, sl_Z, e0, e1, symbol_level_lower_letter, sl_E]
  · unfold lvW lvL
    rw [symbol_level_last, symbol_level_last, sl_U, sl_xi]

theorem lev_const (b : SegBlock (segS X.TT j) X.m) (μ μ' : BV C0 CE1 CE2 X j →₀ ℕ) (hμ : HomExp C0 CE1 CE2 X j b μ)
    (hμ' : HomExp C0 CE1 CE2 X j b μ') (f : ℕ → ℕ) :
    ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ μ v = ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ μ' v := by
  classical
  have key : ∀ ν : BV C0 CE1 CE2 X j →₀ ℕ, HomExp C0 CE1 CE2 X j b ν →
      ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ ν v =
        ∏ ℓ ∈ Finset.univ.image (symLev X.p C0 CE1 CE2 X j), f ℓ ^ (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j)
          (segAPlus X.TT X.aT j) b (lvW C0 CE1 CE2 X j ℓ) (lvL C0 CE1 CE2 X j ℓ)) := by
    intro ν hν
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (symLev X.p C0 CE1 CE2 X j))
      (g := symLev X.p C0 CE1 CE2 X j) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v))]
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [← hν _ _ (lev_balanced C0 CE1 CE2 X j ℓ), ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold lvW
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero, pow_zero]
  rw [key μ hμ, key μ' hμ']

def mu0F (b : SegBlock (segS X.TT j) X.m) : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, c) => if c = 0 then Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
      (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a else 0
  | Sum.inr (l, false) => Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
      (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
        b.o (uTop (X.seg C0 CE1 CE2 j) l')) l
  | Sum.inr (_, true) => 0

def mu0 (b : SegBlock (segS X.TT j) X.m) : BV C0 CE1 CE2 X j →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (mu0F C0 CE1 CE2 X j b)

theorem leading_exponent_homogeneous (b : SegBlock (segS X.TT j) X.m) : HomExp C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b) := by
  classical
  intro ω ωL hB
  obtain ⟨h1, -, -⟩ := hB
  show ∑ v, mu0F C0 CE1 CE2 X j b v * ω v = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have a1 : ∀ a : Fin (2 * segS X.TT j + 1 + 1), ∑ c : Fin X.m, mu0F C0 CE1 CE2 X j b (Sum.inl (a, c)) * ω (Sum.inl (a, c)) =
      Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
        (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a * ωL a := by
    intro a
    rw [Finset.sum_eq_single (0 : Fin X.m)]
    · simp only [mu0F, if_true, h1]
    · intro c _ hc
      simp only [mu0F, if_neg hc, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have a2 : ∀ l : Fin ((X.seg C0 CE1 CE2 j).t + 1), ∑ β : Bool, mu0F C0 CE1 CE2 X j b (Sum.inr (l, β)) * ω (Sum.inr (l, β)) =
      Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
        (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) l * ω (Sum.inr (l, false)) := by
    intro l
    rw [Fintype.sum_bool]
    simp only [mu0F, zero_mul, zero_add]
  rw [Finset.sum_congr rfl fun a _ => a1 a, Finset.sum_congr rfl fun l _ => a2 l]
  have s1 : ∑ a : Fin (2 * segS X.TT j + 1 + 1), Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
        (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a * ωL a =
      ∑ a' : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a' *
        ωL (Fin.castSucc a') + (X.seg C0 CE1 CE2 j).bPlus * ωL (Fin.last _) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have s2 : ∑ l : Fin ((X.seg C0 CE1 CE2 j).t + 1), Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
        (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) l * ω (Sum.inr (l, false)) =
      ∑ l' : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) * ω (Sum.inr (Fin.castSucc l', false)) +
        (segAPlus X.TT X.aT j - b.oPlus) * ω (Sum.inr (Fin.last _, false)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [s1, s2]
  unfold OmB
  ring

def PhiB (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  Rblk C0 CE1 CE2 X j b * ∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
    (symLev X.p C0 CE1 CE2 X j v).factorial ^ (mu0 C0 CE1 CE2 X j b v)

end

def KapNumAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      (facSeg X j).factorization X.p ≤ (X.m + 1) * lgSeg X j +
          (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p +
          (PhiB C0 CE1 CE2 X j b).factorization X.p ∧
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p +
          (PhiB C0 CE1 CE2 X j b).factorization X.p ≤ lgSeg X j + (facSeg X j).factorization X.p

theorem facSeg_ne (X : Loc) (j : Fin (numSeg X.TT)) : facSeg X j ≠ 0 := by
  have : 0 < facSeg X j := by
    unfold facSeg
    positivity
  omega

theorem PhiB_ne (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    PhiB C0 CE1 CE2 X j b ≠ 0 := by
  have : 0 < PhiB C0 CE1 CE2 X j b := by
    unfold PhiB Rblk
    positivity
  omega

theorem kapAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hN : KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    KapAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ _ w hw h2 hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  have hO : CharZero O := charZero_of_w hp hw h2
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨n1, n2⟩ := hN X hD1 hH hc j b hb
  set sp := specConst X.p (X.seg C0 CE1 CE2 j) b with hsp
  have hsp0 : sp ≠ 0 := specConst_ne _ _ _
  have hc0 : (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
  have hvN : padicValNat X.p (Nblk C0 CE1 CE2 X j b) =
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p + sp.factorization X.p := by
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ hp]
    unfold Nblk
    rw [Nat.factorization_mul hc0 hsp0]
    rfl
  have hBf : (facSeg X j * sp).factorization X.p = (facSeg X j).factorization X.p + sp.factorization X.p := by
    rw [Nat.factorization_mul (facSeg_ne X j) hsp0]
    rfl
  obtain ⟨κ, hκ0, hκv, hκ⟩ := kap_transport hp hw h2 (PhiB_ne C0 CE1 CE2 X j b) (mul_ne_zero (facSeg_ne X j) hsp0)
    ((X.m + 1) * lgSeg X j + padicValNat X.p (Nblk C0 CE1 CE2 X j b)) ((X.m + 2) * lgSeg X j)
    (by rw [hBf, hvN]; omega) (by
      rw [hBf, hvN]
      have : (X.m + 2) * lgSeg X j = (X.m + 1) * lgSeg X j + lgSeg X j := by ring
      omega)
  refine ⟨κ, hκ0, hκv, ?_⟩
  intro μ hμ
  have hΦ : Rblk C0 CE1 CE2 X j b * ∏ v : BV C0 CE1 CE2 X j,
      (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial * (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ v) =
      PhiB C0 CE1 CE2 X j b := by
    unfold PhiB
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      lev_const C0 CE1 CE2 X j b μ _ hμ (leading_exponent_homogeneous C0 CE1 CE2 X j b) Nat.factorial]
  have hΦK := congrArg (fun n : ℕ => (n : KK O)) hΦ
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow] at hΦK
  have hκK := congrArg (algebraMap O (KK O)) hκ
  simp only [map_mul, map_pow, map_natCast, Nat.cast_mul] at hκK
  have hf0 : (facSeg X j : KK O) ≠ 0 := Nat.cast_ne_zero.2 (facSeg_ne X j)
  unfold zSeg
  rw [mul_assoc (_ * _) _ _, hΦK, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hf0, ← pow_add, hκK]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

