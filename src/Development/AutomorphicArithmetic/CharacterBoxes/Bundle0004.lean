module

public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0003
public import Development.AutomorphicArithmetic.MeanSquareBounds.realDecomp
public import Development.AutomorphicArithmetic.MeanSquareBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.BoundedTw
section
open Formalism.HC UpperTheory.Top

private theorem UpperTheory.Top.boundedTw_key (ψ : PChar) (φ : Frame) (H : HostRaw φ) (htw : TwistForm ψ H) (hdiv : ψ.N ∣ H.QS)
    (hpr : ∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * ψ.N) (θ : φ.Char) (hθ : θ ∈ H.Bounded (Level.cyc ψ).KEPT)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (hχ : H.IsPrimOf θ χ) :
    ∃ (ξ : DirichletCharacter ℂ ψ.N) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) ∧
      An.Induces χ (tw (fun a => ξ (a : ZMod ψ.N)) H.q H.d i j) (2 * ψ.N * H.q * H.d) := by
  have hθ' : θ ∈ φ.Xp ∧ ¬H.Kept (Level.cyc ψ).KEPT θ ∨ θ ∈ φ.Xm := hθ
  have hχ' : An.Induces χ (H.dirAt θ) H.condN := hχ
  have htriv : Frame.TrivialOnFirstFactor θ := by
    rcases hθ' with ⟨h, -⟩ | h
    · exact h.1
    · exact h.1
  obtain ⟨ξ, hξ, i, j, hiod, heq⟩ := htw θ htriv
  have hNc : ψ.N ∣ H.condN := Dvd.dvd.mul_right (Dvd.dvd.mul_right hdiv _) _
  refine ⟨ξ, i, j, ?_, hχ'.1, ?_⟩
  · by_contra hij
    push_neg at hij
    obtain ⟨rfl, rfl⟩ := hij
    rcases hθ' with ⟨-, hnk⟩ | hm
    · apply hnk
      refine ⟨PChar.of ξ, (Level.mem_ofSub _ _).2 ⟨ξ, hξ, rfl⟩, (PChar.of ξ).prim, fun a ha => ?_⟩
      have ha' : a.Coprime ψ.N := Nat.Coprime.coprime_dvd_right hNc ha
      rw [(An.induces_of ξ).2 a ha', heq a ha]
      simp [tw]
    · have h1 := hm.2
      rw [h1] at hiod
      have h2 := congrArg Units.val hiod
      norm_num at h2
  · intro a ha
    have hq : a.Coprime H.q :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) ha
    have hd : a.Coprime H.d := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) ha
    have hQ : a.Coprime H.QS := by
      apply Nat.coprime_of_dvd
      intro l hl hla hlQ
      have hl2 : l ∣ 2 * ψ.N * H.q * H.d :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hpr l hl hlQ) _) _
      exact hl.not_dvd_one (ha.gcd_eq_one ▸ Nat.dvd_gcd hla hl2)
    have hc : a.Coprime H.condN := Nat.Coprime.mul_right (Nat.Coprime.mul_right hQ hq) hd
    rw [hχ'.2 a hc, heq a hc]

theorem UpperTheory.Top.boundedTw :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ) (eps Y x : ℝ), 0 < eps → 1 ≤ x → Y ≤ x → TwistForm ψ H → ψ.N ∣ H.QS →
      (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * ψ.N) → PairGood ψ.N eps Y x H.q H.d →
      H.BoundedCharsPointwise (Level.cyc ψ).KEPT x eps ∧
        ∀ θ ∈ H.Bounded (Level.cyc ψ).KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ → ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log x := by
  intro ψ φ H eps Y x he hx hY htw hdiv hpr hg
  refine ⟨fun θ hθ N _ χ hχ => ?_, fun θ hθ N _ χ hχ => ?_⟩
  · obtain ⟨ξ, i, j, hij, hI⟩ := UpperTheory.Top.boundedTw_key ψ φ H htw hdiv hpr θ hθ N χ hχ
    exact (hg.bounds ξ i j hij N χ hI x hY le_rfl).1.trans
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  · obtain ⟨ξ, i, j, hij, hI⟩ := UpperTheory.Top.boundedTw_key ψ φ H htw hdiv hpr θ hθ N χ hχ
    exact (hg.bounds ξ i j hij N χ hI x hY le_rfl).2
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.IsChiField
section
open Formalism.HC UpperTheory.Top

theorem UpperTheory.Top.isChiField :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ), KerChi ψ H → IsChiField ψ φ.e H.q H.d H.E := by
  intro ψ φ H h
  obtain ⟨hψ, hart⟩ := h
  have hyp := H.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hyp
  have hq := hyp.1.pos
  have hd := hyp.2.1.pos
  have hQS := H.QS_pos
  have hNpos : 0 < H.QS * H.q * H.d := Nat.mul_pos (Nat.mul_pos hQS hq) hd
  haveI : NeZero (H.QS * H.q * H.d) := ⟨hNpos.ne'⟩
  have hζ := H.cycZeta_prim
  refine ⟨H.QS * H.q * H.d, inferInstance, H.cycEmb, H.cycZeta, ?_, ?_, ?_, ?_, hζ, ?_⟩
  · exact dvd_trans H.tower_dvd (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans hψ (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _))
  · exact dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)
  · exact dvd_mul_left _ _
  · intro τ a hτ
    have hprim : IsPrimitiveRoot (H.cycZeta ^ a) (H.QS * H.q * H.d) := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime (H.QS * H.q * H.d) := (hζ.pow_iff_coprime hNpos a).mp hprim
    have hcop' : a.Coprime H.condN := hcop
    rw [← hart a hcop']
    set u := ZMod.unitOfCoprime a hcop' with hu
    have hτu : τ H.cycZeta = H.cycZeta ^ (u : ZMod (H.QS * H.q * H.d)).val := by
      rw [hτ]
      have hv : (u : ZMod (H.QS * H.q * H.d)).val = a % (H.QS * H.q * H.d) := by
        rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      rw [hv]
      conv_lhs => rw [← Nat.mod_add_div a (H.QS * H.q * H.d)]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hspec := H.art_spec u τ hτu
    constructor
    · intro hfix
      have hg : H.gal.symm (H.art u) = 1 := by
        ext x
        apply H.cycEmb.injective
        exact (hspec x).trans (hfix x)
      have h1 := congrArg H.gal hg
      rw [MulEquiv.apply_symm_apply, map_one] at h1
      exact h1
    · intro h1 x
      have h2 := hspec x
      rw [h1, map_one] at h2
      rw [← h2]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.PairHyp
section
open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top

private theorem jac_neg_of_dvd {p d : ℕ} (h : p ∣ d + 1) : jacobiSym (-(d : ℤ)) p = 1 := by
  have h1 : (-(d : ℤ)) ≡ 1 [ZMOD (p : ℤ)] := by
    apply Int.modEq_iff_dvd.2
    have h2 := Int.natCast_dvd_natCast.2 h
    push_cast at h2
    have h3 : (1 : ℤ) - -(d : ℤ) = (d : ℤ) + 1 := by ring
    rw [h3]
    exact h2
  rw [jacobiSym.mod_left' h1, jacobiSym.one_left]

private theorem jac_neg_recip {n a : ℕ} (hn : n % 4 = 3) (ha : Odd a) :
    jacobiSym (-(n : ℤ)) a = jacobiSym (a : ℤ) n := by
  have hno : Odd n := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ ha]
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 ha) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hno]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four h hn]
    ring

theorem UpperTheory.Top.pairHyp :
    ∀ (eps Y : ℝ) (q d : ℕ), WinPair eps Y q d → HostHyp q d ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1) ∧
      (∀ a : ℕ, Odd a → jacobiSym (-(q : ℤ)) a = jacobiSym (a : ℤ) q ∧ jacobiSym (-(d : ℤ)) a = jacobiSym (a : ℤ) d) := by
  intro eps Y q d hw
  have hq4 : q % 4 = 3 := by have := hw.q_mod; omega
  have hd4 : d % 4 = 3 := by have := hw.d_mod; omega
  refine ⟨⟨hw.q_prime, hw.d_prime, hw.q_mod, hw.d_mod, jac_neg_of_dvd hw.d_q⟩, ?_, ?_⟩
  · intro p hp hp2 hpY
    exact jac_neg_of_dvd (hw.d_small p hp hp2 hpY)
  · intro a ha
    exact ⟨jac_neg_recip hq4 ha, jac_neg_recip hd4 ha⟩
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.RealSplit
section
open Formalism.HC UpperTheory.Top

private theorem UpperTheory.Top.realSplit_step (f q i : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f) (hξ : ξ.IsPrimitive)
    (hq : q.Prime) (h2 : q ≠ 2) (hf : ¬ q ∣ f) (hi : i ≤ 1) :
    ∃ (M : ℕ) (ψ : DirichletCharacter ℂ M), M = f * q ^ i ∧ ψ.IsPrimitive ∧
      ∀ n : ℕ, ψ (n : ZMod M) = ξ (n : ZMod f) * QH.J q n ^ i := by
  interval_cases i
  · exact ⟨f, ξ, by simp, hξ, fun n => by simp⟩
  · obtain ⟨ψ, h1, -, h3⟩ := QH.twist_prim f q ξ hξ hq h2 hf
    exact ⟨f * q, ψ, by simp, h1, fun n => by simpa using h3 n⟩

private theorem UpperTheory.Top.realSplit_J (q n i : ℕ) (h : n.Coprime q) : (QH.J q n ^ i) ^ 2 = 1 := by
  have h1 : jacobiSym (n : ℤ) q = 1 ∨ jacobiSym (n : ℤ) q = -1 :=
    jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact h)
  rw [← pow_mul, mul_comm, pow_mul]
  unfold QH.J
  rcases h1 with h1 | h1 <;> simp [h1]

private theorem im_dirichletCharacter_eq_zero_of_coprime (c N₀ : ℕ) [NeZero c] [NeZero N₀] (ρ : DirichletCharacter ℂ c)
    (hc : c ∣ N₀) (h : ∀ n : ℕ, n.Coprime N₀ → (ρ n).im = 0) : ∀ x : ZMod c, (ρ x).im = 0 := by
  intro x
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hc u
    have hn : (v : ZMod N₀).val.Coprime N₀ :=
      (ZMod.isUnit_iff_coprime _ _).1 (by rw [ZMod.natCast_zmod_val]; exact v.isUnit)
    have hux : (u : ZMod c) = ((v : ZMod N₀).val : ZMod c) := by
      rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val]
    rw [hux]
    exact h _ hn
  · rw [MulChar.map_nonunit _ hx]
    simp

private theorem im_mul_intCast_eq_zero_of_im_eq_zero (z : ℂ) (hz : z.im = 0) (A B : ℤ) : (z * (A : ℂ) * (B : ℂ)).im = 0 := by
  simp [Complex.mul_im, hz]

private theorem exists_real_pchar_twist_decomposition (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχp : χ.IsPrimitive) (S q d : ℕ) (hreal' : ∀ x : ZMod N, (χ x).im = 0) (hS : 0 < S)
    (hq : q.Prime) (hd : d.Prime) (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hcop : Nat.Coprime S (q * d)) (hdvd : N ∣ S * q * d) :
    ∃ (ρ : PChar) (i j : Fin 2), ρ.IsReal ∧ ρ.N ∣ 8 * ordCompl[2] S ∧
      N = ρ.N * q ^ (i : ℕ) * d ^ (j : ℕ) ∧ ∀ a : ℕ, χ a = tw ρ.val q d i j a := by
  have hN₀ : 0 < 8 * ordCompl[2] S := Nat.mul_pos (by norm_num) (Nat.ordCompl_pos 2 hS.ne')
  have hnd : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ S → ¬ r ∣ 8 * ordCompl[2] S := by
    intro r hr hr2 hrS h
    rcases (hr.dvd_mul).1 h with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
        (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 3 by norm_num; exact h)))
    · exact hrS (h.trans (Nat.ordCompl_dvd S 2))
  have hqS : ¬ q ∣ S := fun h => (Nat.Prime.coprime_iff_not_dvd hq).1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right q d) hcop).symm h
  have hdS : ¬ d ∣ S := fun h => (Nat.Prime.coprime_iff_not_dvd hd).1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_left d q) hcop).symm h
  have hq8 := hnd q hq hq2 hqS
  have hd8 := hnd d hd hd2 hdS
  have hsq : χ ^ 2 = 1 := MulChar.ext fun u => by
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have h1 := DirichletCharacter.unit_norm_eq_one χ u
    have h2 : (starRingEnd ℂ) (χ u) = χ u := Complex.conj_eq_iff_im.2 (hreal' u)
    calc χ u ^ 2 = χ u * (starRingEnd ℂ) (χ u) := by rw [h2, sq]
      _ = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; norm_num
  have hNdvd : N ∣ 8 * ordCompl[2] S * q * d := by
    refine QH.real_cond _ q d N χ hχp hsq (dvd_mul_right 8 _) hq hd fun p hp hpN => ?_
    have h := hpN.trans hdvd
    rcases (hp.dvd_mul).1 h with h | h
    · rcases (hp.dvd_mul).1 h with h | h
      · left
        by_cases hp2 : p = 2
        · subst hp2
          exact Dvd.dvd.mul_right (by norm_num) _
        · refine Dvd.dvd.mul_left ?_ 8
          have hc2 : p.Coprime (2 ^ S.factorization 2) :=
            ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right _
          refine Nat.Coprime.dvd_of_dvd_mul_left hc2 ?_
          rw [Nat.ordProj_mul_ordCompl_eq_self]
          exact h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hd).1 h))
  obtain ⟨ξ, a, b, ha, hb, hξ⟩ :=
    QH.real_decomp _ q d N χ hsq hN₀ hq hd hq2 hd2 hqd hq8 hd8 hNdvd
  haveI : NeZero (8 * ordCompl[2] S) := ⟨hN₀.ne'⟩
  haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  haveI : NeZero (8 * ordCompl[2] S * q * d) :=
    ⟨mul_ne_zero (mul_ne_zero hN₀.ne' hq.ne_zero) hd.ne_zero⟩
  have hprim : ∀ n : ℕ, n.Coprime (8 * ordCompl[2] S) → ξ n = ξ.primitiveCharacter n := by
    intro n hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter
      ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have hcN₀ : ξ.conductor ∣ 8 * ordCompl[2] S := ξ.conductor_dvd_level
  have hqc : ¬ q ∣ ξ.conductor := fun h => hq8 (h.trans hcN₀)
  obtain ⟨M1, ψ1, hM1, hψ1, hψ1eq⟩ := UpperTheory.Top.realSplit_step ξ.conductor q a
    ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqc ha
  subst hM1
  haveI : NeZero (ξ.conductor * q ^ a) := ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hq.ne_zero)⟩
  have hdc : ¬ d ∣ ξ.conductor * q ^ a := by
    intro h
    rcases (hd.dvd_mul).1 h with h | h
    · exact hd8 (h.trans hcN₀)
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).1 (hd.dvd_of_dvd_pow h)).symm
  obtain ⟨M2, ψ2, hM2, hψ2, hψ2eq⟩ :=
    UpperTheory.Top.realSplit_step (ξ.conductor * q ^ a) d b ψ1 hψ1 hd hd2 hdc hb
  subst hM2
  haveI : NeZero (ξ.conductor * q ^ a * d ^ b) :=
    ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hd.ne_zero)⟩
  have hbig : ξ.conductor ∣ 8 * ordCompl[2] S * q * d := hcN₀.trans (Dvd.intro (q * d) (by ring))
  have heq := QH.ind_unique N (ξ.conductor * q ^ a * d ^ b) (8 * ordCompl[2] S * q * d) χ ψ2
    (mul_ne_zero (mul_ne_zero hN₀.ne' hq.ne_zero) hd.ne_zero) hχp hψ2 (fun n hn => by
      rw [hξ n hn, hψ2eq, hψ1eq,
        hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (q * d) (by ring)) hn)])
  obtain ⟨hN, hχψ⟩ := Sigma.mk.inj_iff.1 heq
  subst hN
  have hc : χ = ψ2 := eq_of_heq hχψ
  subst hc
  have hρreal := im_dirichletCharacter_eq_zero_of_coprime ξ.conductor (8 * ordCompl[2] S * q * d) ξ.primitiveCharacter hbig
    (fun n hn => by
      rw [← hprim _ (Nat.Coprime.coprime_dvd_right (Dvd.intro (q * d) (by ring)) hn)]
      have hJq := UpperTheory.Top.realSplit_J q n a
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) (Nat.Coprime.coprime_dvd_right
          (Dvd.intro d rfl) hn))
      have hJd := UpperTheory.Top.realSplit_J d n b
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hn)
      have hξn : ξ n = χ n * QH.J q n ^ a * QH.J d n ^ b := by
        rw [hξ n hn]
        linear_combination (-(ξ n) * (QH.J d n ^ b) ^ 2) * hJq + (-(ξ n)) * hJd
      have e1 : QH.J q n ^ a = ((jacobiSym n q ^ a : ℤ) : ℂ) := by
        unfold QH.J
        push_cast
        rfl
      have e2 : QH.J d n ^ b = ((jacobiSym n d ^ b : ℤ) : ℂ) := by
        unfold QH.J
        push_cast
        rfl
      rw [hξn, e1, e2]
      exact im_mul_intCast_eq_zero_of_im_eq_zero _ (hreal' n) _ _)
  refine ⟨⟨ξ.conductor, ξ.primitiveCharacter, ξ.primitiveCharacter_isPrimitive⟩, ⟨a, by omega⟩,
    ⟨b, by omega⟩, hρreal, hcN₀, rfl, fun n => ?_⟩
  simp only [PChar.val, tw]
  rw [hψ2eq, hψ1eq]
  rfl

theorem UpperTheory.Top.realSplit :
    ∀ (χ : PChar) (S q d : ℕ), χ.IsReal → 0 < S → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → Nat.Coprime S (q * d) → χ.N ∣ S * q * d →
      ∃ (ρ : PChar) (i j : Fin 2), ρ.IsReal ∧ ρ.N ∣ 8 * ordCompl[2] S ∧ χ.N = ρ.N * q ^ (i : ℕ) * d ^ (j : ℕ) ∧
        ∀ a : ℕ, a.Coprime χ.N → χ.val a = tw ρ.val q d i j a := by
  intro χ0
  cases χ0 with
  | mk N χ hχp =>
    intro S q d hreal hS hq hd hq2 hd2 hqd hcop hdvd
    obtain ⟨ρ, i, j, hρ, hρN, hN, hval⟩ :=
      exists_real_pchar_twist_decomposition N χ hχp S q d hreal hS hq hd hq2 hd2 hqd hcop hdvd
    exact ⟨ρ, i, j, hρ, hρN, hN, fun a _ => hval a⟩
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.WinPairs
section
open Formalism.HC UpperTheory.Top

theorem UpperTheory.Top.winPairs :
    ∀ (ψ : PChar) (eps c : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ c → VWinAt ψ 401 → PairEx →
      ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
        ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J c x Y q d e := by
  intro ψ eps c heps heps52 hc hV hP
  obtain ⟨e, he⟩ := exists_pageN eps heps
  obtain ⟨J, hJ, X0, hX0⟩ := hV eps heps heps52 e he
  have hN : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨Y1, hY1⟩ := hP ψ.N hN eps J heps heps52 hJ
  have ha : 0 < 2 + 8 * eps := by linarith
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨k, hk1, hka⟩ : ∃ k : ℝ, 1 ≤ k ∧ k ^ (2 + 8 * eps) = c := by
    refine ⟨c ^ (1 / (2 + 8 * eps)), Real.one_le_rpow hc (one_div_nonneg.2 ha.le), ?_⟩
    rw [one_div, Real.rpow_inv_rpow hc0 ha.ne']
  have hk0 : 0 ≤ k := by linarith
  refine ⟨J, hJ, fun y => ?_⟩
  have hJ0 : J ≠ 0 := ne_of_gt (by linarith)
  have hJi : 0 ≤ 1 / J := one_div_nonneg.2 (by linarith)
  obtain ⟨M, hM1, hMy, hMY1, hMk3, hMk400⟩ : ∃ M : ℝ, 1 ≤ M ∧ y ≤ M ∧ Y1 ≤ M ∧
      k ^ (3 : ℝ) ≤ M ∧ k ^ (400 : ℝ) ≤ M :=
    ⟨max 1 (max y (max Y1 (max (k ^ (3 : ℝ)) (k ^ (400 : ℝ))))), by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨X, hXX0, hXM⟩ : ∃ X : ℝ, X0 ≤ X ∧ M ^ J ≤ X := ⟨max X0 (M ^ J), le_max_left _ _, le_max_right _ _⟩
  have hM0 : 0 ≤ M := by linarith
  have hX1 : 1 ≤ X := (Real.one_le_rpow hM1 (by linarith)).trans hXM
  have hX0' : 0 ≤ X := by linarith
  have hY0M : M ≤ X ^ (1 / J) := by
    calc M = (M ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hM0 hJ0]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hXM hJi
  have hXJ : (X ^ (1 / J)) ^ J = X := by rw [one_div, Real.rpow_inv_rpow hX0' hJ0]
  obtain ⟨q, d, hpg⟩ := hY1 (X ^ (1 / J)) (hMY1.trans hY0M)
  obtain ⟨W, hW0, hW2, hWV⟩ := hX0 X hXX0 q d hpg.pair
  have hWM : M ≤ W := hY0M.trans hW0
  have hW1 : 1 ≤ W := hM1.trans hWM
  have hWnn : 0 ≤ W := by linarith
  have hk3 : k ^ (3 : ℝ) ≤ W := hMk3.trans hWM
  have hlem : (k * W) ^ ((3 : ℝ) / 2) ≤ W ^ (2 : ℝ) := by
    have h1 : (k * W) ^ ((3 : ℝ) / 2) = ((k * W) ^ (3 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (mul_nonneg hk0 hWnn)]
      norm_num
    have h2 : W ^ (2 : ℝ) = (W ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hWnn]
      norm_num
    rw [h1, h2]
    apply Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hk0 hWnn) _) _ (by norm_num)
    rw [Real.mul_rpow hk0 hWnn, show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith : 0 < W),
      Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hk3 (Real.rpow_nonneg hWnn _)
  refine ⟨k * W, hMy.trans (hWM.trans (le_mul_of_one_le_left hWnn hk1)), fun x hZx hxZ => ?_⟩
  have hkpos : 0 < k := by linarith
  have hxW2 : x ≤ W ^ (2 : ℝ) := hxZ.trans hlem
  have hxX : x ≤ X := hxW2.trans hW2
  have hx1 : W ≤ x := (le_mul_of_one_le_left hWnn hk1).trans hZx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨x', rfl⟩ : ∃ x', x = k * x' := ⟨x / k, by field_simp⟩
  have hWx' : W ≤ x' := le_of_mul_le_mul_left hZx hkpos
  have hx'0 : 0 ≤ x' := hWnn.trans hWx'
  have hx'1 : 1 ≤ x' := hW1.trans hWx'
  have hx'x : x' ≤ k * x' := le_mul_of_one_le_left hx'0 hk1
  have hpage : x' ^ (2 + 8 * eps) ≤ 2 ^ (e x') ∧ 2 ^ (e x') ≤ 2 * x' ^ (2 + 8 * eps) := he x' hx'1
  have hpow : (k * x') ^ (2 + 8 * eps) = c * x' ^ (2 + 8 * eps) := by rw [Real.mul_rpow hk0 hx'0, hka]
  refine ⟨X ^ (1 / J), q, d, e x', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.rpow_le_rpow hx0 hxX hJi
  · exact hW0.trans hx1
  · exact hpg.mono (by rw [hXJ]; exact hxX)
  · rw [hpow]
    exact mul_le_mul_of_nonneg_left hpage.1 hc0
  · rw [hpow]
    calc c * 2 ^ (e x') ≤ c * (2 * x' ^ (2 + 8 * eps)) := mul_le_mul_of_nonneg_left hpage.2 hc0
      _ = 2 * (c * x' ^ (2 + 8 * eps)) := by ring
  · intro E _ _ hE
    have hv := hWV x' hWx' (hx'x.trans hxW2) E hE
    refine hv.mono ?_ ?_
    · apply Nat.floor_mono
      rw [Real.mul_rpow hk0 hx'0, show (401 : ℝ) = 1 + 400 by norm_num, Real.rpow_add (by linarith : 0 < x'),
        Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (hMk400.trans (hWM.trans hWx')) (Real.rpow_nonneg hx'0 _)
    · exact Real.sqrt_le_sqrt (Real.exp_le_exp.2 (Real.rpow_le_rpow hx'0 hx'x heps.le))
end

