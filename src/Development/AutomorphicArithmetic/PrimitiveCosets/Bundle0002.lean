module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.TopsSum
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

open Classical in
private theorem tops_sum_coset {H : Type} [AddCommGroup H] [Fintype H] (A0 : AddSubgroup H) (θ : AddChar H ℂ)
    (h0 : ∀ s ∈ A0, θ s = 1) (t : H) :
    ∑ g : H, (if t - g ∈ A0 then θ g else 0) = (Nat.card A0 : ℂ) * θ t := by
  have step : ∀ g, (if t - g ∈ A0 then θ g else 0) = if t - g ∈ A0 then θ t else 0 := by
    intro g
    split_ifs with hg
    · have e : g = t + -(t - g) := by abel
      rw [e, AddChar.map_add_eq_mul, h0 _ (A0.neg_mem hg), mul_one]
    · rfl
  have eqv : A0 ≃ {g : H // t - g ∈ A0} :=
    { toFun := fun s => ⟨t - s, by simp⟩
      invFun := fun g => ⟨t - g, g.2⟩
      left_inv := fun s => by ext; simp
      right_inv := fun g => by ext; simp }
  have hc : (Finset.univ.filter fun g => t - g ∈ A0).card = Nat.card A0 := by
    rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl fun g _ => step g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc]

open Classical in
private theorem tops_sum_gen {H : Type} [AddCommGroup H] [Fintype H] (A0 : AddSubgroup H) (θ : AddChar H ℂ)
    (h0 : ∀ s ∈ A0, θ s = 1) (h1 : θ ≠ 0) (TT : Finset H) (o : ℕ) (ho : Fintype.card H = o * Nat.card A0)
    (b c η : ℝ)
    (hs : ∀ g : H, |((TT.filter fun t => t - g ∈ A0).card : ℝ) - (b + if g ∈ A0 then c else 0)| ≤ η) :
    ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ o * η := by
  have hiff : ∀ g : H, 0 - g ∈ A0 ↔ g ∈ A0 := fun g => by rw [zero_sub, neg_mem_iff]
  have hz := tops_sum_coset A0 θ h0 0
  simp only [hiff, AddChar.map_zero_eq_one, mul_one] at hz
  have hB : ∑ g, θ g = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr h1
  have hC : ∑ g, θ g * (if g ∈ A0 then (c : ℂ) else 0) = (Nat.card A0 : ℂ) * c := by
    rw [← hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> ring
  have hA : ∑ g, θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ) = (Nat.card A0 : ℂ) * ∑ t ∈ TT, θ t := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun t _ => (tops_sum_coset A0 θ h0 t).symm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  obtain ⟨e, he⟩ : ∃ e : H → ℝ, ∀ g, e g =
      ((TT.filter fun t => t - g ∈ A0).card : ℝ) - (b + if g ∈ A0 then c else 0) := ⟨_, fun _ => rfl⟩
  have key : (Nat.card A0 : ℂ) * ((∑ t ∈ TT, θ t) - c) = ∑ g, θ g * ((e g : ℝ) : ℂ) := by
    have hsplit : ∀ g, θ g * ((e g : ℝ) : ℂ) = θ g * ((TT.filter fun t => t - g ∈ A0).card : ℂ)
        - (b : ℂ) * θ g - θ g * (if g ∈ A0 then (c : ℂ) else 0) := by
      intro g
      rw [he g]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hA,
      ← Finset.mul_sum, hB, hC]
    ring
  have hnorm : ∀ g, ‖θ g‖ = 1 := by
    intro g
    have hp : θ g ^ Fintype.card H = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have hq : ‖θ g‖ ^ Fintype.card H = 1 := by rw [← norm_pow, hp, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).mp hq
  have hbound : ‖∑ g, θ g * ((e g : ℝ) : ℂ)‖ ≤ Fintype.card H * η := by
    calc ‖∑ g, θ g * ((e g : ℝ) : ℂ)‖ ≤ ∑ g, ‖θ g * ((e g : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _g : H, η := Finset.sum_le_sum fun g _ => by
          rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs, he g]
          exact hs g
      _ = Fintype.card H * η := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Nat.card A0 := by exact_mod_cast Nat.card_pos
  have h3 : (Nat.card A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖ ≤ (Nat.card A0 : ℝ) * (o * η) := by
    calc (Nat.card A0 : ℝ) * ‖(∑ t ∈ TT, θ t) - (c : ℂ)‖
        = ‖(Nat.card A0 : ℂ) * ((∑ t ∈ TT, θ t) - c)‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ g, θ g * ((e g : ℝ) : ℂ)‖ := by rw [key]
      _ ≤ Fintype.card H * η := hbound
      _ = (Nat.card A0 : ℝ) * (o * η) := by rw [ho]; push_cast; ring
  exact le_of_mul_le_mul_left h3 hn

theorem UpperTheory.Comparison₂.tops_sum :
    ∀ (φ : Frame) (TT : Finset φ.A) (δ : ℝ), φ.Shares TT δ → ∀ ψ ∈ PsiA φ.A0, (¬ ∀ h : φ.A, ψ (0, h) = 1) →
      ‖(∑ t ∈ TT, ψ (0, t)) - (((3 * (φ.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤ φ.o * δ * (TT.card : ℝ) := by
  classical
  intro φ TT δ hsh ψ hψ hnt
  have hmem : ∀ s ∈ φ.A0, ψ (0, s) = 1 := by
    simpa [PsiA] using hψ
  let θ : AddChar φ.A ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr E0 φ.A)
  have hθ : ∀ t, θ t = ψ (0, t) := fun t => rfl
  have h1 : θ ≠ 0 := by
    intro h
    apply hnt
    intro t
    rw [← hθ, h, AddChar.zero_apply]
  have ho : Fintype.card φ.A = φ.o * Nat.card φ.A0 := by
    rw [Frame.card_A, Frame.natCard_cyclic_subgroup, Frame.exponent_eq_index_mul_cyclic_order]
  have hpos : (0 : ℝ) < 3 * (φ.o : ℝ) + 1 := by positivity
  have hs : ∀ g : φ.A, |((TT.filter fun t => t - g ∈ φ.A0).card : ℝ) -
      (3 * (3 * (φ.o : ℝ) + 1)⁻¹ * TT.card + if g ∈ φ.A0 then (3 * (φ.o : ℝ) + 1)⁻¹ * TT.card else 0)|
        ≤ δ * TT.card := by
    intro g
    have hg := hsh g
    convert hg using 3
    simp only [Frame.lam]
    split_ifs <;> field_simp <;> ring
  have hfin := tops_sum_gen φ.A0 θ (fun s hs => by rw [hθ]; exact hmem s hs) h1 TT φ.o ho _ _ _ hs
  simp only [hθ] at hfin
  push_cast at hfin ⊢
  exact le_of_le_of_eq hfin (by ring)
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.hostFactsS
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private lemma inPhi_of_jac {φ : Frame} (H : HostAx φ) (u : (ZMod H.toHostRaw.condN)ˣ) (k : ℕ)
    (hk : (u : ZMod H.toHostRaw.condN).val ≡ k [MOD H.d]) (hj : jacobiSym (k : ℤ) H.d = 1) :
    Formalism.D5.InPhi (Multiplicative.toAdd (recH H.toHostRaw u)) := by
  have h1 : ((H.toHostRaw.art u).1.2 : ℤ) = 1 := by
    rw [H.der.art_ch u, jacobi_congr hk, hj]
  have h2 : (H.toHostRaw.art u).1.2 = 1 := Units.ext h1
  show Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H.toHostRaw.art u).1.2) = 0
  rw [Formalism.LFunctionChainParameters.LHost.sgn2_toAdd_eq_zero_iff]
  exact h2

private lemma jac_of_dvd {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    jacobiSym (p : ℤ) H.d = 1 := by
  have hd4 := H.d_mod_four
  rcases (H.dvd_QSq_iff hp).mp h with hQ | rfl
  · by_cases h2 : p = 2
    · subst h2
      exact jac_two_d H.hyp
    · have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
      rw [← jacobi_neg_recip hd4 hodd]
      exact H.QS_split p hp h2 hQ
  · have hodd : H.q % 2 = 1 := by
      have := H.hyp.2.2.1
      omega
    rw [← jacobi_neg_recip hd4 hodd]
    exact H.hyp.2.2.2.2

private lemma d_dvd_ordCompl {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    H.d ∣ ordCompl[p] H.condN := by
  apply Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN
  intro hpd
  have hpe : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp hpd
  exact H.d_not_dvd_QSq (hpe ▸ h)

private lemma toE_iod' (φ : Frame) : Multiplicative.toAdd (toE φ φ.iod) = sgc0 := by
  rw [(toE_bij φ).2.1]
  rfl

private theorem hostFactsS_pf :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (H.QS * H.q).primeFactors := by
  intro φ H
  haveI : NeZero H.toHostRaw.condN := ⟨H.toHostRaw.condN_ne_zero⟩
  have hQq0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
  refine
    { d_prime := H.d_prime
      two_mem := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_of_dvd_left H.two_dvd_QS _, hQq0⟩
      q1_mem := Nat.mem_primeFactors.mpr ⟨H.q_prime, dvd_mul_left _ _, hQq0⟩
      d_not_mem := fun hm => H.d_not_dvd_QSq (Nat.dvd_of_mem_primeFactors hm)
      unram := ?_
      split_inertia := ?_
      split_frob := ?_
      inertia_d := ?_ }
  · intro p hp hpS hpd
    have hpN : ¬ p ∣ H.toHostRaw.condN := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h1, hQq0⟩)
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp h1)
    have hloc := (unramified_spec _ p H.toHostRaw.condN_ne_zero hp hpN).1
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [hloc, Subgroup.mem_bot] at hu
    subst hu
    simp
  · intro p hpS x hx
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [mem_localUnits_iff] at hu
    exact inPhi_of_jac H u 1 (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hu) (by simp)
  · intro p hpS
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    have hf := (frobUnit_modEq (N := H.toHostRaw.condN) hp).1
    exact inPhi_of_jac H _ p (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hf)
      (jac_of_dvd H.toHostRaw hp hdvd)
  · intro x
    have hparts := parts_of_eq (N := H.toHostRaw.condN) (k := 1) (m := H.QS * H.q) H.d_prime
      (by show H.QS * H.q * H.d = _; ring) H.d_not_dvd_QSq hQq0
    refine (mem_inertia_iff H.q H.d (recH H.toHostRaw) H.d x).trans ?_
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [mem_localUnits_iff, hparts.2] at hu
      rcases H.art_d u hu with h | h
      · left
        simp [recH, h]
      · right
        show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
        rw [h]
        exact toE_iod' φ
    · rintro (rfl | rfl)
      · exact ⟨1, Subgroup.one_mem _, by simp⟩
      · obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.toHostRaw.condN) (a := H.QS * H.q) (b := H.d)
          rfl H.coprime_QSq_d (dvd_mul_right _ _) H.d_dvd_condN 1 (-1)
        have hloc : (u : ZMod H.toHostRaw.condN).val ≡ 1 [MOD H.QS * H.q] :=
          (unitsMap_eq_one_iff _ u).mp hu1
        refine ⟨u, ?_, ?_⟩
        · rw [mem_localUnits_iff, hparts.2]
          exact hloc
        · have hcast : (((u : ZMod H.toHostRaw.condN).val : ℤ) : ZMod H.d) = ((-1 : ℤ) : ZMod H.d) := by
            have h3 := congrArg (fun v : (ZMod H.d)ˣ => (v : ZMod H.d)) hu2
            simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
              Units.val_neg, Units.val_one] at h3
            push_cast
            rw [ZMod.natCast_val]
            exact h3
          rw [ZMod.intCast_eq_intCast_iff] at hcast
          have hjac : ((H.toHostRaw.art u).1.2 : ℤ) = -1 := by
            rw [H.der.art_ch u, jacobiSym.mod_left,
              show (((u : ZMod H.toHostRaw.condN).val : ℕ) : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) from hcast,
              ← jacobiSym.mod_left, jacobiSym.at_neg_one (H.d_prime.odd_of_ne_two H.d_ne_two),
              ZMod.χ₄_nat_three_mod_four H.d_mod_four]
          rcases H.art_d u hloc with h | h
          · exfalso
            rw [h] at hjac
            simp at hjac
          · show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
            rw [h]
            exact toE_iod' φ

theorem UpperTheory.Comparison₂.hostFactsS :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (insert H.q H.small) := by
  intro φ H
  have hset : insert H.q H.small = (H.QS * H.q).primeFactors := by
    rw [Nat.primeFactors_mul H.QS_ne_zero H.q_prime.ne_zero, H.q_prime.primeFactors]
    show insert H.q H.QS.primeFactors = _
    ext a
    simp [or_comm]
  rw [hset]
  exact hostFactsS_pf φ H
end

