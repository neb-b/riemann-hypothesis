module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Adj2
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem int_units_mul_neg_one_eq_of_ne (u v : ℤˣ) (h : u ≠ v) : u * -1 = v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all

theorem UpperTheory.V.Ws.adj2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (g : G ℚ Ω) (s₁ s₂ s₃ : ℤˣ), ∃ g', X.φ g' = s₁ ∧ X.η g' = s₂ ∧ X.η' g' = s₃ ∧ D.Psi g' = D.Psi g ∧ D.ξ g' = D.ξ g ∧ D.om g' = D.om g ∧ X.κ g' = X.κ g := by
  intro Ω _ _ _ l _ c D hD X g s₁ s₂ s₃
  obtain ⟨huniq, -, -, -, hout⟩ := away D hD
  have hφ := X.hφ
  have hη := X.hη
  have hη' := X.hη'
  have pp₃ := hφ.prime
  have pp := hη.prime
  have pp' := hη'.prime
  have n₃ : X.p₃ ∉ D.S := hφ.nm
  have n₁ : X.p ∉ D.S := fun h => hη.nm (Finset.mem_insert_of_mem h)
  have n₂ : X.p' ∉ D.S := fun h => hη'.nm (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have d₃ : X.p ≠ X.p₃ := fun h => hη.nm (h ▸ Finset.mem_insert_self _ _)
  have d₃' : X.p' ≠ X.p₃ := fun h => hη'.nm (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have d' : X.p' ≠ X.p := fun h => hη'.nm (h ▸ Finset.mem_insert_self _ _)
  have kill : ∀ q, Nat.Prime q → q ∉ D.S → ∀ t ∈ Ine (D.pl q),
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    intro q hq hqS t ht
    obtain ⟨haw, hk⟩ := hout (D.pl q) q hq hqS (hD.pl_over q hq)
    obtain ⟨a1, a2, a3⟩ := hk t ht
    exact ⟨a1, a2, a3, MonoidHom.mem_ker.1 (X.kap.unrS (D.pl q) haw ht)⟩
  have off : ∀ q r, Nat.Prime q → Nat.Prime r → q ≠ r → ¬ (D.pl q).valuation (r : Ω) < 1 := by
    intro q r hq hr hqr hv
    exact hqr (huniq (D.pl q) q r hq hr (hD.pl_over q hq) hv)
  obtain ⟨h₃, m₃, e₃⟩ := hφ.ram (D.pl X.p₃) (hD.pl_over _ pp₃)
  obtain ⟨h₁, m₁, e₁⟩ := hη.ram (D.pl X.p) (hD.pl_over _ pp)
  obtain ⟨h₂, m₂, e₂⟩ := hη'.ram (D.pl X.p') (hD.pl_over _ pp')
  have a₃ : X.η h₃ = 1 := MonoidHom.mem_ker.1 (hη.unr _ (off _ _ pp₃ pp d₃.symm) m₃)
  have b₃ : X.η' h₃ = 1 := MonoidHom.mem_ker.1 (hη'.unr _ (off _ _ pp₃ pp' d₃'.symm) m₃)
  have a₁ : X.φ h₁ = 1 := MonoidHom.mem_ker.1 (hφ.unr _ (off _ _ pp pp₃ d₃) m₁)
  have b₁ : X.η' h₁ = 1 := MonoidHom.mem_ker.1 (hη'.unr _ (off _ _ pp pp' d'.symm) m₁)
  have a₂ : X.φ h₂ = 1 := MonoidHom.mem_ker.1 (hφ.unr _ (off _ _ pp' pp₃ d₃') m₂)
  have b₂ : X.η h₂ = 1 := MonoidHom.mem_ker.1 (hη.unr _ (off _ _ pp' pp d') m₂)
  obtain ⟨k₃, k₃', k₃'', k₃'''⟩ := kill _ pp₃ n₃ h₃ m₃
  obtain ⟨k₁, k₁', k₁'', k₁'''⟩ := kill _ pp n₁ h₁ m₁
  obtain ⟨k₂, k₂', k₂'', k₂'''⟩ := kill _ pp' n₂ h₂ m₂
  obtain ⟨t₃, f₃, u₃, v₃, w₃, x₃, y₃, z₃⟩ : ∃ t, X.φ (g * t) = s₁ ∧ X.η t = 1 ∧ X.η' t = 1 ∧
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    by_cases hc : X.φ g = s₁
    · exact ⟨1, by simpa using hc, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · exact ⟨h₃, by rw [map_mul, e₃]; exact int_units_mul_neg_one_eq_of_ne _ _ hc, a₃, b₃, k₃, k₃', k₃'', k₃'''⟩
  obtain ⟨t₁, f₁, u₁, v₁, w₁, x₁, y₁, z₁⟩ : ∃ t, X.η (g * t₃ * t) = s₂ ∧ X.φ t = 1 ∧ X.η' t = 1 ∧
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    by_cases hc : X.η (g * t₃) = s₂
    · exact ⟨1, by simpa using hc, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · exact ⟨h₁, by rw [map_mul, e₁]; exact int_units_mul_neg_one_eq_of_ne _ _ hc, a₁, b₁, k₁, k₁', k₁'', k₁'''⟩
  obtain ⟨t₂, f₂, u₂, v₂, w₂, x₂, y₂, z₂⟩ : ∃ t, X.η' (g * t₃ * t₁ * t) = s₃ ∧ X.φ t = 1 ∧ X.η t = 1 ∧
      D.Psi t = 1 ∧ D.ξ t = 1 ∧ D.om t = 1 ∧ X.κ t = 1 := by
    by_cases hc : X.η' (g * t₃ * t₁) = s₃
    · exact ⟨1, by simpa using hc, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · exact ⟨h₂, by rw [map_mul, e₂]; exact int_units_mul_neg_one_eq_of_ne _ _ hc, a₂, b₂, k₂, k₂', k₂'', k₂'''⟩
  refine ⟨g * t₃ * t₁ * t₂, ?_, ?_, f₂, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, f₃, u₁, u₂, mul_one, mul_one]
  · rw [map_mul, f₁, v₂, mul_one]
  · simp [map_mul, w₃, w₁, w₂]
  · simp [map_mul, x₃, x₁, x₂]
  · simp [map_mul, y₃, y₁, y₂]
  · simp [map_mul, z₃, z₁, z₂]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsInertiaElementAtTwoXiPowFourNeOne
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

private theorem all_mem_range (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ∈ (proj 2 (2 ^ n)).range := by
  rw [(projFacts (2 ^ n) 2 Nat.prime_two).2.2.2.2.2.1, MonoidHom.mem_ker]
  have e : ordCompl[2] (2 ^ n) = 1 := by
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same, Nat.div_self (by positivity)]
  have : Subsingleton (ZMod (ordCompl[2] (2 ^ n))) := by rw [e]; infer_instance
  exact Subsingleton.elim _ _

private theorem tot_dvd (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two hk]
    simpa using pow_dvd_pow 2 (Nat.sub_le k 1)

private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    exact tot_dvd k
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

theorem UpperTheory.V.Ws.exists_inertia_element_at_two_xi_pow_four_ne_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 → ∃ g ∈ Ine (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  rintro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, -, -, -, -, -, -, hψ, -, hp, ξ', ξ₀, hprim, -, -, hξ⟩ κ j hκ A hA0
  have hA : A.valuation ((2 : ℕ) : Ω) < 1 := by rwa [Nat.cast_ofNat]
  have hlp : l.Prime := hl.out
  have hlo : Odd l := hlp.odd_of_ne_two hG.l_odd
  have hom : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hG.om_bar σ⟩
  have h1 : Ine (F := ℚ) A ≤ D.om.ker := ((omT Ω l c).2 D.om hom).2.2.2.2.2.1 _ (not_over_odd _ hA hlo)
  have hq : 0 < h.q := NeZero.pos _
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨-, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  have b3 : 2 ^ (c2 ψ + 6) ≤ 2 ^ h.nII l ψ := le_trans (by
      rw [mul_assoc, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (by have := hlp.pos; positivity)) b2
  have p1 := pow_cond (psi2 ψ) (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
  clear b2
  generalize h.nII l ψ = n at *
  generalize c2 ψ = k at *
  have h3 : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨u, hu, hc⟩ : ZMod.unitOfCoprime 3 h3 ∈ (Ine (F := ℚ) A).map (Chr.cls ℚ Ω (2 ^ n)) := by
    rw [(compIne Ω (2 ^ n) 2 Nat.prime_two _ hA).1]
    exact all_mem_range _ _
  have hξu : D.ξ u = ξ'.toUnitHom (ZMod.unitOfCoprime 3 h3) := by
    have h4 : Chr.cls ℚ Ω 1 u = 1 := Subsingleton.elim _ _
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, h4, hc, map_one, one_mul]
  have hψu : D.ψ u ^ 2 ^ k = 1 := by
    rw [hψ, ((compIne Ω h.N 2 Nat.prime_two _ hA).2 c.O ψ).1 u hu, Chr.dirG, MonoidHom.comp_apply]
    ext1
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe]
    change (psi2 ψ ^ 2 ^ k) _ = _
    rw [p1, MulChar.one_apply_coe, Units.val_one]
  have hg : u ^ (2 ^ k * l ^ j) ∈ Ine (F := ℚ) A := pow_mem hu _
  refine ⟨u ^ (2 ^ k * l ^ j), hg, ?_, ?_, fun hb => ?_⟩
  · have a1 := hG.om_bar (u ^ (2 ^ k * l ^ j))
    have a2 : D.om (u ^ (2 ^ k * l ^ j)) = 1 := h1 hg
    have a3 : D.ψ (u ^ (2 ^ k * l ^ j)) = 1 := by rw [map_pow, pow_mul, hψu, one_pow]
    simp only [Raw.bar] at a1 ⊢
    rw [a2, Units.val_one, map_one] at a1
    rw [Raw.Psi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, a3, mul_one, Units.val_pow_eq_pow_val,
      map_pow (residue c.O), ← a1, one_pow]
  · rw [map_pow, mul_comm, pow_mul, ← MonoidHom.pow_apply κ (l ^ j), hκ, MonoidHom.one_apply, one_pow]
  · have a1 : D.ξ u ^ (2 ^ (k + 2) * l ^ j) = 1 := by
      refine large₂.redOne c (2 ^ n) (Nat.Coprime.pow_right _ ((Nat.coprime_primes hlp Nat.prime_two).2 hG.l_odd)) _ ?_ ?_
      · obtain ⟨m, hm⟩ := tot_dvd n
        have a2 : D.ξ u ^ 2 ^ n = 1 := by
          rw [hξu, ← map_pow]
          have : ZMod.unitOfCoprime 3 h3 ^ (Nat.totient (2 ^ n) * m) = 1 := by
            rw [pow_mul, ZMod.pow_totient, one_pow]
          rw [← hm] at this
          rw [this, map_one]
        rw [← pow_mul, mul_comm, pow_mul, a2, one_pow]
      · simp only [Raw.bar] at hb
        rw [← hb, ← map_pow (residue c.O), ← Units.val_pow_eq_pow_val, map_pow D.ξ, ← pow_mul]
        congr 3
        ring
    have a2 := congrArg Units.val a1
    rw [Units.val_pow_eq_pow_val, hξu, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime, Units.val_one] at a2
    have a3 := UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ' hprim 3 (k + 2) (l ^ j) (by decide) (by norm_num) hlo.pow a2
    have a4 : 2 ^ (k + 6) = 16 * 2 ^ (k + 2) := by ring
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.NegVal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem neg_val {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (χ : Γ →* Oˣ) (h0 : 0 < orderOf χ)
    (h : Even (orderOf χ)) : ∃ σ, χ σ = -1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : χ ^ k ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  obtain ⟨σ, hσ⟩ : ∃ σ, χ σ ^ k ≠ 1 := by
    by_contra hn
    push Not at hn
    exact h1 (MonoidHom.ext hn)
  have h2 : (χ σ ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_two, ← hk, ← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
  have h3 : ((χ σ ^ k : Oˣ) : O) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  refine ⟨σ ^ k, ?_⟩
  rw [map_pow]
  rcases sq_eq_one_iff.1 h3 with h4 | h4
  · exact absurd (Units.ext h4) hσ
  · exact Units.ext h4

theorem UpperTheory.V.Ws.ev2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∃ t, D.om t = 1 ∧ κ t = 1 ∧ Raw.bar D.Psi t = -1 := by
  intro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, _, _, _, _, ⟨_, hev, _⟩, hO⟩ κ j hκ
  have lp : l.Prime := hl.out
  have hT : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    have := hG.om_bar σ
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact sub_eq_zero.2 this⟩
  have hk := ((omT Ω l c).2 D.om hT).2.1
  obtain ⟨b, -, -, hb⟩ := (psiBar Ω l c D.om hT h.N ψ).1
  have ho := (psiBar Ω l c D.om hT h.N (chiP l ψ)).2.2.1
  obtain ⟨σ, hσ⟩ := neg_val (Chr.dirG ℚ Ω (chiP l ψ)) (ho ▸ (chiP l ψ).orderOf_pos) (ho ▸ hev)
  obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O h.N l lp
  have h1 : comp l (chiP l ψ) = 1 := by rw [chiP, hmul, hinv, (h6 _).1, mul_inv_cancel]
  have hA := hG.pl_over l lp
  have hI := ((compIne Ω h.N l lp _ hA).2 c.O (chiP l ψ)).2.2 h1
  obtain ⟨τ, hτ, hc⟩ : Chr.cls ℚ Ω l σ ∈ (Ine (F := ℚ) (D.pl l)).map (Chr.cls ℚ Ω l) := by
    rw [(compIne Ω l l lp _ hA).1, (projFacts l l lp).2.2.2.2.2.1, MonoidHom.mem_ker]
    have : Subsingleton (ZMod (ordCompl[l] l)) := by
      rw [lp.factorization_self, pow_one, Nat.div_self lp.pos]
      infer_instance
    exact Subsingleton.elim _ _
  have e1 : D.om (σ * τ⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hk, MonoidHom.mem_ker, map_mul, map_inv, hc, mul_inv_cancel]
  have e2 : Chr.dirG ℚ Ω (chiP l ψ) (σ * τ⁻¹) = -1 := by
    rw [map_mul, map_inv, hσ, MonoidHom.mem_ker.1 (hI hτ), inv_one, mul_one]
  have e3 : D.om ((σ * τ⁻¹) ^ l ^ j) = 1 := by rw [map_pow, e1, one_pow]
  have e4 : Chr.dirG ℚ Ω (chiP l ψ) ((σ * τ⁻¹) ^ l ^ j) = -1 := by
    rw [map_pow, e2, ((lp.odd_of_ne_two hG.l_odd).pow).neg_one_pow]
  refine ⟨(σ * τ⁻¹) ^ l ^ j, e3, ?_, ?_⟩
  · rw [map_pow, ← MonoidHom.pow_apply, hκ, MonoidHom.one_apply]
  · have e5 := hb D.e ((σ * τ⁻¹) ^ l ^ j)
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, e3, e4, one_pow, one_mul, ← hO.psi,
      ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at e5
    refine e5.trans ?_
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.OddPowNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem odd_pow_ne {k : Type} [Field k] {x : k} {n : ℕ} (hn : x ^ 2 ^ n = 1) (h4 : x ^ 4 ≠ 1) {m : ℤ} (hm : Odd m) :
    x ^ m ≠ 1 := by
  intro hxm
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hn
  set u := Units.mk0 x hx0 with hu_def
  have hu : u ^ 2 ^ n = 1 := Units.ext (by simpa [u] using hn)
  have hum : u ^ m = 1 := Units.ext (by simpa [u] using hxm)
  obtain ⟨j, -, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)
  have hdm : (orderOf u : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hum
  cases j with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff] at hoj
    apply h4
    have hx1 : x = 1 := by simpa [u] using congrArg Units.val hoj
    simp [hx1]
  | succ j =>
    have h2 : (2 : ℤ) ∣ m := by
      refine dvd_trans ?_ hdm
      rw [hoj]
      exact_mod_cast dvd_pow_self 2 (Nat.succ_ne_zero j)
    exact (Int.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

private theorem dist4 {k : Type} [Field k] {x : k} (h1 : (-1 : k) ≠ 1) (h0 : x ≠ 0) (hx : x ^ 2 ≠ 1) :
    Function.Injective (![x * -1, -1, x, 1] : Fin 4 → k) := by
  have h2 : (2 : k) ≠ 0 := by
    intro h
    apply h1
    linear_combination -h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢
  all_goals first
    | exact absurd (by linear_combination h * h) hx
    | exact absurd (by linear_combination (-x - 1) * h) hx
    | exact absurd (by linear_combination (x - 1) * h) hx
    | exact absurd (by linear_combination (-x + 1) * h) hx
    | exact absurd (by linear_combination (x + 1) * h) hx
    | exact h1 h
    | exact h1 h.symm
    | exact h0 ((mul_eq_zero.mp (by linear_combination -h : (2 : k) * x = 0)).resolve_left h2)
    | exact h0 ((mul_eq_zero.mp (by linear_combination h : (2 : k) * x = 0)).resolve_left h2)

private theorem lab_inj (pr : Bool) : Function.Injective (lab pr) := by
  cases pr <;> decide

private theorem lab_surj (pr : Bool) : ∃ i, lab pr i = 3 := by
  cases pr <;> decide

theorem UpperTheory.V.Ws.ok2A :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ a u t, X.Elts a u t → (∀ w, ∃ g ∈ T.GalL, T.rb w g ≠ Raw.bar D.om (resQ T.F g)) ∧ (∀ w ∈ roots, ∃ g ∈ T.GalL, T.rb w g ≠ 1) ∧ (∀ η : T.GalL →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (∀ g : T.GalL, D.om (resQ T.F g) = 1 → η g = 1) → (∀ i, ∃ j, ∀ g : T.GalL, η g * Raw.bar (chi D T.pr i) (resQ T.F g) = Raw.bar (chi D T.pr j) (resQ T.F g)) → η = 1) ∧ (∃ w ∈ roots, ∀ n : ℕ, 0 < n → n ≤ 4 → ∃ g ∈ T.GalL, T.rb w g ^ n ≠ 1) ∧ (resQ T.F T.g0 = t → ∀ i j, i ≠ j → Raw.bar (chi D T.pr i) (resQ T.F T.g0) ≠ Raw.bar (chi D T.pr j) (resQ T.F T.g0)) := by
  intro Ω _ _ _ l _ c D hD X T hOn a u t hE
  obtain ⟨h1, -, hal, hth, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨n, hn⟩ := X.ord
  have hxord : ∀ g, Raw.bar D.ξ g ^ 2 ^ n = 1 := by
    intro g
    simp only [Raw.bar]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hn]
    simp
  have hchi : ∀ b i, chi D b i = D.ps (lab b i) := fun b i => rfl
  have lift : ∀ y ∈ X.H ⊓ X.η.ker, ∃ s ∈ T.GalL, resQ T.F s = y := by
    intro y hy
    obtain ⟨s, hs⟩ := exists_resQ (F := T.F) (g := y) (by rw [hOn.1]; exact hy.1)
    refine ⟨s, ?_, hs⟩
    unfold Tower.GalL
    rw [Subgroup.mem_comap, hOn.2, hs]
    exact hy.2
  have hbu : Raw.bar D.om u = 1 := by simp [Raw.bar, hE.u_om]
  have hxu1 : Raw.bar D.ξ u ≠ 1 := by
    intro h
    apply hE.u_xi
    rw [h, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rcases Int.even_or_odd w.1 with he | ho
    · obtain ⟨s, hsG, hs⟩ := lift a hE.a_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.a_xi, hE.a_psi, hE.a_om, one_zpow, mul_one, he.neg_one_zpow]
      exact fun h => h1 h.symm
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one, hbu]
      exact odd_pow_ne (hxord u) hE.u_xi ho
  · intro w hw
    by_cases ho : Odd w.1
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one]
      exact odd_pow_ne (hxord u) hE.u_xi ho
    · obtain ⟨w1, w2⟩ := w
      simp [UpperTheory.V.Ws.roots, oddRoots, wAl, wBe, wTh, wPs] at hw
      obtain ⟨s, hsG, hs⟩ := lift t hE.t_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.t_psi]
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact absurd (by decide) ho
        | (split_ifs <;> simpa using h1)
  · intro η hη2 hηom hperm
    obtain ⟨i0, hi0⟩ := lab_surj T.pr
    obtain ⟨j, hj⟩ := hperm i0
    have key : ∀ s : T.GalL, (η s : ResidueField c.O) = Raw.bar (D.ps (lab T.pr j)) (resQ T.F s) := by
      intro s
      have h := hj s
      rw [hchi, hchi, hi0] at h
      have h3 : D.ps 3 = 1 := rfl
      rw [h3] at h
      simpa [Raw.bar] using h
    obtain ⟨su, hsuG, hsu⟩ := lift u hE.u_mem
    obtain ⟨st, hstG, hst⟩ := lift t hE.t_mem
    have hηu : η ⟨su, hsuG⟩ = 1 := hηom _ (by simp only [hsu]; exact hE.u_om)
    have hηt : η ⟨st, hstG⟩ = 1 := hηom _ (by simp only [hst]; exact hE.t_om)
    have ku := key ⟨su, hsuG⟩
    have kt := key ⟨st, hstG⟩
    rw [hηu] at ku
    rw [hηt] at kt
    simp only [hsu] at ku
    simp only [hst] at kt
    generalize lab T.pr j = k at ku kt key
    fin_cases k
    · exfalso
      change _ = Raw.bar D.th u at ku
      simp only [hth, hE.u_psi, mul_one, Units.val_one] at ku
      exact hxu1 ku.symm
    · exfalso
      change _ = Raw.bar D.Psi t at kt
      simp only [hE.t_psi, Units.val_one] at kt
      exact h1 kt.symm
    · exfalso
      change _ = Raw.bar D.al u at ku
      simp only [hal, Units.val_one] at ku
      exact hxu1 ku.symm
    · ext s
      have h0 : D.ps 3 = 1 := rfl
      have := key s
      simp only [Fin.reduceFinMk, Fin.isValue] at this
      rw [h0] at this
      simpa [Raw.bar] using this
  · refine ⟨(1, 0), by simp [UpperTheory.V.Ws.roots, oddRoots, wAl], fun m hm0 hm4 => ?_⟩
    obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
    refine ⟨s, hsG, ?_⟩
    rw [hrb, hs, hE.u_psi]
    simp only [one_zpow, mul_one, zpow_one]
    interval_cases m
    · simpa using hxu1
    · intro h
      apply hE.u_xi
      rw [show 4 = 2 * 2 by rfl, pow_mul, h, one_pow]
    · have h3 := odd_pow_ne (hxord u) hE.u_xi (m := 3) (by decide)
      simpa using h3
    · exact hE.u_xi
  · intro hg0 i j hij heq
    rw [hg0] at heq
    have hx0 : Raw.bar D.ξ t ≠ 0 := by
      intro h0
      have h := hxord t
      rw [h0, zero_pow (by positivity)] at h
      exact zero_ne_one h
    have hinj := dist4 h1 hx0 hE.t_xi
    have hvals : ∀ k, Raw.bar (D.ps k) t = ![Raw.bar D.ξ t * -1, -1, Raw.bar D.ξ t, 1] k := by
      intro k
      fin_cases k
      · show Raw.bar D.th t = _
        simp [hth, hE.t_psi]
      · show Raw.bar D.Psi t = _
        simp [hE.t_psi]
      · show Raw.bar D.al t = _
        simp [hal]
      · show Raw.bar (1 : G ℚ Ω →* (↥c.O)ˣ) t = _
        simp [Raw.bar]
    rw [hchi, hchi, hvals, hvals] at heq
    exact hij (lab_inj T.pr (hinj heq))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Ok2B
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.ok2B :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → (∀ A : ValuationSubring Ω, Ine (F := T.F) A ≤ T.GalL) ∧ (∀ A : ValuationSubring Ω, Raw.Away {l} A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 → D.ψ (resQ T.F g) = 1) ∧ (∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, cycZ T.F Ω l g = 1 → D.ψ (resQ T.F g) ^ m = 1) ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 := by
  intro Ω _ _ _ l hl c D hD X T hT
  obtain ⟨hpq, -, hxi, -, -⟩ := away D hD
  obtain ⟨-, -, -, -, -, hrb, -, -, -⟩ := barFacts D hD
  have hH : ∀ g : G T.F Ω, resQ T.F g ∈ X.H := fun g => hT.1 ▸ resQ_mem T.F g
  refine ⟨fun A g hg => ?_, fun A hA g hg h => ?_, ?_, fun A hA g hg => ?_⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    change resQ T.F g ∈ T.K.fixingSubgroup
    rw [hT.2]
    by_cases hp : A.valuation (X.p : Ω) < 1
    · have hp' : ¬ A.valuation (X.p' : Ω) < 1 := fun h =>
        X.hη'.nm (hpq A _ _ X.hη.prime X.hη'.prime hp h ▸ Finset.mem_insert_self _ _)
      exact (X.mem_H.1 (hH g)).2.1.trans (X.hη'.unr A hp' hg')
    · exact X.hη.unr A hp hg'
  · exact X.kap.kb A hA _ ((resQ_Ine T.F A g).1 hg) ((hrb _).1 h).2 (X.mem_H.1 (hH g)).2.2
  · obtain ⟨m, hm, h⟩ := X.kap.kc
    exact ⟨m, hm, fun g hg => h _ ((resQ_cyc T.F g).trans hg) (X.mem_H.1 (hH g)).2.2⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    have h3 : ¬ A.valuation (X.p₃ : Ω) < 1 := fun h =>
      X.hφ.nm (hpq A _ _ hl.out X.hφ.prime hA h ▸ hD.l_mem)
    have h1 : D.ξ (resQ T.F g) = 1 := hxi A hA hg'
    have h2 : X.φ (resQ T.F g) = 1 := X.hφ.unr A h3 hg'
    refine (hrb _).2 ⟨?_, ?_⟩
    · rw [Raw.bar, h1, Units.val_one, map_one]
    · rw [(X.mem_H.1 (hH g)).1, h2, Units.val_one, Int.cast_one]
end

