module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vanish
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OfEMulStar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.UnitAdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPSmul

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.EvUnit
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem hs_sq {K : Type} [Field K] (D x : K) : hs D x * hs D x = 1 := by
  unfold hs; split_ifs <;> norm_num

private theorem ev_unit {O K : Type} [CommRing O] [Field K] [Algebra O K] {u : O} (hu : IsUnit u) : EvenVal O (algebraMap O K u) :=
  ⟨hu.unit, 1, one_ne_zero, by simp⟩

private theorem ev_neg {O K : Type} [CommRing O] [Field K] [Algebra O K] {x : K} (h : EvenVal O x) : EvenVal O (-x) := by
  obtain ⟨u, s, hs, e⟩ := h
  exact ⟨-u, s, hs, by simp [e]⟩

private theorem ev_mul {O K : Type} [CommRing O] [Field K] [Algebra O K] {x y : K} (h : EvenVal O x) (h' : EvenVal O y) : EvenVal O (x * y) := by
  obtain ⟨u, s, hs, e⟩ := h
  obtain ⟨u', s', hs', e'⟩ := h'
  exact ⟨u * u', s * s', mul_ne_zero hs hs', by rw [e, e', Units.val_mul, map_mul]; ring⟩

theorem UpperTheory.V.Z.Sym.Loc.kappa : UpperTheory.V.Z.Sym.Loc.Kappa := by
  intro O K _ _ _ _ _ Δ τ L hreg c hc lam hl hX z hz j χ hj hχ
  haveI := L.frac
  have HL := hsLaw O K Δ L
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨u, s, hs, e⟩ := hc
    rw [zero_mul] at e
    exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs) e.symm
  have hU : Unr O χ := fun u => by
    have := hχ (Units.map (algebraMap O K : O →* K) u) u rfl
    rw [Ideal.span_singleton_eq_top.2 u.isUnit, Nat.card_unique] at this
    refine Units.ext ?_
    rw [this, show ((Units.map (algebraMap O K : O →* K) u : Kˣ) : K) = algebraMap O K u from rfl, HL.2.1 _ _ L.even (ev_unit u.isUnit)]
    simp
  have h0 := datLam K Δ τ c hreg hc0 lam hl z hz
  by_cases hτ : τ ∈ (algebraMap O K).range
  swap
  · have h1 : ∀ t : Kˣ, lcount O c (dLam lam z) ((t : K) • (1 : EL Δ τ)) = 0 := fun t => by
      by_contra h'
      exact hτ (vanish O K Δ τ L c _ _ (datSmul K Δ τ c _ _ h0 t) h').1
    have h2 : gOrb O j χ z = 0 := by
      by_contra h'
      exact hτ (gVanish O K Δ τ L j hj χ z (.inr hz) h')
    simp only [kapSum, h1, h2, mul_zero, finsum_zero]
  obtain ⟨a, ha⟩ := exists_a (K := K) (τ := τ)
  have GV := gVals O K Δ τ L hreg hτ j χ hj hU a ha z hz
  have hτ' := hτ
  obtain ⟨τ₀, e₀⟩ := hτ
  have ep : algebraMap O K (2 + τ₀) = 2 + τ := by simp [map_ofNat, e₀]
  have em : algebraMap O K (2 - τ₀) = 2 - τ := by simp [map_ofNat, e₀]
  change _ = eps τ lam * _ * _
  have red : ∀ lam' : Lsq K Δ, QuadraticAlgebra.norm lam' = 2 + τ → 2 + τ + QuadraticAlgebra.trace lam' ≠ 0 → ∀ x : ℂ,
      eps τ lam' * kapSum O c (dLam lam' z) 1 = x → kapSum O c (dLam lam z) 1 = eps τ lam * x := fun lam' h1 h2 x h3 => by
    rw [← h3, ← kapMove O K Δ τ L hreg c hc0 z hz lam lam' hl h1 hX h2, ← mul_assoc]
    have : eps τ lam * eps τ lam = 1 := by
      unfold eps
      rw [mul_mul_mul_comm, hs_sq, hs_sq, mul_one]
    rw [this, one_mul]
  have val : ∀ lam' : Lsq K Δ, QuadraticAlgebra.norm lam' = 2 + τ → ∀ e x : ℂ,
      (∀ t : Kˣ, lcount O c (dLam lam' z) ((t : K) • (1 : EL Δ τ)) = if hs (τ ^ 2 - 4) (t : K) = e then x else 0) →
      (∃ t : Kˣ, hs (τ ^ 2 - 4) (t : K) = e) → kapSum O c (dLam lam' z) 1 = e * x := fun lam' h1 e x H He =>
    ((sumShift O K Δ τ L hreg (fun t => lcount O c (dLam lam' z) ((t : K) • (1 : EL Δ τ)))
      (lcount_inv L (datLam K Δ τ c hreg hc0 lam' h1 z hz)) 1).2.2 e x H He).2
  rw [mul_assoc]
  rcases tri L τ₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨r, hr, hr2⟩ := sqrtO O K Δ L (2 + τ₀) 2 L.two (by convert h1 using 1; ring)
    have hr' : algebraMap O K r ^ 2 = 2 + τ := by rw [← map_pow, hr, ep]
    have h4 : IsUnit (4 : O) := by rw [show (4 : O) = 2 * 2 by ring]; exact L.two.mul L.two
    obtain ⟨w, hw, hw2⟩ := sqrtO O K Δ L (2 * (r * (r + 2))) 4 h4 (by
      rw [show 2 * (r * (r + 2)) - 4 ^ 2 = (2 * (r + 4)) * (r - 2) by ring]; exact Ideal.mul_mem_left _ _ hr2)
    have hwu : IsUnit w := by
      by_contra h'
      have : w - (w - 4) ∈ IsLocalRing.maximalIdeal O := sub_mem h' hw2
      rw [sub_sub_cancel] at this
      exact this h4
    have hXu : IsUnit (r * (r + 2)) := isUnit_of_mul_isUnit_right (hw ▸ hwu.pow 2)
    have eX : 2 + τ + QuadraticAlgebra.trace (algebraMap K (Lsq K Δ) (algebraMap O K r)) = algebraMap O K (r * (r + 2)) := by
      rw [QuadraticAlgebra.trace_algebraMap, ← hr', map_mul, map_add (f := _), map_ofNat]; ring
    have hX0 : algebraMap O K (r * (r + 2)) ≠ 0 := (hXu.map _).ne_zero
    have hn : QuadraticAlgebra.norm (algebraMap K (Lsq K Δ) (algebraMap O K r)) = 2 + τ := by rw [QuadraticAlgebra.norm_algebraMap, hr']
    refine red _ hn (eX ▸ hX0) _ ?_
    rw [val _ hn _ _ (caseP O K Δ τ L hreg r hr2 hr' c hc j χ hj hU a ha z hz)
      ⟨Units.mk0 (-2 * c) (mul_ne_zero (neg_ne_zero.2 L.two_ne) hc0), rfl⟩, GV.1 ⟨h2.unit, ep⟩, eps, eX,
      HL.2.1 Δ _ L.even (ev_unit hXu), show -2 * c = 2 * -c by ring, hsMul O K Δ L _ _ _ hreg L.two_ne (neg_ne_zero.2 hc0)]
    have e2 : hs (τ ^ 2 - 4) 2 * hs (τ ^ 2 - 4) (algebraMap O K (r * (r + 2))) = 1 := by
      rw [← hsMul O K Δ L _ _ _ hreg L.two_ne hX0]
      exact if_pos ⟨algebraMap O K w, 0, by rw [← map_pow, hw, map_mul, map_ofNat]; ring⟩
    linear_combination (hs (τ ^ 2 - 4) (-c) * gOrb O j χ a) * e2
  · by_cases he : EvenVal O (2 + τ)
    · obtain ⟨ε, s, hs0, e⟩ := id he
      have hsi : IsIntegral O s := by
        refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
        have : s ^ 2 = algebraMap O K ((2 + τ₀) * (ε⁻¹ : Oˣ)) := by
          rw [map_mul, ep, e, mul_comm (algebraMap O K ε), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
        rw [this]; exact isIntegral_algebraMap
      obtain ⟨s₀, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hsi
      have e' : 2 + τ = algebraMap O K (ε * s₀ ^ 2) := by rw [e, map_mul, map_pow]
      have hsm : s₀ ∈ IsLocalRing.maximalIdeal O := fun hu => by
        have : τ₀ + 2 = ε * s₀ ^ 2 := IsFractionRing.injective O K (by rw [← e', ← ep, add_comm])
        exact (this ▸ h1 : (ε * s₀ ^ 2 : O) ∈ IsLocalRing.maximalIdeal O) (ε.isUnit.mul (hu.pow 2))
      have hce : EvenVal O c := EvenVal.of_mul_unit h2 (em ▸ hc)
      have hDe : EvenVal O (τ ^ 2 - 4) := by
        rw [show τ ^ 2 - 4 = -((2 - τ) * (2 + τ)) by ring]
        exact ev_neg (ev_mul (em ▸ ev_unit h2) he)
      rw [kapM O K Δ τ L hreg ⟨h2.unit, em⟩ s₀ ε hsm e' c hce z hz lam hl hX, GV.2.2 ⟨h2.unit, em⟩ (Units.mk0 _ hs0) ε e,
        HL.2.1 _ _ hDe (ev_neg hce), one_mul, mul_assoc, Units.val_inv_eq_inv_val, hχ (Units.mk0 _ hs0) s₀ rfl, inv_div, Units.val_mk0]
      congr 1
      rw [div_eq_mul_inv, mul_comm, ← eq_inv_of_mul_eq_one_left (hs_sq Δ _)]
    · have hn : QuadraticAlgebra.norm (1 + ω : Etau K τ) = 2 + τ := by
        simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring
      rw [(kapRam O K Δ τ L c _ _ h0 hτ' he).2, gOdd O K Δ τ L j χ z hreg hj (by rwa [hz, hn]), mul_zero, mul_zero]
  · obtain ⟨l₀, hi, hl₀⟩ := normEx O K Δ L h1.unit
    have hl' : QuadraticAlgebra.norm l₀ = 2 + τ := by rw [hl₀, IsUnit.unit_spec, ep]
    have hD : ∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4 := ⟨-(h1.unit * h2.unit), by
      simp only [Units.val_neg, Units.val_mul, IsUnit.unit_spec, map_neg, map_mul, ep, em]; ring⟩
    have hDe : EvenVal O (τ ^ 2 - 4) := by
      obtain ⟨u, hu⟩ := hD
      exact hu ▸ ev_unit u.isUnit
    have hce : EvenVal O c := EvenVal.of_mul_unit h2 (em ▸ hc)
    obtain ⟨ε, s, hs0, hΔ⟩ := L.even
    obtain ⟨x, hx⟩ := ((descent O K Δ L s⁻¹ ε (by rw [hΔ]; field_simp) l₀).1.1 hi).1
    have main : ∀ (l₁ : Lsq K Δ) (X : O), IsInt O l₁ → QuadraticAlgebra.norm l₁ = 2 + τ → IsUnit X →
        2 + τ + QuadraticAlgebra.trace l₁ = algebraMap O K X →
        kapSum O c (dLam lam z) 1 = eps τ lam * (hs (τ ^ 2 - 4) (-c) * gOrb O j χ z) := fun l₁ X i1 n1 hXu eX => by
      refine red l₁ n1 (eX ▸ (hXu.map _).ne_zero) _ ?_
      rw [val l₁ n1 1 1 (caseG O K Δ τ L hD c hce l₁ i1 n1 z hz) ⟨1, if_pos ⟨1, 0, by simp⟩⟩, eps, eX, GV.1 ⟨h1.unit, ep⟩, GV.2.1 hD,
        HL.2.1 _ _ hDe (ev_unit hXu), HL.2.1 _ _ L.even (ev_unit hXu), HL.2.1 _ _ hDe (ev_neg hce)]
      simp
    by_cases hu : IsUnit (2 + τ₀ + 2 * x)
    · exact main l₀ _ hi hl' hu (by rw [map_add (f := _), ep, map_mul, map_ofNat, hx, QuadraticAlgebra.trace_def]; ring)
    · have hu' : IsUnit (2 + τ₀ - 2 * x) := by
        by_contra h'
        have : (2 + τ₀ + 2 * x) + (2 + τ₀ - 2 * x) ∈ IsLocalRing.maximalIdeal O := add_mem hu h'
        rw [show (2 + τ₀ + 2 * x) + (2 + τ₀ - 2 * x) = 2 * (2 + τ₀) by ring] at this
        exact this (L.two.mul h1)
      exact main (-l₀) _ hi.neg (by rw [QuadraticAlgebra.norm_neg, hl']) hu'
        (by rw [map_sub, ep, map_mul, map_ofNat, hx, map_neg, QuadraticAlgebra.trace_def]; ring)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Stable
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.stable : UpperTheory.V.Z.Sym.Loc.Stable := by
  unfold Stable
  intro O K _ _ _ _ _ Δ τ hL c d m hD hev j hj χ hχ a ha
  have hreg := hD.reg
  have hc := hD.c_ne
  have h2K : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hshift : ∀ (f : Kˣ → ℂ), (∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x) → ∀ g : Kˣ,
      (∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g)) → stabSum O c d m = ∑ᶠ t : Kˣ ⧸ NE τ, f (Quotient.out t) := by
    intro f hf g hk
    unfold stabSum
    rw [finsum_congr (fun t => hk _)]
    exact (sumShift O K Δ τ hL hreg f hf g).1
  by_cases hτ : τ ∈ (algebraMap O K).range
  swap
  · have h0 : ∀ t : Kˣ, lcount O c d ((t : K) • m) = 0 := by
      intro t
      by_contra hne
      exact hτ (vanish O K Δ τ hL c d _ (datSmul K Δ τ c d m hD t) hne).1
    have hg : gOrb O j χ a = 0 := by
      by_contra hne
      exact hτ (gVanish O K Δ τ hL j hj χ a (Or.inl ha) hne)
    rw [hg]
    unfold stabSum
    simp only [h0, finsum_zero]
  obtain ⟨τ₀, hτ₀⟩ := hτ
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator hreg
  rcases tri hL τ₀ with ⟨hm, hu⟩ | ⟨hm, hu⟩ | ⟨hu1, hu2⟩
  · have hx : (2 + τ₀) - 2 ^ 2 ∈ IsLocalRing.maximalIdeal O := by
      have e : (2 + τ₀) - 2 ^ 2 = τ₀ - 2 := by ring
      rw [e]
      exact hm
    obtain ⟨r, hr2, hrm⟩ := sqrtO O K Δ hL (2 + τ₀) 2 hL.two hx
    have hrK : (algebraMap O K) r ^ 2 = 2 + τ := by
      rw [← map_pow, hr2, map_add (f := _), map_ofNat, hτ₀]
    have hlam : QuadraticAlgebra.norm ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) = 2 + τ := by
      rw [QuadraticAlgebra.norm_algebraMap, hrK]
    have hD0 := datLam K Δ τ c hreg hc _ hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c _ hlam z hz m' hm'
    have hP := caseP O K Δ τ hL hreg r hrm hrK c hev j χ hj hχ a ha z hz
    let f : Kˣ → ℂ := fun y => lcount O c (dLam ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk]
    have hc2 : -2 * c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2K) hc
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hP ⟨Units.mk0 _ hc2, by rw [Units.val_mk0]⟩).1
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hm2 : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) = τ₀ + 2 := by push_cast; ring
      rw [e]
      exact hm
    obtain ⟨x, y, _, hsq, hn⟩ := rootEx O K Δ τ hL τ₀ (-1) hτ₀ hm2
    set u : Etau K τ := { re := (algebraMap O K) x, im := (algebraMap O K) y } with hu_def
    have hu2' : u ^ 2 = -ω := by
      rw [hsq]
      push_cast
      ring
    obtain ⟨ν, hνI, hνN⟩ := normEx O K Δ hL (-1)
    have hνN' : QuadraticAlgebra.norm ν = -1 := by
      rw [hνN]
      simp
    obtain ⟨ε, s, hs0, hΔ⟩ := hL.even
    have hΔ' : Δ * (s⁻¹) ^ 2 = (algebraMap O K) ↑ε := by
      rw [hΔ]
      field_simp
    obtain ⟨hdn, hform⟩ := datFormM O K Δ τ hL c u hu2' hn ν hνN' s⁻¹ (inv_ne_zero hs0)
    obtain ⟨m', hm'', hmove⟩ := dat_move hL hD hdn
    obtain ⟨t₁, rfl⟩ := hform m' hm''
    have hM := caseM O K Δ τ hL hreg τ₀ hτ₀ hm c hevc u hu2' hn ν hνI hνN' s⁻¹ ε hΔ'
    let g : Kˣ := t₁ * Units.mk0 _ hreg
    let f : Kˣ → ℂ := fun y => pcount O τ (y : K)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := by
      intro t ht x
      simp only [f, Units.val_mul]
      exact pNorm O K Δ τ hL t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g) := by
      intro k
      rw [hmove, ← smul_assoc, smul_smul, ← Units.val_mul, hM]
      simp only [f, g, Units.val_mul, Units.val_mk0, mul_assoc]
    rw [hshift f hf g hk]
    exact pStable O K Δ τ hL hreg j χ hj hχ a ha
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu2
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hU : (algebraMap O K) ↑(-(hu1.unit * hu2.unit)) = τ ^ 2 - 4 := by
      rw [Units.val_neg, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, map_neg, map_mul, map_add (f := _), map_sub,
        map_ofNat, hτ₀]
      ring
    obtain ⟨lam, hlamI, hlamN⟩ := normEx O K Δ hL hu1.unit
    have hlam : QuadraticAlgebra.norm lam = 2 + τ := by
      rw [hlamN, IsUnit.unit_spec, map_add (f := _), map_ofNat, hτ₀]
    have hD0 := datLam K Δ τ c hreg hc lam hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c lam hlam z hz m' hm'
    have hG := caseG O K Δ τ hL ⟨_, hU⟩ c hevc lam hlamI hlam z hz
    have hga := (gVals O K Δ τ hL hreg ⟨τ₀, hτ₀⟩ j χ hj hχ a ha z hz).2.1 ⟨_, hU⟩
    let f : Kˣ → ℂ := fun y => lcount O c (dLam lam z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk, hga]
    have h1 : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1 := by
      rw [Units.val_one]
      unfold hs
      rw [if_pos ⟨1, 0, by ring⟩]
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hG ⟨1, h1⟩).1
end

