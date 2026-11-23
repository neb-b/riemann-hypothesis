module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatIso
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.datIso : UpperTheory.V.Z.Sym.Loc.DatIso := by
  intro O K _ _ _ Δ τ c d m y
  constructor
  · unfold lcount
    letI := torAct Δ τ
    refine wTrans _ _ _ (Cint O τ) _ _ (fun S S' => S = ⇑(mulE (O := O) y) '' S') ?_ ?_ ?_ ?_ ?_ ?_
    · intro t S
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_tor (O := O) c d m t S).mp h1) h2
      · exact absurd ((isFix_tor (O := O) c d m t S).mpr h3) h1
      · rfl
    · intro t S
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_tor (O := O) c _ _ t S).mp h1) h2
      · exact absurd ((isFix_tor (O := O) c _ _ t S).mpr h3) h1
      · rfl
    · intro t S S' h
      show tor Δ t '' S = ⇑(mulE (O := O) y) '' (tor Δ t '' S')
      subst h
      rw [Set.image_image, Set.image_image]
      congr 1
      funext x
      refine Prod.ext rfl ?_
      change ofE Δ (quo t) * ((y : EL Δ τ) * x.2) = (y : EL Δ τ) * (ofE Δ (quo t) * x.2)
      ring
    · intro S S' h
      subst h
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_mulE (O := O) c d m y S').mp h1) h2
      · exact absurd ((isFix_mulE (O := O) c d m y S').mpr h3) h1
      · rfl
    · intro S _
      refine ⟨(mulE (O := O) y).symm '' S, ?_, fun S' h => ?_⟩
      · show S = ⇑(mulE (O := O) y) '' ((mulE (O := O) y).symm '' S)
        rw [Set.image_image]
        simp
      · subst h
        rw [Set.image_image]
        simp
    · intro S' _
      exact ⟨⇑(mulE (O := O) y) '' S', rfl, fun S h => h⟩
  · intro h
    obtain ⟨hreg, hc, hd, hmu, hms, hmsig⟩ := h
    have e1 : (↑y : EL Δ τ) * ↑y⁻¹ = 1 := Units.mul_inv y
    have e2 : sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y = 1 := by
      rw [← sigL_mul, Units.inv_mul, sigL_one]
    have e3 : star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹) = 1 := by
      rw [← star_mul, e2, star_one]
    refine ⟨hreg, hc, ?_, ?_, ?_, ?_⟩
    · simp only [sigL_mul, sigL_sigL]
      linear_combination hd + (d * sigL d) * (sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y) * e1 + (d * sigL d) * e2
    · exact (hmu.mul y.isUnit).mul ⟨⟨_, _, e3, by rw [mul_comm, e3]⟩, rfl⟩
    · simp only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hms]
      ring
    · simp only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hmsig]
      linear_combination (-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ)) * (star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹))) * e1 + (-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ))) * e3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPMul
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem fixP_mul {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (y : (Etau K τ)ˣ) (x : K) (S : Set (Etau K τ))
    (h : IsFixP O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) S) : IsFixP O τ x (((y : Etau K τ) * ·) '' S) := by
  obtain ⟨hfg, hdual, hstab⟩ := h
  have hmem : ∀ z, z ∈ ((y : Etau K τ) * ·) '' S ↔ (↑y⁻¹ : Etau K τ) * z ∈ S := by
    intro z
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hz
      exact ⟨_, hz, by simp⟩
  have hy : (y : Etau K τ)
      = algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) * star (↑y⁻¹ : Etau K τ) := by
    rw [algebraMap_norm_eq_mul_star, mul_assoc, ← star_mul, Units.inv_mul, star_one, mul_one]
  have key : ∀ a z : Etau K τ, x * ((y : Etau K τ) * a * star z).im
      = QuadraticAlgebra.norm (y : Etau K τ) * x * (a * star ((↑y⁻¹ : Etau K τ) * z)).im := by
    intro a z
    have e : (y : Etau K τ) * a * star z
        = algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) * (a * star ((↑y⁻¹ : Etau K τ) * z)) := by
      conv_lhs => rw [hy]
      rw [star_mul]
      ring
    rw [e]
    simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := hfg
    classical
    refine ⟨s.image ((y : Etau K τ) * ·), ?_⟩
    rw [Finset.coe_image]
    change ⇑(LinearMap.mulLeft O (y : Etau K τ)) '' _
      = ↑(Submodule.span O (⇑(LinearMap.mulLeft O (y : Etau K τ)) '' _))
    rw [← Submodule.map_coe, Submodule.map_span]
  · intro z
    rw [hmem, hdual]
    constructor
    · rintro H _ ⟨a, ha, rfl⟩
      have := H a ha
      rw [key]
      exact this
    · intro H a ha
      have := H (↑y * a) ⟨a, ha, rfl⟩
      rw [key] at this
      exact this
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨ω * a, hstab a ha, mul_left_comm _ _ _⟩

private theorem fixP_iff {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (y : (Etau K τ)ˣ) (x : K) (S : Set (Etau K τ)) :
    IsFixP O τ x (((y : Etau K τ) * ·) '' S) ↔ IsFixP O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) S := by
  refine ⟨fun h => ?_, fixP_mul y x S⟩
  have := fixP_mul y⁻¹ (QuadraticAlgebra.norm (y : Etau K τ) * x) (((y : Etau K τ) * ·) '' S) (by rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
  simpa [← Set.image_comp, Function.comp_def] using this

theorem UpperTheory.V.Z.Sym.Loc.pNorm : UpperTheory.V.Z.Sym.Loc.PNorm := by
  intro O K _ _ _ _ _ Δ τ hL t ht x
  obtain ⟨y, rfl⟩ := ht
  show pcount O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) = pcount O τ x
  unfold pcount
  letI := quoAct (K := K) τ
  have inv : ∀ (z : (Etau K τ)ˣ) (r : K) (S : Set (Etau K τ)),
      IsFixP O τ r ((quo z * ·) '' S) ↔ IsFixP O τ r S := by
    intro z r S
    have hq : QuadraticAlgebra.norm (quo z) = 1 := by
      rw [quo, map_mul, QuadraticAlgebra.norm_star, ← map_mul, Units.mul_inv, map_one]
    let u : (Etau K τ)ˣ := ⟨quo z, star (quo z), quo_mul_star z, by rw [mul_comm]; exact quo_mul_star z⟩
    have := fixP_iff (O := O) u r S
    rwa [show QuadraticAlgebra.norm (u : Etau K τ) = 1 from hq, one_mul] at this
  refine wTrans _ _ _ (Cint O τ) _ _ (fun S S' => S' = ((y : Etau K τ) * ·) '' S) ?_ ?_ ?_ ?_ ?_ ?_
  · intro z S
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd ((inv z _ S).mp h1) h2
    · exact absurd ((inv z _ S).mpr h3) h1
    · rfl
  · intro z S
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd ((inv z _ S).mp h1) h2
    · exact absurd ((inv z _ S).mpr h3) h1
    · rfl
  · intro z S S' h
    subst h
    show (quo z * ·) '' (((y : Etau K τ) * ·) '' S) = ((y : Etau K τ) * ·) '' ((quo z * ·) '' S)
    rw [Set.image_image, Set.image_image]
    congr 1
    funext a
    ring
  · intro S S' h
    subst h
    have e := fixP_iff (O := O) y x S
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd (e.mpr h1) h2
    · exact absurd (e.mp h3) h1
    · rfl
  · intro S _
    exact ⟨_, rfl, fun _ h => h⟩
  · intro S' _
    refine ⟨((↑y⁻¹ : Etau K τ) * ·) '' S', ?_, fun S h => ?_⟩
    · show S' = ((y : Etau K τ) * ·) '' (((↑y⁻¹ : Etau K τ) * ·) '' S')
      rw [Set.image_image]
      simp
    · subst h
      rw [Set.image_image]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GOdd
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.gOdd : UpperTheory.V.Z.Sym.Loc.GOdd := by
  intro O K _ _ _ _ _ Δ τ L j χ z _ hj h
  by_contra h'
  obtain ⟨s, u, t, h1, -⟩ := exists_of_gOrb_ne hj h'
  exact h ⟨u, s, s.ne_zero, h1⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVanish
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.gVanish : UpperTheory.V.Z.Sym.Loc.GVanish := by
  intro O K _ _ _ _ _ Δ τ hL j hj χ z hz hne
  haveI := hL.frac
  obtain ⟨s, u, t, hn, ht⟩ := exists_of_gOrb_ne (O := O) hj hne
  have hu : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1 := by
    rw [← map_mul]
    simp
  rcases hz with h | h
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have h2 : (s : K) ^ 2 = algebraMap O K ↑u⁻¹ := by
      calc (s : K) ^ 2 = algebraMap O K ↑u⁻¹ * (algebraMap O K ↑u * s ^ 2) := by
            rw [← mul_assoc, hu, one_mul]
        _ = _ := by rw [← hn, mul_one]
    have hi : IsIntegral O (s : K) :=
      IsIntegral.of_pow two_pos (h2 ▸ isIntegral_algebraMap)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨y * t, by rw [map_mul, hy, ht]⟩
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have e : algebraMap O K t = algebraMap O K ↑u * s := by
      apply mul_left_cancel₀ s.ne_zero
      linear_combination hn - ht
    have hs : (s : K) = algebraMap O K (↑u⁻¹ * t) := by
      rw [map_mul, e, ← mul_assoc, hu, one_mul]
    refine ⟨↑u⁻¹ * t * t - 2, ?_⟩
    rw [map_sub, map_mul, ← hs, map_ofNat]
    linear_combination -ht
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.H90
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem UpperTheory.V.Z.Sym.Loc.one_eq_zero_of_products_vanish {A : Type} [CommRing A] (b c d e w u v : A)
    (hbc : b * c = 1) (hde : d * e = 1) (hwu : w * u = 1) (h2v : 2 * v = 1)
    (E1 : (1 + c) * (1 + b) * (1 + e) * (1 + d) = 0)
    (E2 : (w * (1 - c)) * (-w * (1 - b)) * ((1 - e) * w) * ((1 - d) * -w) = 0)
    (E3 : (1 + c + w * (1 - c)) * (1 + b + -w * (1 - b)) * (1 + e + (1 - e) * w)
      * (1 + d + (1 - d) * -w) = 0)
    (E4 : (1 + c - w * (1 - c)) * (1 + b - -w * (1 - b)) * (1 + e - (1 - e) * w)
      * (1 + d - (1 - d) * -w) = 0) :
    (1 : A) = 0 := by
  have s1 : (2 + (b + c)) * (2 + (d + e)) = 0 := by
    linear_combination E1 - (2 + (d + e) + (d * e - 1)) * hbc - (2 + (b + c)) * hde
  have t2 : (1 - c) * (1 - b) * (1 - e) * (1 - d) = 0 := by
    linear_combination u ^ 4 * E2
      - (1 - c) * (1 - b) * (1 - e) * (1 - d) * (w * u + 1) * (w ^ 2 * u ^ 2 + 1) * hwu
  have s2 : (2 - (b + c)) * (2 - (d + e)) = 0 := by
    linear_combination t2 - (2 - (d + e) + (d * e - 1)) * hbc - (2 - (b + c)) * hde
  have s3 : (b + c) + (d + e) = 0 := by
    linear_combination v ^ 2 * (s1 - s2) - ((b + c) + (d + e)) * (2 * v + 1) * h2v
  have s4 : (b + c) * (d + e) + 4 = 0 := by
    linear_combination v * (s1 + s2) - ((b + c) * (d + e) + 4) * h2v
  have t3 : (2 + (b + c) - w ^ 2 * (2 - (b + c)) + 2 * (w * (b - c)))
      * (2 + (d + e) - w ^ 2 * (2 - (d + e)) + 2 * (w * (d - e))) = 0 := by
    linear_combination E3
      - (1 - w ^ 2) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) + 2 * (w * (d - e))
        + (d * e - 1) * (1 - w ^ 2)) * hbc
      - (1 - w ^ 2) * (2 + (b + c) - w ^ 2 * (2 - (b + c)) + 2 * (w * (b - c))) * hde
  have t4 : (2 + (b + c) - w ^ 2 * (2 - (b + c)) - 2 * (w * (b - c)))
      * (2 + (d + e) - w ^ 2 * (2 - (d + e)) - 2 * (w * (d - e))) = 0 := by
    linear_combination E4
      - (1 - w ^ 2) * (2 + (d + e) - w ^ 2 * (2 - (d + e)) - 2 * (w * (d - e))
        + (d * e - 1) * (1 - w ^ 2)) * hbc
      - (1 - w ^ 2) * (2 + (b + c) - w ^ 2 * (2 - (b + c)) - 2 * (w * (b - c))) * hde
  have t5 : 8 * (w * (b - c) * (w * (d - e))) - 32 * w ^ 2 = 0 := by
    linear_combination t3 + t4 - 2 * (1 + w ^ 2) ^ 2 * s4 - 4 * (1 - w ^ 4) * s3
  have t6 : (w * (b - c) * (w * (d - e))) ^ 2 = 0 := by
    linear_combination w ^ 4 * (2 - (b + c)) * (2 - (d + e)) * s1
      - 4 * w ^ 4 * ((d + e) ^ 2 - 4 - 4 * (d * e - 1)) * hbc
      - 4 * w ^ 4 * ((b + c) ^ 2 - 4) * hde
  have t7 : 1024 * w ^ 4 = 0 := by
    linear_combination 64 * t6 - (8 * (w * (b - c) * (w * (d - e))) + 32 * w ^ 2) * t5
  linear_combination v ^ 10 * u ^ 4 * t7
    - (w * u) ^ 4 * (1 + 2 * v + (2 * v) ^ 2 + (2 * v) ^ 3 + (2 * v) ^ 4 + (2 * v) ^ 5
      + (2 * v) ^ 6 + (2 * v) ^ 7 + (2 * v) ^ 8 + (2 * v) ^ 9) * h2v
    - ((w * u) ^ 3 + (w * u) ^ 2 + w * u + 1) * hwu

theorem UpperTheory.V.Z.Sym.Loc.h90 : UpperTheory.V.Z.Sym.Loc.H90 := by
  intro O K _ _ _ _ _ Δ τ hL hτ β hβ
  have h2 : (2 : K) ≠ 0 := by
    have := (hL.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨u0, s, hs, hΔeq⟩ := hL.even
  have hΔ : Δ ≠ 0 := by
    rw [hΔeq]
    exact mul_ne_zero (u0.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  let w : EL Δ τ := ⟨⟨0, 1⟩, 0⟩
  have hsw : sigL w = -w := by ext <;> simp [w, sigL]
  have hstw : star w = w := by ext <;> simp [w]
  let u : EL Δ τ := ⟨⟨0, Δ⁻¹⟩, 0⟩
  have hwu : w * u = 1 := by ext <;> simp [w, u, hΔ]
  let v : EL Δ τ := ⟨⟨2⁻¹, 0⟩, 0⟩
  have h2v : 2 * v = 1 := by ext <;> simp [v, h2]
  have sadd : ∀ x y : EL Δ τ, sigL (x + y) = sigL x + sigL y := by
    intro x y
    ext <;> simp [sigL]
  have ssub : ∀ x y : EL Δ τ, sigL (x - y) = sigL x - sigL y := by
    intro x y
    ext <;> simp [sigL]
  have hne : (1 : EL Δ τ) ≠ 0 := fun h => by
    have := congrArg (fun z => z.re.re) h
    simp at this
  have dich : ∀ x : EL Δ τ, sigL x = x → star x = x → IsUnit x ∨ x = 0 := by
    rintro ⟨⟨r1, r2⟩, ⟨r3, r4⟩⟩ hs' ht
    have a := congrArg (fun z => z.re.im) hs'
    have c := congrArg (fun z => z.im.re) ht
    have d := congrArg (fun z => z.im.im) ht
    simp [sigL] at a c d
    have z2 : r2 = 0 := by
      have h : (2 : K) * r2 = 0 := by linear_combination -a
      exact (mul_eq_zero.mp h).resolve_left h2
    have z3 : r3 = 0 := by
      have h : (2 : K) * r3 = 0 := by linear_combination -c
      exact (mul_eq_zero.mp h).resolve_left h2
    have z4 : r4 = 0 := by
      have h : (2 : K) * r4 = 0 := by linear_combination -d
      exact (mul_eq_zero.mp h).resolve_left h2
    subst z2 z3 z4
    by_cases hr : r1 = 0
    · right
      subst hr
      ext <;> simp
    · left
      refine isUnit_iff_exists_inv.mpr ⟨⟨⟨r1⁻¹, 0⟩, 0⟩, ?_⟩
      ext <;> simp [hr]
  let M : EL Δ τ → EL Δ τ := fun z => z * sigL z * star z * star (sigL z)
  have fixσ : ∀ z, sigL (M z) = M z := by
    intro z
    simp only [M, sigL_mul, sigL_sigL, sigL_star]
    ring
  have fixs : ∀ z, star (M z) = M z := by
    intro z
    simp only [M, star_mul, star_star]
    ring
  have key : ∀ z : EL Δ τ, sigL z = β * z → IsUnit (M z) →
      ∃ y : (EL Δ τ)ˣ, sigL (y : EL Δ τ) = β * (y : EL Δ τ) := by
    intro z hz hM
    have hu : IsUnit z := by
      have e : M z = z * (sigL z * star z * star (sigL z)) := by
        simp only [M]
        ring
      rw [e] at hM
      exact isUnit_of_mul_isUnit_left hM
    exact ⟨hu.unit, by rw [hu.unit_spec]; exact hz⟩
  let y1 : EL Δ τ := 1 + sigL β
  let y2 : EL Δ τ := w * (1 - sigL β)
  have g1 : sigL y1 = β * y1 := by
    simp only [y1, sadd, sigL_one, sigL_sigL]
    linear_combination -hβ
  have g2 : sigL y2 = β * y2 := by
    simp only [y2, sigL_mul, ssub, sigL_one, sigL_sigL, hsw]
    linear_combination w * hβ
  have g3 : sigL (y1 + y2) = β * (y1 + y2) := by
    rw [sadd, g1, g2]
    ring
  have g4 : sigL (y1 - y2) = β * (y1 - y2) := by
    rw [ssub, g1, g2]
    ring
  rcases dich (M y1) (fixσ _) (fixs _) with h | h1
  · exact key _ g1 h
  rcases dich (M y2) (fixσ _) (fixs _) with h | h2'
  · exact key _ g2 h
  rcases dich (M (y1 + y2)) (fixσ _) (fixs _) with h | h3
  · exact key _ g3 h
  rcases dich (M (y1 - y2)) (fixσ _) (fixs _) with h | h4
  · exact key _ g4 h
  exfalso
  apply hne
  refine UpperTheory.V.Z.Sym.Loc.one_eq_zero_of_products_vanish β (sigL β) (star β) (star (sigL β)) w u v hβ ?_ hwu h2v ?_ ?_ ?_ ?_
  · have h := congrArg star hβ
    simp only [star_mul, star_one] at h
    linear_combination h
  · rw [← h1]
    simp only [M, y1, sadd, sigL_one, sigL_sigL, star_add, star_one]
  · rw [← h2']
    simp only [M, y2, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_mul, star_sub, star_one,
      star_neg, hstw]
  · rw [← h3]
    simp only [M, y1, y2, sadd, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_add, star_mul,
      star_sub, star_one, star_neg, hstw]
  · rw [← h4]
    simp only [M, y1, y2, sadd, sigL_mul, ssub, sigL_one, sigL_sigL, hsw, star_add, star_mul,
      star_sub, star_one, star_neg, hstw]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.normEx : UpperTheory.V.Z.Sym.Loc.NormEx := by
  intro O K _ _ _ _ _ Δ L u
  obtain ⟨ε, s, hs, e⟩ := L.even
  obtain ⟨a, b, h⟩ := L.nm_unit ε u
  have h' : algebraMap O K a ^ 2 - algebraMap O K ε * algebraMap O K b ^ 2 = algebraMap O K u := by
    rw [← h]; simp
  refine ⟨⟨algebraMap O K a, algebraMap O K b / s⟩, ?_, ?_⟩
  · have e1 : (⟨algebraMap O K a, algebraMap O K b / s⟩ : Lsq K Δ) = algebraMap O _ a + algebraMap O _ b * ⟨0, 1 / s⟩ := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ), IsScalarTower.algebraMap_apply O K (Lsq K Δ) b]
      ext <;> simp [div_eq_mul_inv]
    rw [e1]
    refine isIntegral_algebraMap.add (isIntegral_algebraMap.mul (IsIntegral.of_pow (n := 2) (by norm_num) ?_))
    have : (⟨0, 1 / s⟩ : Lsq K Δ) ^ 2 = algebraMap O _ (ε : O) := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
      ext <;> simp [sq]
      rw [e]; field_simp
    rw [this]; exact isIntegral_algebraMap
  · rw [QuadraticAlgebra.norm_def, ← h']
    simp only
    rw [e]; field_simp; ring
end

