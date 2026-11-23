module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.Descend2
section
namespace UpperTheory.V.Af.Rn

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

private theorem descend2 (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = -(W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    (j : ℕ) : ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x →
      ∃ x, x ≠ 0 ∧ (W x = (2 : ℂ) • x ∨ W x = 0) ∧ L x = 0 := by
  have lower_weight {y : V} {n : ℤ} (hy : W y = (n : ℂ) • y) :
      W (L y) = ((n - 2 : ℤ) : ℂ) • L y := by
    have h := congrArg (fun f : Module.End ℂ V => f y) hL
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply, hy, map_smul] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    push_cast
    module
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx hWx
  have hRL : R (L x) = (((-((j : ℤ) * ((j : ℤ) - 2)) : ℤ) : ℂ) / 4) • x := by
    have h := congrArg (fun f : Module.End ℂ V => f x) hC
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply,
      LinearMap.neg_apply, hWx, map_smul] at h
    calc
      R (L x) = (1 / 4 : ℂ) • ((4 : ℂ) • R (L x)) := by rw [smul_smul]; norm_num
      _ = _ := by rw [h]; push_cast; module
  have hLz : (j : ℤ) * ((j : ℤ) - 2) = 0 → L x = 0 := by
    intro hz
    rw [hz] at hRL
    simp only [neg_zero, Int.cast_zero, zero_div, zero_smul] at hRL
    apply h0
    rw [hH, hRL, map_zero, neg_zero]
  by_cases hLx : L x = 0
  · refine ⟨x, hx, ?_, hLx⟩
    rw [hLx, map_zero] at hRL
    have hc := (smul_eq_zero.1 hRL.symm).resolve_right hx
    have hz : (j : ℤ) * ((j : ℤ) - 2) = 0 := by
      have hc' := (div_eq_zero_iff.mp hc).resolve_right (by norm_num)
      exact neg_eq_zero.mp (Int.cast_eq_zero.mp hc')
    rcases mul_eq_zero.1 hz with h | h
    · right
      rw [hWx, h]
      simp
    · left
      rw [hWx]
      have : (j : ℤ) = 2 := by linarith
      rw [this]
      simp
  · rcases j with _ | _ | _ | j
    · exact absurd (hLz (by norm_num)) hLx
    · have hWx' : W x = x := by simpa using hWx
      have hLw : W (L x) = -L x := by
        have hw := lower_weight hWx
        norm_num at hw
        simpa using hw
      have hRL' : R (L x) = (1 / 4 : ℂ) • x := by
        norm_num at hRL ⊢
        exact hRL
      have h1 : H x (L x) = 0 := by
        have e := hW x (L x)
        rw [hWx', hLw, map_neg] at e
        linear_combination e / 2
      have h2 : H (L x) x = 0 := by
        have e := hW (L x) x
        rw [hLw, hWx', map_neg, LinearMap.neg_apply] at e
        linear_combination -e / 2
      have hdiag : H (L x) (L x) = -(1 / 4 : ℂ) * H x x := by
        simp only [hH, hRL', map_smul, smul_eq_mul, neg_mul]
      have hy : H (x + (2 : ℂ) • L x) (x + (2 : ℂ) • L x) = 0 := by
        simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, map_ofNat, h1, h2, hdiag]
        ring
      have hy0 := h0 _ hy
      have hsum : (2 : ℂ) • x = 0 := by
        calc
          (2 : ℂ) • x = W (x + (2 : ℂ) • L x) + (x + (2 : ℂ) • L x) := by
            rw [map_add, map_smul, hWx', hLw]
            module
          _ = 0 := by rw [hy0, map_zero, add_zero]
      exact (hx ((smul_eq_zero.1 hsum).resolve_left (by norm_num))).elim
    · exact absurd (hLz (by norm_num)) hLx
    · have hw := lower_weight hWx
      refine ih (j + 1) (by omega) (L x) hLx ?_
      rw [hw]
      push_cast
      ring_nf

end

end UpperTheory.V.Af.Rn

theorem UpperTheory.V.Af.Rn.sl2Two :
    UpperTheory.V.Af.Rn.Sl2Two := by
  intro V _ _ W R L H hWR hWL hRL hLR h0 hW hHR hHL hex
  obtain ⟨x, hx, n, hn⟩ := hex
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨y, hy, hWy, hLy⟩ := descend2 hWL hRL h0 hW hHL n.toNat x hx
      (by rw [hn, Int.toNat_of_nonneg hn0])
    rcases hWy with h | h
    · exact ⟨y, hy, Or.inl ⟨h, hLy⟩⟩
    · exact ⟨y, hy, Or.inr (Or.inr ⟨h, hLy⟩)⟩
  · have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, hWR, neg_smul]
    have hC' : (4 : ℂ) • (L * R) = -((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hLR, neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]
    obtain ⟨y, hy, hWy, hRy⟩ := descend2 hL' hC' h0 hW' hHR (-n).toNat x hx
      (by rw [LinearMap.neg_apply, hn, Int.toNat_of_nonneg (by omega)]; push_cast; rw [neg_smul])
    rcases hWy with h | h
    · refine ⟨y, hy, Or.inr (Or.inl ⟨?_, hRy⟩)⟩
      rw [LinearMap.neg_apply, neg_eq_iff_eq_neg] at h
      rw [h, neg_smul]
    · refine ⟨y, hy, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · rw [LinearMap.neg_apply, neg_eq_zero] at h
        exact h
      · rw [LinearMap.neg_apply, neg_eq_zero] at h
        have hR : R (L y) = 0 := by
          have := congrArg (fun T : Module.End ℂ V => T y) hRL
          simp only [LinearMap.smul_apply, mul_apply_eq_comp, LinearMap.neg_apply,
            LinearMap.sub_apply, h, map_zero, smul_zero, sub_zero, neg_zero] at this
          exact (smul_eq_zero.1 this).resolve_left (by norm_num)
        apply h0
        rw [hHL, hR, map_zero, neg_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.LowTwo
section
open Complex in
theorem UpperTheory.V.Af.Rn.lowTwo :
    UpperTheory.V.Af.Rn.Sl2Two → UpperTheory.V.Af.Rn.LowTwo := by
  intro hS V _ _ A B C J H hAB hAC hBC hCB h0 hHA hHB hHC hJ0 hJA hJB hJC hex
  obtain ⟨x, hx, n, hn⟩ := hex
  have h1 : (-(Complex.I • (B - C))) * (A + (Complex.I / 2) • (B + C))
      - (A + (Complex.I / 2) • (B + C)) * (-(Complex.I • (B - C)))
      = (2 : ℂ) • (A + (Complex.I / 2) • (B + C)) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h2 : (-(Complex.I • (B - C))) * (A - (Complex.I / 2) • (B + C))
      - (A - (Complex.I / 2) • (B + C)) * (-(Complex.I • (B - C)))
      = (-2 : ℂ) • (A - (Complex.I / 2) • (B + C)) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h3 : (4 : ℂ) • ((A + (Complex.I / 2) • (B + C)) * (A - (Complex.I / 2) • (B + C)))
      = -((-(Complex.I • (B - C))) * (-(Complex.I • (B - C))) - (2 : ℂ) • (-(Complex.I • (B - C)))) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC, hCB]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h4 : (4 : ℂ) • ((A - (Complex.I / 2) • (B + C)) * (A + (Complex.I / 2) • (B + C)))
      = -((-(Complex.I • (B - C))) * (-(Complex.I • (B - C))) + (2 : ℂ) • (-(Complex.I • (B - C)))) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC, hCB]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h5 : ∀ u v, H ((-(Complex.I • (B - C))) u) v = H u ((-(Complex.I • (B - C))) v) := by
    intro u v
    simp only [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, map_neg, map_smulₛₗ,
      map_sub, hHB, hHC, Complex.conj_I, smul_eq_mul, RingHom.id_apply]
    ring
  have h6 : ∀ u v, H ((A + (Complex.I / 2) • (B + C)) u) v = -H u ((A - (Complex.I / 2) • (B + C)) v) := by
    intro u v
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add (f := _), map_sub,
      map_smulₛₗ, hHA, hHB, hHC, map_div₀, Complex.conj_I, map_ofNat, smul_eq_mul, RingHom.id_apply]
    ring
  have h7 : ∀ u v, H ((A - (Complex.I / 2) • (B + C)) u) v = -H u ((A + (Complex.I / 2) • (B + C)) v) := by
    intro u v
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add (f := _), map_sub,
      map_smulₛₗ, hHA, hHB, hHC, map_div₀, Complex.conj_I, map_ofNat, smul_eq_mul, RingHom.id_apply]
    ring
  have h8 : (-(Complex.I • (B - C))) x = (n : ℂ) • x := by
    rw [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, hn, smul_smul, ← neg_smul]
    congr 1
    ring_nf
    simp [Complex.I_sq]
  obtain ⟨y, hy, hc⟩ := hS V _ _ _ H h1 h2 h3 h4 h0 h5 h6 h7 ⟨x, hx, n, h8⟩
  have eD : ∀ y, B y - C y = Complex.I • (-(Complex.I • (B - C))) y := by
    intro y
    rw [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]
  have eL : ∀ y, (A - (Complex.I / 2) • (B + C)) y = 0 → (2 : ℂ) • A y = Complex.I • (B y + C y) := by
    intro y h
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.add_apply] at h
    rw [h]
    module
  rcases hc with ⟨hW, hL⟩ | ⟨hW, hR⟩ | ⟨hW, hL⟩
  · refine ⟨y, hy, Or.inl ?_, eL y hL⟩
    rw [eD, hW]
    module
  · refine ⟨J y, fun h => hy (hJ0 y h), Or.inl ?_, ?_⟩
    · have e := eD y
      rw [hW] at e
      rw [hJB, hJC, show -J (B y) - -J (C y) = -J (B y - C y) by rw [map_sub]; abel, e, map_smul, map_smul]
      module
    · rw [LinearMap.add_apply, add_eq_zero_iff_eq_neg, LinearMap.smul_apply, LinearMap.add_apply] at hR
      rw [hJA, hJB, hJC, hR, map_neg, map_smul, map_add (f := _)]
      module
  · refine ⟨y, hy, Or.inr ?_, eL y hL⟩
    rw [eD, hW, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.NewHerm
section
open Polynomial UpperTheory.V UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped ComplexConjugate

private theorem quad_inj {a b c d : ℂ} (h : (X ^ 2 - C a * X + C b : ℂ[X]) = X ^ 2 - C c * X + C d) : a = c ∧ b = d := by
  have h0 := congrArg (Polynomial.eval 0) h
  have h1 := congrArg (Polynomial.eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h0 h1
  constructor
  · linear_combination h0 - h1
  · linear_combination h0

theorem UpperTheory.V.Af.Rn.newHerm :
    UpperTheory.V.Published.NewformRep → UpperTheory.V.Af.Rn.UnitTw → UpperTheory.V.Af.Rn.HermOf → UpperTheory.V.Af.Rn.SatHerm → UpperTheory.V.Af.Rn.NewHerm := by
  intro hN hT hO hS k hk f w hw
  obtain ⟨π, hi, hs⟩ := hN k hk f 0
  obtain ⟨π₀, hi₀, ht⟩ := hT k (by omega) 0 π hi
  obtain ⟨H, hH⟩ := hO _ π₀ hi₀
  obtain ⟨B, hB, e⟩ := hs w hw
  obtain ⟨t, h5, h6⟩ := ht w
  obtain ⟨γ, δ, rfl⟩ := Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)
  obtain ⟨α, rfl⟩ : ∃ α, γ = α * t := ⟨γ * t⁻¹, by simp⟩
  obtain ⟨β, rfl⟩ : ∃ β, δ = β * t := ⟨δ * t⁻¹, by simp⟩
  have h0 : π₀.HasSat w {α, β} := (h5 _).2 (by simpa using hB)
  have h1 := hS π₀ H hH w α β h0
  rw [h6, Newform.heckePoly] at e
  obtain ⟨h2, h3⟩ := quad_inj e
  have hp : (normV w : ℂ) ^ (k - 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (UpperTheory.V.Af.Nf.places w).1.ne_zero)
  rw [← h2, ← mul_right_cancel₀ hp h3, map_mul, Complex.conj_ofReal, mul_assoc, h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.PolyInj
section
open Polynomial in
theorem UpperTheory.V.Af.Rn.polyInj :
    UpperTheory.V.Af.Rn.PolyInj := by
  intro q hq j B B' h
  have key : ∀ s : Multiset ℂ,
      (Multiset.map (fun b ↦ Polynomial.X - Polynomial.C ((q : ℂ) ^ j * b)) s).prod.roots
        = s.map (fun b ↦ (q : ℂ) ^ j * b) := by
    intro s
    rw [← Polynomial.roots_multiset_prod_X_sub_C (s.map (fun b ↦ (q : ℂ) ^ j * b)), Multiset.map_map]
    rfl
  have hroots := congrArg Polynomial.roots h
  rw [key, key] at hroots
  have hqC : ((q : ℂ) ^ j) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hq.ne')
  have h1 := Multiset.map_injective (mul_right_injective₀ hqC) hroots
  unfold UpperTheory.V.Af.algSat at h1
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, ← Multiset.map_map] at h1
  refine Multiset.map_injective (fun _ _ e ↦ Units.ext e) (Multiset.map_injective (mul_right_injective₀ ?_) h1)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  first
    | exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hq' _).ne'
    | simp [hq.ne']
    | exact_mod_cast (Real.rpow_pos_of_pos hq' _).ne'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.SatHerm
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.TR UpperTheory.V.Sd UpperTheory.V.Af.Gk GlobalTheory.LFun

theorem UpperTheory.V.Af.Rn.satHerm :
    UpperTheory.V.Af.Rn.SatHerm := by
  intro π H hH w α β hB
  have hB0 : HasSatGL w (π.locRep w) {α, β} := hB
  have hK : ∀ k ∈ KGL w (n := 2), GlobalTheory.CuspRep.invT 2 _ k ∈ KGL w (n := 2) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT 2 _ k, InvT.map_invT _ k⟩
  have hB' : HasSatGL w ((π.locRep w).comp (GlobalTheory.CuspRep.invT 2 (w.adicCompletion ℚ))) (({α, β} : Multiset ℂˣ).map (·⁻¹)) :=
    InvT.hasSatGL_invT (ρ := π.locRep w) (LinearEquiv.refl ℂ π.V) (fun _ _ => rfl) hB0
  obtain ⟨x, hx'⟩ := hB0.exists_vec
  have hx := hx'.2.1
  have h0 := hx'.1
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have h2 := hB'.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix _ (hK k hk)) h0
  have hϖ := unif_spec w
  have e := heckeAdj ℚ 2 w π.V (π.locRep w) H (fun g => hH.fin (GlobalTheory.CuspRep.locGL ℚ 2 w g)) x hx _ hϖ 1
  rw [hx'.2.2.2 _ hϖ 1 (by norm_num), h2.2.2.2 _ hϖ 1 (by norm_num), H.map_smulₛₗ, (H x).map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul] at e
  have e' := mul_right_cancel₀ (fun h => h0 (hH.definite x h)) e
  have hq : 0 < Formalism.UG.qV ℚ w := Nat.pos_of_ne_zero (qV_ne_zero w)
  have hc : ∀ B, satEig (Formalism.UG.qV ℚ w) 2 B 1 =
      ((((Formalism.UG.qV ℚ w : ℝ) ^ (1 / 2 : ℝ) : ℝ)) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm 1 := fun B => by
    rw [Complex.ofReal_cpow (by positivity), satEig]
    norm_num
  have hne : ((((Formalism.UG.qV ℚ w : ℝ) ^ (1 / 2 : ℝ) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  rw [hc, hc, map_mul, Complex.conj_ofReal] at e'
  have e'' := mul_left_cancel₀ hne e'
  have e3 : (starRingEnd ℂ) ((α : ℂ) + β) = (α : ℂ)⁻¹ + (β : ℂ)⁻¹ := by
    simpa [Multiset.esymm, Multiset.powersetCard_one, add_comm] using e''
  rw [e3, Units.val_mul]
  field_simp
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.UnitTw
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Rn.unitTw :
    UpperTheory.V.Af.Rn.UnitTw := by
  intro k hk1 j π hπ
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow ℚ (-s)
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ (-s)
  have hi : ∀ v, (π.twist χ).HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)} := fun v => by
    have := (hπ v).twist χ
    rw [absExpo ℚ (-s) v] at this
    convert this using 1
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]
    exact congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)
  refine ⟨π.twist χ, hi, fun w => ⟨(χ⁻¹).val w, fun B => ?_, fun α β => ?_⟩⟩
  · have hu0 : χ.UnrAt w := fun u hu => hE.1 w u hu
    have hu : (χ⁻¹).UnrAt w := fun u hu => by
      have := hE.1 w u hu
      exact inv_eq_one.2 this
    constructor
    · intro hsat
      have h3 := hsat.twist hu
      rwa [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one] at h3
    · intro hsat
      have h3 := hsat.twist hu0
      have e : (χ⁻¹).val w = (χ.val w)⁻¹ := rfl
      rw [Multiset.map_map, e] at h3
      simpa using h3
  have hp := (places w).1
  have hq := (places w).2.2.1
  have hq0 : (0 : ℝ) < normV w := by exact_mod_cast hp.pos
  have hval0 : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-(-s)) : ℝ) : ℂ) := by
    rw [hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]; simp
  have hval : (((χ⁻¹).val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ) := by
    have e : (χ⁻¹).val w = (χ.val w)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, hval0, ← Complex.ofReal_inv, ← Real.rpow_neg hq0.le, neg_neg]
  set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
  have key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * (χ⁻¹).val w : ℂˣ) : ℂ)) =
      r * a := fun a => by
    have : ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
        (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 1
      rw [hs]; push_cast; ring
    rw [hr, this, Units.val_mul, hval]; push_cast; ring
  have hrr : r * r = (normV w : ℂ) ^ (k - 1) := by
    rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
    push_cast; rfl
  simp only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind,
    Multiset.singleton_add, key]
  rw [← hrr]
  simp only [Units.val_mul, C_mul, C_add]
  ring
end

