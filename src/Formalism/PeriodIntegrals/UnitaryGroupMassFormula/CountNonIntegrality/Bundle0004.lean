module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseAlgebraMap
section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_coeF (D : Formalism.BasicNotions.D7) (t : D.host.F) : star (t : D.host.E) = t := by
  haveI := D.host.isCMField_hostE
  first
  | exact (NumberField.IsCMField.complexConj_eq_self_iff _).mpr t.2
  | exact (NumberField.IsCMField.complexConj_eq_self_iff (K := D.host.E) (t : D.host.E)).mpr t.2
  | exact NumberField.IsCMField.complexConj_apply_of_mem_maximalRealSubfield t.2
  | exact NumberField.IsCMField.complexConj_apply_eq_self_of_mem t.2
  | exact (NumberField.IsCMField.star_eq_self_iff _).mpr t.2
  | exact (NumberField.IsCMField.mem_maximalRealSubfield_iff_star_eq _).mp t.2
  | exact (NumberField.IsCMField.complexConj D.host.E).commutes t

theorem resChar_mem' (D : Formalism.BasicNotions.D7) (p : PlF D) : ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  first
  | exact ringChar.Nat.cast_ringChar
  | (unfold Loc.resChar; exact ringChar.Nat.cast_ringChar)

theorem val_resChar_lt (D : Formalism.BasicNotions.D7) (p : PlF D) :
    valuation (D.s.atP p).Fp (((Loc.resChar p : ℕ) : (D.s.atP p).Fp)) < 1 := by
  have hmem := resChar_mem' D p
  have h1 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) =
      (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F) := (map_natCast _ _).symm
  rw [h1]
  have hv : p.valuation D.host.F ((Loc.resChar p : ℕ) : D.host.F) < 1 := by
    have := (p.valuation_lt_one_iff_mem (K := D.host.F) ((Loc.resChar p : ℕ) : 𝓞 D.host.F)).mpr hmem
    simpa using this
  have hnot : ¬ ((D.s.atP p).ιF 1 ≤ᵥ (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F)) := by
    rw [(D.s.atP p).val, map_one]
    exact not_le.mpr hv
  rw [map_one] at hnot
  rw [← not_le, ← map_one (valuation (D.s.atP p).Fp)]
  first
  | exact fun h => hnot ((Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)
  | exact fun h => hnot ((Valuation.Compatible.rel_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)
  | exact fun h => hnot (ValuativeRel.valuation_le_valuation.mp h)
  | exact fun h => hnot ((ValuativeRel.valuation_le_valuation_iff _ _).mp h)
  | simpa using hnot
  | simpa [ValuativeRel.valuation_le_valuation] using hnot

theorem locDiff_of (hT : TrDual) (hA : DualApprox) (hS : PowSmall) : LocDiff := by
  intro D δ M hag p
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).ellPrime
  have hδ : δ p ≠ 0 := (hag p).2.1
  have hz := hT D δ M hag p
  obtain ⟨k, hk⟩ := hS (D.s.atP p).Fp (δ p) ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) (val_resChar_lt D p)
  obtain ⟨t, htr, μ, hμ, hι⟩ := hA D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont (D.s.atP p).qlFin
    (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val (δ p)⁻¹ hz k
  refine ⟨t, htr, ?_⟩
  have he : δ p * (D.s.atP p).ιF t =
      1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ := by
    rw [hι, mul_add, mul_inv_cancel₀ hδ]
    ring
  have hμ' : valuation (D.s.atP p).Fp μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
  have hwv : valuation (D.s.atP p).Fp (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hμ') hk
  have h1 : valuation (D.s.atP p).Fp (1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h2 := congrArg (valuation (D.s.atP p).Fp) h0
    rw [h1, map_zero] at h2
    exact one_ne_zero h2
  · exact (Valuation.mem_integer_iff _ _).mpr (le_of_eq h1)
  · exact (Valuation.mem_integer_iff _ _).mpr (by rw [map_inv₀, h1, inv_one])

theorem unitAt_mul_natCast (D : Formalism.BasicNotions.D7) (p : PlF D) : ∃ n : ℕ, (uP p : ℚ) * n = 1 := by
  have h0 : (D.host.g 0 : ℚ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have h1 : (D.host.g 1 : ℚ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  unfold uP gpart Lat.gS
  split_ifs with ha hb
  · refine ⟨D.host.g 1, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)
  · refine ⟨D.host.g 0, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)
  · refine ⟨D.host.g 0 * D.host.g 1, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)

theorem algMap_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c =
      algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨c, hc⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

theorem locGen_of (hD : LocDiff) (hP : DualPow) : LocGen := by
  intro D δ M hag p m
  obtain ⟨t, htr, hu0, -, hinv⟩ := hD D δ M hag p
  obtain ⟨n, hn⟩ := unitAt_mul_natCast D p
  have hx : ((t : D.host.E) * (n : D.host.E)) ^ m ∈
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [mul_pow]
    have h := Submodule.smul_mem
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E).coeToSubmodule
      ((n : 𝓞 D.host.E) ^ m) (hP D t htr m)
    rw [Algebra.smul_def] at h
    simpa [mul_comm] using h
  have hstar : star (((t : D.host.E) * (n : D.host.E)) ^ m) = ((t : D.host.E) * (n : D.host.E)) ^ m := by
    rw [star_pow, star_mul', star_coeF D t, star_natCast]
  have hnE : ((uP p : ℚ) : D.host.E) * (n : D.host.E) = 1 := by
    have h := congrArg (fun q : ℚ => (q : D.host.E)) hn
    simpa using h
  have ha : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (t : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t) := by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
      (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) = _
    rw [(D.s.atP p).compat t, ← map_mul]
  have key : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
      ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) = 1 := by
    have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
        ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) =
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (t : D.host.E)) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
        ((D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) := by ring
    rw [e1, ha, ← map_mul (D.s.atP p).ιE, hnE, map_one, mul_one, ← map_mul, mul_inv_cancel₀ hu0, map_one]
  have alg : ∀ (R : Type) [CommRing R] (a b c d e : R), a * b * c * (d * e) = 1 →
      (a * b) ^ m * (c ^ m * (d * e) ^ m) = 1 := by
    intro R _ a b c d e h
    calc (a * b) ^ m * (c ^ m * (d * e) ^ m) = (a * b * c * (d * e)) ^ m := by ring
      _ = 1 := by rw [h, one_pow]
  have hprod : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ m *
      ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m *
        (D.s.atP p).ιE (((t : D.host.E) * (n : D.host.E)) ^ m)) = 1 := by
    rw [map_pow, map_mul]
    exact alg _ _ _ _ _ _ key
  refine ⟨((t : D.host.E) * (n : D.host.E)) ^ m, hx, hstar,
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m,
    Subring.pow_mem _ (algMap_mem_O D p _ hinv) m, ?_⟩
  exact Ring.inverse_unit ⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩

end PI.CntNotIntW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.TrDual
section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_trOne (D : Formalism.BasicNotions.D7) : ∃ x : D.host.E, IsIntegral ℤ x ∧ x + D.host.conj x = 1 := by
  have hc := Formalism.BasicNotions.Examples₂.conj_bE (H := D.host)
  refine ⟨(1 + D.host.sqd) / 2, Formalism.BasicNotions.Examples₂.isIntegral_halfB (H := D.host), ?_⟩
  first
    | (rw [Formalism.BasicNotions.Examples₂.conj_half (H := D.host), hc]; ring)
    | (rw [map_div₀, map_add (f := _), map_one, hc, map_ofNat]; ring)

theorem trace_iE_eq_one (D : Formalism.BasicNotions.D7) (p : PlF D) (x : D.host.E) (hx1 : x + D.host.conj x = 1) :
    Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιE x) = 1 := by
  haveI := (D.s.atP p).free
  haveI : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep := by
    first
      | exact Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
      | exact Module.finite_of_finrank_eq_succ (D.s.atP p).rank
      | exact FiniteDimensional.of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  haveI : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hsum : (D.s.atP p).ιE x + (D.s.atP p).cj ((D.s.atP p).ιE x) = 1 := by
    rw [(D.s.atP p).cj_ιE, D.conjF_eq, ← map_add (f := _), hx1, map_one]
  have hinv : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).cj ((D.s.atP p).ιE x)) =
      Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιE x) := by
    first
      | exact Algebra.trace_eq_of_algEquiv (D.s.atP p).cj _
      | exact (Algebra.trace_eq_of_algEquiv (D.s.atP p).cj _).symm
  have hone : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep 1 = 2 := by
    have h := Algebra.trace_algebraMap (S := (D.s.atP p).Ep) (1 : (D.s.atP p).Fp)
    rw [map_one, (D.s.atP p).rank] at h
    rw [h]
    norm_num
  have h2 : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
      ((D.s.atP p).ιE x + (D.s.atP p).cj ((D.s.atP p).ιE x)) =
      Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep 1 := by
    rw [hsum]
  rw [map_add (f := _), hinv, hone] at h2
  linear_combination h2 / 2

theorem norm_trace_le_of_psi {ℓ : ℕ} [Fact ℓ.Prime] {Fp Ep : Type} [Field Fp] [CommRing Ep] [Algebra Fp Ep]
    [Algebra ℚ_[ℓ] Fp] (ψ : AddChar Ep ℂ)
    (hψ : ∀ y : Ep, ∃ a : ℚ, (∃ n : ℕ, a.den = ℓ ^ n) ∧
      ‖(letI := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra;
        Algebra.trace ℚ_[ℓ] Ep y) - (a : ℚ_[ℓ])‖ ≤ 1 ∧
      ψ y = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)))
    (y : Ep) (h1 : ψ y = 1) :
    ‖(letI := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra; Algebra.trace ℚ_[ℓ] Ep y)‖ ≤ 1 := by
  obtain ⟨a, -, hle, hexp⟩ := hψ y
  rw [h1] at hexp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp.symm
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have ha : (a : ℂ) = ((n : ℚ) : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hn]
    push_cast
    ring
  have haq : a = (n : ℚ) := by exact_mod_cast ha
  have hna : ‖((a : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    rw [haq]
    push_cast
    first
      | exact Padic.norm_int_le_one n
      | exact PadicInt.norm_le_one (n : ℤ_[ℓ])
      | simpa using (PadicInt.norm_le_one (n : ℤ_[ℓ]))
  have key : ∀ T : ℚ_[ℓ], ‖T - ((a : ℚ) : ℚ_[ℓ])‖ ≤ 1 → ‖T‖ ≤ 1 := by
    intro T hT
    calc ‖T‖ = ‖(T - ((a : ℚ) : ℚ_[ℓ])) + ((a : ℚ) : ℚ_[ℓ])‖ := by rw [sub_add_cancel]
      _ ≤ max ‖T - ((a : ℚ) : ℚ_[ℓ])‖ ‖((a : ℚ) : ℚ_[ℓ])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hT hna
  exact key _ hle

theorem trace_tower_theta {ℓ : ℕ} [Fact ℓ.Prime] {Fp Ep : Type} [Field Fp] [CommRing Ep] [Algebra Fp Ep]
    [Algebra ℚ_[ℓ] Fp] [FiniteDimensional ℚ_[ℓ] Fp] [Module.Free Fp Ep] [Module.Finite Fp Ep]
    (θ : Ep) (hθ : Algebra.trace Fp Ep θ = 1) (z : Fp) :
    (letI := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra;
      Algebra.trace ℚ_[ℓ] Ep (θ * algebraMap Fp Ep z)) = Algebra.trace ℚ_[ℓ] Fp z := by
  letI : Algebra ℚ_[ℓ] Ep := ((algebraMap Fp Ep).comp (algebraMap ℚ_[ℓ] Fp)).toAlgebra
  haveI : IsScalarTower ℚ_[ℓ] Fp Ep := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h1 : Algebra.trace Fp Ep (θ * algebraMap Fp Ep z) = z := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, hθ, smul_eq_mul, mul_one]
  have h2 := Algebra.trace_trace (R := ℚ_[ℓ]) (S := Fp) (T := Ep) (θ * algebraMap Fp Ep z)
  rw [h1] at h2
  exact h2.symm

theorem trace_dual_lattice : TrDual := by
  intro D δ M hA p c hc
  have h := hA p
  simp only [Agree] at h
  obtain ⟨-, -, -, hO, hpsi, -⟩ := h
  obtain ⟨x, hxint, hx1⟩ := exists_trOne D
  have htr := trace_iE_eq_one D p x hx1
  haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).qlFin
  haveI := (D.s.atP p).free
  haveI : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep := by
    first
      | exact Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
      | exact Module.finite_of_finrank_eq_succ (D.s.atP p).rank
      | exact FiniteDimensional.of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  have hθO : (D.s.atP p).ιE x ∈ (D.s.atP p).O := by
    rw [(D.s.atP p).O_def]
    exact (hxint.map (D.s.atP p).ιE.toIntAlgHom).tower_top
  have hcO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
    rw [(D.s.atP p).O_def]
    have hi := isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := ⟨c, hc⟩)
    first
      | exact hi
      | simpa [IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep] using hi
  have hyO : -((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c) ∈ (M p).L.O := by
    rw [hO]
    exact neg_mem (mul_mem hθO hcO)
  have h1 : (M p).L.psi0 (-((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c)) = 1 := by
    have h0 := ((M p).L.additive_character_dual_ring _).mpr hyO 1 (one_mem _)
    rwa [mul_one] at h0
  rw [hpsi] at h1
  have hAB : (D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (c * (δ p)⁻¹)
      = -(-((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c) *
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) := by
    rw [map_mul]
    ring
  have h2 : (D.s.atP p).psiE
      ((D.s.atP p).ιE x * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (c * (δ p)⁻¹)) = 1 := by
    rw [hAB]
    exact h1
  have key := norm_trace_le_of_psi (D.s.atP p).psiE (D.s.atP p).psiE_def _ h2
  rw [trace_tower_theta _ htr] at key
  exact key

end PI.CntNotIntW
end
end

