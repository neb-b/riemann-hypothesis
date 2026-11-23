module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
theorem UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound :
    _root_.UpperTheory.V.Af.NumberSp4Alt → ∃ C A : ℕ, ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ k : ℕ, 0 < k → D.ψ ^ k = 1 → D.ξ ^ k = 1 → D.om ^ k = 1 → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ N → p ∉ D.S → ∀ ι, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) → ∃ σ : G ℚ Ω, D.AllIrr (fun r => D.aVal σ r ≠ 0) ∧ (D.Ineq σ → Chr.nrm l c.O D.sha * Real.log l ≤ 2 * C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p) := by
  classical
  rintro ⟨C, A, hnum⟩
  refine ⟨C, A, ?_⟩
  intro Ω _ _ _ l hl c D hD N hN hψN hξN hoN k hk hψ hξ ho p hp hp5 hpN hpS ι haut
  have hlp : l ≠ p := fun h => hpS (h ▸ hD.l_mem)
  obtain ⟨-, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  have hB : ML.Over (D.pl p) p := hD.pl_over p hp
  obtain ⟨σ, hσ⟩ := hfr _ p hp hB
  obtain ⟨w, hw, -, hpw⟩ := hpl _ p hp hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hB ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have hχ : (((chiO ℚ Ω l c.O σ : c.Oˣ) : c.O) : PadicAlgCl l) = (p : PadicAlgCl l) := by
    have hz : (cycZ ℚ Ω l σ : ℤ_[l]) = (p : ℤ_[l]) := by
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      exact cycZ_toZModPow_eq hlw hw hσ.2 n
    simp only [chiO, MonoidHom.comp_apply, Units.coe_map]
    rw [hz]
    simp
  have h3 : (D.om⁻¹ * D.ξ) ^ k = 1 := by rw [mul_pow, inv_pow, ho, hξ, inv_one, one_mul]
  have h1 : (D.om⁻¹ * D.ξ * D.ψ) ^ k = 1 := by rw [mul_pow, h3, hψ, one_mul]
  have mapped_pow (χ : G ℚ Ω →* c.Oˣ) (h : χ ^ k = 1) :
      ι ((χ σ : c.O) : PadicAlgCl l) ^ k = 1 := by
    have hσpow : χ σ ^ k = 1 := by
      rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
    rw [← map_pow]
    have hcast : ((χ σ : c.O) : PadicAlgCl l) ^ k = 1 := by
      rw [← Subalgebra.coe_pow, ← Units.val_pow_eq_pow_val, hσpow]
      rfl
    rw [hcast, map_one]
  obtain ⟨NN, hNN, hlog, hX⟩ := hnum D.e hD.two_le N hN p w hp hpw hp5 hpN k hk _ _ _
    (mapped_pow _ h1) (mapped_pow _ hψ) (mapped_pow _ h3)
  replace hX := hX l hD.l_odd hlp Ω ι (D.pl p) hw σ hσ
  have htrace : (D.r0E σ).trace = ι.symm (Af.eis4 p D.e
      (ι (((D.om⁻¹ * D.ξ * D.ψ) σ : c.O) : PadicAlgCl l))
      (ι ((D.ψ σ : c.O) : PadicAlgCl l)) (ι (((D.om⁻¹ * D.ξ) σ : c.O) : PadicAlgCl l))) := by
    have hsum : (D.r0E σ).trace = ∑ i, (((D.ps i σ : c.Oˣ) : c.O) : PadicAlgCl l) := by
      simp [Raw.r0E, Raw.r0, mapRep, diagRep, Matrix.trace]
    rw [hsum]
    simp only [Fin.sum_univ_four, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, Af.eis4, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      zpow_natCast, MonoidHom.mul_apply, MonoidHom.one_apply, MonoidHom.inv_apply, MonoidHom.pow_apply,
      Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Subalgebra.coe_mul, Subalgebra.coe_one,
      Subalgebra.coe_pow, map_add, map_mul, map_pow, map_natCast, map_one, RingEquiv.symm_apply_apply, hχ]
    ring
  rw [← htrace] at hX
  have hadm : ∀ r, D.EPt r → Irr r → _root_.UpperTheory.V.Af.AdmRAlt ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits := by
    intro r hr hi
    obtain ⟨hlev, θ, hθ, hdual, -⟩ := level D hD N hN hψN hξN hoN r hr
    exact ⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, _root_.UpperTheory.V.Z.Win.A4.safe4' D hD N hN hψN hξN hoN r hr⟩
  have hne : D.AllIrr (fun r => D.aVal σ r ≠ 0) := by
    intro r hr hi
    have h := (hX {r.toHomUnits} (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hadm r hr hi)
      (fun s hs s' hs' _ => by rw [Finset.mem_singleton.1 hs, Finset.mem_singleton.1 hs'])).1 _
      (Finset.mem_singleton_self _)
    exact sub_ne_zero.2 h
  refine ⟨σ, hne, ?_⟩
  rintro ⟨-, Xi, hXi, hconj, hle⟩
  have hinj : Function.Injective fun r : G ℚ Ω →* M4 (PadicAlgCl l) => r.toHomUnits := fun r r' h =>
    MonoidHom.ext fun g => congrArg Units.val (DFunLike.congr_fun h g)
  have h := (hX (Xi.image fun r => r.toHomUnits) (fun s hs => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hadm r (hXi r hr).1 (hXi r hr).2) (fun s hs s' hs' hss => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hs'
      rw [hconj r hr r' hr' (((irrIff _).2 r r').2 hss)])).2
  rw [Finset.prod_image hinj.injOn] at h
  change _ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖ at h
  have hN0 : 0 < ‖(NN : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast hNN)
  have h4 := Real.log_le_log hN0 h
  rw [Real.log_prod fun r hr => norm_ne_zero_iff.2 (hne r (hXi r hr).1 (hXi r hr).2)] at h4
  have h5 : -Real.log ‖(NN : PadicAlgCl l)‖ ≤ Real.log |(NN : ℝ)| := by
    have hq : (NN : ℚ) ≠ 0 := by exact_mod_cast hNN
    have hx : ‖(NN : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℤ)) := by
      have hc : (((NN : ℚ) : ℚ_[l]) : PadicAlgCl l) = (NN : PadicAlgCl l) := by simp
      rw [← hc, PadicAlgCl.norm_extends, Padic.eq_padicNorm]
      have hnorm := padicNorm.eq_zpow_of_ne_zero (p := l) hq
      rw [padicValRat.of_int] at hnorm
      rw [hnorm]
      push_cast
      rfl
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    have hdvd : ((l : ℤ) ^ padicValInt l NN) ∣ NN := padicValInt_dvd NN
    have hle : ((l : ℤ) ^ padicValInt l NN) ≤ |NN| :=
      Int.le_of_dvd (abs_pos.mpr hNN) ((dvd_abs _ _).mpr hdvd)
    have hle' : (l : ℝ) ^ padicValInt l NN ≤ |(NN : ℝ)| := by exact_mod_cast hle
    rw [hx, Real.log_zpow]
    push_cast
    rw [neg_mul, neg_neg, ← Real.log_pow]
    exact Real.log_le_log (pow_pos hl0 _) hle'
  have h6 : (C : ℝ) * Nat.totient k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p ≤
      C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p := by
    have : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
    have := Real.log_natCast_nonneg p
    gcongr
  rw [Finset.sum_neg_distrib] at hle
  linarith
end
