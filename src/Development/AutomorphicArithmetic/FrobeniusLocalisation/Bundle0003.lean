module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.RdLower
section
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem rd_lower_num (e : ℕ) (he : 2 ≤ e) :
    (6.7 : ℝ) < (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by
  have he' : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have h1 : (2 : ℝ) ^ (-(e : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ ((11 : ℝ) / 4) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [he', h1])
  refine lt_of_lt_of_le ?_ h3
  have h4 : ((2 : ℝ) ^ ((11 : ℝ) / 4)) ^ (4 : ℕ) = 2 ^ (11 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    norm_num
  refine lt_of_pow_lt_pow_left₀ 4 (by positivity) ?_
  rw [h4]; norm_num

theorem UpperTheory.HF.rd_lower :
    ∀ {φ : Frame} (H : HostAx φ), (6.7 : ℝ) < (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ∧ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ≤ H.rd / Real.sqrt H.d ∧ 8 < H.rd / 2 ∧ 2 * 2 ^ φ.e ≤ 2 * φ.ord ∧ 2 * φ.ord ≤ 2 * φ.o * 2 ^ φ.e := by
  intro φ H
  have h1 := rd_lower_num φ.e H.two_le_e
  have h2 := H.der.rd_ge
  have hd : 7 ≤ H.d := by have := H.d_mod_sixteen; omega
  have hd' : (7 : ℝ) ≤ (H.d : ℝ) := by exact_mod_cast hd
  have hs : (2.6 : ℝ) ≤ Real.sqrt H.d := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < Real.sqrt H.d := by linarith
  refine ⟨h1, (le_div_iff₀ hs0).2 h2, ?_, Nat.mul_le_mul_left 2 φ.two_pow_le_ord, ?_⟩
  · have h3 : (6.7 : ℝ) * 2.6 ≤ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d :=
      mul_le_mul h1.le hs (by norm_num) (by positivity)
    linarith
  · rw [mul_assoc]
    exact Nat.mul_le_mul_left 2 φ.ord_le_o_mul_two_pow
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.RhoArt
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rho_art :
    ∀ {φ : Frame} (H : HostRaw φ) {f : ℕ}, f ∣ H.condN → Formalism.HC.Der.Rd.rho H.art.ker f = 1 - 1 / (Nat.card (H.imgOne f) : ℝ) := by
  intro φ H f hf
  classical
  rw [Formalism.HC.Der.Rd.rho_eq _ hf]
  have h1 := (H.art.ker.subgroupOf (H.unitsOne f)).card_mul_index
  have h2 : (H.art.ker.subgroupOf (H.unitsOne f)).index = Nat.card (H.imgOne f) :=
    Subgroup.relIndex_ker (H.unitsOne f) H.art
  have h3 : Nat.card (H.unitsOne f) = (Formalism.HC.Der.Rd.KK H.condN f).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf])
  have h4 : Nat.card (H.art.ker.subgroupOf (H.unitsOne f)) =
      ((Formalism.HC.Der.Rd.KK H.condN f).filter fun u => u ∈ H.art.ker).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ H.unitsOne f)
      (fun u => u ∈ H.art.ker)).trans (Equiv.subtypeEquivRight fun u => ?_))
    rw [Finset.mem_filter, Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf]
  rw [h2, h3, h4] at h1
  have h5 := Formalism.HC.Der.Rd.card_KK hf
  rw [← h1] at h5
  have h6 := congrArg (Nat.cast : ℕ → ℝ) h5
  push_cast at h6
  have hN : (H.condN.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos H.condN)).ne'
  have hI : (Nat.card (H.imgOne f) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  congr 1
  rw [div_eq_div_iff hN hI, one_mul, ← h6]
  rw [mul_right_comm]
  congr!
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.locOnto
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.loc_onto :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (J : L →+* PadicAlgCl l), ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver (span {(l : ℤ)}) ∧ (∀ x : 𝓞 L, x ∈ P ↔ ‖J (x : L)‖ < 1) ∧ (∀ τ : L ≃ₐ[ℚ] L, τ ∈ MulAction.stabilizer _ P ↔ ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : L, σ (J x) = J (τ x)) ∧ (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ τ : L ≃ₐ[ℚ] L, ∀ x : L, σ (J x) = J (τ x)) ∧ Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range J)) = Nat.card (MulAction.stabilizer (L ≃ₐ[ℚ] L) P) := by
  intro l _ L _ _ _ J
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hl : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p l]
    have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  let I : Ideal (𝓞 L) :=
    { carrier := {x : 𝓞 L | ‖J (x : L)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        show ‖J ((a : L) + (b : L))‖ < 1
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        show ‖J ((c : L) * (x : L))‖ < 1
        rw [map_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (LocStab.norm_int_le J c)) hx }
  have hmem : ∀ x : 𝓞 L, x ∈ I ↔ ‖J (x : L)‖ < 1 := fun x => Iff.rfl
  have hIp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem] at hab
      rw [hmem, hmem]
      have hab' : ‖J (a : L)‖ * ‖J (b : L)‖ < 1 := by
        rw [← norm_mul, ← map_mul]
        exact hab
      by_contra h
      push_neg at h
      nlinarith [h.1, h.2]
  have hlI : ((l : ℤ) : 𝓞 L) ∈ I := by
    rw [hmem]
    simpa using hl
  have hIne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlI
    have hne : ((l : ℤ) : 𝓞 L) ≠ 0 := by
      simp [(Fact.out : l.Prime).ne_zero]
    exact hne hlI
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨I, hIp, hIne⟩
  have hlo : I.LiesOver (Ideal.span {(l : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible
        (Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hIp.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 L) (l : ℤ) ∈ I
    rw [eq_intCast]
    exact hlI
  refine ⟨I, hIp, hlo, hmem, ?_, ?_, ?_⟩
  · intro τ
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hτ
      have hr := LocStab.root_of_stab J α τ v hmem hτ
      have hint := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) (J α)).isIntegral
      have hmin : minpoly ℚ_[l] (J (τ α)) = minpoly ℚ_[l] (J α) :=
        (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr (minpoly.monic hint)).symm
      obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[l]) (E := PadicAlgCl l)).mp hmin
      refine ⟨σ, fun x => ?_⟩
      have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
        (J.comp (τ : L →+* L)) (by simpa [AlgEquiv.smul_def] using hσ)
      exact RingHom.congr_fun hext x
    · rintro ⟨σ, hσ⟩
      apply LocStab.stab_of_root J hα τ v hmem
      rw [← hσ α]
      simp [Polynomial.aeval_algEquiv]
  · intro σ
    obtain ⟨s, hs⟩ := LocStab.exists_aut_of_root J α (r := σ (J α)) (by simp [Polynomial.aeval_algEquiv])
    refine ⟨s, fun x => ?_⟩
    have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
      (J.comp (s : L →+* L)) (by simpa using hs.symm)
    exact RingHom.congr_fun hext x
  · exact LocStab.finrank_adjoin_range_eq_card_stabilizer l L J v hmem
end

