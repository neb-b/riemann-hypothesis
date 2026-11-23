module

public import Mathlib
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.AutApprox

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostApprox
section
open NumberField Formalism.HC KStar.Tree

theorem UpperTheory.Mu.hostApprox :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (v : (ZMod H.condN)ˣ), H.art v = 1 → ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ H.condN.factorization l ∣ (u : ℤ_[l]) - (((v : ZMod H.condN).val : ℕ) : ℤ_[l]) → ∀ k : ℕ, ∃ g : Ω ≃ₐ[H.E] Ω, (l : ℤ_[l]) ^ k ∣ ((cyc l H.E Ω g : ℤ_[l]ˣ) : ℤ_[l]) - u := by
  intro φ H l _ Ω _ _ _ v hv u hu k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap H.E Ω).injective
  haveI : IsScalarTower ℚ H.E Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.E
  haveI : Algebra.IsAlgebraic H.E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ H.E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have hN : H.condN ≠ 0 := by
    obtain ⟨hq, hd, -⟩ := H.hyp
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_pos.ne' hq.ne_zero) hd.ne_zero
  haveI : NeZero (H.QS * H.q * H.d) := ⟨hN⟩
  haveI : NeZero (((H.QS * H.q * H.d : ℕ)) : ℚ) := ⟨by exact_mod_cast hN⟩
  haveI : IsGalois ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    @IsCyclotomicExtension.isGalois {H.QS * H.q * H.d} ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension (H.QS * H.q * H.d) ℚ)
  letI : Algebra H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) := H.cycEmb.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let ι : CyclotomicField (H.QS * H.q * H.d) ℚ →ₐ[H.E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ιQ : CyclotomicField (H.QS * H.q * H.d) ℚ →ₐ[ℚ] Ω := ι.restrictScalars ℚ
  have hι : ∀ x : H.E, ιQ (H.cycEmb x) = algebraMap H.E Ω x := fun x => ι.commutes x
  have hζ : IsPrimitiveRoot (ιQ H.cycZeta) H.condN := H.cycZeta_prim.map_of_injective ιQ.injective
  obtain ⟨σ, hσζ, hσu⟩ := UpperTheory.Mu.autApprox l Ω H.condN hN (ιQ H.cycZeta) hζ v u hu k
  letI : Algebra (CyclotomicField (H.QS * H.q * H.d) ℚ) Ω := ιQ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let τ := σ.restrictNormal (CyclotomicField (H.QS * H.q * H.d) ℚ)
  have hτ : ∀ y, ιQ (τ y) = σ (ιQ y) := fun y => AlgEquiv.restrictNormal_commutes σ _ y
  have hτζ : τ H.cycZeta = H.cycZeta ^ ((v : ZMod H.condN).val) := by
    have e : ιQ (τ H.cycZeta) = ιQ (H.cycZeta ^ ((v : ZMod H.condN).val)) := by
      rw [hτ, hσζ, map_pow]
    exact ιQ.injective e
  have hfix : ∀ x : H.E, σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
    intro x
    have h := H.art_spec v τ hτζ x
    rw [show H.art v = 1 from hv, map_one, AlgEquiv.one_apply] at h
    rw [← hι, ← hτ, ← h]
  exact ⟨{ σ with commutes' := hfix }, hσu⟩
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.SplitNotDvd
section
open NumberField IsDedekindDomain Formalism.HC

open Ideal in
theorem UpperTheory.Mu.splitNotDvd :
    ∀ (φ : Frame) (H : HostAx φ), H.toHostRaw.Exact → ∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E → ¬ p ∣ H.QS := by
  intro φ H hex p hp hcard hdvd
  haveI hpf : Fact p.Prime := ⟨hp⟩
  haveI hgal : IsGalois ℚ H.E := H.galois
  obtain ⟨u, hu, hne⟩ := hex p hp hdvd
  set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hpZ
  haveI hmax : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hmem : ∀ P : Ideal (𝓞 H.E), P.IsPrime → (((p : ℕ) : 𝓞 H.E) ∈ P ↔ P.LiesOver pZ) := by
    intro P hP
    constructor
    · intro h
      rw [Ideal.liesOver_iff]
      refine hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) ?_
      rw [hpZ, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under] using h
    · intro h
      have hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [← (Ideal.liesOver_iff P pZ).1 h]
        exact Ideal.subset_span rfl
      simpa [Ideal.under] using hz
  have hset : (pZ.primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E := by
    rw [← hcard]
    have heq : pZ.primesOver (𝓞 H.E) =
        (fun v : HeightOneSpectrum (𝓞 H.E) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal} := by
      ext P
      constructor
      · rintro ⟨hP, hl⟩
        have hnb : P ≠ ⊥ := by
          intro hb
          have hz := (hmem P hP).2 hl
          rw [hb, Ideal.mem_bot] at hz
          exact hp.ne_zero (by exact_mod_cast hz)
        exact ⟨⟨P, hP, hnb⟩, (hmem P hP).2 hl, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.isPrime, (hmem _ v.isPrime).1 hv⟩
    rw [heq, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  have hn : 0 < Module.finrank ℚ H.E := Module.finrank_pos
  obtain ⟨P, hPp, hPl⟩ := Set.nonempty_of_ncard_ne_zero (hset ▸ hn.ne')
  haveI := hPp
  haveI := hPl
  have key := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(H.E/ℚ)) pZ P
  rw [hset, IsGalois.card_aut_eq_finrank, mul_assoc] at key
  have h1 : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) * P.inertiaDeg ℤ = 1 :=
    Nat.eq_of_mul_eq_mul_left hn (key.trans (mul_one _).symm)
  have hI : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hbot := Subgroup.eq_bot_of_card_eq _ hI
  set σ : Gal(H.E/ℚ) := H.gal.symm (H.art u) with hσ
  have hin : ∀ x : 𝓞 H.E, σ • x - x ∈ P := by
    refine (H.der.inertia p P σ).2 ⟨u, ?_, by simp [σ]⟩
    refine Nat.ModEq.of_dvd ?_ hu
    have hpc : p ∣ H.condN := dvd_trans hdvd (HostRaw.QS_dvd_condN _)
    have hv : p ^ H.condN.factorization p ∣ H.condN := Nat.ordProj_dvd _ _
    refine Nat.div_dvd_div_left hv ?_
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd hp (HostRaw.condN_ne_zero _) hpc).ne'
  have hσI : σ ∈ Ideal.inertia Gal(H.E/ℚ) P := AddSubgroup.mem_inertia.2 hin
  rw [hbot, Subgroup.mem_bot] at hσI
  apply hne
  simpa [σ] using congrArg H.gal hσI
end

