module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLocalizationAtPrimeFactorsThroughAway
section
open IsLocalRing TensorProduct

namespace GlobalTheory
namespace FactorAway

theorem factor_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime]
    (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p)
      (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift
        (algebraMap B (Localization.AtPrime p)) g
        (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  intro R A B _ _ _ _ _ _ p _ φ
  let φ' : B ⊗[R] A →ₐ[B] Localization.AtPrime p :=
    Algebra.TensorProduct.lift (Algebra.ofId B _) φ (fun _ _ => Commute.all _ _)
  obtain ⟨g, hg, s, ι, hι⟩ := SpreadOut.spread_out B (B ⊗[R] A) p φ'
  refine ⟨g, hg, (s.restrictScalars R).comp Algebra.TensorProduct.includeRight, fun a => ?_⟩
  have hext : (Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
      (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl))) =
      (ι : Localization.Away g →+* Localization.AtPrime p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext b
    simp [Localization.awayLift]
  have h1 := congrArg (fun h => h ((1 : B) ⊗ₜ[R] a)) hι
  simp only [AlgHom.comp_apply, φ', Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h1
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
  rw [hext]
  exact h1

end FactorAway
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorAvoidsFibreMinimalPrimesStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B),
    (∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) →
    ∀ u : PrimeSpectrum B, ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  first | exact @GlobalTheory.annihilator_avoids_fibre_minimalPrimes | exact GlobalTheory.annihilator_avoids_fibre_minimalPrimes | (intros; apply GlobalTheory.annihilator_avoids_fibre_minimalPrimes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorLiftOfMulEqPStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_lift_of_mul_eq_p_alt : ∀ (p : ℕ) (O : Type) [CommRing O] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), (p : k) = 0 → (p : Λ) ^ 2 = 0 → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], (∀ m : M, (p : Λ) • m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ ϖ z : O, ϖ * z - (p : O) ∈ Ideal.span {(p : O) ^ 2} → ∀ n : N, ((1 : k) ⊗ₜ[ℤ] ϖ) • n = 0 → n ∈ Ideal.span {a : k ⊗[ℤ] O | ((1 : k) ⊗ₜ[ℤ] ϖ) * a = 0} • (⊤ : Submodule (k ⊗[ℤ] O) N) := by
  first | (exact @GlobalTheory.annihilator_lift_of_mul_eq_p) | (exact GlobalTheory.annihilator_lift_of_mul_eq_p) | (intros; apply GlobalTheory.annihilator_lift_of_mul_eq_p  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssociatedOfHeightOneAgree
section
namespace GlobalTheory

theorem exists_unit_eq_mul_of_height_one_avoiding (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (hdiv : ∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) :
    ∃ u : Rˣ, a = u * b := by

  have avoid : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → ∀ x : R, x ≠ 0 → x ∈ Q →
      (∀ j ∈ J, Prime (π j) → ¬ π j ∣ x) → ∀ j ∈ J, π j ∉ Q := by
    intro Q hQ h1 x hx hxQ hnd j hj hjQ
    rcases hπ j hj with hu | hp
    · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hjQ hu)
    · have hmin := mem_minimalPrimes_span_singleton_of_height_eq_one h1 hp.ne_zero hjQ
      have hsp : (Ideal.span {π j}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      have hle : Q ≤ Ideal.span {π j} :=
        hmin.2 ⟨hsp, le_refl _⟩ ((Ideal.span_singleton_le_iff_mem Q).mpr hjQ)
      exact hnd j hj hp (Ideal.mem_span_singleton.mp (hle hxQ))
  have hba : b ∣ a := dvd_of_forall_height_eq_one hb fun Q _ h1 hbQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 b hb hbQ fun j hj hp => (hdiv j hj hp).2)
    exact ⟨d, hd, c, by rw [mul_comm d a, e]⟩
  have hab : a ∣ b := dvd_of_forall_height_eq_one ha fun Q _ h1 haQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 a ha haQ fun j hj hp => (hdiv j hj hp).1)
    exact ⟨c, hc, d, by rw [mul_comm c b, ← e]⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hba hab
  exact ⟨u, by rw [← hu, mul_comm]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayCongrModOfIsCoprimeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.away_congr_mod_of_isCoprime : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ Ideal.span {algebraMap A C g}) → ∀ c' : Localization.Away (algebraMap A C f), ∃ b : Localization.Away f, c' - Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} := by
  first | (exact @GlobalTheory.away_congr_of_isCoprime) | (exact GlobalTheory.away_congr_of_isCoprime) | (intros; apply GlobalTheory.away_congr_of_isCoprime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapSpanSingletonDivisibilityDescendsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.awayMap_span_singleton_divisibility_descends : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), (∀ a : A, algebraMap A C a ∈ Ideal.span {algebraMap A C g} → a ∈ Ideal.span {g}) → ∀ b : Localization.Away f, Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} → b ∈ Ideal.span {algebraMap A (Localization.Away f) g} := by
  first | (exact @GlobalTheory.awayMap_descends_divisibility) | (exact GlobalTheory.awayMap_descends_divisibility) | (intros; apply GlobalTheory.awayMap_descends_divisibility <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaAlgEquivMatrixOfIdempotentStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e = c • e) → (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (exact GlobalTheory.azumaya_algEquiv_matrix_of_idempotent) | (intros; apply GlobalTheory.azumaya_algEquiv_matrix_of_idempotent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChangeStatement
section
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_base_change : ∀ (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ], IsAzumaya S (S ⊗[A] Λ) := by
  first | (exact @GlobalTheory.isAzumaya_baseChange) | (exact GlobalTheory.isAzumaya_baseChange) | (intros; apply GlobalTheory.isAzumaya_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BarMSingle
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.DMComm

variable {n : ℕ}

theorem barM_single (ε : Fin n → Bool) (x : Mode ε) :
    barM ε (Matrix.single x.1.2 x.1.1 1) = Matrix.single x.1.1 x.1.2 1 := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := x
  ext i j
  simp only [barM, Matrix.single_apply]
  by_cases h : b = j ∧ a = i
  · obtain ⟨rfl, rfl⟩ := h
    simp only at ha hb
    simp [sg, ha, hb]
  · have h' : ¬ (a = i ∧ b = j) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [h, h']

theorem dM_inl (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inl (i, j))) = (if j = x.1.1 then X (Sum.inl (i, x.1.2)) else 0)
      - (if i = x.1.2 then X (Sum.inl (x.1.1, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inl, Finset.sum_sub_distrib]
  congr 1
  · by_cases h : j = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem dM_inr (ε : Fin n → Bool) (x : Mode ε) (i j : Fin n) :
    dM ε x (X (Sum.inr (i, j))) = (if j = x.1.2 then X (Sum.inr (i, x.1.1)) else 0)
      - (if i = x.1.1 then X (Sum.inr (x.1.2, j)) else 0) := by
  simp only [dM, dZ, mkDerivation_X, Sum.elim_inr, Finset.sum_sub_distrib, barM_single]
  congr 1
  · by_cases h : j = x.1.2
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]
  · by_cases h : i = x.1.1
    · subst h
      simp [Matrix.single_apply, apply_ite]
    · simp [Matrix.single_apply, h, Ne.symm h]

theorem mode_ne (ε : Fin n → Bool) (w x : Mode ε) : x.1.2 ≠ w.1.1 := by
  intro h
  have h1 := x.2.2
  rw [h, w.2.1] at h1
  exact absurd h1 (by simp)

theorem dM_comm_X (ε : Fin n → Bool) (w x : Mode ε) (v : (Fin n × Fin n) ⊕ (Fin n × Fin n)) :
    dM ε w (dM ε x (X v)) = dM ε x (dM ε w (X v)) := by
  have h1 := mode_ne ε w x
  have h2 := mode_ne ε x w
  have h3 := h1.symm
  have h4 := h2.symm
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [dM_inl, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all
  · simp only [dM_inr, map_sub, apply_ite (dM ε w), apply_ite (dM ε x), map_zero, h1, h2, h3, h4, if_false]
    split_ifs <;> simp_all

theorem dM_comm : GlobalTheory.PsCo.Cw2a.T_dM_comm := by
  intro n ε w x P
  have h : ⁅dM ε w, dM ε x⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, dM_comm_X, sub_self]
    rfl
  have h2 := congrArg (fun D : Derivation ℂ (Poly n) (Poly n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

end GlobalTheory.PsCo.DMComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiffStatement
section
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) → (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) → ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  first | exact @GlobalTheory.bichar_deriv_contDiff | exact GlobalTheory.bichar_deriv_contDiff | (intros; apply GlobalTheory.bichar_deriv_contDiff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLinearCombinationOfRankAtStalkStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearCombination_bijective_of_rankAtStalk_eq : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ), (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M, Module.support R (M ⧸ Submodule.span R (Set.range s)) = ∅ → Function.Bijective (Fintype.linearCombination R s) := by
  first | (exact @GlobalTheory.bijective_linearCombination_of_rankAtStalk) | (exact GlobalTheory.bijective_linearCombination_of_rankAtStalk) | (intros; apply GlobalTheory.bijective_linearCombination_of_rankAtStalk  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinQuadRepresentsUnitOfFiniteReduced
section
open Polynomial

namespace GlobalTheory

theorem binQuad_represents_unit_of_finite_reduced (S : Type) [CommRing S] [Finite S]
    [IsReduced S] (t m f : S) (hd : IsUnit (t ^ 2 - 4 * m)) (hf : IsUnit f) :
    ∃ a b : S, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  first
  | exact @_root_.GlobalTheory.FieldCaseReduction.main
  | exact _root_.GlobalTheory.FieldCaseReduction.main
  | (apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FieldCaseReduction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FieldCaseReduction.main ..)

theorem norm_surj_of_finite_reduced_involution : ∀ (R : Type) [CommRing R] [Finite R]
    [IsReduced R] (τ : R →+* R), (∀ x, τ (τ x) = x) → ∀ θ : R, IsUnit (θ - τ θ) →
    ∀ f : R, IsUnit f → τ f = f → ∃ c : R, τ c * c = f := by
  intro R _ _ _ τ hτ θ hθ f hf hτf
  classical
  let A : Subring R := τ.eqLocus (RingHom.id R)
  have memA : ∀ x, τ x = x → x ∈ A := fun x hx => show τ x = RingHom.id R x from hx
  have fixA : ∀ x : A, τ (x : R) = x := fun x => x.2
  obtain ⟨u, hu⟩ := hθ
  have h4 : ((4 : A) : R) = 4 := map_ofNat A.subtype 4
  have hτd : τ (θ - τ θ) = -(θ - τ θ) := by rw [map_sub, hτ]; ring
  have hτdi : τ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : τ (↑u⁻¹ : R) * (θ - τ θ) = -1 := by
      have := congrArg τ u.inv_mul
      rw [map_mul, map_one, hu, hτd] at this
      linear_combination -this
    calc τ (↑u⁻¹ : R) = τ ↑u⁻¹ * ((θ - τ θ) * ↑u⁻¹) := by rw [← hu, u.mul_inv, mul_one]
      _ = -↑u⁻¹ := by rw [← mul_assoc, h1]; ring
  obtain ⟨v, hv⟩ := hf
  have hτfi : τ (↑v⁻¹ : R) = ↑v⁻¹ := by
    have h1 : τ (↑v⁻¹ : R) * f = 1 := by
      rw [← hτf, ← map_mul, ← hv, v.inv_mul, map_one]
    calc τ (↑v⁻¹ : R) = τ ↑v⁻¹ * (f * ↑v⁻¹) := by rw [← hv, v.mul_inv, mul_one]
      _ = ↑v⁻¹ := by rw [← mul_assoc, h1, one_mul]
  let tA : A := ⟨θ + τ θ, memA _ (by rw [map_add (f := _), hτ, add_comm])⟩
  let mA : A := ⟨θ * τ θ, memA _ (by rw [map_mul, hτ, mul_comm])⟩
  let fA : A := ⟨f, memA _ hτf⟩
  let wA : A := ⟨↑u⁻¹ * ↑u⁻¹, memA _ (by rw [map_mul, hτdi]; ring)⟩
  let vA : A := ⟨↑v⁻¹, memA _ hτfi⟩
  have hdisc : IsUnit (tA ^ 2 - 4 * mA) := by
    suffices h : (tA ^ 2 - 4 * mA) * wA = 1 from ⟨⟨_, wA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    have e1 : (θ + τ θ) ^ 2 - 4 * (θ * τ θ) = ↑u * ↑u := by rw [hu]; ring
    push_cast [tA, mA, wA]
    rw [h4, e1, show (↑u : R) * ↑u * (↑u⁻¹ * ↑u⁻¹) = (↑u * ↑u⁻¹) * (↑u * ↑u⁻¹) by ring, u.mul_inv,
      one_mul]
  have hfA : IsUnit fA := by
    suffices h : fA * vA = 1 from ⟨⟨_, vA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    push_cast [fA, vA]
    rw [← hv, v.mul_inv]
  haveI : IsReduced A := ⟨fun x hx => Subtype.ext (IsNilpotent.eq_zero (hx.map A.subtype))⟩
  obtain ⟨a, b, hab⟩ := binQuad_represents_unit_of_finite_reduced A tA mA fA hdisc hfA
  have hab' := congrArg Subtype.val hab
  push_cast [tA, mA, fA] at hab'
  refine ⟨(a : R) + θ * b, ?_⟩
  rw [map_add (f := _), map_mul, fixA a, fixA b]
  linear_combination hab'

end GlobalTheory
end

