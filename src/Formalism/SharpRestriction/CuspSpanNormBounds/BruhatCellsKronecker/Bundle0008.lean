module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0007
public import Lemmata.GeneralBFactUpperVersion.Imports

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

def LAdj {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (B B' : S.V →ₗ[E] S.V) : Prop :=
  ∀ x y, S.hT (B x) y = S.hT x (B' y)

def LInt {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} (Λ : Submodule (𝓞 E) S.V)
    (B : S.V →ₗ[E] S.V) : Prop := ∀ l ∈ Λ, B l ∈ Λ

def IntegralAdjointUnimodular : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V),
    Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → ∀ B : S.V →ₗ[E] S.V, LInt Λ B → ∃ B' : S.V →ₗ[E] S.V, LAdj S B B' ∧ LInt Λ B'

def IntegralRetraction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V),
    Submodule.IsLattice E Λ → ∃ P : S.V →ₗ[E] S.V, (∀ x ∈ X, P x = x) ∧ (∀ y, P y ∈ X) ∧ LInt Λ P

def IntegralTraceSurjective : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∃ θ : 𝓞 E, (θ : E) + star (θ : E) = 1

def IsotropicIntegralRetraction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V),
    Formalism.HermitianLatticesTheory.IsCMUnram E → Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) →
    ∃ P P' : S.V →ₗ[E] S.V, LAdj S P P' ∧ (∀ x ∈ X, P x = x) ∧ (∀ y, P y ∈ X) ∧ LInt Λ P ∧ LInt Λ P' ∧
      ∀ w y, S.hT (P' w) (P' y) = 0

def UnitriangularFrameIntegral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F F' : LFlag S r T), IsFixedConv Λ g F → IsFixedConv Λ g F' → (∀ a, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) →
    ∀ U : S.V →ₗ[E] S.V, (∀ a, U (F.fl.e a) = F'.fl.e a) → ∀ x ∈ Λ, x ∈ Xsp F → U x ∈ Λ

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdRoot
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain

theorem iroot_mem {R : Type} [CommRing R] [IsDomain R] (ζ : R) (M : ℕ) (P : Ideal R) (h1 : ζ ≠ 1) (hM : ζ ^ M = 1)
    (hP : ζ - 1 ∈ P) : (M : R) ∈ P := by
  first | exact Bl.general_b_fact_upper_version.goal1 .. | (apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM hP | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R

theorem id_root : RootsOfUnityFormal := by
  intro R _ _ ζ N g1 g2 P1 P2 hN hζN hg1 hg2 hne hP1 hP2 h1 h2 hz1 hz2
  by_contra hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hζN⟩
  have hMpos : 0 < orderOf ζ := orderOf_pos_iff.2 hfin
  have hM1 : ((orderOf ζ : ℕ) : R) ∈ P1 := iroot_mem ζ _ P1 hζ (pow_orderOf_eq_one ζ) hz1
  have hdvd : g1 ∣ orderOf ζ := by
    by_contra hnd
    exact id_coprime_notMem P1 hP1 g1 _ ((Nat.Prime.coprime_iff_not_dvd hg1).2 hnd) h1 hM1
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hklt : k < orderOf ζ := by
    rw [hk]
    have := hg1.two_le
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    nlinarith
  have hη : ζ ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hklt
  have hηg : (ζ ^ k) ^ g1 = 1 := by
    rw [← pow_mul, mul_comm, ← hk]
    exact pow_orderOf_eq_one ζ
  have hηP : ζ ^ k - 1 ∈ P2 := by
    obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow ζ 1 k
    rw [one_pow] at hw
    rw [hw]
    exact P2.mul_mem_right _ hz2
  have hg1P2 : (g1 : R) ∈ P2 := iroot_mem (ζ ^ k) g1 P2 hη hηg hηP
  exact id_coprime_notMem P2 hP2 g2 g1 ((Nat.coprime_primes hg2 hg1).2 hne.symm) h2 hg1P2

theorem id_over : ExistsPrimeAbove := by
  intro E _ _ p hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (Int.natCast_ne_zero.2 hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp) |>.isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.2 hp.ne_zero)
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hpQ⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Submodule.mem_bot _).1 hpQ)

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdUnit
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

theorem id_unit : ScalarRootOfUnity := by
  intro E _ _ _ S r T Λ F F' c hsc hzΛ hprim hcc hz hX
  have hz'o : F'.fl.z ∈ orth S (Xsp F) := by
    rw [p_mem_orth]
    intro x hx
    have hx' : x ∈ F'.fl.X := by rw [hX]; exact hx
    exact tie_X_le_ker F'.fl _ F'.fl.z_orth x hx'
  have hzo : F.fl.z ∈ orth S (Xsp F) := by
    rw [p_mem_orth]
    exact tie_X_le_ker F.fl _ F.fl.z_orth
  have hmem : c • F.fl.z ∈ Lsub Λ F := by
    unfold Lsub
    refine ⟨?_, (orth S (Xsp F)).smul_mem c hzo⟩
    have e : c • F.fl.z = F'.fl.z - (F'.fl.z - c • F.fl.z) := by abel
    rw [e]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hz)
    exact ⟨hzΛ, hz'o⟩
  obtain ⟨o, ho⟩ := hprim c hmem
  refine ⟨o, ho, ?_⟩
  have hn : ∀ φ : E →+* ℂ, ‖φ (o : E)‖ = 1 := by
    intro φ
    have h1 := b_tau_norm hsc φ c
    rw [mul_comm, hcc, map_one] at h1
    have h2 : ‖φ c‖ ^ 2 = 1 := by exact_mod_cast h1.symm
    rw [ho]
    have h3 : 0 ≤ ‖φ c‖ := norm_nonneg _
    nlinarith
  obtain ⟨n, hn0, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ (x := (o : E)) o.isIntegral_coe hn
  refine ⟨n, hn0, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using h

theorem id_cong : ScalarCongruentOne := by
  intro E _ _ _ S r T Λ g F F' o hU hzΛ hadm hz P hg hT
  obtain ⟨ξ, _, hξ2, hξ3⟩ := hadm
  obtain ⟨s, hs, hw⟩ := hξ3 (Fin.last r) P hg

  have hzX : ∀ x ∈ Xsp F, S.hT F.fl.z x = 0 := fun x hx =>
    p_symm_zero S (tie_X_le_ker F.fl _ F.fl.z_orth x hx)
  have hze : ∀ a : Fin r, S.hT F.fl.z (F.fl.e a) = 0 := fun a => hzX _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : S.hT F.fl.z F'.fl.z = (o : E) * (-(T : E)) := by
    have e : F'.fl.z = (F'.fl.z - (o : E) • F.fl.z) + (o : E) • F.fl.z := by abel
    rw [e, map_add (f := _), hzX _ hz, zero_add, map_smul, smul_eq_mul, F.fl.z_norm]
  have h2 : S.hT F.fl.z (frameAct (frame F) ξ (Fin.last r)) = -(T : E) := by
    unfold frameAct
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Fin.sum_univ_castSucc]
    have hl : frame F (Fin.last r) = F.fl.z := by simp [FlagG.fvec]
    have hc : ∀ a : Fin r, frame F a.castSucc = F.fl.e a := fun a => by simp [FlagG.fvec]
    rw [hl, hξ2, map_smul, F.fl.z_norm]
    have : ∑ a : Fin r, S.hT F.fl.z (((ξ a.castSucc (Fin.last r) : 𝓞 E) : E) • frame F a.castSucc) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [hc, map_smul, hze, smul_zero]
    rw [this, zero_add]
    simp
  have h3 : S.hT F.fl.z (frame F' (Fin.last r) - frameAct (frame F) ξ (Fin.last r)) =
      -(((o - 1 : 𝓞 E) : E) * (T : E)) := by
    have hl : frame F' (Fin.last r) = F'.fl.z := by simp [FlagG.fvec]
    rw [map_sub, hl, h1, h2]
    push_cast
    ring

  have h4 : ∀ y ∈ Ideal.span {(g : 𝓞 E)} • Λ, ∃ a : 𝓞 E, S.hT F.fl.z y = (((g : 𝓞 E) * a : 𝓞 E) : E) := by
    intro y hy
    rw [Submodule.ideal_span_singleton_smul] at hy
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have hd : l ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU]; exact hl
    obtain ⟨a, ha⟩ := d_mem_dual.1 hd _ hzΛ
    refine ⟨a, ?_⟩
    rw [← algebraMap_smul E (g : 𝓞 E) l, map_smul, smul_eq_mul, ← ha]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := h4 _ hw
  rw [← algebraMap_smul E s, map_smul, smul_eq_mul, h3] at ha
  have h5 : s * ((o - 1) * (T : 𝓞 E)) = -((g : 𝓞 E) * a) := by
    apply RingOfIntegers.coe_injective
    have : (algebraMap (𝓞 E) E s) * (((o - 1 : 𝓞 E) : E) * (T : E)) = -(((g : 𝓞 E) * a : 𝓞 E) : E) := by
      rw [← ha]; ring
    simpa using this
  have h6 : s * ((o - 1) * (T : 𝓞 E)) ∈ P.asIdeal := by
    rw [h5]
    exact P.asIdeal.neg_mem (P.asIdeal.mul_mem_right _ hg)
  rcases P.isPrime.mem_or_mem h6 with h | h
  · exact absurd h hs
  · rcases P.isPrime.mem_or_mem h with h | h
    · exact h
    · exact absurd h hT

end Formalism.MainNotions.BridgeLemma

end
end

