module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0050
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueUpperUnipotentLift
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp

theorem tauM_val_blocks {L : Type} [Field L] {n : ℕ} (w : Lˣ) :
    ((tauM (n := n) w : GL (Ix n) L) : Matrix (Ix n) (Ix n) L) =
      fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;>
    simp [tauM, pM, scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem twist_low : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw x hx
  classical
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : IsLocalRing.ResidueField O → O, ∀ a, IsLocalRing.residue O (ℓ a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  have hmapℓ : ∀ B : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      (B.map ℓ).map (IsLocalRing.residue O) = B := by
    intro B
    ext i k
    simp [hℓ]
  obtain ⟨A, hA⟩ : ∃ A, A = x.1.toBlocks₁₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = x.1.toBlocks₂₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = x.1.toBlocks₂₂.map ℓ := ⟨_, rfl⟩
  have hred : (fromBlocks A 0 C D).map (IsLocalRing.residue O) = x.1 := by
    rw [Matrix.fromBlocks_map, hA, hC, hD, hmapℓ, hmapℓ, hmapℓ,
      Matrix.map_zero _ (map_zero _), ← hx, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (A.det * D.det) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have h1 : IsLocalRing.residue O (A.det * D.det) = x.1.det := by
      rw [← Matrix.det_fromBlocks_zero₁₂ A C D, RingHom.map_det, RingHom.mapMatrix_apply, hred]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero
  let j' : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 C D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  let j : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 (ϖ • C) D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  refine ⟨j, j', ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, tauM_val_blocks]
    show (fromBlocks A 0 (ϖ • C) D).map (algebraMap O L) * _ =
      _ * (fromBlocks A 0 C D).map (algebraMap O L)
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · ext i k
      simp [hw, Matrix.map_apply, Matrix.smul_apply]
      rw [Algebra.smul_def]
    · ext i k
      simp [hw]
  · apply Units.ext
    exact hred

end GlobalTheory.CompanionTheory.Jp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommuting
section
open Polynomial

namespace GlobalTheory.CompanionTheory.Centraliser

variable {K : Type} [Field K] {n : ℕ}

theorem act_mul (γ : Matrix (Fin n) (Fin n) K) (a b : K[X]) (v : Fin n → K) :
    (aeval γ (a * b)).mulVec v = (aeval γ a).mulVec ((aeval γ b).mulVec v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

theorem charpoly_dvd_of_aeval_eq_zero (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) {p : K[X]} (hp : aeval γ p = 0) : γ.charpoly ∣ p := by
  have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ p hp
  rcases Nat.eq_zero_or_pos (Fintype.card (Fin n)) with h0 | h0
  · rw [h0, pow_zero] at h
    exact h.trans (one_dvd p)
  · exact (hs.squarefree.dvd_pow_iff_dvd h0.ne').1 h

theorem exists_vec_ann (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) (q : K[X]) :
    q ∣ γ.charpoly → ∃ v : Fin n → K, (aeval γ q).mulVec v = 0 ∧
      ∀ h : K[X], (aeval γ h).mulVec v = 0 → q ∣ h := by
  have hf0 : γ.charpoly ≠ 0 := γ.charpoly_monic.ne_zero
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.1 h) hf0
  · intro x hx _
    exact ⟨0, by simp, fun h _ => hx.dvd⟩
  · intro a p ha hp ih hd
    obtain ⟨v', hv1, hv2⟩ := ih ((dvd_mul_left a p).trans hd)
    obtain ⟨g, hg⟩ : p ∣ γ.charpoly := (dvd_mul_right p a).trans hd
    have hgne : g ≠ 0 := by
      rintro rfl
      exact hf0 (by simpa using hg)
    have hg0 : aeval γ g ≠ 0 := fun h => by
      obtain ⟨c, hc⟩ := charpoly_dvd_of_aeval_eq_zero γ hs h
      rw [hg] at hc
      have h1 : g * (p * c) = g * 1 := by
        rw [mul_one]
        calc g * (p * c) = p * g * c := by ring
          _ = g := hc.symm
      exact hp.not_unit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hgne h1))
    obtain ⟨u, hu⟩ : ∃ u, (aeval γ g).mulVec u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hg0 (Matrix.mulVec_injective (funext fun u => by simpa using hcon u))
    set w := (aeval γ g).mulVec u with hw
    have hpw : (aeval γ p).mulVec w = 0 := by
      rw [hw, ← act_mul, ← hg, Matrix.aeval_self_charpoly, Matrix.zero_mulVec]
    have hkey : ∀ h : K[X], (aeval γ h).mulVec w = 0 → p ∣ h := by
      intro h hh
      by_contra hnd
      obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd hp).2 hnd
      apply hu
      have h1 : (aeval γ (s * p + t * h)).mulVec w = w := by
        rw [hst]; simp
      rw [map_add (f := _), Matrix.add_mulVec, act_mul, act_mul, hpw, hh] at h1
      simpa using h1.symm
    have hpa : ¬ p ∣ a := by
      rintro ⟨c, rfl⟩
      exact hp.not_unit (hs.squarefree p
        ((mul_dvd_mul_left p (dvd_mul_right p c)).trans hd))
    have hcop : IsCoprime p a := (Prime.coprime_iff_not_dvd hp).2 hpa
    refine ⟨v' + w, ?_, ?_⟩
    · rw [Matrix.mulVec_add, act_mul, hv1, mul_comm, act_mul, hpw]
      simp
    · intro h hh
      have h1 : (aeval γ (h * p)).mulVec v' = 0 := by
        have h2 : (aeval γ (h * p)).mulVec (v' + w) = 0 := by
          rw [mul_comm, act_mul, hh, Matrix.mulVec_zero]
        rw [Matrix.mulVec_add, act_mul γ h p w, hpw, Matrix.mulVec_zero, add_zero] at h2
        exact h2
      have hah : a ∣ h := hcop.symm.dvd_of_dvd_mul_right (hv2 _ h1)
      obtain ⟨c, rfl⟩ := hah
      have h3 : (aeval γ (a * c)).mulVec v' = 0 := by
        rw [mul_comm, act_mul, hv1]; simp
      rw [Matrix.mulVec_add, h3, zero_add] at hh
      exact hcop.mul_dvd (hkey _ hh) (dvd_mul_right a c)

theorem exists_cyclic_vec (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v : Fin n → K, ∀ w : Fin n → K, ∃ q : K[X], (aeval γ q).mulVec v = w := by
  obtain ⟨v, -, hv⟩ := exists_vec_ann γ hs γ.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  let L : K[X] →ₗ[K] (Fin n → K) :=
    { toFun := fun p => (aeval γ p).mulVec v
      map_add' := fun a b => by rw [map_add (f := _), Matrix.add_mulVec]
      map_smul' := fun c a => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  let φ : degreeLT K n →ₗ[K] (Fin n → K) := L.domRestrict (degreeLT K n)
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨p, hp⟩ h0
    have hd : γ.charpoly ∣ p := hv p h0
    have hlt : p.degree < γ.charpoly.degree := by
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact Polynomial.mem_degreeLT.1 hp
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd hlt)
  have hfr : Module.finrank K (degreeLT K n) = Module.finrank K (Fin n → K) :=
    (degreeLTEquiv K n).finrank_eq
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  intro w
  obtain ⟨⟨q, _⟩, hq⟩ := hsurj w
  exact ⟨q, hq⟩

theorem a1 : PositivityTheory.Rg.Tf.Loc.A1 := by
  intro K _ n γ hs M hM
  obtain ⟨v, hv⟩ := exists_cyclic_vec γ hs
  obtain ⟨p, hp⟩ := hv (M.mulVec v)
  refine ⟨p, Matrix.mulVec_injective (funext fun w => ?_)⟩
  obtain ⟨q, rfl⟩ := hv w
  have hc : Commute M (aeval γ q) := by
    rw [aeval_eq_sum_range]
    exact Commute.sum_right _ _ _ fun i _ => (hM.pow_right i).smul_right _
  rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, ← hp, ← act_mul, mul_comm, act_mul]

end GlobalTheory.CompanionTheory.Centraliser
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMemRangeLTensorOfLTensorEqZero
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_mem_range_lTensor_of_lTensor_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R)
      (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀]
      (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂]
      (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂)
      (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) →
      (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) →
      (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) →
      (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) →
      ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := by
  intro p _ R _ _ _ r N _ _ K₀ _ _ K₁ _ _ K₂ _ _ K₃ _ _ d₀ d₁ d₂ hr hdd h1 h2 h3 w hw k
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : ∀ k, r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    intro k
    rw [← pow_two, ← pow_add, Nat.sub_add_cancel hp]
    exact (hr k).symm
  have hsat : ∀ (a : R) (x : K₂), a ≠ 0 → a • x ∈ LinearMap.range d₁ →
      ∀ k, r k • x ∈ LinearMap.range d₁ := by
    rintro a x ha ⟨y, hy⟩ k
    have hax : a • d₂ x = 0 := by
      rw [← map_smul, ← hy, hdd]
    have h0 : d₂ (r (k + 1) • x) = 0 := by
      rw [map_smul]
      exact h3 a _ ha hax (k + 1)
    have h4 := h2 _ h0 (k + 1)
    rw [hrk k, mul_smul, mul_smul]
    exact Submodule.smul_mem _ _ h4
  have hsub : (LinearMap.range d₁).subtype ∘ₗ d₁.rangeRestrict = d₁ := by
    ext x
    rfl
  have hw' : (LinearMap.range d₁).subtype.lTensor N (d₁.rangeRestrict.lTensor N w) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsub]
    exact hw
  have h5 := smul_eq_zero_of_lTensor_subtype_eq_zero R r N K₂ (LinearMap.range d₁) hsat _ hw' (k + 1)
  have h6 : d₁.rangeRestrict.lTensor N (r (k + 1) • w) = 0 := by
    rw [map_smul]
    exact h5
  have hex : Function.Exact (LinearMap.ker d₁).subtype d₁.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hx' : d₁ x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Subtype.ext z.2
  obtain ⟨u, hu⟩ := (lTensor_exact N hex d₁.surjective_rangeRestrict _).1 h6
  have h7 : ∀ u : N ⊗[R] LinearMap.ker d₁,
      r (k + 1) • (LinearMap.ker d₁).subtype.lTensor N u ∈ LinearMap.range (d₀.lTensor N) := by
    intro u
    induction u with
    | tmul n z =>
      obtain ⟨y, hy⟩ := h1 z z.2 (k + 1)
      exact ⟨n ⊗ₜ y, by simp [hy, TensorProduct.tmul_smul]⟩
    | add a b ha hb =>
      rw [map_add (f := _), smul_add]
      exact Submodule.add_mem _ ha hb
  rw [hrk k, mul_smul, mul_smul, ← hu]
  exact Submodule.smul_mem _ _ (h7 u)

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparabilityStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_preserves_closedness_comparability : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T), Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := by
  first | exact @GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | exact GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | (intros; apply GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorIdealMapInjective
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Descent

theorem mem_of_includeRight_mem_map :
  ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O'] [Module.Free O O'] [CommRing R] [Algebra O R] (I : Ideal R) (x : R), (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I → x ∈ I := by
  intro O O' R _ _ _ _ _ _ _ I x hx
  have hnt : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton O' (Module.subsingleton O O')
  have : Module.FaithfullyFlat O O' := inferInstance
  have : Module.FaithfullyFlat R (R ⊗[O] O') := inferInstance
  let c : O' ⊗[O] R ≃ₐ[O] R ⊗[O] O' := Algebra.TensorProduct.comm O O' R
  have hc : ∀ y : R, c (Algebra.TensorProduct.includeRight y) = algebraMap R (R ⊗[O] O') y := by
    intro y
    simp [c, Algebra.TensorProduct.algebraMap_apply]
  have hle : Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I ≤
      Ideal.comap c (Ideal.map (algebraMap R (R ⊗[O] O')) I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [hc]
    exact Ideal.mem_map_of_mem _ hy
  have h1 : algebraMap R (R ⊗[O] O') x ∈ Ideal.map (algebraMap R (R ⊗[O] O')) I := by
    have h2 := hle hx
    simp only [Ideal.mem_comap] at h2
    rwa [hc] at h2
  have h4 := Ideal.comap_map_eq_self_of_faithfullyFlat (B := R ⊗[O] O') I
  rw [← h4]
  exact h1

end GlobalTheory.CompanionTheory.Descent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsQuot
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B →
    ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧
      q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧
      (VAL π → VAL (q π)) := by
  intro p _ B _ π h
  have hp : p.Prime := Fact.out
  obtain ⟨⟨F, hF⟩, hred, -, -, -⟩ := pf_facts p B h

  have hpow : ∀ (N : ℕ) (x : B), π ^ N * x = 0 → π * x = 0 := by
    intro N x e
    apply hred _ (N + 1)
    calc (π * x) ^ (N + 1) = π * x ^ N * (π ^ N * x) := by ring
      _ = 0 := by rw [e, mul_zero]

  have hfrob : ∀ x : B, π * x ^ p = 0 → π * x = 0 := by
    intro x e
    apply hred _ p
    have h1 : p = (p - 1) + 1 := by have := hp.one_lt; omega
    rw [mul_pow]
    conv_lhs => rw [h1, pow_succ π]
    rw [← h1, mul_assoc, e, mul_zero]
  let I : Ideal B :=
    { carrier := {x | π * x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [mul_left_comm, hx, mul_zero] }
  have hI : ∀ x, Ideal.Quotient.mk I x = 0 ↔ π * x = 0 := fun x => Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  refine ⟨B ⧸ I, inferInstance, Ideal.Quotient.mk I, hsurj, ⟨?_, ?_, ?_⟩, ?_, hI, ?_, ?_⟩
  · rw [← map_natCast (Ideal.Quotient.mk I), h.char, map_zero]
  · intro a b e
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    simp only at e
    rw [← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, hI] at e
    rw [← sub_eq_zero, ← map_sub, hI]
    apply hfrob
    have : (x - y) ^ p = x ^ p - y ^ p := by
      rw [← hF, map_sub, hF, hF]
    rw [this, e]
  · intro a
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := h.bij.2 x
    exact ⟨Ideal.Quotient.mk I y, by simp only [map_pow]⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro a e
    obtain ⟨x, rfl⟩ := hsurj a
    rw [← map_mul, hI] at e
    rw [hI]
    apply hpow 2
    rw [← e]
    ring
  · intro hA P hP hdeg
    have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
      (Polynomial.map_surjective _ hsurj P).imp (fun Q hQ => by simpa using hQ) |> fun ⟨Q, hQ⟩ =>
        (Polynomial.mem_lifts _).2 ⟨Q, hQ⟩
    obtain ⟨Q, rfl, hQd, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨x, hx⟩ := hA Q hQm (hQd ▸ hdeg)
    exact ⟨Ideal.Quotient.mk I x, hx.map (Ideal.Quotient.mk I)⟩
  · intro hV f₁ g₁ ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := hsurj f₁
    obtain ⟨g, rfl⟩ := hsurj g₁
    obtain ⟨a₁, b₁, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := hsurj a₁
    obtain ⟨b, rfl⟩ := hsurj b₁
    have ht : π * (a * f + b * g - π ^ N) = 0 := by
      rw [← hI, map_sub, map_add (f := _), map_mul, map_mul, map_pow, hab, sub_self]
    have hmem : π ^ (N + 1) ∈ Ideal.span {f, g} := by
      refine Ideal.mem_span_pair.2 ⟨π * a, π * b, ?_⟩
      linear_combination ht
    obtain ⟨e, he, h1, h2⟩ := hV f g ⟨N + 1, hmem⟩
    refine ⟨Ideal.Quotient.mk I e, he.map _, ?_, ?_⟩
    · rw [Ideal.mem_span_singleton] at h1 ⊢
      rw [← map_mul]
      exact map_dvd _ h1
    · rw [Ideal.mem_span_singleton] at h2 ⊢
      have : (1 - Ideal.Quotient.mk I e) * Ideal.Quotient.mk I g
          = Ideal.Quotient.mk I ((1 - e) * g) := by
        rw [map_mul, map_sub, map_one]
      rw [this]
      exact map_dvd _ h2

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormulaStatement
section
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_diagonal_block_conjugate_formula : ∀ (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnit g.det → X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) → (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) → ∀ Y : Matrix (Fin n) (Fin n) ℂ, trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g)) = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | exact GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingFrobeniusCompatStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_frobenius_compat : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀) (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L), (∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y) → ∀ (pT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y) → (∀ a, φC (c a) = c (φA a)) → (∀ x, φC (k x) = k (fr x)) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | exact GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariantStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_galois_equivariant : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (σA : A →+* A) (σC : C₀ →+* C₀) (gT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y) → (∀ a, σC (c a) = c (σA a)) → (∀ x, σC (k x) = k x) → ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (gT z) = σC (T c k hk f z) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_gal | exact GlobalTheory.CompanionTheory.FrobPairing.T_gal | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_gal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulLeftStatement
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_smul_left : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L), T c k hk f (a • z) = c a * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_smul | exact GlobalTheory.CompanionTheory.FrobPairing.T_smul | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProductStatement
section
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_denominator_product : ∀ {n : ℕ} (z : Fin n → ℂ), (∀ a, z a ≠ 0) → (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | exact GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow <;> assumption)
end

