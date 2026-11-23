module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem inert_fixes_root_of_unit_ratio (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω) :
    0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N →
      B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  intro hN hvN hin hgc hc hgθ hvθ
  set v := B.valuation
  by_cases hθ : θ = 0
  · simp [hθ]
  set u := θ / c with hu
  have hu0 : u ≠ 0 := div_ne_zero hθ hc
  have hvu : v u = 1 := by
    have h1 : v u ^ N = 1 := by rw [← map_pow, hu, div_pow]; exact hvθ
    exact (pow_eq_one_iff_left (Nat.pos_iff_ne_zero.mp hN)).mp h1
  have hgu : g u = g θ / c := by rw [hu, map_div₀, hgc]
  have hguN : (g u) ^ N = u ^ N := by
    rw [← map_pow, hu, div_pow, map_div₀, map_pow g c, hgc, hgθ]
  set ξ := g u / u with hξ
  have hξN : ξ ^ N = 1 := by rw [hξ, div_pow, hguN, div_self (pow_ne_zero _ hu0)]
  have hvξ1 : v (ξ - 1) < 1 := by
    have h2 : ξ - 1 = (g u - u) / u := by rw [hξ, sub_div, div_self hu0]
    rw [h2, map_div₀, hvu, div_one]
    exact hin u hvu.le
  have hvξ : v ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add v _ _).trans (max_le hvξ1.le (by simp))
  have hpow : ∀ j : ℕ, v (ξ ^ j - 1) < 1 := by
    intro j
    have h3 : ξ ^ j - 1 = (∑ i ∈ Finset.range j, ξ ^ i) * (ξ - 1) := (geom_sum_mul ξ j).symm
    rw [h3, map_mul]
    have h4 : v (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 :=
      Valuation.map_sum_le v (fun i _ => by rw [map_pow]; exact pow_le_one' hvξ i)
    calc v (∑ i ∈ Finset.range j, ξ ^ i) * v (ξ - 1) ≤ 1 * v (ξ - 1) := mul_le_mul_left h4 _
      _ = v (ξ - 1) := one_mul _
      _ < 1 := hvξ1
  set S := ∑ i ∈ Finset.range N, ξ ^ i with hS
  have hSN : S - (N : Ω) = ∑ i ∈ Finset.range N, (ξ ^ i - 1) := by
    rw [hS, Finset.sum_sub_distrib]; simp
  have hvSN : v (S - (N : Ω)) < 1 := by
    rw [hSN]; exact Valuation.map_sum_lt v one_ne_zero (fun i _ => hpow i)
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hvN] at hvSN
    exact lt_irrefl _ hvSN
  have hmul : S * (ξ - 1) = 0 := by rw [hS, geom_sum_mul, hξN, sub_self]
  have hξ1 : ξ = 1 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hS0
    · exact sub_eq_zero.mp h
  have : g u = u := by
    rw [hξ, div_eq_one_iff_eq hu0] at hξ1; exact hξ1
  rw [hgu, hu] at this
  exact (div_left_inj' hc).mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
section
noncomputable section

namespace GlobalTheory

open IsLocalRing Polynomial TensorProduct

theorem ker_includeRight_residueField_le_jacobson (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] :
    RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) ≤
      (⊥ : Ideal B).jacobson := by
  intro x hx
  apply mem_jacobson_bot_of_forall_isMaximal
  intro n hn
  haveI := hn
  have hc := comap_eq_maximalIdeal_of_finite (R := R) n
  let φ : ResidueField R →ₐ[R] B ⧸ n :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R (B ⧸ n)) fun a ha => by
      rw [Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
        ← Ideal.mem_comap, hc]
      exact ha
  let ψ := Algebra.TensorProduct.lift φ (Ideal.Quotient.mkₐ R n) fun _ _ => Commute.all _ _
  have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] x) = Ideal.Quotient.mk n x := by
    simp [ψ]
  have h0 : (1 : ResidueField R) ⊗ₜ[R] x = 0 := by
    simpa using RingHom.mem_ker.mp hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, h0, map_zero]

theorem includeRight_residueField_surjective (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] :
    Function.Surjective (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) := by
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  exact Algebra.TensorProduct.includeRight_surjective B hs

theorem isUnit_of_isUnit_one_tmul_residueField (R : Type*) {B : Type*} [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B] {x : B}
    (hx : IsUnit ((1 : ResidueField R) ⊗ₜ[R] x)) : IsUnit x := by
  apply isUnit_of_isUnit_mk_of_le_jacobson (ker_includeRight_residueField_le_jacobson R B)
  let e := Ideal.quotientKerAlgEquivOfSurjective (includeRight_residueField_surjective R B)
  have he : e (Ideal.Quotient.mk _ x) = (1 : ResidueField R) ⊗ₜ[R] x := rfl
  have h := hx.map e.symm
  rwa [← he, AlgEquiv.symm_apply_apply] at h

theorem isLocalRing_of_isLocalRing_residueField_tensor (R B : Type*) [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    [IsLocalRing (ResidueField R ⊗[R] B)] : IsLocalRing B := by
  haveI : Nontrivial B := (includeRight_residueField_surjective R B).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((1 : ResidueField R) ⊗ₜ[R] x) with h | h
  · exact Or.inl (isUnit_of_isUnit_one_tmul_residueField R h)
  · right
    apply isUnit_of_isUnit_one_tmul_residueField R
    rwa [TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]

theorem existsUnique_idempotent_lift_quotient (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    {c : S ⧸ (maximalIdeal R).map (algebraMap R S)} (hc : IsIdempotentElem c) :
    ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  refine existsUnique_idempotent_lift_of_henselian R (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective ?_ hc
  rw [Ideal.mk_ker]
  exact map_maximalIdeal_le_jacobson_of_finite R S

theorem bijective_baseChange_residueField_of_etale (R A B : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Module.Finite R B] :
    Function.Bijective fun f : A →ₐ[R] B ↦
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f := by
  have hG := bijective_algHom_comp_of_etale_of_henselian R (A := A)
    (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B)
    (includeRight_residueField_surjective R B) (ker_includeRight_residueField_le_jacobson R B)
  have key : ∀ f : A →ₐ[R] B,
      ((Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f).restrictScalars
        R).comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeRight.comp f := by
    intro f
    ext a
    simp
  refine ⟨fun f g hfg => ?_, fun h => ?_⟩
  · apply hG.1
    dsimp only at hfg ⊢
    rw [← key f, ← key g, hfg]
  · obtain ⟨f, hf⟩ := hG.2 ((h.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    refine ⟨f, ?_⟩
    dsimp only at hf ⊢
    apply Algebra.TensorProduct.ext'
    intro a b
    have hb : Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f
        ((1 : ResidueField R) ⊗ₜ[R] b) = h ((1 : ResidueField R) ⊗ₜ[R] b) := by
      have := congrArg (fun φ : A →ₐ[R] ResidueField R ⊗[R] B => φ b) hf
      simpa using this
    have hab : a ⊗ₜ[R] b = a • ((1 : ResidueField R) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hab, map_smul, map_smul, hb]

theorem etale_adjoinRoot_of_isUnit_derivative {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic)
    (h : IsUnit (AdjoinRoot.mk f f.derivative)) : Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (↑u⁻¹ : AdjoinRoot f)
  have h1 : AdjoinRoot.mk f (derivative f * p - 1) = 0 := by
    rw [map_sub, map_mul, hp, ← hu, Units.mul_inv, map_one, sub_self]
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_zero.mp h1
  let P : StandardEtalePair R :=
    ⟨f, hf, 1, p, -q, 0, by rw [pow_zero]; linear_combination hq⟩
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by
    simp [P]
  let e2 : AdjoinRoot f ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot f) (Localization.Away (AdjoinRoot.mk P.f P.g)) _
      hunit).restrictScalars R
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e2.symm)

theorem exists_etale_lift_of_isSeparable.{u} (R : Type u) (L : Type*) [CommRing R] [IsLocalRing R]
    [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
    [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      IsLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField R) L
  have hsep : (minpoly (ResidueField R) pb.gen).Separable :=
    Algebra.IsSeparable.isSeparable _ pb.gen
  have hmon : (minpoly (ResidueField R) pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  obtain ⟨f, hfmap, hfdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ hs _)) hmon
  haveI hfin : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  letI : Algebra R L :=
    ((algebraMap (ResidueField R) L).comp (algebraMap R (ResidueField R))).toAlgebra
  haveI : IsScalarTower R (ResidueField R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : Polynomial.aeval pb.gen f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap (ResidueField R), hfmap, minpoly.aeval]
  let g : AdjoinRoot f →ₐ[R] L := AdjoinRoot.liftAlgHom f (Algebra.ofId R L) pb.gen hroot
  let ψ : ResidueField R ⊗[R] AdjoinRoot f →ₐ[ResidueField R] L :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) g fun _ _ => Commute.all _ _
  have hψroot : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.root f) = pb.gen := by
    simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsurjψ : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← pb.adjoin_gen_eq_top, Algebra.adjoin_le_iff,
      Set.singleton_subset_iff]
    exact (AlgHom.mem_range ψ).mpr ⟨_, hψroot⟩
  let bT := Algebra.TensorProduct.basis (ResidueField R) (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Finite (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) :=
    Module.Finite.of_basis bT
  have hdim : Module.finrank (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) =
      Module.finrank (ResidueField R) L := by
    rw [Module.finrank_eq_card_basis bT, Fintype.card_fin, AdjoinRoot.powerBasis'_dim, pb.finrank,
      ← pb.natDegree_minpoly, Polynomial.natDegree_eq_of_degree_eq hfdeg]
  have hinjψ : Function.Injective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := ψ.toLinearMap)).mpr
      hsurjψ
  let e := AlgEquiv.ofBijective ψ ⟨hinjψ, hsurjψ⟩
  haveI : Nontrivial (ResidueField R ⊗[R] AdjoinRoot f) := hsurjψ.nontrivial
  haveI : IsLocalRing (ResidueField R ⊗[R] AdjoinRoot f) :=
    IsLocalRing.of_surjective' e.symm.toRingEquiv.toRingHom e.symm.surjective
  have hloc : IsLocalRing (AdjoinRoot f) := isLocalRing_of_isLocalRing_residueField_tensor R _
  have hder : IsUnit (AdjoinRoot.mk f (derivative f)) := by
    apply isUnit_of_isUnit_one_tmul_residueField R
    have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f)) =
        Polynomial.aeval pb.gen (derivative (minpoly (ResidueField R) pb.gen)) := by
      rw [← hfmap, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
      simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    have h2 : IsUnit (e ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f))) := by
      rw [show e _ = ψ _ from rfl, h1, isUnit_iff_ne_zero]
      exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
    simpa using h2.map e.symm
  haveI := etale_adjoinRoot_of_isUnit_derivative hf hder
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, hfin, inferInstance, hloc, ⟨e⟩⟩

theorem exists_etale_lift_of_etale.{u, v} (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R]
    [CommRing E] [Algebra (ResidueField R) E] [Algebra.Etale (ResidueField R) E] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] E) := by
  obtain ⟨I, hI, Ai, _, _, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField R) E).mp inferInstance
  have H : ∀ i, ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ IsLocalRing A ∧
        Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] Ai i) := fun i => by
    haveI := (hAi i).1
    haveI := (hAi i).2
    exact exists_etale_lift_of_isSeparable R (Ai i)
  choose A hA1 hA2 hfin het _ hiso using H
  have := Fintype.ofFinite I
  classical
  refine ⟨Π i, A i, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R (ResidueField R) (ResidueField R) A).trans
    ((AlgEquiv.piCongrRight fun i => (hiso i).some).trans e.symm)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfForallMemDiscreteValuationSubring
section
open IsLocalRing

namespace GlobalTheory

theorem isIntegral_of_forall_mem_discreteValuationSubring : ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] (t : K), (∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ s : S, algebraMap S K s ∈ V) → t ∈ V) → IsIntegral S t := by
  intro S K _ _ _ _ _ _ t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType S K := .of_isLocalization K (nonZeroDivisors S)
  have hic : IsIntegrallyClosedIn (integralClosure S K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure S K) K)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure S K).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_of_valuationSubring (R := S) W
    (fun r => hW ((integralClosure S K).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  exact (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left ht0 (ht V h1 h2)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCupProductCongruence
section
open GlobalTheory.K5

namespace GlobalTheory.CuspCup

theorem cup_identity {R : Type*} [CommRing R]
    (N P A B A' B' i m ag bg bh bgh qg qh qgh zg zh zgh x gx gy ghy e₁ e₂ tb tq tz : R)
    (h₁ : P * ag - A * qg - B * zg - (gx - x) = N * e₁)
    (h₂ : P * bh - A' * qh - B' * zh - (ghy - gy) = N * e₂)
    (hb : bgh = bg + bh - N * tb) (hq : qgh = qg + qh - N * tq) (hz : zgh = zg + zh - N * tz)
    (hi : 2 * i = 1 + N * m) :
    (P * ag) * (P * bh) + (A * B' - B * A') * (zg * qh) -
      ((gx * (P * bh) - (A * qh + B * zh) * ghy - i * (A * A') * qh ^ 2 - A * B' * (qh * zh)
          - i * (B * B') * zh ^ 2)
        - (x * (P * bgh) - (A * qgh + B * zgh) * ghy - i * (A * A') * qgh ^ 2
          - A * B' * (qgh * zgh) - i * (B * B') * zgh ^ 2)
        + (x * (P * bg) - (A * qg + B * zg) * gy - i * (A * A') * qg ^ 2 - A * B' * (qg * zg)
          - i * (B * B') * zg ^ 2)) =
    N * (e₁ * (P * bh) + (A * qg + B * zg) * e₂ - P * x * tb + (A * tq + B * tz) * ghy
      - m * (A * A') * (qg * qh) - m * (B * B') * (zg * zh)
      + i * (A * A') * (2 * tq * (qg + qh) - N * tq ^ 2)
      + A * B' * (tq * (zg + zh) + tz * (qg + qh) - N * (tq * tz))
      + i * (B * B') * (2 * tz * (zg + zh) - N * tz ^ 2)) := by
  subst hb hq hz
  linear_combination (P * bh) * h₁ + (A * qg + B * zg) * h₂
    - (A * A' * (qg * qh) + B * B' * (zg * zh)) * hi

theorem exists_val_add {R : Type*} [CommRing R] (p n : ℕ) (hp : p ≠ 0) (u v : ZMod (p ^ n)) :
    ∃ t : ℕ, (((u + v).val : ℕ) : R) = (u.val : R) + (v.val : R) - (p : R) ^ n * (t : R) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp⟩
  refine ⟨(u.val + v.val) / p ^ n, ?_⟩
  have h := Nat.mod_add_div (u.val + v.val) (p ^ n)
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → R) h
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] at h'
  linear_combination h'

theorem exists_half (p n : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ i m : ℤ, 2 * i = 1 + (p : ℤ) ^ n * m := by
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two h2).pow (n := n)
  refine ⟨k + 1, 1, ?_⟩
  have := congrArg (Nat.cast : ℕ → ℤ) hk
  push_cast at this
  rw [this]; ring

theorem cup_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (H : Subgroup (Gal p Ω)) (n c : ℕ)
  (a b lz lq : Gal p Ω → ZMod (p ^ n)) (A B A' B' : Ω),
  (∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g + a h) → (∀ g ∈ H, ∀ h ∈ H, b (g * h) = b g + b h) →
  (∀ g ∈ H, ∀ h ∈ H, lz (g * h) = lz g + lz h) → (∀ g ∈ H, ∀ h ∈ H, lq (g * h) = lq g + lq h) →
  (∀ g ∈ H, g A = A ∧ g B = B ∧ g A' = A' ∧ g B' = B') →
  IsInt (p := p) ((p : Ω) ^ c * A) → IsInt (p := p) ((p : Ω) ^ c * B) →
  IsInt (p := p) ((p : Ω) ^ c * A') → IsInt (p := p) ((p : Ω) ^ c * B') →
  (∀ g, ∃ S : Finset Ω, ∀ h : Gal p Ω, (∀ x ∈ S, h x = g x) → a h = a g ∧ b h = b g ∧ lz h = lz g ∧ lq h = lq g) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * A * ((lq g).val : Ω) - (p : Ω) ^ c * B * ((lz g).val : Ω)) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((b g).val : Ω) - (p : Ω) ^ c * A' * ((lq g).val : Ω) - (p : Ω) ^ c * B' * ((lz g).val : Ω)) →
  Cob2 n H (fun g h => (p : Ω) ^ (4 * c) * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ (4 * c) * (A * B' - B * A') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p hp h2 Ω _ _ H n c a b lz lq A B A' B' _ hb hz hq hfix iA iB iA' iB' hlc ⟨x, ix, hx⟩
    ⟨y, iy, hy⟩
  classical
  obtain ⟨i, m, him⟩ := exists_half p n hp.out h2
  have him' : 2 * (i : Ω) = 1 + (p : Ω) ^ n * (m : Ω) := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) him
  let R := integralClosure (O0 p) Ω
  have key : ∀ v : Ω, IsInt (p := p) v ↔ v ∈ R := fun v => Iff.rfl
  have hmap : ∀ (g : Gal p Ω) (v : Ω), v ∈ R → g v ∈ R := fun g v hv =>
    IsIntegral.map g.toAlgHom hv
  rw [key] at iA iB iA' iB' ix iy
  have iP : (p : Ω) ^ c ∈ R := pow_mem (natCast_mem R p) c
  have iN : (p : Ω) ^ n ∈ R := pow_mem (natCast_mem R p) n
  have i2 : (2 : Ω) ∈ R := ofNat_mem R 2
  refine ⟨fun k => ((p : Ω) ^ c) ^ 2 * (x * ((p : Ω) ^ c * ((b k).val : Ω))
    - ((p : Ω) ^ c * A * ((lq k).val : Ω) + (p : Ω) ^ c * B * ((lz k).val : Ω)) * k y
    - (i : Ω) * (((p : Ω) ^ c * A) * ((p : Ω) ^ c * A')) * ((lq k).val : Ω) ^ 2
    - ((p : Ω) ^ c * A) * ((p : Ω) ^ c * B') * (((lq k).val : Ω) * ((lz k).val : Ω))
    - (i : Ω) * (((p : Ω) ^ c * B) * ((p : Ω) ^ c * B')) * ((lz k).val : Ω) ^ 2), ⟨?_, ?_⟩, ?_⟩
  · intro k
    rw [key]
    have h1 := hmap k y iy
    generalize (p : Ω) ^ c * A = A₁ at *
    generalize (p : Ω) ^ c * B = B₁ at *
    generalize (p : Ω) ^ c * A' = A₂ at *
    generalize (p : Ω) ^ c * B' = B₂ at *
    generalize (p : Ω) ^ c = P at *
    repeat' first
      | assumption
      | exact natCast_mem R _
      | exact intCast_mem R _
      | apply mul_mem
      | apply sub_mem
      | apply add_mem
      | apply pow_mem
  · intro k
    obtain ⟨S, hS⟩ := hlc k
    refine ⟨insert y S, fun h hh => ⟨0, (key _).2 (zero_mem R), ?_⟩⟩
    obtain ⟨-, e1, e2, e3⟩ := hS h (fun x hx => hh x (Finset.mem_insert_of_mem hx))
    have e4 := hh y (Finset.mem_insert_self _ _)
    simp only [e1, e2, e3, e4, sub_self, mul_zero]
  · intro g hg h hh
    obtain ⟨e₁, ie₁, h₁⟩ := hx g hg
    obtain ⟨e₂, ie₂, h₂⟩ := hy h hh
    obtain ⟨fA, fB, fA', fB'⟩ := hfix g hg
    have h₂' := congrArg g h₂
    simp only [map_sub, map_mul, map_pow, map_natCast, fA', fB'] at h₂'
    obtain ⟨tb, htb⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (b g) (b h)
    obtain ⟨tq, htq⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lq g) (lq h)
    obtain ⟨tz, htz⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lz g) (lz h)
    rw [← hb g hg h hh] at htb
    rw [← hq g hg h hh] at htq
    rw [← hz g hg h hh] at htz
    have main := cup_identity _ _ _ _ _ _ _ _ _ ((b g).val : Ω) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      h₁ h₂' htb htq htz him'
    refine ⟨_, ?_, Eq.trans ?_
      ((congrArg (fun t => ((p : Ω) ^ c) ^ 2 * t) main).trans (mul_left_comm _ _ _))⟩
    swap
    · simp only [map_sub, map_add (f := _), map_mul, map_pow, map_natCast, map_intCast, fA, fB, fA', fB',
        AlgEquiv.mul_apply]
      ring
    · rw [key] at ie₁ ie₂ ⊢
      have h1 := hmap g _ (hmap h y iy)
      have h3 := hmap g _ ie₂
      clear main h₁ h₂ h₂' hx hy htb htq htz him'
      generalize (p : Ω) ^ c * A = A₁ at *
      generalize (p : Ω) ^ c * B = B₁ at *
      generalize (p : Ω) ^ c * A' = A₂ at *
      generalize (p : Ω) ^ c * B' = B₂ at *
      generalize (p : Ω) ^ c = P at *
      generalize (p : Ω) ^ n = N at *
      repeat' first
        | assumption
        | exact natCast_mem R _
        | exact intCast_mem R _
        | apply mul_mem
        | apply sub_mem
        | apply add_mem
        | apply pow_mem

end GlobalTheory.CuspCup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesAlgebraicConstant
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem addVal_eq_zero_of_root_sub_const {k K : Type} [Field k] [Field K] (φ : k →+* K)
    (v : AddValuation K (WithTop ℤ)) (hv : ∀ a : k, a ≠ 0 → v (φ a) = 0) (f : K) (P : k[X])
    (hP : P ≠ 0) (hf : eval₂ φ f P = 0) (c : k) (h : f - φ c ≠ 0) : v (f - φ c) = 0 := by
  letI : Algebra k K := φ.toAlgebra
  have h1 : IsAlgebraic k f := ⟨P, hP, hf⟩
  have h2 : IsAlgebraic k (f - φ c) := h1.sub (isAlgebraic_algebraMap c)
  haveI : Valuation.IsTrivialOn k (AddValuation.toValuation v) := ⟨fun a ha => hv a ha⟩
  by_contra hne
  exact Valuation.transcendental_of_ne_one k (v := AddValuation.toValuation v) _ h hne h2

theorem laurentSeries_eq_C_of_root : ∀ (k : Type) [Field k] (f : LaurentSeries k),
    (∃ P : k[X], P ≠ 0 ∧ eval₂ HahnSeries.C f P = 0) → ∃ c : k, f = HahnSeries.C c := by
  rintro k _ f ⟨P, hP, hf⟩
  refine ⟨f.coeff 0, ?_⟩
  by_contra hne
  have h : f - HahnSeries.C (f.coeff 0) ≠ 0 := sub_ne_zero.2 hne
  have h0 := addVal_eq_zero_of_root_sub_const (K := LaurentSeries k) HahnSeries.C
    (HahnSeries.addVal ℤ k) (fun a ha => by
      rw [HahnSeries.addVal_apply_of_ne (HahnSeries.C_ne_zero ha), HahnSeries.order_C]; rfl)
    f P hP hf _ h
  rw [HahnSeries.addVal_apply] at h0
  have h1 := HahnSeries.coeff_orderTop_ne (g := 0) h0
  apply h1
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSpanEigenOfBaseChangeEigenStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_eigen_of_baseChange_eigen' : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
  (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]), (∀ s, ∀ b ∈ B, g s b ∈ B) →
  ∀ x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype),
  (∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) →
  x ∈ Submodule.span (PadicAlgCl l) {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  first | exact @GlobalTheory.mem_span_eigen_of_baseChange_eigen | exact GlobalTheory.mem_span_eigen_of_baseChange_eigen | (intros; apply GlobalTheory.mem_span_eigen_of_baseChange_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotientStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω), 1 ≤ n → IsPrimitiveRoot ζ (l ^ n) → A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_zeta_sub_one_pow_totient | exact GlobalTheory.valuation_zeta_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_zeta_sub_one_pow_totient <;> assumption)
end

