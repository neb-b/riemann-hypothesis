module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicAlgebraHilbertNinety
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FirstApprox

private theorem tensorProduct_congr_refl_pow_tmul_lemma {O O' κ : Type} [CommRing O] [CommRing O']
    [Algebra O O'] [CommRing κ] [Algebra O κ] (τ : O' ≃ₐ[O] O') (j : ℕ) (k : κ) (x : O') :
    (Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ ^ j) (k ⊗ₜ[O] x) =
      k ⊗ₜ[O] (τ ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ', AlgEquiv.mul_apply,
      Algebra.TensorProduct.congr_apply]
    exact Algebra.TensorProduct.map_tmul ..

theorem res_fixed (O O' κ : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing κ] [Algebra O κ] (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hs : Function.Surjective (algebraMap O κ)) (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1) (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (htr : ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) (z : κ ⊗[O] O') (hz : Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ z = z) : z ∈ Set.range (algebraMap κ (κ ⊗[O] O')) := by
  obtain ⟨a, ha⟩ := htr
  obtain ⟨σ, hσ⟩ : ∃ σ : κ ⊗[O] O' ≃ₐ[κ] κ ⊗[O] O',
      σ = Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ := ⟨_, rfl⟩
  rw [← hσ] at hz
  have hpow : ∀ (j : ℕ) (k : κ) (x : O'), (σ ^ j) (k ⊗ₜ[O] x) = k ⊗ₜ[O] (τ ^ j) x := by
    intro j k x
    rw [hσ]
    exact tensorProduct_congr_refl_pow_tmul_lemma τ j k x
  have hzfix : ∀ j : ℕ, (σ ^ j) z = z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hz]
  have htrace : ∀ t : κ ⊗[O] O',
      ∑ j ∈ Finset.range ℓ, (σ ^ j) t ∈ Set.range (algebraMap κ (κ ⊗[O] O')) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k x =>
      have hfx : τ (∑ j ∈ Finset.range ℓ, (τ ^ j) x) = ∑ j ∈ Finset.range ℓ, (τ ^ j) x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        have e := (Finset.sum_range_succ' (fun j => (τ ^ j) x) ℓ).symm.trans
          (Finset.sum_range_succ (fun j => (τ ^ j) x) ℓ)
        rw [hτ, pow_zero] at e
        rw [← add_right_cancel e]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ', AlgEquiv.mul_apply]
      obtain ⟨c, hc⟩ := hfix _ hfx
      refine ⟨c • k, ?_⟩
      simp only [hpow]
      rw [← TensorProduct.tmul_sum, ← hc, Algebra.algebraMap_eq_smul_one (A := O') c,
        ← TensorProduct.smul_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨u₁, hu₁⟩ := h₁
      obtain ⟨u₂, hu₂⟩ := h₂
      exact ⟨u₁ + u₂, by simp only [map_add (f := _), Finset.sum_add_distrib, hu₁, hu₂]⟩
  have key : ∑ j ∈ Finset.range ℓ, (σ ^ j) ((1 ⊗ₜ[O] a) * z) = z := by
    simp only [map_mul, hpow, hzfix]
    rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ha, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← key]
  exact htrace _

theorem res_compare (O O' R κ A : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ] [CommRing A] [Algebra O A] [Algebra κ A] [IsScalarTower O κ A] (π : R →ₐ[O] A) (hπ : Function.Surjective π) : ∃ ψ : O' ⊗[O] R →+* (κ ⊗[O] O') ⊗[κ] A, Function.Surjective ψ ∧ RingHom.ker ψ ≤ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (RingHom.ker π) ∧ (∀ x : R, ψ ((Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x) = Algebra.TensorProduct.includeRight (π x)) ∧ ∀ (f : O' →ₐ[O] O') (s : O' ⊗[O] R), ψ (Algebra.TensorProduct.map f (AlgHom.id O R) s) = Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id κ κ) f) (AlgHom.id κ A) (ψ s) := by
  let ψ : O' ⊗[O] R →+* (κ ⊗[O] O') ⊗[κ] A :=
    (((Algebra.TensorProduct.comm κ A (κ ⊗[O] O') :
        A ⊗[κ] (κ ⊗[O] O') →+* (κ ⊗[O] O') ⊗[κ] A).comp
      ((Algebra.TensorProduct.cancelBaseChange O κ κ A O').symm :
        A ⊗[O] O' →+* A ⊗[κ] (κ ⊗[O] O'))).comp
      (Algebra.TensorProduct.comm O O' A : O' ⊗[O] A →+* A ⊗[O] O')).comp
      (Algebra.TensorProduct.map (AlgHom.id O O') π : O' ⊗[O] R →+* O' ⊗[O] A)
  have hψ : ∀ t, ψ t = Algebra.TensorProduct.comm κ A (κ ⊗[O] O')
      ((Algebra.TensorProduct.cancelBaseChange O κ κ A O').symm
        (Algebra.TensorProduct.comm O O' A (Algebra.TensorProduct.map (AlgHom.id O O') π t))) :=
    fun t => rfl
  have hψt : ∀ (x : O') (r : R), ψ (x ⊗ₜ[O] r) = (1 ⊗ₜ[O] x) ⊗ₜ[κ] π r := by
    intro x r
    rw [hψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.comm_tmul]
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨t, ht⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id O O') π Function.surjective_id hπ
      ((Algebra.TensorProduct.comm O O' A).symm ((Algebra.TensorProduct.cancelBaseChange O κ κ A O')
        ((Algebra.TensorProduct.comm κ A (κ ⊗[O] O')).symm w)))
    refine ⟨t, ?_⟩
    rw [hψ, ht]
    simp only [AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]
  · intro t ht
    have hm : Algebra.TensorProduct.map (AlgHom.id O O') π t = 0 := by
      rw [RingHom.mem_ker, hψ] at ht
      simpa using ht
    have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id O O') π) =
        Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (RingHom.ker π) := by
      rw [Algebra.TensorProduct.map_ker _ _ Function.surjective_id hπ,
        (RingHom.injective_iff_ker_eq_bot (AlgHom.id O O')).mp Function.injective_id, Ideal.map_bot,
        bot_sup_eq]
    rw [← hker]
    exact hm
  · intro x
    simp only [Algebra.TensorProduct.includeRight_apply, hψt, ← Algebra.TensorProduct.one_def]
  · intro f s
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hψt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem main : PositivityTheory.Rg.Tf.Loc.N1 → ∀ (O O' R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing R] [Algebra O R] [Module.Finite O R] (ℓ : ℕ) (τ : O' ≃ₐ[O] O'), 0 < ℓ → τ ^ ℓ = 1 → (∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) → (∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) → (∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) → ∀ r : Rˣ, ∃ s : (O' ⊗[O] R)ˣ, (∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) (s : O' ⊗[O] R)) - (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (r : R) ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson := by
  intro hNI O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual htr r
  obtain ⟨J, hJ⟩ : ∃ J : Ideal R, J = (⊥ : Ideal R).jacobson := ⟨_, rfl⟩
  have hmJ : Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ J :=
    hJ ▸ (GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le O R).1
  letI : Algebra (IsLocalRing.ResidueField O) (R ⧸ J) :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O (R ⧸ J)) fun c hc => by
      first
        | exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmJ (Ideal.mem_map_of_mem _ hc))
        | (rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
           exact hmJ (Ideal.mem_map_of_mem _ hc))).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (R ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : Module.Finite O (R ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap (Ideal.Quotient.mkₐ_surjective O J)
  haveI : Module.Finite (IsLocalRing.ResidueField O) (R ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O _ _
  have hrad : J.IsRadical := by
    rw [hJ]
    exact Ideal.radical_le_jacobson.trans Ideal.jacobson_idem.le
  haveI : IsReduced (R ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp hrad
  haveI : Module.Finite (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O') :=
    Module.Finite.base_change O _ O'
  have hres : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) :=
    IsLocalRing.residue_surjective
  obtain ⟨x, y, hxy⟩ := hdual
  have hτ' : Algebra.TensorProduct.congr
      (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
      τ ^ ℓ = 1 := by
    refine AlgEquiv.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k w => rw [tensorProduct_congr_refl_pow_tmul_lemma, hτ]; rfl
    | add t₁ t₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  have hfix' : ∀ z : IsLocalRing.ResidueField O ⊗[O] O',
      Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ z = z →
      z ∈ Set.range (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O')) :=
    fun z hz => GlobalTheory.CompanionTheory.FirstApprox.res_fixed O O'
      (IsLocalRing.ResidueField O) ℓ τ hres hℓ hτ hfix htr z hz
  have hdual' : ∃ x' y' : Fin ℓ → IsLocalRing.ResidueField O ⊗[O] O', ∀ j < ℓ,
      ∑ i, x' i * (Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ ^ j) (y' i) = if j = 0 then 1 else 0 := by
    refine ⟨fun i => 1 ⊗ₜ[O] x i, fun i => 1 ⊗ₜ[O] y i, fun j hj => ?_⟩
    simp only [tensorProduct_congr_refl_pow_tmul_lemma, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← TensorProduct.tmul_sum, hxy j hj]
    split_ifs
    · exact (Algebra.TensorProduct.one_def).symm
    · exact TensorProduct.tmul_zero _ _
  obtain ⟨sb, hsb⟩ := hNI (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O') (R ⧸ J) ℓ
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O) τ)
    hℓ hτ' hfix' hdual' (Units.map (Ideal.Quotient.mk J).toMonoidHom r)
  obtain ⟨ψ, hψs, hψk, hψi, hψe⟩ := GlobalTheory.CompanionTheory.FirstApprox.res_compare O O' R
    (IsLocalRing.ResidueField O) (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hkerπ : RingHom.ker (Ideal.Quotient.mkₐ O J) = J := by
    ext w
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hkerπ] at hψk
  obtain ⟨s0, hs0⟩ := hψs ↑sb
  obtain ⟨t0, ht0⟩ := hψs ↑(sb⁻¹)
  have hunit : IsUnit s0 := by
    have h1 : s0 * t0 - 1 ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) J :=
      hψk (by rw [RingHom.mem_ker, map_sub, map_mul, hs0, ht0, Units.mul_inv, map_one, sub_self])
    have h2 : IsUnit (1 + (s0 * t0 - 1)) :=
      GlobalTheory.CompanionTheory.JacUnit.main O O' R _ (by rw [← hJ]; exact h1)
    rw [show (1 : O' ⊗[O] R) + (s0 * t0 - 1) = s0 * t0 by ring] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hmap : ∀ j : ℕ, Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))
      ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) =
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ ^ j).toAlgHom := by
    intro j
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k w =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, tensorProduct_congr_refl_pow_tmul_lemma]
    | add t₁ t₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hJ]
  refine hψk ?_
  rw [RingHom.mem_ker, map_sub, map_prod]
  simp_rw [hψe]
  rw [hψi, hs0, sub_eq_zero]
  refine Eq.trans ?_ (hsb.trans ?_)
  · refine Finset.prod_congr rfl fun j _ => ?_
    exact congrArg (fun g : (IsLocalRing.ResidueField O ⊗[O] O') →ₐ[IsLocalRing.ResidueField O]
        (IsLocalRing.ResidueField O ⊗[O] O') =>
      Algebra.TensorProduct.map g (AlgHom.id (IsLocalRing.ResidueField O) (R ⧸ J)) (sb : _)) (hmap j)
  · first
      | rfl
      | simp [Units.coe_map]

end GlobalTheory.CompanionTheory.FirstApprox
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKill
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.BigStep

def gens {A : Type} [CommRing A] (𝓔 : Set (Set (MvPolynomial (Fin 3) A))) :
    Set (MvPolynomial (𝓔 × Fin 3) A) :=
  {f | ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
    f = MvPolynomial.rename (fun t => (E, t)) q}

theorem exists_kill (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A)
    {𝓔 : Set (Set (MvPolynomial (Fin 3) A))}
    (hfin : ∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 →
      ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
        ∀ E ∈ J, Pt (algebraMap A B) E)
    (F : Finset (MvPolynomial (𝓔 × Fin 3) A)) (hF : (F : Set _) ⊆ gens 𝓔) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ τ : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B, ∀ g ∈ F, τ g = 0 := by
  classical
  have hg : ∀ g : {g // g ∈ F}, ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
      g.1 = MvPolynomial.rename (fun t => (E, t)) q := fun g => hF g.2
  choose Eg qg hq hgq using hg
  obtain ⟨B₁, i1, i2, hP, hC, hpt⟩ := hfin (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    (Set.finite_range _) (by rintro _ ⟨g, rfl⟩; exact (Eg g).2)
  have hpt' : ∀ E : 𝓔, ∃ y : Fin 3 → B₁, E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1) →
      ∀ q ∈ E.1, MvPolynomial.eval₂ (algebraMap A B₁) y q = 0 := by
    intro E
    by_cases h : E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    · obtain ⟨y, hy⟩ := hpt _ h
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose y hy using hpt'
  refine ⟨B₁, i1, i2, hP, hC, MvPolynomial.aeval (fun v => y v.1 v.2), ?_⟩
  intro g hg
  have e := hgq ⟨g, hg⟩
  simp only at e
  rw [e, MvPolynomial.aeval_rename, MvPolynomial.aeval_def]
  exact hy _ ⟨⟨g, hg⟩, rfl⟩ _ (hq ⟨g, hg⟩)

theorem big_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → (∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ (∀ E ∈ 𝓔, Pt (algebraMap A B) E) ∧ ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → (∀ E ∈ 𝓔, Pt x E) → ∃ y : B →+* T, y.comp (algebraMap A B) = x := by
  classical
  intro p _ A _ r 𝓔 hA hfin
  have hpS : (p : MvPolynomial (𝓔 × Fin 3) A) = 0 := by
    have := congrArg (algebraMap A (MvPolynomial (𝓔 × Fin 3) A)) hA.char
    simpa using this
  obtain ⟨B, instB, i, hQ⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (MvPolynomial (𝓔 × Fin 3) A)
    (Ideal.span (gens 𝓔)) hpS
  letI instAB : Algebra A B := (i.comp MvPolynomial.C).toAlgebra
  let iA : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B := { i with commutes' := fun _ => rfl }
  refine ⟨B, instB, instAB, hQ.pf, ?_, ?_, ?_⟩
  · apply GlobalTheory.CompanionTheory.CovCmp.cov_of_solv
    intro m n a c hS
    obtain ⟨k, s, hs⟩ := GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow p A (MvPolynomial (𝓔 × Fin 3) A) B iA
      (Ideal.span (gens 𝓔)) m n a c hA.char hQ hS
    have hT := fun t => Submodule.mem_span_finite_of_mem_span (hs t)
    choose G hGs hGm using hT
    obtain ⟨B₁, i1, i2, hP, hC, τ, hτ⟩ := exists_kill p r hfin (Finset.univ.biUnion G) (by
      intro g hg
      obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hg)
      exact hGs t ht)
    refine ⟨B₁, i1, i2, hC,
      GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow p A B₁ m n k a c hP ⟨fun j => τ (s j), fun t => ?_⟩⟩
    have hle : Ideal.span (G t : Set (MvPolynomial (𝓔 × Fin 3) A)) ≤ RingHom.ker τ :=
      Ideal.span_le.2 fun g hg =>
        hτ g (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, Finset.mem_coe.1 hg⟩)
    have h0 := hle (hGm t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, map_sum, AlgHom.commutes, sub_eq_zero] at h0
    simpa only [map_smul] using h0
  · intro E hE
    refine ⟨fun t => i (MvPolynomial.X ((⟨E, hE⟩ : 𝓔), t)), fun q hq => ?_⟩
    have hz : i (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 :=
      (hQ.ker _).2 ⟨0, by
        have h : MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q ∈ Ideal.span (gens 𝓔) :=
          Ideal.subset_span ⟨⟨E, hE⟩, q, hq, rfl⟩
        simpa using h⟩
    have hi : i = MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v)) :=
      MvPolynomial.ringHom_ext (by simp) (by simp)
    have hz' : MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v))
        (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 := by
      rw [← hi]; exact hz
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename] at hz'
    exact hz'
  · intro T _ x hT hpts
    have hpts' : ∀ E : 𝓔, ∃ y : Fin 3 → T, ∀ q ∈ E.1, MvPolynomial.eval₂ x y q = 0 :=
      fun E => hpts E.1 E.2
    choose y hy using hpts'
    have hle : Ideal.span (gens 𝓔) ≤
        RingHom.ker (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨E, q, hq, rfl⟩
      show MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2) _ = 0
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
      exact hy E q hq
    obtain ⟨ψ, hψ, -⟩ := GlobalTheory.CompanionTheory.PerfectRing.pq_lift p _ B T i _
      (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) hQ hT (fun g hg => hle hg)
    refine ⟨ψ, RingHom.ext fun a => ?_⟩
    have := RingHom.congr_fun hψ (MvPolynomial.C a)
    show ψ (i (MvPolynomial.C a)) = x a
    simpa using this

end GlobalTheory.CompanionTheory.BigStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRetraction
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovRoot

theorem exists_retraction {A : Type} [CommRing A] (P : Polynomial A) (hP : P.Monic)
    (hd : 0 < P.natDegree) : ∃ ρ : AdjoinRoot P →ₗ[A] A, ρ 1 = 1 := by
  let b := AdjoinRoot.powerBasis' hP
  have h0 : 0 < b.dim := by simpa [b] using hd
  refine ⟨b.basis.coord ⟨0, h0⟩, ?_⟩
  have h1 : b.basis ⟨0, h0⟩ = 1 := by simp
  change b.basis.repr 1 ⟨0, h0⟩ = 1
  rw [← h1, b.basis.repr_self]
  simp

theorem cov_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A)
    (P : Polynomial A), Pf p A → P.Monic → 0 < P.natDegree →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ x : B, Polynomial.aeval x P = 0 := by
  intro p _ A _ r P hA hP hd
  have hpS : (p : AdjoinRoot P) = 0 := by
    have := congrArg (algebraMap A (AdjoinRoot P)) hA.char
    simpa using this
  obtain ⟨T, _, i, hq⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (AdjoinRoot P) ⊥ hpS
  letI : Algebra A T := (i.comp (algebraMap A (AdjoinRoot P))).toAlgebra
  let i' : AdjoinRoot P →ₐ[A] T := { i with commutes' := fun _ => rfl }
  have hq' : PQ p (i' : AdjoinRoot P →+* T) ⊥ := hq
  refine ⟨T, inferInstance, inferInstance, hq.pf, ?_, i' (AdjoinRoot.root P), ?_⟩
  · refine GlobalTheory.CompanionTheory.CovCmp.cov_of_solv p A T r fun m n a c hs => ?_
    refine ⟨A, inferInstance, inferInstance, GlobalTheory.CompanionTheory.CovMono.cov_self p A r, ?_⟩
    obtain ⟨k, s, hs'⟩ := _root_.GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow p A (AdjoinRoot P) T i' ⊥ m n a c hA.char hq' hs
    refine _root_.GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow p A A m n k a c hA ?_
    obtain ⟨ρ, hρ⟩ := exists_retraction P hP hd
    have hρa : ∀ x : A, ρ (algebraMap A (AdjoinRoot P) x) = x := fun x => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hρ, smul_eq_mul, mul_one]
    refine ⟨fun j => ρ (s j), fun t => ?_⟩
    have h := sub_eq_zero.mp ((Ideal.mem_bot).mp (hs' t))
    have h2 := congrArg ρ h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hρa] at h2
    simpa using h2
  · rw [Polynomial.aeval_algHom_apply]
    have : Polynomial.aeval (AdjoinRoot.root P) P = 0 := by
      simp [AdjoinRoot.aeval_eq]
    rw [this, map_zero]

end GlobalTheory.CompanionTheory.CovRoot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLaw
section
noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisExt

variable {G : Type} [Group G]

theorem ext_mul {K P : Subgroup G} {f : G → ℝ} (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (hfK : ∀ p ∈ P, p ∈ K → f p = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) :
    PositivityTheory.RgEis.ext K P f (p * k) = f p := by
  have hex : ∃ c : K, p * k * (c : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [PositivityTheory.RgEis.ext, dite_eq_left hex]
  have hcP : p * k * (hex.choose : G)⁻¹ ∈ P := hex.choose_spec
  have hq : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ P := P.mul_mem (P.inv_mem hp) hcP
  have hqK : p⁻¹ * (p * k * (hex.choose : G)⁻¹) ∈ K := by
    have he : p⁻¹ * (p * k * (hex.choose : G)⁻¹) = k * (hex.choose : G)⁻¹ := by group
    rw [he]
    exact K.mul_mem hk (K.inv_mem hex.choose.2)
  have h0 := hfK _ hq hqK
  have hsplit := hadd p hp _ hq
  rw [mul_inv_cancel_left] at hsplit
  rw [hsplit, h0, add_zero]

theorem extLaw : ExtLaw := by
  intro G _ _ _ _ Γ K P f hK hP hIwa hadd hfc hfK hfΓ
  have hval : ∀ p ∈ P, ∀ k ∈ K, PositivityTheory.RgEis.ext K P f (p * k) = f p :=
    fun p hp k hk => ext_mul hadd hfK hp hk
  have hone : ∀ p ∈ P, PositivityTheory.RgEis.ext K P f p = f p := by
    intro p hp
    simpa using hval p hp 1 K.one_mem
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hval⟩
  · intro p hp g
    obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
    rw [← mul_assoc, hval _ (P.mul_mem hp hq) k hk, hval q hq k hk, hone p hp, hadd p hp q hq]
  · intro g k hk
    obtain ⟨q, hq, k', hk', rfl⟩ := hIwa g
    rw [mul_assoc, hval q hq _ (K.mul_mem hk' hk), hval q hq k' hk']
  · intro γ hγ hγP
    rw [hone γ hγP]
    exact hfΓ γ hγP hγ
  · open Pointwise in
    · rw [continuous_iff_isClosed]
      intro C hC
      have hset : PositivityTheory.RgEis.ext K P f ⁻¹' C = ((P : Set G) ∩ f ⁻¹' C) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          obtain ⟨q, hq, k, hk, rfl⟩ := hIwa g
          have hC' : PositivityTheory.RgEis.ext K P f (q * k) ∈ C := hg
          rw [hval q hq k hk] at hC'
          exact Set.mem_mul.mpr ⟨q, ⟨hq, hC'⟩, k, hk, rfl⟩
        · intro hg
          obtain ⟨q, ⟨hq, hqC⟩, k, hk, rfl⟩ := Set.mem_mul.mp hg
          show PositivityTheory.RgEis.ext K P f (q * k) ∈ C
          rw [hval q hq k hk]
          exact hqC
      rw [hset]
      exact (hfc.preimage_isClosed_of_isClosed hP hC).mul_right_of_isCompact hK

end GlobalTheory.CompanionTheory.RgEisExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportProductQuotientStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_product_quotient : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite → (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite → (∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) → (∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) → (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  first | exact @GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | exact GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite | (intros; apply GlobalTheory.CompanionTheory.ProdQuotient.support_mul_out_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianTubeTransformContinuousStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_tube_transform_continuous : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (G : T → ℂ × ℂ → X) (x : ℝ × ℝ), Continuous (fun p : (ℝ × ℝ) × T => G p.2 (pt x p.1)) → (∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ, ‖G g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → Continuous (fun p : (ℝ × ℝ) × T => phi (G p.2) x p.1) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous | exact GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCardStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrices_card : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ n : ℕ, Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | exact GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg <;> assumption)
end

