module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCmAdeleTensorEquivMixedFinite
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.AdeleCM

theorem exists_adele_tensor_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∃ Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (1 ⊗ₜ[F] x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (ε : AdeleRing (𝓞 F) F), ε.1 = 0 → ε.2 v = 1 → (∀ v', v' ≠ v → ε.2 v' = 0) → (Φ (ε ⊗ₜ[F] 1)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (ε ⊗ₜ[F] 1)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AdeleRing (𝓞 F) F)ˣ, Φ ((a : AdeleRing (𝓞 F) F) ⊗ₜ[F] 1) = x := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI t1 : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI t2 : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  letI t3 : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  obtain ⟨e, he, -, hec⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  obtain ⟨ι, hι1, hι2, hι3⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιc := GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  obtain ⟨θ, hθ1, hθc, hθ3⟩ := _root_.GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace F E σ hF hE h2 hσ
  have he1 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).1 = a.1 ⊗ₜ[F] x :=
    fun a x => (he _).1.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  have he2 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).2 = a.2 ⊗ₜ[F] x :=
    fun a x => (he _).2.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  let Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E) :=
    e.trans (RingEquiv.prodCongr θ ι)
  have hΦ : ∀ z, Φ z = (θ (e z).1, ι (e z).2) := fun z => rfl
  refine ⟨Φ, fun x => ?_, fun y => ?_, fun v ε h0 h1 hv => ⟨?_, fun P => ?_⟩, ?_, fun x hx2 hx1 => ?_⟩
  · rw [hΦ, he1, he2]
    exact Prod.ext (hθ1 x) (hι1 x)
  · rw [← (he y).2]
    exact hι2 (e y).2
  · rw [hΦ, he1, h0]
    simp
  · rw [hΦ, he2]
    exact hι3 v ε.2 h1 hv P
  · have : (Φ.symm : _ → _) = fun w => e.symm (θ.symm w.1, ι.symm w.2) := rfl
    rw [this]
    exact hec.comp ((hθc.comp continuous_fst).prodMk (hιc.comp continuous_snd))
  · obtain ⟨a, ha⟩ := hθ3 (Units.map (RingHom.fst (mixedSpace E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x) hx1
    refine ⟨⟨((a : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)),
      ((a⁻¹ : (InfiniteAdeleRing F)ˣ), (1 : FiniteAdeleRing (𝓞 F) F)), ?_, ?_⟩, ?_⟩
    · exact Prod.ext a.mul_inv (mul_one _)
    · exact Prod.ext a.inv_mul (mul_one _)
    · rw [hΦ, he1, he2]
      refine Prod.ext ha ?_
      rw [hx2]
      exact map_one ι

end GlobalTheory.AdeleCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsRealEmbeddingEqHom
section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isReal_embedding_eq_hom {F : Type} [Field F] (σ : F →+* ℝ) :
    ∃ (v : InfinitePlace F) (hv : v.IsReal), InfinitePlace.embedding_of_isReal hv = σ := by
  have hr : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hv : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hr, rfl⟩
  refine ⟨_, hv, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hr]
  rfl

theorem hasseNorm : GlobalTheory.Published.HasseNorm := by
  intro K L _ _ _ _ _ hG hC a ha hf hi
  refine _root_.GlobalTheory.CNorm.np_cyclic K L hG hC a ha ⟨hf, fun alg => ?_⟩
  obtain ⟨v, hv, hσ⟩ := exists_isReal_embedding_eq_hom (algebraMap K ℝ)
  let φ : v.Completion →ₐ[K] ℝ :=
    { InfinitePlace.Completion.extensionEmbeddingOfIsReal hv with
      commutes' := fun x => by
        rw [← hσ]
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
          Algebra.algebraMap_self_apply]
        exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x) }
  exact (_root_.GlobalTheory.CNorm.tnorm_baseChange K L).1 v.Completion ℝ φ a (hi v)

end GlobalTheory.CNorm
end

