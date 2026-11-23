module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionTheta
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem exists_ratLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), ∃ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁

  have hD : ∀ p q, symp (cA σ) (-1) (incM F X.J) (incM F W.J) p q =
      (M.co.e p).1 ⬝ᵥ (M.co.e q).2 - (M.co.e q).1 ⬝ᵥ (M.co.e p).2 := M.co.form
  have hcross := GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic F E σ n d d₁ X.J W.J H' (fun u => (hH.orth u).1)
  have hiso : ∀ a ∈ lagr M M₁ H', ∀ b ∈ lagr M M₁ H', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    intro a ha b hb
    obtain ⟨u, hu, z, hz, hea⟩ := ha
    obtain ⟨u', hu', z', hz', heb⟩ := hb
    have ea : hat a = M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [← hea, LinearEquiv.apply_symm_apply]
    have eb : hat b = M.co.e (u' + incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) := by
      rw [← heb, LinearEquiv.apply_symm_apply]
    have h1 := GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic F E σ n d d₁ X.J W.J H' hH.xx u hu u' hu'
    have h2 := hcross u' hu' z
    have h3 := hcross u hu z'
    have h4 := GlobalTheory.T.symplectic_form_restricted_plane F E σ n d d₁ X.J W.J W₁.J H'.ι hH.gram z z'
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W₁.J) z z' at h4
    rw [M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_zero] at h4
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = 0 at h4
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u' = 0 at h1
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) u' = 0 at h2
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) u = 0 at h3
    rw [hD] at h1 h2 h3 h4
    apply (AdeleRing.algebraMap_injective (𝓞 F) F)
    have ha1 : (fun i => algebraMap F (AF F) (a.1 i)) = (hat a).1 := rfl
    have ha2 : (fun i => algebraMap F (AF F) (a.2 i)) = (hat a).2 := rfl
    have hb1 : (fun i => algebraMap F (AF F) (b.1 i)) = (hat b).1 := rfl
    have hb2 : (fun i => algebraMap F (AF F) (b.2 i)) = (hat b).2 := rfl
    rw [RingHom.map_dotProduct, RingHom.map_dotProduct]
    simp only [Function.comp_def]
    rw [ha1, ha2, hb1, hb2, ea, eb]
    simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination h1 + h2 - h3 + h4
  refine ⟨lagr M M₁ H', hiso, ?_, ?_⟩
  ·
    have hrat := _root_.GlobalTheory.MixedLagr.ratCoord_linear_injective F E σ n d X W M hP.good.rat
    have hrat₁ := _root_.GlobalTheory.MixedLagr.ratCoord_linear_injective F E σ n d₁ X W₁ M₁ hP₁.good.rat
    obtain ⟨f, hf, hfe⟩ := hrat
    obtain ⟨f₁, hf₁, hfe₁⟩ := hrat₁
    have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
    obtain ⟨K, hK, hKz⟩ := _root_.GlobalTheory.MixedLagr.rat_first_zero_dim F E σ n d₁ X W₁ M₁ h2 f₁ hf₁ hfe₁
    have hinj := mul_transpose_injective F E σ n d d₁ W.J W₁.J H'.ι hH.gram
      (_root_.GlobalTheory.SkewGram.det_ne_zero F E σ B d₁ W₁ r₁ s₁ hP₁.skew)
    refine le_antisymm ?_ ?_
    · exact GlobalTheory.T.lagrangian_dimension_bound F _ _ hiso
    · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact _root_.GlobalTheory.MixedLagr.le_finrank_lagr F E σ n d d₁ X W W₁ M M₁ H' h2 hH.rank hH.xy (fun u => (hH.orth u).2) hinj f hf hfe K hK hKz
  ·
    intro t w hw
    obtain ⟨u, ⟨y, rfl⟩, z, hz, he⟩ := hw
    have ew : hat w = M.co.e (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [← he, LinearEquiv.apply_symm_apply]
    refine ⟨Matrix.vecMulVec (t • y) (incV F H'.x), ⟨t • y, rfl⟩, t • z, by simp [hz], fun φ => ?_⟩
    have h0 := hcross _ ⟨t • y, rfl⟩ (t • z)
    change symp (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)
      (Matrix.vecMulVec (t • y) (incV F H'.x)) = 0 at h0
    rw [hD] at h0
    rw [Darboux.rho, Darboux.rho, schr_comp, ← map_add (f := _)]
    have hs : (M.co.e (Matrix.vecMulVec (t • y) (incV F H'.x))).1 ⬝ᵥ
          (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)).2 -
        (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)).1 ⬝ᵥ
          (M.co.e (Matrix.vecMulVec (t • y) (incV F H'.x))).2 = 0 := by linear_combination -h0
    rw [hs, mul_zero, AddChar.map_zero_eq_one, one_smul]
    have hm : Matrix.vecMulVec (t • y) (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ =
        t • (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [smul_add, Matrix.smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul]
    rw [hm, LinearEquiv.map_smul, ← ew]
    rfl

end GlobalTheory.MixedLagr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneModularCharacter
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.LeviSplit

open Matrix

section Ring

variable {R : Type} [CommRing R] {n n₁ k : ℕ}

end Ring

theorem exists_prod_equiv {G B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group B] [TopologicalSpace B]
    (A T : Subgroup G) (m : B → A) (π : A → B) (hm : Continuous m) (hπ : Continuous π) (hmm : ∀ a b, m (a * b) = m a * m b)
    (hππ : ∀ a b, π (a * b) = π a * π b) (hπm : ∀ b, π (m b) = b) (hTA : T ≤ A) (hT : ∀ a : A, a.1 ∈ T ↔ π a = 1)
    (hc : ∀ τ ∈ T, ∀ b, τ * (m b : G) = m b * τ) : ∃ φ : T × B ≃ₜ* A, ∀ p, (φ p : G) = p.1 * m p.2 := by
  let π' := MonoidHom.mk' π hππ
  have h1 : ∀ τ : T, π' ⟨τ, hTA τ.2⟩ = 1 := fun τ => (hT ⟨τ, hTA τ.2⟩).1 τ.2
  have h2 : ∀ b, π' (m b) = b := hπm
  have h3 : ∀ (τ : T) b, π' (⟨τ, hTA τ.2⟩ * m b) = b := fun τ b => by rw [map_mul, h1, h2, one_mul]
  refine ⟨{ toFun := fun p => ⟨p.1, hTA p.1.2⟩ * m p.2
            invFun := fun a => (⟨(a * (m (π' a))⁻¹ : A), (hT _).2 (show π' _ = 1 by rw [map_mul, map_inv, h2, mul_inv_cancel])⟩, π' a)
            left_inv := fun p => Prod.ext (Subtype.ext ?_) (h3 _ _)
            right_inv := fun a => Subtype.ext ?_
            map_mul' := fun p q => Subtype.ext ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun p => rfl⟩
  · simp only [h3]
    simp
  · simp
  · simp only [Prod.fst_mul, Prod.snd_mul, hmm, Subgroup.coe_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (q.1 : G), hc _ q.1.2, mul_assoc]
  · exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).mul (hm.comp continuous_snd)
  · exact ((continuous_subtype_val.comp (continuous_id.mul (hm.comp hπ).inv)).subtype_mk _).prodMk hπ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}





open GlobalTheory.StdPar GlobalTheory.SiegelSet in
theorem mem_leviOne {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}
    {g : GAd σ J} : g ∈ leviOne σ J X Y S ↔ ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols Y k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols X k) ((GlobalTheory.Doubling.absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
  simp only [leviOne, levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
  exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩,
    fun k hk => (h k hk).2.2⟩⟩


end GlobalTheory.LeviSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDeriv
section
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem slice_word_fderivs (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type)
    [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)))
    (vs : List (κ → mixedEmbedding.mixedSpace F)) :
    (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y))) := by
  induction vs with
  | nil => exact ⟨rfl, hΦ⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd : Differentiable ℝ (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [h1]; exact h2.differentiable (by simp)
    refine ⟨?_, ?_⟩
    · funext x
      simp only [List.map_cons, List.foldr_cons]
      rw [word_cons, _root_.GlobalTheory.WeilL2Words.dS_adeleJoin_eq F κ ψ ℓ hψ _ y hd (v, 0) x, h1]
      simp
    · simp only [List.foldr_cons]
      exact (h2.fderiv_right (by simp)).clm_apply contDiff_const

theorem slice_word_mul_fderivs : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hΦ u i vs x
  obtain ⟨h1, h2⟩ := slice_word_fderivs F κ ψ ℓ hψ Φ y hΦ vs
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) := by
    let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
      ℓ ∘ₗ ∑ k, (LinearMap.mulRight ℝ (u k)) ∘ₗ LinearMap.proj k
    have hLe : (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) = L := by
      funext x; simp [L, LinearMap.sum_apply]
    rw [hLe]
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => 2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hL)
  suffices H : ∀ i : ℕ,
      (fun x => word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) by
    exact congrFun (H i).1 x
  intro i
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · funext x; simp only [List.replicate_zero, List.nil_append, pow_zero, one_mul]; exact congrFun h1 x
    · simpa using h2
  | succ i ih =>
    obtain ⟨e1, e2⟩ := ih
    have hd : Differentiable ℝ (fun x =>
        word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [e1]; exact e2.differentiable (by simp)
    refine ⟨?_, (hc.pow (i + 1)).mul h2⟩
    funext x
    rw [List.replicate_succ, List.cons_append, word_cons, _root_.GlobalTheory.WeilL2Words.dS_adeleJoin_eq F κ ψ ℓ hψ _ y hd (0, u) x]
    have e1x := congrFun e1 x
    simp only [ContinuousLinearMap.map_zero, zero_add, e1x]
    ring

end GlobalTheory.WeilL2Words
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFractionFieldIsPullbackOfUnramified
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem spec_fraction_field_isPullback_of_unramified : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → IsPullback (spMap (algebraMap W K')) (spMap (algebraMap K K')) (spMap (algebraMap R W)) (spMap (algebraMap R K)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax

  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRW : Function.Injective (algebraMap R W) := by
    rw [IsScalarTower.algebraMap_eq R W K'] at hRK'
    exact Function.Injective.of_comp hRK'

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖW : Irreducible (algebraMap R W ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid W (nonZeroDivisors R)) K' := by
    rw [IsLocalization.iff_of_le_of_exists_dvd (M := Algebra.algebraMapSubmonoid W (nonZeroDivisors R))
      (S := K') (nonZeroDivisors W)]
    · infer_instance
    · rintro _ ⟨r, hr, rfl⟩
      refine mem_nonZeroDivisors_of_ne_zero ?_
      intro h0
      exact nonZeroDivisors.ne_zero hr (hRW (by rw [h0, map_zero]))
    · intro w hw
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hw) hϖW
      refine ⟨algebraMap R W (ϖ ^ n), ⟨ϖ ^ n, mem_nonZeroDivisors_of_ne_zero
        (pow_ne_zero _ hϖ.ne_zero), rfl⟩, ?_⟩
      refine ⟨(↑u⁻¹ : W), ?_⟩
      rw [hu, map_pow, _root_.mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have hpo : Algebra.IsPushout R W K K' :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mp hloc
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_iff_isPushout.mpr hpo)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinates
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealCharF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infPartF_cAF (σ : E →ₐ[F] E) (z : AEF F E) :
    infPartF F E (cAF σ z) = sigR (Ainf F) σ (infPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem conj_theta_tmul_one [IsTotallyReal F] {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val τ w hw θ h a, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem theta_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    (y : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ y) = starRingEnd ℂ (θ y) := by
  haveI : IsTotallyReal F := hσ.1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    have e1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e') := by
      intro e'; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show θ (a ⊗ₜ[F] σ e) = _
    rw [e1 (σ e), e1 e, map_mul, map_mul, map_mul, h.1, h.1, hσ.2.2.2, conj_theta_tmul_one hw h a]
    rfl

theorem theta_infPartF_incAF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (e : E) :
    θ (infPartF F E (incAF F E e)) = τ e := by
  have : infPartF F E (incAF F E e) = (1 : Ainf F) ⊗ₜ[F] e := by
    show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [this, h.1]

theorem theta_fstA_symplOHF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT) :
    θ (fstA F (symplOHF σ JS JT ξ₀ x y) ⊗ₜ[F] (1 : E)) =
      ((τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y))).re : ℂ) := by
  set z := incAF F E ξ₀ * hOF σ JS JT x y with hz
  have h1 : fstA F (symplOHF σ JS JT ξ₀ x y) =
      algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (infPartF F E z) := by
    unfold symplOHF symplOF
    rw [map_mul, AlgHom.commutes, GlobalTheory.HeisLineDiffF.map_trace_tens]
    rfl
  have h2 : ∀ c : Ainf F, c ⊗ₜ[F] (1 : E) = algebraMap (Ainf F) (Ainf F ⊗[F] E) c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h3 : θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
    rw [← IsScalarTower.algebraMap_apply]
    have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    exact this
  have h4 : θ (infPartF F E z) = τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y)) := by
    rw [hz, map_mul, map_mul, theta_infPartF_incAF h]
  rw [h1, h2, map_mul, map_mul, GlobalTheory.SelfDualLatticeCompare.trace_tensor (Ainf F) hσ, map_add (f := _),
    theta_sigR hσ hw h, h3, h4, Complex.add_conj]
  push_cast
  ring

theorem theta_hOF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {tau : InfinitePlace F → (E →+* ℂ)}
    (hw : ∀ w, w.embedding = (tau w).comp (algebraMap F E)) {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)}
    (hθ : IsInfFamF tau θ) {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} (JT : Matrix (Fin nT) (Fin nT) E) (hJS : JS.det ≠ 0)
    (u v : IxF F nS nT → ℂ) (w : InfinitePlace F) :
    θ w (infPartF F E (hOF σ JS JT (iotaVF ι u) (iotaVF ι v))) =
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [GlobalTheory.OrientedChar.map_inv_field _ _ hJS, GlobalTheory.OrientedChar.trace_four]
  unfold hOF
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, infPartF_cAF, theta_sigR hσ (hw w) (hθ w), theta_infPartF_incAF (hθ w),
    iotaVF, Matrix.of_apply, hι.comp, cpt, Matrix.map_apply]

theorem trace_HMF {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (tau : InfinitePlace F → (E →+* ℂ)) (u v : IxF F nS nT → ℂ) :
    star v ⬝ᵥ HMF JS JT ξ₀ tau *ᵥ u = ∑ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) *
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [star_dotProduct_eq]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold HMF
  rw [cpt_blk, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem psi_symplOHF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  haveI : IsTotallyReal F := hσ.1
  have hψ := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end GlobalTheory.RealCharF
end
end

