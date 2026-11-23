module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProduct
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaRatGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem exists_eval_ne (ψ : Polynomial E) (hψ : ψ ≠ 0) : ∃ t : F, ψ.eval (algebraMap F E t) ≠ 0 := by
  classical
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have hinf : (Set.range (algebraMap F E)).Infinite := Set.infinite_range_of_injective (algebraMap F E).injective
  obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hinf.exists_notMem_finset ψ.roots.toFinset
  refine ⟨t, fun h => hy ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hψ]
  exact h

theorem hyp1 : ∀ ψ : Polynomial E, (∀ (Ω : Type) [Field Ω] (φ : E →+* Ω), φ 1 = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit ((1 : E) * ψ.eval (algebraMap F E t) + (1 - 1)) := by
  intro ψ h
  have hψ : ψ ≠ 0 := by simpa using h E (RingHom.id E) (map_one _)
  obtain ⟨t, ht⟩ := exists_eval_ne (F := F) ψ hψ
  exact ⟨t, by simpa using ht⟩

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ρ : E, ρ ≠ 0 ∧ σ ρ = -ρ := by
  have hne : σ ≠ AlgHom.id F E := by
    intro hσ
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hσ] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    exact hne (AlgHom.ext hc)
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, invol h]
  ring

variable (F) in
theorem incM_mul {m n k : Type} [Fintype n] (A : Matrix m n E) (B : Matrix n k E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

variable (F) in
theorem incM_dbl {β : Type} (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext i j
  cases i <;> cases j <;> simp [incM, dbl]

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (A : Matrix m n E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA_inclR]

variable (F) in
theorem incM_transpose {m n : Type} (A : Matrix m n E) : (incM F A)ᵀ = incM F Aᵀ := rfl

variable (F) in
theorem incM_diag {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 1 := by
  simp [incM, Matrix.fromRows_map]

variable (F) in
theorem incM_nabla {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (-1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1) := by
  simp [incM, Matrix.fromRows_map, Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]

theorem incM_inj {m n : Type} {A B : Matrix m n E} (h : incM F A = incM F B) : A = B := by
  ext i j
  exact inclR_inj (congrFun (congrFun h i) j)

def up (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p : UG σ (dbl JB)) : UG (cA σ) (dbl (incM F JB)) :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) p.1, by
    have hp : ((p.1 : Matrix _ _ E))ᵀ * dbl JB * (p.1 : Matrix _ _ E).map σ = dbl JB := p.2
    show (incM F (p.1 : Matrix _ _ E))ᵀ * dbl (incM F JB) * (incM F (p.1 : Matrix _ _ E)).map (cA σ) = dbl (incM F JB)
    rw [incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul, hp]⟩

theorem up_mul (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p q : UG σ (dbl JB)) :
    up σ JB (p * q) = up σ JB p * up σ JB q :=
  Subtype.ext (map_mul _ _ _)

theorem down (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (g : UG (cA σ) (dbl (incM F JB)))
    (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E)
    (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∃ g₁ : UG σ (dbl JB), ((g₁ : GL (Fin b ⊕ Fin b) E) : Matrix _ _ E) = g₀ ∧ g = up σ JB g₁ := by
  have hdet : IsUnit g₀.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu : IsUnit (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).det :=
      (Matrix.isUnit_iff_isUnit_det (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))).mp (Units.isUnit _)
    have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := (RingHom.map_det _ _).symm
    rw [hg, e, h0, map_zero, isUnit_zero_iff] at hu
    exact zero_ne_one (inclR_inj (F := F) (E := E) (by rw [map_zero, map_one]; exact hu))
  have hu : IsUnit g₀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hmem : hu.unit ∈ UG σ (dbl JB) := by
    show (hu.unit : Matrix _ _ E)ᵀ * dbl JB * (hu.unit : Matrix _ _ E).map σ = dbl JB
    rw [IsUnit.unit_spec]
    have h2 : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ * dbl (incM F JB) *
        ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F JB) := g.2
    rw [hg, incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul] at h2
    exact incM_inj h2
  refine ⟨⟨hu.unit, hmem⟩, IsUnit.unit_spec hu, Subtype.ext (Units.ext ?_)⟩
  rw [hg]
  exact (congrArg (incM F) (IsUnit.unit_spec hu)).symm

end GlobalTheory.ThetaRatGen

namespace GlobalTheory.ThetaRatGen

theorem gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b : ℕ) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 → ∀ (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F g₀ → ∃ (p q p' : UG (cA σ) (dbl (incM F JB))) (p₀ q₀ p₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (t s t' : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀ ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀' ∧ ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (AE F E)) ∧ g = p * q * p' := by
  intro F E _ _ _ _ _ σ hσ b JB ε hJ hdet g g₀ hg
  haveI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  obtain ⟨g₁, -, rfl⟩ := down σ JB g g₀ hg
  set G : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := (g₁.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hG
  set H : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E :=
    ((g₁.1⁻¹ : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hH
  set Nt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 (-1) with hNt
  set N : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 (-1) with hN
  set Dt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 1 with hDt
  set Δ : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 1 with hΔ
  have hGH : G * H = 1 := by rw [hG, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNN : Nt * N = (2 : E) • 1 := by
    rw [hNt, hN, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have e2' : Δ * Dt + N * Nt = (2 : E) • 1 := GlobalTheory.BigCell.e2
  have hPQ : (Nt * G * N) * ((4 : E)⁻¹ • (Nt * H * N)) + (Nt * G * Δ) * ((4 : E)⁻¹ • (Dt * H * N)) = 1 := by
    calc _ = (4 : E)⁻¹ • (Nt * G * (Δ * Dt + N * Nt) * H * N) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
          abel
      _ = 1 := by
          rw [e2']
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          rw [show Nt * G * H * N = Nt * N by rw [Matrix.mul_assoc Nt G H, hGH, Matrix.mul_one], hNN, smul_smul]
          norm_num
  obtain ⟨x₀, hx₀⟩ := _root_.GlobalTheory.exists_corner_unit_of_right_inverse (F := F) (1 : E) (mul_one 1) hyp1 _ _ _ _ hPQ
  obtain ⟨ρ, hρ0, hρ⟩ := exists_anti hσ
  have hJ' : (JB.map (σ : E →+* E))ᵀ = ((ε : ℤ) : E) • JB := by
    ext i j
    simp [hJ]
  obtain ⟨x, hxS, hx⟩ := _root_.GlobalTheory.exists_conj_skew_det_unit_of_avoidance (F := F) (σ : E →+* E) (invol hσ) (fun t => σ.commutes t) 1 hyp1 ρ
    (isUnit_iff_ne_zero.mpr hρ0) hρ JB ε hJ' (isUnit_iff_ne_zero.mpr hdet) _ _ x₀ hx₀
  obtain ⟨p, hpΔ, hcorner⟩ := _root_.GlobalTheory.siegel_unip_corner (R₀ := F) σ JB x hxS
  have hunit : IsUnit (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E) *
      (((g₁ * p : UG σ (dbl JB)) : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      Matrix.fromRows (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E)).det := by
    rw [Subgroup.coe_mul, Units.val_mul, hcorner]
    have hx' : IsUnit (Nt * G * N + Nt * G * Δ * x).det := by simpa using hx
    exact hx'
  obtain ⟨p₀, q₀, t, s, hp₀, hq₀, hpq⟩ := GlobalTheory.BigCell.bigCell_factor F E σ (Fin b) JB (g₁ * p) hunit
  have hg₁ : g₁ = p₀ * q₀ * p⁻¹ := eq_mul_inv_of_mul_eq hpq
  have hpinv : ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
    have h1 : (p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) =
        (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
      exact hpΔ.trans (Matrix.mul_one _)
    calc _ = ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
          ((p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
            (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E)) := by rw [h1]
      _ = diagCols (Fin b) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.one_mul]
  refine ⟨up σ JB p₀, up σ JB q₀, up σ JB p⁻¹, p₀.1, q₀.1, (p⁻¹).1,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) s, 1, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (incM F) hp₀
    rw [incM_mul, incM_mul, incM_diag] at h
    exact h
  · have h := congrArg (incM F) hq₀
    rw [incM_mul, incM_mul, incM_nabla] at h
    exact h
  · have h := congrArg (incM F) hpinv
    rw [incM_mul, diagCols, incM_diag] at h
    exact h.trans (Matrix.mul_one _).symm
  · rw [hg₁, up_mul, up_mul]

end GlobalTheory.ThetaRatGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.LocGlobRing

noncomputable def pbIso (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    pullback g (Spec.map (CommRingCat.ofHom (algebraMap A O))) ≅ Spec (CommRingCat.of (O ⊗[A] X)) :=
  pullback.congrHom hg rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso A O X

theorem pbIso_inv_fst (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : X →ₐ[A] O ⊗[A] X).toRingHom) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_snd]

theorem pbIso_inv_snd (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : O →+* O ⊗[A] X)) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_fst]

end GlobalTheory.LocGlobRing

namespace GlobalTheory.LocGlobRing

theorem square (A B C O : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing O] [Algebra A B] [Algebra A C] [Algebra A O]
    (φ : B →ₐ[A] C)
    (hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (h₁ h₂) :
    (pbIso A C O _ hC).inv ≫ pullback.map (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) (𝟙 _) h₁ h₂ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) ≫ (pbIso A B O _ rfl).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pbIso_inv_fst, Category.assoc, pbIso_inv_fst,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pbIso_inv_snd, Category.assoc, pbIso_inv_snd,
      ← Spec.map_comp]
    congr 1
    ext x
    simp

end GlobalTheory.LocGlobRing

theorem GlobalTheory.LocGlobRing.main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C), (∀ (O : Type) [CommRing O] [Algebra A O], SH O → IndEt A O → Eqv R (spMap (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) F) → Eqv R (spMap φ.toRingHom) F := by
  intro R _ F hF A B C _ _ _ _ _ φ hyp
  have hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks R F hF (Spec (CommRingCat.of C)) (Spec (CommRingCat.of B)) (Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hInd, rfl⟩ := GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine A O s hs
  have h := @hyp O _ inst hSH hInd
  have eb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  rw [← Iso.hom_inv_id_assoc (GlobalTheory.LocGlobRing.pbIso A C O _ hC) (pullback.map _ _ _ _ _ _ _ _ _),
    GlobalTheory.LocGlobRing.square A B C O φ hC, Functor.map_comp, Functor.map_comp]
  exact (eb.2.1 _ _ _ _ _).1 (eb.1 _ _ _ inferInstance) ((eb.2.1 _ _ _ _ _).1 h (eb.1 _ _ _ inferInstance))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegralStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) → (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  first | (exact @GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (exact GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (intros; apply GlobalTheory.EtC.CechDescHInv.hInv_of_integral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem rat_mem_adicCompletionIntegers_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} (b : Module.Basis κ ℚ C) (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul [Fintype κ] (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem isIntB_mul_star_eventually : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (σ : C →+* Cᵐᵒᵖ) (κ : Type)
    (b : Module.Basis κ ℚ C), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) ∧
      (∀ y, IsIntB v b y → IsIntB v b (starT σ (v.adicCompletion ℚ) y).unop) := by
  intro C _ _ _ σ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (σ (b t.1)).unop t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and hs)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, hsv⟩ := hv
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : κ → (v.adicCompletion ℚ ⊗[ℚ] C)ᵐᵒᵖ), (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : v.adicCompletion ℚ ⊗[ℚ] C ≃+ _).symm f Finset.univ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul b v y, map_sum, hu, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.AdicSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegral
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem eventually_int_of_isCompact {p : ℕ} (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ K, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨s, hs⟩ := hK.elim_directed_cover
    (fun s : Finset (AwayP p) => {z : AfP p | ∀ v ∉ s, AfP.eval v z ∈ v.1.adicCompletionIntegers ℚ})
    (fun s => RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ s))
    (fun y _ => by
      have h : {v : AwayP p | ¬ AfP.eval v y ∈ v.1.adicCompletionIntegers ℚ}.Finite := y.2
      refine Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc))
    (fun s t => ⟨s ∪ t, fun y hy v hv => hy v fun h => hv (Finset.mem_union_left _ h),
      fun y hy v hv => hy v fun h => hv (Finset.mem_union_right _ h)⟩)
  rw [Filter.eventually_cofinite]
  refine (s.finite_toSet).subset fun v hv => ?_
  by_contra hvs
  exact hv fun a ha => hs ha v hvs

theorem repr_map_eval {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (y : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem cptInt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), piV G v '' Ω ⊆ IntV G v := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set bA := Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C) with hbA
  have hrep : ∀ i, Continuous (fun y : AfP p ⊗[ℚ] G.C => bA.repr y i) := fun i => by
    have := IsModuleTopology.continuous_of_linearMap (R := AfP p) (bA.coord i)
    exact this
  have hg1 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hg2 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hg3 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hg4 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  have h1 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg1))
  have h2 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg2))
  have h3 := eventually_int_of_isCompact _ (hΩ.image hg3)
  have h4 := eventually_int_of_isCompact _ (hΩ.image hg4)
  filter_upwards [h1, h2, h3, h4] with v hv1 hv2 hv3 hv4
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e : ((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv1 i _ ⟨g, hg, rfl⟩
  · have e : (((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv2 i _ ⟨g, hg, rfl⟩
  · exact hv3 _ ⟨g, hg, rfl⟩
  · exact hv4 _ ⟨g, hg, rfl⟩

end GlobalTheory.OrbFinAf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOneTmulAdicIntegralCoords
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_finset_isIntB_one_tmul (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type)
    (b : Module.Basis κ ℚ M) (x : M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  have hfin : (⋃ i ∈ ((b.repr x).support : Set κ), HeightOneSpectrum.Support ℤ (b.repr x i)).Finite :=
    (b.repr x).support.finite_toSet.biUnion fun i _ => HeightOneSpectrum.Support.finite ℤ (b.repr x i)
  refine ⟨hfin.toFinset, fun v hv i => ?_⟩
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  by_cases hi : b.repr x i = 0
  · rw [hi, map_zero]; exact zero_mem _
  · have h1 : v ∉ HeightOneSpectrum.Support ℤ (b.repr x i) := fun h =>
      hv (hfin.mem_toFinset.2 (Set.mem_biUnion (Finsupp.mem_support_iff.2 hi) h))
    have h2 : v.valuation ℚ (b.repr x i) ≤ 1 := not_lt.1 h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b.repr x i)
    rw [← h3] at h2
    convert h2 using 2
    rfl

end GlobalTheory.AdicSpan
end

