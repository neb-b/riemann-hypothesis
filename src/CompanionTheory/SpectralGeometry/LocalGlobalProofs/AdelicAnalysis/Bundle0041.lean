module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0040
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianDiagonalizeOverReducedTensor
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicOrbitOfRationalTuple
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransUC

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext a b
  simp [cT, sigR_inclR]

theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, hR, hform, gramE, hE, ratTup, JR, map_sum, map_mul, sigR_inclR]

theorem gramE_herm (σ : E →ₐ[F] E) (hσ : ∀ x : E, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → E) (a b : Fin n) :
    σ (gramE σ J X b a) = gramE σ J X a b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramE, hE, hform, map_sum, map_mul, RingHom.coe_coe, AlgHom.commutes]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hσ, hJ]
  ring

theorem inclR_algebraMap (d : F) :
    inclR (E := E) R (algebraMap F E d) = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  change (1 : R) ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d) ⊗ₜ[F] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

end SlopeTestRemainingChoices

theorem trans_uc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR R σ J Y = (gramE σ J X).map (inclR R) →
    ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  intro F E _ _ _ _ _ σ hCM R _ _ uc n M J hJ X Y hdet hY
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  have hT : IsHermND σ (gramE σ J X) := ⟨gramE_herm σ hσ J hJ.1 X, hdet⟩
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian F E σ hCM n _ hT
  set G : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g : Matrix (Fin n) (Fin n) E).map (inclR R) with hG
  set G' : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (inclR R) with hG'
  have hGG' : G * G' = 1 := by
    have h1 : (g : Matrix (Fin n) (Fin n) E) * ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 :=
      Units.mul_inv g
    have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map (inclR (F := F) R)) h1
    simp only [Matrix.map_mul] at h2
    rw [hG, hG', h2, Matrix.map_one _ (map_zero _) (map_one _)]
  let D' : Fin n → Rˣ := fun i => Units.map (algebraMap F R).toMonoidHom (D i)
  have hdiag : cT (sigR R σ) G * (gramE σ J X).map (inclR R) * G =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [hG, cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hg]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [D', inclR_algebraMap]
    · simp [Matrix.diagonal_apply_ne _ hab, hab]
  have P := fun (Z : Fin n → Fin M → R ⊗[F] E) (H H' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =>
    _root_.GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z H H'
  have hX1 : gramR R σ J (rmul R (ratTup R X) G) =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [(P _ G G).1, gramR_ratTup, hdiag]
  have hY1 : gramR R σ J (rmul R Y G) = gramR R σ J (rmul R (ratTup R X) G) := by
    rw [hX1, (P _ G G).1, hY, hdiag]
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag F E σ hCM R uc M J hJ n D' _ _ hX1 hY1
  refine ⟨h, ?_⟩
  have undo : ∀ Z : Fin n → Fin M → R ⊗[F] E, rmul R (rmul R Z G) G' = Z := by
    intro Z
    rw [(P Z G G').2.1, hGG', (P Z G G').2.2.1]
  calc actW R σ J h (ratTup R X)
      = actTup R (HA.mat R σ J h) (rmul R (rmul R (ratTup R X) G) G') := by
        rw [undo]; rfl
    _ = rmul R (actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G)) G' :=
        (P _ G' G').2.2.2 _
    _ = rmul R (rmul R Y G) G' := by
        rw [show actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G) = rmul R Y G from hh]
    _ = Y := undo Y

end GlobalTheory.CompanionTheory.SW.TransUC
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRing
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittTuples

theorem exists_actW_eq_of_gramR_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = gramR R σ J Y → IsUnit (gramR R σ J X).det → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ n X Y hXY hdet
  have hσ := HermTop.sigma_sigma hCM
  have hS : cT (sigR R σ) (gramR R σ J X) = gramR R σ J X := by
    ext a b
    exact HermTop.gramR_mem (R := R) hσ hJ.1 X a b
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.exists_diagonal_congr F E σ hCM R n _ hS hdet
  have hgram : ∀ Z : Fin n → Fin M → R ⊗[F] E, gramR R σ J (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J Z * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    fun Z => (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g 1).1
  have hX' := (hgram X).trans hg
  have hY' : gramR R σ J (rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      gramR R σ J (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    rw [hgram, hgram, hXY]
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag F E σ hCM R (GlobalTheory.CompanionTheory.SW.unitChoice_of_isArtinianRing_isReduced R) M J hJ n D _ _ hX' hY'
  refine ⟨h, ?_⟩
  have hk : actTup R (HA.mat R σ J h) (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      rmul R (actTup R (HA.mat R σ J h) X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J X g 1).2.2.2 _
  have he : rmul R (actW R σ J h X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := hk.symm.trans hh
  have hcancel : ∀ Z : Fin n → Fin M → R ⊗[F] E,
      rmul R (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Z := by
    intro Z
    have h1 := GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [h1.2.1, Units.mul_inv, h1.2.2.1]
  rw [← hcancel (actW R σ J h X), he, hcancel]

end GlobalTheory.CompanionTheory.SW.WittTuples
end

