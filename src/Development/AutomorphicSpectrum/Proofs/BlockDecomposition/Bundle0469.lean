module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationEquivariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatible
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink


open GroundTheory.Global GroundTheory.Global.SemiLocal in
theorem local_restriction_abelianization_artin : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  intro E Ω _ _ _ _ _ w Ωv _ _ _ j hj a σ g hgj hloc L _ _
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨w'⟩ := GroundTheory.Global.IdeleGroup.nonempty_placesOver_of_finite (K := E) (L := L) w
  haveI : IsSepClosed Ωv := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  haveI : Algebra.IsSeparable (w.adicCompletion E) (w'.1.adicCompletion L) := inferInstance
  let ι : w'.1.adicCompletion L →ₐ[w.adicCompletion E] Ωv := IsSepClosed.lift
  set s := restrictAb L (le_maximalAbelianExtension L)
    (artinMap E Ω (GroundTheory.Global.IdeleClassGroup.mk E (IdeleGroup.finiteEmbedding w a))) with hs
  have hres : PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) = s :=
    congrArg (restrictAb L (le_maximalAbelianExtension L))
      ((topologicalAbelianizationEquiv E Ω).apply_symm_apply _)
  have h1 : ∀ l : L, ι (algebraMap L (w'.1.adicCompletion L) (s l)) =
      g (ι (algebraMap L (w'.1.adicCompletion L) l)) := fun l => by
    rw [hs, artinMap_finiteEmbedding_apply L w w' ι a l]
    exact hloc _ _
  rw [hres, PositivityTheory.FamInh.res_toAb]
  letI : Algebra E Ωv := ((algebraMap (w.adicCompletion E) Ωv).comp (algebraMap E (w.adicCompletion E))).toAlgebra
  let m₂ : L →ₐ[E] Ωv :=
    { toRingHom := j.comp (algebraMap L Ω)
      commutes' := fun y => by
        show j (algebraMap L Ω (algebraMap E L y)) = _
        rw [← IsScalarTower.algebraMap_apply]
        exact hj y }
  have hcomp : ∀ y : E, algebraMap L (w'.1.adicCompletion L) (algebraMap E L y) =
      algebraMap (w.adicCompletion E) (w'.1.adicCompletion L) (algebraMap E (w.adicCompletion E) y) := by
    intro y
    rw [← IsScalarTower.algebraMap_apply E L (w'.1.adicCompletion L),
      ← IsScalarTower.algebraMap_apply E (w.adicCompletion E) (w'.1.adicCompletion L)]
  let m₁ : L →ₐ[E] Ωv :=
    { toRingHom := (ι : w'.1.adicCompletion L →+* Ωv).comp (algebraMap L (w'.1.adicCompletion L))
      commutes' := fun y => by
        show ι (algebraMap L (w'.1.adicCompletion L) (algebraMap E L y)) = _
        rw [hcomp, ι.commutes]
        rfl }
  letI : Algebra L Ωv := m₂.toRingHom.toAlgebra
  haveI : IsScalarTower E L Ωv := IsScalarTower.of_algebraMap_eq fun y => (m₂.commutes y).symm
  let τ : L ≃ₐ[E] L := Normal.algHomEquivAut E Ωv L m₁
  have hτ : ∀ l : L, m₂ (τ l) = m₁ l := fun l =>
    DFunLike.congr_fun ((Normal.algHomEquivAut E Ωv L).symm_apply_apply m₁) l
  have h2 : ∀ l : L, τ (s l) = AlgEquiv.restrictNormalHom L σ (τ l) := fun l => by
    apply m₂.toRingHom.injective
    show m₂ (τ (s l)) = j (algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)))
    have hρ : algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)) = σ (algebraMap L Ω (τ l)) :=
      AlgEquiv.restrictNormal_commutes σ L (τ l)
    rw [hρ, ← hgj, hτ]
    have hj₂ : j (algebraMap L Ω (τ l)) = m₁ l := hτ l
    rw [hj₂]
    exact h1 l
  have h3 : τ * s = AlgEquiv.restrictNormalHom L σ * τ := AlgEquiv.ext h2
  have h4 : τ * s = τ * AlgEquiv.restrictNormalHom L σ := by
    rw [h3]
    exact IsMulCommutative.is_comm.comm _ _
  exact (mul_left_cancel h4).symm

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

theorem absEw_mul_locInf_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w)
    (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0)
    (hz : ∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) (hc : ∀ f, ‖infEmb e (z f)‖₊ ≤ c) :
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  classical
  have hnorm : ∀ (τ : EmbOver E w) (y : w.Completion ⊗[F] E), ‖infEmb τ y‖₊ = ‖infEmb e y‖₊ := by
    intro τ y
    rcases infEmb_eq_or_conj hσ e τ with h | h
    · rw [h]
    · rw [h, RingHom.comp_apply, RCLike.nnnorm_conj]
  have hterm : ∀ p : EmbOver E w × J, ‖infEmb e δ.1‖₊ * ‖p.1.1 (u p.2)‖₊ ≤ c := by
    rintro ⟨τ, f⟩
    have h1 : infEmb τ (z f) = τ.1 (u f) * infEmb τ δ.1 := by
      rw [hz f, map_mul, infEmb_tmul, map_one, one_mul]
    calc ‖infEmb e δ.1‖₊ * ‖τ.1 (u f)‖₊ = ‖infEmb τ δ.1‖₊ * ‖τ.1 (u f)‖₊ := by rw [hnorm τ]
      _ = ‖infEmb τ (z f)‖₊ := by rw [h1, nnnorm_mul, mul_comm]
      _ = ‖infEmb e (z f)‖₊ := hnorm τ _
      _ ≤ c := hc f
  have hsup : ‖infEmb e δ.1‖₊ * (Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) ≤ c := by
    rw [Finset.mul_sup₀]
    exact Finset.sup_le fun p _ => hterm p
  unfold locInf
  rw [GlobalTheory.Doubling.absEw_eq_sq hσ e, ← mul_pow]
  convert pow_le_pow_left' hsup 2
end GlobalTheory.CompanionTheory.GodementH

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOne
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem lt_local_artin_inertia : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  intro F _ _ _ _ Ωv _ _ _ _ _ _ _ _ π hπ f hf u τ hτd hτ y hy
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ hf L
  have hE := isUnramifiedSubextension_unramifiedTower (K := F) (Ω := Ωv) m
  have := hE.1
  have := hE.isGalois
  have hab := isAbelianGalois_lubinTateField_sup hπ hf n.succ_pos hE
  have key := restrictAb_localArtinMap_lubinTate hπ hf n.succ_pos (unramifiedTower F Ωv m)
    hE.le_maximalUnramifiedExtension u⁻¹ 0 τ (by rw [hτd]; simp)
    (by intro x hx; rw [inv_inv]; exact hτ _ x hx)
  have hx : unitUniformizerPow hπ u⁻¹ 0 = unitsIncl F u⁻¹ := by
    rw [unitUniformizerPow_eq, zpow_zero, one_mul]
  rw [hx] at key
  have h2 := congrArg (fun σ => ((σ ⟨y, h hyL⟩ : (lubinTateField Ωv hπ hf (n + 1) ⊔ unramifiedTower F Ωv m : IntermediateField F Ωv)) : Ωv)) key
  simp only [restrictAb_apply, AlgEquiv.restrictNormalHom_apply] at h2
  exact h2

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicFrameBlockZero
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem single_mul_mul_single_eq_zero {R : Type} [CommRing R] {r : ℕ} {B : Matrix (Fin r) (Fin r) R}
    {m i : Fin r} (h : B m i = 0) :
    (single m m (1 : R) : Matrix (Fin r) (Fin r) R) * B * single i i (1 : R) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  rcases eq_or_ne m a with rfl | ha <;> rcases eq_or_ne i b with rfl | hb <;>
    simp [*, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem map_single_one_eq {E : Type} [Field E] {r : ℕ} (f : E →+* ℂ) (i : Fin r) :
    (single i i (1 : E) : Matrix (Fin r) (Fin r) E).map f = single i i (1 : ℂ) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem mul_mul_frameLine {n r : ℕ} {A G : Matrix (Fin n) (Fin n) ℂ} {P : Matrix (Fin n) (Fin r) ℂ}
    {B : Matrix (Fin r) (Fin r) ℂ} (hG : G * P = P * B) (Q : Matrix (Fin r) (Fin n) ℂ) (i : Fin r)
    (h : A * P * B * single i i (1 : ℂ) = 0) :
    A * G * (P * single i i (1 : ℂ) * Q) = 0 := by
  calc A * G * (P * single i i (1 : ℂ) * Q) = A * (G * P) * single i i (1 : ℂ) * Q := by
        simp only [Matrix.mul_assoc]
    _ = A * P * B * single i i (1 : ℂ) * Q := by
        rw [hG]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem minPar_frame_block_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ g ∈ minPar σ J X, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r) (α β : FrameIx r), frameLev s α < 2 → frameLev s β = 2 → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * archMat σ J τ (projArch σ J w g) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW g hg w τ s α β hα hβ
  obtain ⟨-, -, -, hστ⟩ := hCM
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hστ, hστ, star_star])
  have cT_mul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      cT (σ : E →+* E) (A * B) = cT (σ : E →+* E) B * cT (σ : E →+* E) A := by
    intro a b c A B
    simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have cT_cT : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := by
    intro a b A
    ext i j
    simp [Formalism.UG.cT, hσσ]
  have cT_J : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [Formalism.UG.cT] using hJ.1 i j
  have cT_one : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, hij, Ne.symm hij]
  have hyx : cT (σ : E →+* E) Y * (J * X) = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [cT_mul, cT_mul, cT_cT, cT_J, cT_one] at h
    exact h
  have hxx : cT (σ : E →+* E) X * (J * X) = 0 := by
    rw [← Matrix.mul_assoc]
    exact hW.xx
  obtain ⟨B, hBt, hB⟩ := hg
  let φ : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) E →+* ℂ :=
    (GlobalTheory.AdelicU.infEmb τ).comp (GlobalTheory.AdelicU.compInf F E w)
  have hφ : ∀ x : E, φ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) = τ.1 x := by
    intro x
    simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compInf, GlobalTheory.AdelicU.infEmb]
  have hAd : (GlobalTheory.SiegelSet.adMat F X).map φ = X.map τ.1 := by
    ext i j
    simp only [GlobalTheory.SiegelSet.adMat, Matrix.map_apply]
    exact hφ (X i j)
  have hA : archMat σ J τ (projArch σ J w g) =
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map φ := by
    ext i j
    simp [GlobalTheory.Orb.archMat, GlobalTheory.AdelicU.matHom_projArch, Formalism.UG.bc, φ]
  have hG : archMat σ J τ (projArch σ J w g) * X.map τ.1 = X.map τ.1 * B.map φ := by
    rw [hA, ← hAd, ← Matrix.map_mul, hB, Matrix.map_mul]
  rcases β with _ | (i | i)
  · change 1 = 2 at hβ
    exact absurd hβ (by decide)
  · by_cases hi : i ≤ s
    · have hframe : (frameIdem (σ : E →+* E) J X Y (some (Sum.inl i))).map τ.1 =
          X.map τ.1 * single i i (1 : ℂ) * (cT (σ : E →+* E) Y * J).map τ.1 := by
        change (X * single i i (1 : E) * (cT (σ : E →+* E) Y * J)).map τ.1 = _
        simp only [Matrix.map_mul, map_single_one_eq]
      rw [hframe]
      apply mul_mul_frameLine hG
      rw [← Matrix.map_mul]
      rcases α with _ | (j | j)
      · have h0 : frameIdem (σ : E →+* E) J X Y none * X = 0 := by
          change (1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)) * X = 0
          simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, hxx,
            Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
        rw [h0]
        simp
      · have hj : ¬ j ≤ s := by
          intro h
          change (if j ≤ s then 2 else 1) < 2 at hα
          rw [if_pos h] at hα
          exact absurd hα (by decide)
        have hij : i < j := lt_of_le_of_lt hi (not_le.mp hj)
        have hBji : (B.map φ) j i = 0 := by
          simp [Matrix.map_apply, hBt hij]
        have h1 : frameIdem (σ : E →+* E) J X Y (some (Sum.inl j)) * X = X * single j j (1 : E) := by
          change X * single j j (1 : E) * (cT (σ : E →+* E) Y * J) * X = _
          simp only [Matrix.mul_assoc, hyx, Matrix.mul_one]
        rw [h1, Matrix.map_mul, map_single_one_eq, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc (single j j (1 : ℂ)), single_mul_mul_single_eq_zero hBji, Matrix.mul_zero]
      · have h2 : frameIdem (σ : E →+* E) J X Y (some (Sum.inr j)) * X = 0 := by
          change Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) * X = 0
          simp only [Matrix.mul_assoc, hxx, Matrix.mul_zero]
        rw [h2]
        simp
    · change (if i ≤ s then 2 else 1) = 2 at hβ
      rw [if_neg hi] at hβ
      exact absurd hβ (by decide)
  · change (if i ≤ s then 0 else 1) = 2 at hβ
    by_cases hi : i ≤ s
    · rw [if_pos hi] at hβ
      exact absurd hβ (by decide)
    · rw [if_neg hi] at hβ
      exact absurd hβ (by decide)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishing
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem twist_integral_eq_JJ_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB b M v v' hb hfix hM
  obtain ⟨hg, hdet⟩ := GlobalTheory.CompanionTheory.MirPair.shearGL_mulVec_and_nabs_det b hb
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hcoef : ∀ x, GlobalTheory.CompanionTheory.MirPair.coef T B v
      (T' (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b)) v') x =
      GlobalTheory.CompanionTheory.MirPair.coef T B v v'
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := hlevi (GlobalTheory.CompanionTheory.MirPair.shearGL n b) x v v'
    rw [hfix] at h
    rw [h, GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.val_absPow, hdet]
    simp
  have hgg : ∀ x : Fin (n + 1) → k,
      ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        ((((GlobalTheory.CompanionTheory.MirPair.shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hset : {y : Fin (n + 1) → k | ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} = M := Set.ext fun y => hM y
  have key := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n
      (((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) *
      GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  rw [hdet, hset] at key
  simp only [hgg, Complex.ofReal_one, NNReal.coe_one, one_mul] at key
  rw [GlobalTheory.CompanionTheory.MirPair.JJ]
  simp_rw [hcoef]
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hlast : (x + (b ⬝ᵥ x) • GlobalTheory.BZMir.eLast k n) (Fin.last n) = x (Fin.last n) + b ⬝ᵥ x := by
    simp [GlobalTheory.BZMir.eLast]
  simp only [GlobalTheory.CompanionTheory.MirPair.wt]
  rw [hg x, hlast, show -(x (Fin.last n) + b ⬝ᵥ x) = -(b ⬝ᵥ x) + -x (Fin.last n) by ring,
    AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

theorem rat_mem_hermA (β : HermE D r) : rat β.1 ∈ hermA D r := by
  show adj (rat β.1) = rat β.1
  rw [← rat_conjTranspose]
  congr 1
  exact β.2

def ofHermE (β : HermE D r) : ratHerm D r :=
  ⟨⟨rat β.1, rat_mem_hermA β⟩, ⟨β.1, rfl⟩⟩

theorem ofHermE_val (β : HermE D r) : (ofHermE β).1.1 = β.1.map (incA D) := rfl

theorem ofHermE_bijective : Function.Bijective (ofHermE (D := D) (r := r)) := by
  refine ⟨fun a b h => Subtype.ext (rat_injective (congrArg (fun c : ratHerm D r => c.1.1) h)), ?_⟩
  rintro ⟨⟨x, hx⟩, hr⟩
  obtain ⟨γ, hγ⟩ := (mem_ratMx).1 (AddSubgroup.mem_comap.1 hr)
  have hγ' : rat γ = x := hγ
  refine ⟨⟨γ, rat_injective ?_⟩, Subtype.ext (Subtype.ext hγ')⟩
  have hx' : adj x = x := hx
  have : rat γᴴ = rat γ := by rw [rat_conjTranspose, hγ', hx']
  exact this

def hermEquiv : HermE D r ≃ ratHerm D r := Equiv.ofBijective _ ofHermE_bijective

theorem W_eq (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    W ψ V μ lam φ β = ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul (ofHermE β).1.1 b.1 : Mx D r r))) ∂lam := rfl

end GlobalTheory.CompanionTheory.HermPoisson
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationEquivariantStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd | exact GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphismStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_preserves_isomorphism : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)), MIso A B → MIso (phiN ψ A) (phiN ψ B) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.miso_phiN | exact GlobalTheory.CompanionTheory.LeibOrd.miso_phiN | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.miso_phiN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOneStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_lower_block_at_one : ∀ (n : ℕ) (lev : Fin n → ℕ) (f h : GlobalTheory.CompanionTheory.ModelS.SmF n), f ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → f.1 1 = 1 → h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → ∀ X : Mat n, (∀ a b, lev a < lev b → X a b = 0) → (GlobalTheory.CompanionTheory.ModelS.DR X h).1 1 = (GlobalTheory.CompanionTheory.ModelS.DR X f).1 1 * h.1 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv <;> assumption)
end

