module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ArchUnimod
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PArchGroup
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.PArchGroup

theorem cT_star' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem isUnit_of_form {n : ℕ} {J M : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (h : Mᴴ * J * M = J) :
    IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h2
  exact hJ.ne_zero h2.symm

theorem isClosed_form {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | Mᴴ * J * M = J} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

end MainStatements.WeightKernel.PArchGroup

namespace MainStatements.WeightKernel

open PArchGroup in
theorem archGroup : ArchGroup := by
  intro D V w τ
  have h := isCMExt_host D
  have hu : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
  have hJ : IsUnit (V.gram.map τ.1).det := by
    rw [show V.gram.map τ.1 = τ.1.mapMatrix V.gram from rfl, ← RingHom.map_det]
    exact hu.map _
  have hr : ∀ M, M ∈ Set.range (archMat D.sp.cm.sig V.gram τ) ↔ Mᴴ * V.gram.map τ.1 * M = V.gram.map τ.1 := by
    intro M
    constructor
    · rintro ⟨g, rfl⟩
      rw [archMat_eq_archEquiv V.gram h τ g, ← cT_star']
      exact (archEquiv V.gram h τ g).2
    · intro hM
      have hU := isUnit_of_form hJ hM
      have hmem : hU.unit ∈ Formalism.UG.UJ (starRingEnd ℂ) (V.gram.map τ.1) := by
        change Formalism.UG.cT (starRingEnd ℂ) (hU.unit : Matrix (Fin _) (Fin _) ℂ) * V.gram.map τ.1 *
          (hU.unit : Matrix (Fin _) (Fin _) ℂ) = V.gram.map τ.1
        rw [cT_star', IsUnit.unit_spec]
        exact hM
      refine ⟨(archEquiv V.gram h τ).symm ⟨hU.unit, hmem⟩, ?_⟩
      rw [archMat_eq_archEquiv V.gram h τ, MulEquiv.apply_symm_apply]
      exact IsUnit.unit_spec hU
  refine ⟨hJ, ⟨isEmbedding_archMat V.gram h τ, ?_⟩, hr⟩
  have : Set.range (matCoord (archMat D.sp.cm.sig V.gram τ)) =
      {M : Matrix (Fin _) (Fin _) ℂ | Mᴴ * V.gram.map τ.1 * M = V.gram.map τ.1} := by
    ext M
    exact hr M
  rw [this]
  exact isClosed_form _

end MainStatements.WeightKernel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PArchUnimod
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel

theorem archUnimod : ArchUnimod := by
  intro D V w μ hμ
  obtain ⟨hcm, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  haveI : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := D.sp.cm.sig) w.Completion hcm hJ).1
  exact hU.2.2.2.2.2.2 μ hμ

end MainStatements.WeightKernel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

abbrev NF {k : ℕ} (C : Matrix (Fin n) (Fin k) E) : Subgroup (GAd σ J) := ratPts σ J ⊓ unipRad σ J C

variable {σ J}

def nsum (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ) (z g : GAd σ J) : ℂ := ∑' ν : Γ, f (z * ν * g)

def Van (N : Subgroup (GAd σ J)) (f : GAd σ J → ℂ) : Prop :=
  ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GAd σ J), ∫ m : N, f (x * m * y) ∂ν = 0

end

def SmOf : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, GlobalTheory.UAut.IsSm σ J f

def DerMem : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, ∀ b : ℝ → GAd σ J, IsRealLine σ J b → lineDer b f ∈ CcAd σ J

def DerVan : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ N : Subgroup (GAd σ J), IsClosed (N : Set (GAd σ J)) → ∀ f ∈ CcAd σ J, ∀ b : ℝ → GAd σ J, IsRealLine σ J b →
      Van N f → Van N (lineDer b f)

def Level : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g

def SumSm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ Γ : Subgroup (GAd σ J), Γ ≤ ratPts σ J → ∀ f ∈ CcAd σ J, ∀ z, GlobalTheory.UAut.IsSm σ J (nsum Γ f z) ∧
      ∀ b : ℝ → GAd σ J, IsRealLine σ J b → lineDer b (nsum Γ f z) = nsum Γ (lineDer b f) z

def Variation : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (k : ℕ) (C : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J C → ∀ f : GAd σ J → ℂ, Continuous f →
      HasCompactSupport f → Van (unipRad σ J C) f → ∀ (z g : GAd σ J) (e : ℝ),
      (∀ m ∈ unipRad σ J C, ‖nsum (NF σ J C) f z (m * g) - nsum (NF σ J C) f z g‖ ≤ e) → ‖nsum (NF σ J C) f z g‖ ≤ e

def NearCusp : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Cm : Set (GAd σ J)) (c : ℝ)
      (U : Subgroup (GAd σ J)), IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∀ s : Fin r,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ m ∈ unipRad σ J (pre X s),
        ∃ γ ∈ NF σ J (pre X s), ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧
          m * (a * k) = γ * (a * k) * u * κ

def Base : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∃ A : ℕ,
    ∀ Γ : Subgroup (GAd D.sp.cm.sig V.gram), Γ ≤ ratPts D.sp.cm.sig V.gram →
    ∀ f : GAd D.sp.cm.sig V.gram → ℂ, Continuous f → HasCompactSupport f →
    ∀ C W : Set (GAd D.sp.cm.sig V.gram), IsCompact C → IsCompact W → ∃ B : ℝ, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖nsum Γ f (x * a⁻¹) (a * y)‖ ≤ B * (∏ i, max (t i) 1) ^ A

def Core : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ s : Fin r, ∃ A : ℕ, ∀ m : ℕ,
    ∀ f ∈ CcAd D.sp.cm.sig V.gram, Van (unipRad D.sp.cm.sig V.gram (pre X s)) f →
    ∀ C W : Set (GAd D.sp.cm.sig V.gram), IsCompact C → IsCompact W → ∃ B : ℝ, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖nsum (NF D.sp.cm.sig V.gram (pre X s)) f (x * a⁻¹) (a * y)‖ ≤ B * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m

def Bridge : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r),
    NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j)

def Decay : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (c : ℝ), 0 < c → ∀ (j : Fin r) (f : GA D V → ℂ), f ∈ CcGA V →
    GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish (frameFlag (isIsoFrame_firstCols hW j)) f →
    ∀ C W : Set (GA D V), IsCompact C → IsCompact W → ∃ A : ℕ, ∀ m : ℕ, ∃ B : ℝ,
      ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, f (x * (a⁻¹ * rat V ν * a) * y)‖ ≤
          B * (∏ i, max (t i) 1) ^ A * (root t j)⁻¹ ^ m

end MainStatements.WeightKernel.Dec

end
end

