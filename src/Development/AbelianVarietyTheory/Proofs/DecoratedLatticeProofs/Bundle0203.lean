module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
section
namespace I195MixedCoordinates_234e4f75c563de28cf3cb155

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_234e4f75c563de28cf3cb155

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HandHom
variable {D : D7}

theorem mixS_smul {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (T : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (a : ℂ) (f : WO V T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.source d) T ψ μ 𝓕 (a • f) x = a • (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.source d) T ψ μ 𝓕 f x := by
  funext w₀
  simp only [_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.source, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext a'; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem mixT_smul {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (a : ℂ) (f : WO S W → ℂ) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.target d) S ψ μ 𝓕 (a • f) y = a • (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.target d) S ψ μ 𝓕 f y := by
  funext w₀
  simp only [_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.target, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext a'; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem flatAt_smul (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (μS : Measure (Mx D W.rank ρ)) (𝓕S : Set (Mx D W.rank ρ)) (μT : Measure (Mx D σ V₀.rank))
    (𝓕T : Set (Mx D σ V₀.rank)) (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (a : ℂ)
    (Ψ : WO V W → ℂ) :
    GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y (a • Ψ) = a • GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y Ψ := by
  have hS (f : WO V W → ℂ) (z : Mx D W.rank ρ) :
      _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ μS 𝓕S (a • f) z =
        a • _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ μS 𝓕S f z :=
    mixS_smul dV W ψ μS 𝓕S a f z
  have hT (f : WO V₀ W → ℂ) (z : Mx D V₀.rank σ) :
      _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ μT 𝓕T (a • f) z =
        a • _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ μT 𝓕T f z :=
    mixT_smul dW V₀ ψ μT 𝓕T a f z
  funext w
  simp only [GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt, hS, Pi.smul_apply,
    smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext u; rw [hT]; simp only [Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem flatBF_smul {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (a : ℂ) (Ψ : WO B.V J.W → ℂ) :
    flatBF s (a • Ψ) = a • flatBF s Ψ := by
  simp only [GlobalTheory.Unf.flatBF, GlobalTheory.MixPer.flat, flatAt_smul]

theorem flatFB_smul {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (a : ℂ) (Ψ : WO J.W B.V → ℂ) :
    flatFB s (a • Ψ) = a • flatFB s Ψ := by
  simp only [GlobalTheory.Unf.flatFB, GlobalTheory.MixPer.flatLast, flatAt_smul]

theorem handBF_smul {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D}
    {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') (φ : GA D B.A → ℂ) (a : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) :
    handBF s l φ (a • Ξ) = star a • handBF s l φ Ξ := by
  funext h w
  simp only [GlobalTheory.Unf.handBF, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (φ _) a]
  rw [integral_const_mul, star_mul']

theorem handBF_zero {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D}
    {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') (φ : GA D B.A → ℂ) :
    handBF s l φ 0 = 0 := by
  funext h w
  simp [GlobalTheory.Unf.handBF]

theorem handFB_smul {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (c b : ℂ) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) :
    handFB s vL (c • Y) (b • Ξ) = (star c * b) • handFB s vL Y Ξ := by
  funext h₁
  simp only [GlobalTheory.Unf.handFB, GlobalTheory.Unf.pairKer, GlobalTheory.MixPer.contractT, GlobalTheory.MixPer.thPair, LinearMap.map_smul,
    Pi.smul_apply, smul_eq_mul, star_mul']
  simp_rw [show ∀ x y : ℂ, b * x * (star c * y) = (star c * b) * (x * y) from fun x y => by ring, integral_const_mul]

theorem per_smul {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (a b : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (a • φ) (b • f) = a * b * B.per ψ φ f := by
  simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer, GlobalTheory.MixPer.besFun, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ x y z : ℂ, a * x * (b * y) * z = (a * b) * (x * y * z) from fun x y z => by ring, integral_const_mul]

end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7}

theorem hand_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), (∀ (Ψ₁ : WO B.V J.W → ℂ) (Ψ₂ : WO J.W B'.V → ℂ) (a b : ℂ), handFB s₂ vL (handBF s₁ l φ (flatBF s₁ (a • Ψ₁))) (flatFB s₂ (b • Ψ₂)) = (a * b) • handFB s₂ vL (handBF s₁ l φ (flatBF s₁ Ψ₁)) (flatFB s₂ Ψ₂)) ∧ (∀ Ξ₂, handFB s₂ vL (handBF s₁ l φ 0) Ξ₂ = 0) ∧ ∀ (a b : ℂ) (φ' : GA D B'.A → ℂ) (f : GA D B'.V → ℂ), B'.per ψ (a • φ') (b • f) = a * b * B'.per ψ φ' f := by
  intro D ψ σ B J B' s₁ s₂ l vL φ
  refine ⟨fun Ψ₁ Ψ₂ a b => ?_, fun Ξ₂ => ?_, fun a b φ' f => per_smul B' ψ a b φ' f⟩
  · rw [flatBF_smul, flatFB_smul, handBF_smul, handFB_smul, star_star]
  · rw [handBF_zero]
    funext h₁
    simp [GlobalTheory.Unf.handFB, GlobalTheory.Unf.pairKer, GlobalTheory.MixPer.contractT, GlobalTheory.MixPer.thPair]

end GlobalTheory.HandHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivativeDiagonalHalfEqSchrodingerDer
section
namespace I195MixedCoordinates_bf5641df9836f7a59c2c5fdd

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_bf5641df9836f7a59c2c5fdd

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.DiagDeriv

variable {D : D7}

theorem compAt_mul_rat (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n k : ℕ} (w : Mx D m n)
    (Q : Matrix (Fin n) (Fin k) D.host.E) : compAt θ τ (w * rat Q) = compAt θ τ w * Q.map (tauE D τ) := by
  have h : compAt θ τ (w * rat Q) = (w * rat Q).map ((θ τ).comp (infPart D)) := rfl
  rw [h, Matrix.map_mul]
  congr 1
  ext i j
  exact (hθ τ).1 (Q i j)

theorem isLineAt_extX (θ : InfFam D) (hθ : IsInfFam θ) (A B : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin B.rank) (Fin A.rank) ℂ) (L : ℝ →+ Mx D B.rank A.rank) (hL : IsLineAt θ τ X L) :
    IsLineAt θ τ (X * (dblDec A).qX.map (tauE D τ)) (((dblDec A).extX B).comp L) := by
  refine ⟨(continuous_id.matrix_mul continuous_const).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
  · show ((L t) * (dblDec A).pX).map (finPart D) = 0
    rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
  · show compAt θ τ' (L t * rat (dblDec A).qX) = _
    rw [compAt_mul_rat θ hθ, hL.2.2 t τ']
    split_ifs with h
    · subst h; rw [Matrix.smul_mul]
    · rw [Matrix.zero_mul]

theorem lineAt_isLineAt (θ : InfFam D) (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) : IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

theorem lineAt_extX (θ : InfFam D) (hθ : IsInfFam θ) (A B : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin B.rank) (Fin A.rank) ℂ) :
    (lineAt θ τ (X * (dblDec A).qX.map (tauE D τ)) : ℝ →+ WO (dblSp A) B) =
      ((dblDec A).extX B).comp (lineAt θ τ X) :=
  GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (lineAt_isLineAt θ hθ τ _)
    (isLineAt_extX θ hθ A B τ X _ (lineAt_isLineAt θ hθ τ X))

theorem hasDerivAt_mixS_extX {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (M : ℝ →+ WO S T) (hM : IsRealDir T S M) (x : Mx D T.rank ρ) (w : WO S₀ T) :
    HasDerivAt (fun t : ℝ => (_root_.I195MixedCoordinates_bf5641df9836f7a59c2c5fdd.source d) T ψ μ 𝓕 (heisO ψ S T (M t) f) x w)
      ((_root_.I195MixedCoordinates_bf5641df9836f7a59c2c5fdd.source d) T ψ μ 𝓕 (GlobalTheory.OrientedHeis.dLine ψ S T M f) x w) 0 := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hM hf)
  have e2 : GlobalTheory.OrientedHeis.dLine ψ S T M f = heisO ψ S T (M 0) (GlobalTheory.OrientedHeis.dLine ψ S T M f) := by
    rw [M.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
  rw [e2]
  have hI : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IntegrableOn (fun a => ψ (symplOH S T (d.extY T a) (d.extX T x)) *
      g (d.extY T a + d.extX T x + d.ext0 T w)) 𝓕 μ := fun g hg => by
    simpa only [HypDec.integrandS_eq] using HypDec.integrableOn_mixS d hψ.1.1 hμ hg x w
  change HasDerivAt (fun t : ℝ => d.mixS T ψ μ 𝓕 (heisO ψ S T (M t) f) x w)
    (d.mixS T ψ μ 𝓕 (heisO ψ S T (M 0) (GlobalTheory.OrientedHeis.dLine ψ S T M f)) x w) 0
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
    (F' := fun t a => ψ (symplOH S T (d.extY T a) (d.extX T x)) *
      heisO ψ S T (M t) (GlobalTheory.OrientedHeis.dLine ψ S T M f) (d.extY T a + d.extX T x + d.ext0 T w))
    (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
  · exact Filter.Eventually.of_forall fun t =>
      (hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 t) hf)).aestronglyMeasurable
  · exact hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 0) hf)
  · exact (hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 0)
      (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hM hf))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a t _ => ?_
    rw [norm_mul, hψ.1.2.1, one_mul]
    unfold heisO
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hK _
  · exact Filter.Eventually.of_forall fun a t _ =>
      (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hM hf _ t).const_mul _

theorem sch_dRho_diag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ
      (X * (dblDec A).qX.map (tauE D τ)) f) x = deriv (fun t : ℝ => sch ψ A B ν 𝓨 f (x + lineAt θ τ X t)) 0 := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν f hf τ X x
  let v : GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  let M : ℝ →+ WO (dblSp A) B := ((dblDec A).extX B).comp (lineAt θ τ X)
  have hL := lineAt_isLineAt θ hθ τ X
  have hM : IsRealDir B (dblSp A) M := by
    refine ⟨(continuous_id.matrix_mul continuous_const).comp hL.1, fun t => ?_⟩
    show ((lineAt θ τ X t) * (dblDec A).pX).map (finPart D) = 0
    rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
  have e1 : (fun t : ℝ => sch ψ A B ν 𝓨 f (x + lineAt θ τ X t)) =
      fun t => (dblDec A).mixS B ψ ν 𝓨 (heisO ψ (dblSp A) B (M t) f) x 0 := by
    funext t
    have h := congrFun ((GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) v f hf).1 x
      (lineAt θ τ X t)) 0
    exact h.symm
  rw [e1]
  change _ = deriv (fun t : ℝ => _root_.I195MixedCoordinates_bf5641df9836f7a59c2c5fdd.source (dblDec A) B ψ ν 𝓨 (heisO ψ (dblSp A) B (M t) f) x 0) 0
  rw [(hasDerivAt_mixS_extX hψ hθ (dblDec A) (μ := ν) (𝓕 := 𝓨) hν hf M hM x 0).deriv]
  show (dblDec A).mixS B ψ ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ
      (X * (dblDec A).qX.map (tauE D τ)) f) x 0 = _
  rw [GlobalTheory.OrientedHeis.dRho_eq_dLine, lineAt_extX θ hθ A B τ X]
  rfl

end GlobalTheory.StdUnn.DiagDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem holValueAt_npow_sub_mul : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c →
    (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  intro h h' s₀ c r σ hr hh e
  have ha : AnalyticOnNhd ℂ (fun s => npow r (s₀ - s)) (GlobalTheory.Cont.rightOf (s₀.re - 1)) := by
    intro s _
    rw [funext fun s => npow_eq_exp hr (s₀ - s)]
    fun_prop
  have hg := GlobalTheory.Cont.holValueAt_self ha (s₀ := s₀) (by linarith)
  have h1 : npow r (s₀ - s₀) = 1 := by simp [npow_eq_exp hr]
  have hm := hg.mul hh
  simp only [h1, one_mul] at hm
  exact hm.congr ⟨σ, fun s hs => (e s hs).symm⟩

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIdealIsUnitSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.NormIdealUnit

theorem unit_at_split_place : ∀ (D : D7) (PP : Pl D.host.E), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) := by
  intro D PP hPP v φ hφ
  have hq : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun h => hPP (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have unit : ∀ x : 𝓞 D.host.E, x ∉ PP.asIdeal → Valued.v (rdQ φ (x : D.host.E)) = 1 := fun x hx =>
    le_antisymm (GlobalTheory.TameLiftChar.val_rdQ_le_one φ x) (not_lt.1 fun h => hx ((hφ x).2 h))
  refine ⟨⟨_, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D, ?_⟩, ?_⟩
  · have := unit _ hN
    simpa using this
  · have hnot : ¬ D.host.𝔟 ≤ PP.asIdeal :=
      haveI := PP.isPrime; UpperTheory.Ram.half_not_le D.host _ hq
    obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
    have hz1 := unit z hzP
    have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
    have hAA0 : ∀ a : D.host.E, a ∈ D.host.AA0 → Valued.v (rdQ φ a) ≤ 1 := by
      intro a ha
      unfold Host.AA0 at ha
      rw [FractionalIdeal.mem_inv_iff hB] at ha
      obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
      have h3 := GlobalTheory.TameLiftChar.val_rdQ_le_one φ w
      rw [RingOfIntegers.coe_eq_algebraMap, hw, ← GlobalTheory.TameLiftChar.rdQHom_apply, map_mul, map_mul,
        GlobalTheory.TameLiftChar.rdQHom_apply, GlobalTheory.TameLiftChar.rdQHom_apply] at h3
      rw [← RingOfIntegers.coe_eq_algebraMap] at h3
      rw [hz1] at h3
      simpa using h3
    have hle : D.host.AA ≤ D.host.AA0 := by
      unfold Host.AA
      calc (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
          ≤ 1 * D.host.AA0 := by first | exact FractionalIdeal.mul_right_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | gcongr; exact FractionalIdeal.coeIdeal_le_one
        _ = D.host.AA0 := one_mul _
    exact fun a ha => hAA0 a (hle ha)

end GlobalTheory.NormIdealUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotZero

theorem left_and_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {R : Subgroup G}
    (hR : IsClosed (R : Set G)) (μR : Measure R) [μR.IsHaarMeasure] [μR.IsInvInvariant]
    (μG : Measure G) [μG.IsHaarMeasure] {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 μR μG f z) :
    (∀ r ∈ R, ∀ x, f (r * x) = f x) ∧ (f = 0 → z = 0) := by
  haveI : LocallyCompactSpace R := hR.locallyCompactSpace
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  refine ⟨fun r hr x => h.left hr x, ?_⟩
  rintro rfl
  exact h.unique hR IsQuotIntL1.zero


open scoped Pointwise Topology in
theorem isClosed_of_locallyCompactSpace {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (R : Subgroup G) [LocallyCompactSpace R] : IsClosed (R : Set G) := by
  obtain ⟨K, hKn, hK⟩ := local_compact_nhds (x := (1 : R)) (n := Set.univ) Filter.univ_mem
  have hKc : IsCompact K := hK.2
  rw [nhds_subtype, Filter.mem_comap] at hKn
  obtain ⟨U, hU, hUK⟩ := hKn
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset hU
  set W : Set G := V ∩ V⁻¹
  have hWo : IsOpen W := hVo.inter hVo.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  set K' : Set G := Subtype.val '' K
  have hK'c : IsCompact K' := hKc.image continuous_subtype_val
  have hK'R : K' ⊆ R := by rintro _ ⟨k, -, rfl⟩; exact k.2
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨y, hyW, hyR⟩ := mem_closure_iff.1 hx (x • W) (hWo.smul x) (by simpa using Set.smul_mem_smul_set (a := x) hW1)
  obtain ⟨v₁, hv₁, rfl⟩ := hyW
  have hsub : (x • W) ∩ (R : Set G) ⊆ (x • v₁) • K' := by
    rintro r ⟨⟨v₂, hv₂, rfl⟩, hr⟩
    have hm : v₁⁻¹ * v₂ ∈ U := hVV (Set.mul_mem_mul (by simpa using hv₁.2) hv₂.1)
    have hmR : v₁⁻¹ * v₂ ∈ R := by
      have := R.mul_mem (R.inv_mem hyR) hr
      simpa [smul_eq_mul, mul_assoc] using this
    refine ⟨v₁⁻¹ * v₂, ⟨⟨v₁⁻¹ * v₂, hmR⟩, hUK hm, rfl⟩, ?_⟩
    simp [smul_eq_mul, mul_assoc]
  have hx' : x ∈ closure ((x • W) ∩ (R : Set G)) :=
    (hWo.smul x).inter_closure ⟨by simpa using Set.smul_mem_smul_set (a := x) hW1, hx⟩
  have hcl : IsClosed ((x • v₁) • K') := (hK'c.smul _).isClosed
  have := closure_minimal hsub hcl hx'
  obtain ⟨k, hk, hkx⟩ := this
  simp only [smul_eq_mul] at hkx hyR
  rw [← hkx]
  exact R.mul_mem hyR (hK'R hk)

theorem jac_haar_inv {D : D7} {ρ : ℕ} (J : JacLev D ρ) :
    IsClosed (jacGrp J.d : Set (GA D J.W)) ∧ J.μR.IsHaarMeasure ∧ J.μR.IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨hN, h𝓝, h𝓝1⟩ := J.vN.unit
  obtain ⟨K, hK, hcov⟩ := J.cpt
  have hμ := J.v0.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.JacProj.exists_continuous_proj D J.W J.W₀ ρ J.d
  have hNc := GlobalTheory.Mem.TrueRecord.isClosed_NFlag J.W (isIsoSub_e J.d)
  haveI : LocallyCompactSpace (flagN J.d) := hNc.locallyCompactSpace
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN J.d) J.d.emb0 (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1
    J.d.continuous_embed ⟨p, hpc, hp⟩
  haveI : LocallyCompactSpace (jacGrp J.d) := e.symm.isClosedEmbedding.locallyCompactSpace
  refine ⟨isClosed_of_locallyCompactSpace (jacGrp J.d), ?_⟩
  exact GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN J.d) J.d.emb0 hNc J.d.continuous_embed
    (flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.2.1 ⟨p, hpc, hp⟩
    (GQ J.W) (GQ J.W₀) (fun _ h => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h) hK hcov J.v0.μ J.v0.fund J.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)

theorem bes_haar_inv {D : D7} {ρ : ℕ} (B : BesLev D ρ) :
    IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ B.μR.IsHaarMeasure ∧ B.μR.IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨hN, h𝓝, h𝓝1⟩ := B.vN.unit
  obtain ⟨K, hK, hcov⟩ := B.cpt
  have hμ := B.vA.haar
  obtain ⟨p, hpc, hp⟩ := GlobalTheory.BesProj.exists_continuous_proj D B.V B.V₀ B.A B.L ρ B.d B.o
  obtain ⟨hc, hcl, hnorm, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  have hΛ : ∀ δ ∈ GQ B.A, embA B.d B.o δ ∈ GQ B.V := fun δ hδ => by
    simpa using (hrat 1 (one_mem _) δ).2 ⟨one_mem _, hδ⟩
  haveI : LocallyCompactSpace (flagN B.d) := hcl.locallyCompactSpace
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN B.d) (embA B.d B.o) hnorm hc ⟨p, hpc, hp⟩
  haveI : LocallyCompactSpace (besGrp B.d B.o) := e.symm.isClosedEmbedding.locallyCompactSpace
  refine ⟨isClosed_of_locallyCompactSpace (besGrp B.d B.o), ?_⟩
  exact GlobalTheory.SemiHaar.semiMeas_haar_inv (flagN B.d) (embA B.d B.o) hcl hc hnorm ⟨p, hpc, hp⟩
    (GQ B.V) (GQ B.A) hΛ hK hcov B.vA.μ B.vA.fund B.vN.ν h𝓝
    (by rw [h𝓝1]; exact ENNReal.one_ne_top)

end GlobalTheory.QuotZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBoundW D := by
  first | exact @GlobalTheory.ChainOnto.parBoundW | exact GlobalTheory.ChainOnto.parBoundW | (intros; apply GlobalTheory.ChainOnto.parBoundW <;> assumption)
end

