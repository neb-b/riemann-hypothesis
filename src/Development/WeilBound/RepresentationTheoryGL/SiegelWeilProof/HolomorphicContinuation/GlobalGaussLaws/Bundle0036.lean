module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0034
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0035

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}


open Classical in
def atT {m : ℕ} (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (M : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  fun i j => σ (Pi.single τ (M i j))

theorem compAt_atT {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin m) (Fin n) ℂ) : compAt θ τ (atT σ τ M) = M := by
  classical
  ext i j
  simp only [compAt, atT, Matrix.map_apply, h.comp, Pi.single_eq_same]

theorem compAt_atT_ne {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {τ τ' : D.what₂.Tau}
    (hne : τ' ≠ τ) (M : Matrix (Fin m) (Fin n) ℂ) : compAt θ τ' (atT σ τ M) = 0 := by
  classical
  ext i j
  simp only [compAt, atT, Matrix.map_apply, h.comp, Matrix.zero_apply]
  exact Pi.single_eq_of_ne hne _

theorem finPart_atT {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) : finPart D (atT σ τ M i j) = 0 := h.fin _

theorem compAt_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j; simp [compAt]

def intW (D : D7) (m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) where
  carrier := {a | ∀ i j, a i j ∈ intAE D}
  add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => (intAE D).zero_mem
  neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j)


open Classical in
def g0 (D : D7) (m n : ℕ) : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
  if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ intW D m n) = 0 then (1 : ℂ) else 0

theorem gaussian_mem_schwartz_bruhat (D : D7) (m n : ℕ) : g0 D m n ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  classical
  have hWe : (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  exact GlobalTheory.SchwartzBruhatTensor.coset_mem_SB (intW D m n) hWo hWc 0

theorem gaussian_at_zero_eq_one (D : D7) (m n : ℕ) : g0 D m n 0 = 1 := by
  classical
  simp only [g0]
  rw [if_pos]
  exact (QuotientAddGroup.eq_zero_iff (N := intW D m n) (0 : Matrix (Fin m) (Fin n) _)).2 (intW D m n).zero_mem

def psi0 (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Mx D V.rank n → ℂ := fun x =>
  evalPoly (1 : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (fun τ => compAt θ τ x) *
    gAway V l s τ (fun τ => compAt θ τ x) * g0 D V.rank n (fun i j => finPart D (x i j))

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ ∈ awayA θ V n l s τ :=
  Submodule.subset_span ⟨1, g0 D V.rank n, gaussian_mem_schwartz_bruhat D V.rank n, fun v hv => by simp at hv, rfl⟩

theorem gAway_of {V : HSp D} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (hz : ∀ τ', τ' ≠ τ → z τ' = 0) : gAway V l s τ z = 1 := by
  classical
  simp only [gAway]
  rw [Finset.sum_eq_zero]
  · simp
  · intro τ' h'
    rw [hz τ' (Finset.mem_filter.1 h').2]
    simp

theorem gaussian_vacuum_archimedean_point {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (M : Matrix (Fin V.rank) (Fin n) ℂ) : psi0 θ V n l s τ (atT σ τ M) = 1 := by
  have e1 : (fun i j => finPart D (atT σ τ M i j)) = (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    funext i j; exact finPart_atT h τ M i j
  simp only [psi0, evalPoly, map_one, one_mul, e1, gaussian_at_zero_eq_one, mul_one]
  exact gAway_of l s τ _ fun τ' h' => compAt_atT_ne h h' M

theorem cmTraceAdditiveCharacter_zero (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ 0 = 1 := by
  have e1 : (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    funext i j; simp
  simp only [psi0, evalPoly, map_one, one_mul, e1, gaussian_at_zero_eq_one, mul_one]
  exact gAway_of l s τ _ fun τ' _ => compAt_zero θ τ'

theorem tens_cancel {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsUnit fr.det) {f f' : (Fin V.rank → Fin n → ℂ) → ℂ}
    (e : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr f' (psi0 θ V n l s τ)) : f = f' := by
  funext u
  let U : Matrix (Fin V.rank) (Fin n) ℂ := u
  have := congrFun e (atT σ τ (fr * U))
  simp only [tens, compAt_atT h, gaussian_vacuum_archimedean_point h, mul_one] at this
  have e2 : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rw [e2] at this
  exact this

theorem tens_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ)
    (Ψ : Mx D m n → ℂ) : tens θ τ fr f Ψ 0 = f 0 * Ψ 0 := by
  simp only [tens, compAt_zero, Matrix.mul_zero]
  rfl

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (hm : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  simp only [phiS, dif_pos hm]

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoC
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem eval_aeval_subst {σ τ' : Type} (x : τ' → ℂ) (f : σ → MvPolynomial τ' ℂ) (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval f p) = MvPolynomial.eval (fun v => MvPolynomial.eval x (f v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]

def intW (D : D7) (m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) where
  carrier := {a | ∀ i j, a i j ∈ intAE D}
  add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => (intAE D).zero_mem
  neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j)


open Classical in
def g0 (D : D7) (m n : ℕ) : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
  if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ intW D m n) = 0 then (1 : ℂ) else 0

theorem gaussian_mem_schwartz_bruhat (D : D7) (m n : ℕ) : g0 D m n ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  classical
  have hWe : ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  convert GlobalTheory.SchwartzBruhatTensor.coset_mem_SB (intW D m n) hWo hWc 0 using 1
  funext a
  unfold g0
  exact if_congr Iff.rfl rfl rfl

theorem gaussian_at_zero_eq_one (D : D7) (m n : ℕ) : g0 D m n 0 = 1 := by
  unfold g0
  split_ifs with h
  · rfl
  · exact (h ((QuotientAddGroup.eq_zero_iff (N := intW D m n) (0 : Matrix (Fin m) (Fin n) _)).2 (intW D m n).zero_mem)).elim

def psi0 (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Mx D V.rank n → ℂ :=
  fun x => gAway V l s τ (fun τ => compAt θ τ x) * g0 D V.rank n (fun i j => finPart D (x i j))

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ ∈ awayA θ V n l s τ := by
  refine Submodule.subset_span ⟨1, g0 D V.rank n, gaussian_mem_schwartz_bruhat D V.rank n, ?_, ?_⟩
  · intro v hv
    simp at hv
  · funext x
    simp [psi0, evalPoly]

def xL (θ : InfFam D) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) : Mx D m n := lineAt θ τ Z 1

theorem compAt_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun τ' => compAt θ τ' (xL θ τ Z)) = GlobalTheory.FockAnnKill.dirAt τ Z := by
  have h := GlobalTheory.FockAnnKill.compAt_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext τ'
  have h0 : compAt θ τ' (0 : Mx D m n) = 0 := by
    ext i j
    simp [compAt]
  simp [h0]

theorem finPart_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun i j => finPart D ((xL θ τ Z) i j)) = 0 := by
  have h := GlobalTheory.FockAnnKill.finPart_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext i j
  simp

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2Isometry
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocalIsometryAlt

variable {D : D7}

theorem eq_of_tens {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {m n : ℕ} {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D m n} (hx₀ : Ψ x₀ ≠ 0)
    {g₁ g₂ : (Fin m → Fin n → ℂ) → ℂ} (h : tens θ τ fr g₁ Ψ = tens θ τ fr g₂ Ψ) : g₁ = g₂ := by
  funext u
  obtain ⟨x, hx1, hx2, hx3⟩ := OG.exists_slice hθ τ x₀ (fr * Matrix.of u)
  have h1 := congrFun h x
  rw [OG.tens_at τ hfr _ _ x (Matrix.of u) hx1, OG.tens_at τ hfr _ _ x (Matrix.of u) hx1, hΨ.1 x x₀ hx2 hx3] at h1
  exact mul_right_cancel₀ hx₀ h1

theorem int_cmul {m n : ℕ} (k : ℂ) (h : (Fin m → Fin n → ℂ) → ℂ) :
    ∫ u, ‖k * h u‖ ^ 2 = ‖k‖ ^ 2 * ∫ u, ‖h u‖ ^ 2 := by
  simp_rw [norm_mul, mul_pow]
  exact integral_const_mul _ _

def rmulEquiv {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) :
    (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (Matrix.of u * a : Matrix (Fin m) (Fin n) ℂ)
      invFun := fun u => (Matrix.of u * a⁻¹ : Matrix (Fin m) (Fin n) ℂ)
      map_add' := fun u v => by
        show Matrix.of (u + v) * a = Matrix.of u * a + Matrix.of v * a
        rw [← Matrix.add_mul]; rfl
      map_smul' := fun c u => by
        show Matrix.of (c • u) * a = c • (Matrix.of u * a)
        ext i j
        simp [Matrix.mul_apply, Finset.smul_sum, mul_assoc]
      left_inv := fun u => by
        show Matrix.of u * a * a⁻¹ = u
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]; rfl
      right_inv := fun u => by
        show Matrix.of u * a⁻¹ * a = u
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]; rfl }

theorem int_comp {m n : ℕ} (R : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : (Fin m → Fin n → ℂ) → ℝ, Continuous F → ∫ u, F (R u) = c * ∫ u, F u := by
  obtain ⟨c1, hc1, h1⟩ := PlanchH.haar_linR (m := m) (n := n) (R.trans FTD.Lc)
  obtain ⟨c2, hc2, h2⟩ := PlanchH.haar_linR (m := m) (n := n) FTD.Lc
  refine ⟨c1 / c2, div_pos hc1 hc2, fun F hF => ?_⟩
  have hG : Continuous (fun w => F (FTD.Lc.symm w)) := hF.comp FTD.Lc.symm.continuous
  have e1 := h1 _ hG
  have e2 := h2 _ hG
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply] at e1 e2
  rw [e1, e2]
  field_simp

theorem norm_phase {m n : ℕ} (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (u : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * (b * gramX ε u).trace).re = 0 := by
    have hgram : (gramX ε u)ᴴ = gramX ε u := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.conjTranspose_apply, gramX, Qp, Qb, evX, map_sum, mul_comm]
    have htrace : star (b * gramX ε u).trace = (b * gramX ε u).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hgram, hb, Matrix.trace_mul_comm]
    rw [← Complex.conj_eq_iff_re.1 htrace]
    simp
  rw [hre, Real.exp_zero]

end PositivityTheory.Rg.Sw.Glob.LocalIsometryAlt

namespace PositivityTheory.Rg.Sw.Glob

theorem local_isometry_of_hypotheses (hU : UnipTau) (hLv : LeviTau) (hW : WEx) (hS : SchOps) (hF : FTfact) (hD : Decomp) (hN : LNe)
    (hP : PlanchLoc) (hZ : AwayNZ) : LocalL2Isometry := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  have hfr : IsUnit fr.det := hC.hfr.1
  obtain ⟨Ψ₀, x₀, hΨ₀, hx₀⟩ := hZ D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  have hl0 : tLoc l τ ≠ 0 := by
    unfold tLoc
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (hN D ψ θ l hC.hψ hC.hθ hC.hl τ)

  have huniq : ∀ y f (hf : IsSch f) g, (ω (ι y) ⟨tens θ τ fr f Ψ₀, hΨ₀.2 f hf⟩).1 = tens θ τ fr g Ψ₀ → L y f = g :=
    fun y f hf g h => LocalIsometryAlt.eq_of_tens hC.hθ hfr hΨ₀ hx₀ ((hL.2 y Ψ₀ hΨ₀ f hf).symm.trans h)
  have hmul : ∀ y₁ y₂ f, IsSch f → L (y₁ * y₂) f = L y₁ (L y₂ f) := by
    intro y₁ y₂ f hf
    apply huniq _ f hf
    have e2 : ω (ι y₂) ⟨tens θ τ fr f Ψ₀, hΨ₀.2 f hf⟩ = ⟨tens θ τ fr (L y₂ f) Ψ₀, hΨ₀.2 _ (hL.1 y₂ f hf)⟩ :=
      Subtype.ext (hL.2 y₂ Ψ₀ hΨ₀ f hf)
    rw [map_mul, map_mul, mul_apply_eq_comp, e2, hL.2 y₁ Ψ₀ hΨ₀ _ (hL.1 y₂ f hf)]

  let Iso : GR n → Prop := fun y => ∃ κ : ℝ, 0 < κ ∧ ∀ f, IsSch f → ∫ u, ‖L y f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2
  have hIso_mul : ∀ y₁ y₂, Iso y₁ → Iso y₂ → Iso (y₁ * y₂) := by
    rintro y₁ y₂ ⟨κ₁, hκ₁, h₁⟩ ⟨κ₂, hκ₂, h₂⟩
    refine ⟨κ₁ * κ₂, mul_pos hκ₁ hκ₂, fun f hf => ?_⟩
    rw [hmul y₁ y₂ f hf, h₁ _ (hL.1 y₂ f hf), h₂ f hf, mul_assoc]
  have hIso_n : ∀ y (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → Iso y := by
    intro y b hb hyb
    refine ⟨1, one_pos, fun f hf => ?_⟩
    have hLf : L y f = fun u => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * f u := by
      apply huniq y f hf
      funext x
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y b hb hyb]
      simp only [tens, mul_assoc]
    rw [hLf, one_mul]
    congr 1
    funext u
    rw [norm_mul, LocalIsometryAlt.norm_phase ε _ b hb u, one_mul]
  have hone : ∀ f (hf : IsSch f), L 1 f = f := by
    intro f hf
    apply huniq 1 f hf
    rw [map_one, map_one, one_apply_eq_self]
  have hzero : ∀ y, L y (fun _ => 0) = fun _ => 0 := by
    intro y
    have h0 : IsSch (fun _ : Fin V.rank → Fin n → ℂ => (0 : ℂ)) := ⟨0, by ext u; simp⟩
    apply huniq y _ h0
    have : (⟨tens θ τ fr (fun _ => 0) Ψ₀, hΨ₀.2 _ h0⟩ : schwartzA θ V.rank n) = 0 :=
      Subtype.ext (funext fun x => by simp [tens])
    rw [this, map_zero]
    funext x
    simp [tens]
  have hIso_m : ∀ y (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → Iso y := by
    intro y a ha hya
    obtain ⟨C, Am, hA1, hA2, hA3, hAf⟩ := hLv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
    have hLf : ∀ f, IsSch f → L y f = fun u => C * f (Matrix.of u * a) := by
      intro f hf
      apply huniq y f hf
      funext x
      rw [hAf]
      have hx1 : compAt θ τ (HMul.hMul x Am : Mx D V.rank n) = compAt θ τ x * a := by
        rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA1]
      have hx2 : Ψ₀ (HMul.hMul x Am : Mx D V.rank n) = Ψ₀ x :=
        hΨ₀.1 _ _ (fun τ' h => by rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA2 τ' h, Matrix.mul_one])
          (by rw [Matrix.map_mul, hA3, Matrix.mul_one])
      have hm : (fr⁻¹ * (compAt θ τ x * a) : Matrix (Fin V.rank) (Fin n) ℂ) =
          (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) * a := by
        rw [← Matrix.mul_assoc]
        rfl
      have e1 : f (fr⁻¹ * (compAt θ τ x * a)) = f (Matrix.of (fr⁻¹ * compAt θ τ x) * a) := congrArg f hm
      change C * (f (fr⁻¹ * compAt θ τ (HMul.hMul x Am : Mx D V.rank n)) * Ψ₀ (HMul.hMul x Am : Mx D V.rank n)) =
        C * f (Matrix.of (fr⁻¹ * compAt θ τ x) * a) * Ψ₀ x
      rw [hx1, hx2, e1, mul_assoc]
    have hC0 : C ≠ 0 := by
      intro hC0
      obtain ⟨f0, hf0, hf00⟩ := (hS V.rank n).2.2.2.2
      have h1 : L y f0 = fun _ => 0 := by
        rw [hLf f0 hf0, hC0]
        funext u
        simp
      have h2 : L (y⁻¹ * y) f0 = f0 := by
        rw [inv_mul_cancel]
        exact hone f0 hf0
      rw [hmul y⁻¹ y f0 hf0, h1, hzero] at h2
      have := congrFun h2 0
      rw [hf00] at this
      exact zero_ne_one this
    obtain ⟨c, hc, hcomp⟩ := LocalIsometryAlt.int_comp (LocalIsometryAlt.rmulEquiv (m := V.rank) a ha)
    refine ⟨‖C‖ ^ 2 * c, mul_pos (pow_pos (norm_pos_iff.2 hC0) 2) hc, fun f hf => ?_⟩
    rw [hLf f hf, LocalIsometryAlt.int_cmul]
    obtain ⟨S, rfl⟩ := hf
    have hcont : Continuous (fun u => ‖S u‖ ^ 2) := S.continuous.norm.pow 2
    change ‖C‖ ^ 2 * ∫ u, (fun u => ‖S u‖ ^ 2) (LocalIsometryAlt.rmulEquiv (m := V.rank) a ha u) = _
    rw [hcomp _ hcont, mul_assoc]
  have hIso_nb : ∀ y (c : Matrix (Fin n) (Fin n) ℂ), cᴴ = c → mR y = nbar c → Iso y := by
    intro y c hc hyc
    obtain ⟨κ, γ, hκ, hγ, hsch, hform⟩ := GenOpsH.gen_nbar hU hW hS hF hC y c hc hyc
    have hγ0 := hγ ⟨Ψ₀, x₀, hΨ₀, hx₀⟩
    obtain ⟨c1, hc1, hP1⟩ := hP V.rank n ε (tLoc l τ) hl0
    obtain ⟨c2, hc2, hP2⟩ := hP V.rank n ε (-tLoc l τ) (neg_ne_zero.2 hl0)
    have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
    refine ⟨‖γ⁻¹‖ ^ 2 * ‖κ‖ ^ 2 * c1 * (‖κ⁻¹‖ ^ 2 * c2), ?_, fun f hf => ?_⟩
    · have h1 : 0 < ‖γ⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hγ0)
      have h2 : 0 < ‖κ‖ := norm_pos_iff.2 hκ
      have h3 : 0 < ‖κ⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hκ)
      positivity
    have hLf := huniq y f hf _ (hform Ψ₀ hΨ₀ f hf)
    have hg : IsSch (fun v => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
        (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) :=
      (hS V.rank n).2.2.2.1 ε (tLoc l τ) (-c) _ hc' (hsch f hf).1
    rw [hLf, LocalIsometryAlt.int_cmul, LocalIsometryAlt.int_cmul, hP1 _ hg]
    have e2 : (∫ v, ‖Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
        (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)‖ ^ 2) = ∫ v, ‖κ⁻¹ * ftLoc ε (-tLoc l τ) f v‖ ^ 2 := by
      congr 1
      funext v
      rw [norm_mul, LocalIsometryAlt.norm_phase ε _ (-c) hc' v, one_mul]
    rw [e2, LocalIsometryAlt.int_cmul, hP2 f hf]
    ring
  intro y
  obtain ⟨y₁, y₂, y₃, y₄, rfl, ⟨t, ht⟩, ⟨c, hc, hc'⟩, ⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hD n y
  have h1 : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  exact hIso_mul _ _ (hIso_mul _ _ (hIso_mul _ _ (hIso_n y₁ _ h1 ht) (hIso_nb y₂ c hc hc')) (hIso_m y₃ a ha ha'))
    (hIso_n y₄ b hb hb')

end PositivityTheory.Rg.Sw.Glob
end
end

