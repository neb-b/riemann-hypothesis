module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0034
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0021
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0038
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
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0033
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReTraceEq
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCell
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0036
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoH
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

def cθ (θ : InfFam D) (τ : D.what₂.Tau) : AE D →+* ℂ := (θ τ).comp (infPart D)

theorem compAt_eq {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (w : Mx D m k) : compAt θ τ w = w.map (cθ θ τ) := rfl

theorem compAt_mul' {θ : InfFam D} {τ : D.what₂.Tau} {m k l : ℕ} (x : Mx D m k) (y : Mx D k l) :
    compAt θ τ (x * y : Mx D m l) = compAt θ τ x * compAt θ τ y := by
  simp only [compAt_eq]; exact Matrix.map_mul

theorem compAt_one' {θ : InfFam D} {τ : D.what₂.Tau} {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  simp only [compAt_eq]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_zero' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} : compAt θ τ (0 : Mx D m k) = 0 := by
  ext i j; simp [compAt_eq]

theorem compAt_add' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x y : Mx D m k) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j; simp [compAt_eq]

theorem component_block_matrix {θ : InfFam D} {τ : D.what₂.Tau} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d : Mx D (n + n) (n + n)) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) :=
  GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem ae_ext {θ : InfFam D} (hθ : IsInfFam θ) {z z' : AE D} (h1 : ∀ τ, cθ θ τ z = cθ θ τ z')
    (h2 : finPart D z = finPart D z') : z = z' := by
  have h := (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 (z - z') (fun τ => by
      have := h1 τ
      simp only [cθ, RingHom.comp_apply] at this
      rw [RingHom.map_sub, RingHom.map_sub, this, sub_self])
    (by rw [RingHom.map_sub, h2, sub_self])
  exact sub_eq_zero.mp h

theorem mx_ext {θ : InfFam D} (hθ : IsInfFam θ) {m k : ℕ} {x x' : Mx D m k} (h1 : ∀ τ, compAt θ τ x = compAt θ τ x')
    (h2 : x.map (finPart D) = x'.map (finPart D)) : x = x' := by
  ext i j
  exact ae_ext hθ (fun τ => congrFun (congrFun (h1 τ) i) j) (congrFun (congrFun h2 i) j)

theorem cθ_cA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : AE D) : cθ θ τ (cA D z) = conj (cθ θ τ z) :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 z τ

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) z) =
    (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) z)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
  rfl

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayNZ
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayNZ : AwayNZ := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  classical
  have hl : ∀ τ', l τ' ≠ 0 := fun τ' => lNe D ψ θ l hC.hψ hC.hθ hC.hl τ'
  let W : AddSubgroup (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin V.rank) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let Ψ : Mx D V.rank n → ℂ := fun x =>
    evalPoly (1 : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (fun τ => compAt θ τ x) *
      gAway V l s τ (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))
  have hΨ : Ψ ∈ awayA θ V n l s τ := Submodule.subset_span ⟨1, g, hg, by simp, rfl⟩
  refine ⟨Ψ, 0, awayIn D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl Ψ hΨ, ?_⟩
  have h0 : ∀ τ', compAt θ τ' (0 : Mx D V.rank n) = 0 := fun τ' => by
    ext i j
    simp [compAt]
  have hg0 : g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 1 := by
    simp only [g]
    rw [if_pos]
    simp only [Matrix.zero_apply, map_zero]
    exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin V.rank) (Fin n) _)).2 W.zero_mem
  show evalPoly _ _ * gAway V l s τ _ * g _ ≠ 0
  rw [hg0]
  simp only [evalPoly, map_one, one_mul, mul_one, gAway, h0]
  simp

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousBw
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (a b : Mx D m n) :
    compAt θ τ (a + b) = compAt θ τ a + compAt θ τ b := by
  ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]

set_option synthInstance.maxHeartbeats 400000 in
theorem finMap_add (a b : Mx D m n) : (a + b).map (finPart D) = a.map (finPart D) + b.map (finPart D) := by
  ext i j; simp only [Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]

theorem away_add {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (y : Mx D m n) (u : Fin m → Fin n → ℂ) :
    Ψ (y + sIns τ fr u) = Ψ y := by
  refine hΨ.1 _ _ (fun τ' hne => ?_) ?_
  · rw [compAt_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, compAt_insT hθ, ite_eq_right hne,
      add_zero]
  · rw [finMap_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, finMap_insT, add_zero]

theorem cont_of_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) : Continuous Ψ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hc := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨_, hmem⟩
  have hg : Continuous fun x : Mx D m n => gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    have h1 : Continuous fun x : Mx D m n => (S (piF θ τ fr x)) := S.continuous.comp (continuous_piF hθ τ fr)
    refine h1.congr fun x => ?_
    rw [hS]; rfl
  have hne : ∀ x : Mx D m n, gs (n := n) 1 (fr⁻¹ * compAt θ τ x) ≠ 0 := fun x => Complex.exp_ne_zero _
  have e : Ψ = fun x => tens θ τ fr (gs 1) Ψ x / gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    funext x
    simp only [tens]
    field_simp [hne x]
  rw [e]
  exact hc.div hg hne

def Bw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) : ℂ :=
  Ψ y * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y - sIns τ fr (piF θ τ fr y)))))

theorem Bw_add {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (x y : Mx D V.rank n) (u : Fin V.rank → Fin n → ℂ) :
    Bw ψ V θ τ fr Ψ x (y + sIns τ fr u) = Bw ψ V θ τ fr Ψ x y := by
  have e : y + sIns τ fr u - sIns τ fr (piF θ τ fr (y + sIns τ fr u)) = y - sIns τ fr (piF θ τ fr y) := by
    rw [map_add (piF θ τ fr), piF_sIns hθ τ hdet, map_add (sIns τ fr)]
    abel
  unfold Bw
  rw [away_add hθ hΨ, e]

set_option synthInstance.maxHeartbeats 800000 in
theorem continuous_Bw {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (x : Mx D V.rank n) :
    Continuous (Bw ψ V θ τ fr Ψ x) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : ContinuousSub (Mx D V.rank n) := inferInstance
  refine (cont_of_away hθ hΨ).mul ?_
  have htr : Continuous (trA (D := D)) := by
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    exact IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hinner : Continuous (fun y : Mx D V.rank n => GlobalTheory.StdUnn.inner V x y) := by
    unfold GlobalTheory.StdUnn.inner
    exact continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id)
  have h := hψ.1.comp (htr.comp hinner.matrix_trace)
  exact h.comp (continuous_id.sub ((continuous_sIns τ fr).comp (continuous_piF hθ τ fr)))

theorem norm_Bw {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    ‖Bw ψ V θ τ fr Ψ x y‖ = ‖Ψ y‖ := by
  unfold Bw; rw [norm_mul, hψ.2.1, mul_one]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem lIcell_of' (hAw : AwayAct) (hLc : LIcont) (hLl : LIlaw) (hLv : LIvac) : LIcell :=
  lIcell_of hAw decompAway unipTau awayIn schFP lNe hLc hLl hLv

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem lIlin : LIlin := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  have hfr : IsUnit fr.det := hC.hfr.1
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  refine ⟨fun y a P Q => ?_, fun P => ?_⟩
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have hlin : phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (a • P + Q) =
        a • phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P + phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) Q := by
      apply Subtype.ext
      rw [LocLawH.phiS_val (mem _), Submodule.coe_add, Submodule.coe_smul, LocLawH.phiS_val (mem P), LocLawH.phiS_val (mem Q)]
      funext x
      simp only [tens, fP, evX, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), MvPolynomial.smul_eval]
      ring
    rw [← hL y _ hΨ (a • P + Q), hlin, map_add (f := _), map_smul, Submodule.coe_add, Submodule.coe_smul, hL y _ hΨ P,
      hL y _ hΨ Q]
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    show a * (L y (fP (cLoc l τ) P) _ * _) + L y (fP (cLoc l τ) Q) _ * _ =
      (a * L y (fP (cLoc l τ) P) _ + L y (fP (cLoc l τ) Q) _) * _
    ring
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have e := hL 1 _ hΨ P
    rw [map_one, map_one, Module.End.one_apply, LocLawH.phiS_val (mem P)] at e
    exact e.symm

theorem lIcont : LIcont := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have key : sLd L (cLoc l τ) P = fun y => (ω (ι y) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 := by
    funext y
    rw [hL y _ hΨ P, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one]
    rfl
  rw [key]
  obtain ⟨𝓕, h𝓕⟩ := hC.hμ
  exact (GlobalTheory.StdUnn.weilSch_apply_zero_continuous D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 h𝓕 ω hC.hω
    (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).comp hC.hι.1

theorem lIkact : LIkact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  have hk' : ω (ι k) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P) =
      phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P) := by
    apply Subtype.ext
    rw [hL k _ hΨ P, hρ k P hk, LocLawH.phiS_val (mem _)]
  have e : (ω (ι (g * k)) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 =
      (ω (ι g) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P))).1 0 := by
    rw [map_mul, map_mul, Module.End.mul_apply, hk']
  rw [hL (g * k) _ hΨ P, hL g _ hΨ (ρ k P), LocLawH.tens_zero, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one, mul_one] at e
  exact e

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem locOpEx_of_locFact (hF : LocFact) : LocOpEx := locOpEx_of_fact hF awayIn schFP lNe

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoI
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
set_option maxHeartbeats 4000000

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  delta PositivityTheory.Rg.Sw.Glob.phiS
  rw [dite_eq_left h]

theorem tens_add_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (a : ℂ)
    (f g : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) :
    tens θ τ fr (a • f + g) Ψ = a • tens θ τ fr f Ψ + tens θ τ fr g Ψ := by
  funext x
  delta PositivityTheory.Rg.Sw.Glob.tens
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (a * f (fr⁻¹ * compAt θ τ x) + g (fr⁻¹ * compAt θ τ x)) * Ψ x = _
  ring

theorem tensor_gaussian_vacuum_injective {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr g (psi0 θ V n l s τ)) : f = g := by
  have hdet : IsUnit fr.det := hfr.1
  suffices hU : ∀ U : Matrix (Fin V.rank) (Fin n) ℂ, f U = g U from funext hU
  intro U
  have hx := congrFun h (xL θ τ (fr * U))
  have hc : compAt θ τ (xL θ τ (fr * U)) = fr * U := by
    have h1 := congrFun (compAt_xL hθ τ (fr * U)) τ
    simpa [dirAt_self] using h1
  have hp : psi0 θ V n l s τ (xL θ τ (fr * U)) = 1 := by
    show gAway V l s τ (fun τ' => compAt θ τ' (xL θ τ (fr * U))) *
      g0 D V.rank n (fun i j => finPart D (xL θ τ (fr * U) i j)) = 1
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ, gaussian_at_zero_eq_one, one_mul]
  have hinv : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hdet, Matrix.one_mul]
  change f (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) =
    g (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) at hx
  rw [hc, hp, hinv, mul_one, mul_one] at hx
  exact hx

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

