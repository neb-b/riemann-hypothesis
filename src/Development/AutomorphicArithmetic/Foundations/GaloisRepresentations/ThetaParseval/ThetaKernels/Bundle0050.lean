module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0017
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousCjK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
def Ap_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (hU.1 u).choose
theorem inFrame_uM_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) := (hU.1 u).choose_spec
theorem uM_add_k (hU : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU (u + v)) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k]
theorem uM_zero_k (hU : L.UData uM ν 𝓤) : uM 0 = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := 1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU 0) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.fromBlocks_one]
theorem uM_neg_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
theorem Ap_neg_mul_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u = 1 := by
  have h := congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_one, ← Matrix.fromBlocks_one] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact (Matrix.fromBlocks_inj.1 h).2.2.2
theorem frame_conj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    inFrame d.b ((uM u)⁻¹ * nb β * uM u) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) 0 1 := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_neg_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, hN β,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU]
theorem cj_mem_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u ∈ nA σ d.Y d.b :=
  AddSubgroup.subset_closure ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN u β⟩
def cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b →+ nA σ d.Y d.b where
  toFun β := ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mem_k hU hN u β⟩
  map_zero' := Subtype.ext (by simp)
  map_add' β β' := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
theorem cj_val_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1 = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u := rfl
theorem nb_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = (uM u)⁻¹ * nb β * uM u := by
  apply kunf.inFrame_injective d.b
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN, hN]
  rfl
theorem cj_inv_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = β := by
  apply Subtype.ext
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k]
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) = 1 := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU (-u)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, neg_neg]
  calc _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)
      = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u)) * β.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)) := by simp only [Matrix.mul_assoc]
    _ = β.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
theorem continuous_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) :
    Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u) :=
  ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
def cjE_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b ≃ₜ+ nA σ d.Y d.b where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u
  invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u)
  left_inv β := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN u β
  right_inv β := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN (-u) β
  map_add' := map_add _
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN u
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN (-u)
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousPhzK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem continuous_phz_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : d.G → ℂ} (hf : Continuous f) (s₁ z : ℂ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  have ha := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_a'_k d
  have e : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁) := by
    funext x; rw [_root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
  have h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) := by
    rw [e]
    exact (Complex.continuous_ofReal.comp ha).cpow continuous_const
      (fun x => Complex.ofReal_mem_slitPlane.2 (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d x))
  exact h1.mul hf
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
structure Hyp_k (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 A'
  δ0 : δ ≠ 0
def sM_k (b : Fin L.n → AE F E) : d.G := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.elt_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b))
def pb_k (β : nA σ d.Y d.b) : Fin L.n → AE F E := fun j => β.1 L.i₀ (L.em j)
def pa_k (δ : E) (β : nA σ d.Y d.b) : AF F := ellA δ (β.1 L.i₀ L.i₀)
def eisensteinSecondTerm (Φ : d.G → ℂ) (g : d.G) : ℂ := ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, Φ (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSeriesAbsoluteConvergence
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_absolute_convergence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  first | exact @_root_.GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane_k | exact _root_.GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane_k | (intros; apply _root_.GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSeriesLeftInvariance
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_left_invariance : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  first | exact @_root_.GlobalTheory.CompanionTheory.EisHalf.eis_half_plane_k | exact _root_.GlobalTheory.CompanionTheory.EisHalf.eis_half_plane_k | (intros; apply _root_.GlobalTheory.CompanionTheory.EisHalf.eis_half_plane_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsLagrIntNeZeroK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.LagrUniq
theorem exists_lagrInt_ne_zero_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ φ ∈ schA F κ, GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 hν h𝓕
  have hstd : IsStd B.ψ := hB.std
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  set C : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hC
  set C₀ : Matrix (Fin (nT + nT)) (Fin nT) E :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) E).submatrix finSumFinEquiv.symm id with hC₀
  have hCC : C = incM F C₀ := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> by_cases h : i = j <;>
      simp only [hC, hC₀, incM, diagCols, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply, id,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply, h, if_true, if_false, map_one, map_zero]
  let mC : WOF F E nS nT →ₗ[AF F] Matrix (Fin (nT + nT)) (Fin nS) (AF F ⊗[F] E) :=
    { toFun := fun u => C * u
      map_add' := fun u v => Matrix.mul_add _ _ _
      map_smul' := fun t u => Matrix.mul_smul _ _ _ }
  let Lm : WOF F E nS nT →ₗ[AF F] (κ → AF F) × (κ → AF F) := co.e.toLinearMap ∘ₗ mC
  have hLm : ∀ u, Lm u = co.e (C * u) := fun u => rfl
  let S := LinearMap.range Lm
  have hiso : ∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    have h := co.form (C * u) (C * u')
    rw [GlobalTheory.WeilDiagIso.symp_diag_eq_zero F E σ nS nT JT JB ξ u u'] at h
    rw [hLm, hLm]
    exact (sub_eq_zero.mp h.symm)
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      Lm (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro x
    have e : C * incM F x = incM F (C₀ * x) := by
      rw [hCC]
      simp only [incM]
      exact (Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E))).symm
    obtain ⟨y, z, h⟩ := hco (C₀ * x)
    exact ⟨y, z, by rw [hLm, e, h]⟩
  have hspan : S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} := by
    rintro _ ⟨u, rfl⟩
    have hu := Submodule.mem_map_of_mem (f := Lm) (GlobalTheory.matrix_mem_span_incM F E nT nS u)
    rw [Submodule.map_span] at hu
    refine Submodule.span_mono ?_ hu
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨⟨incM F x, rfl⟩, y, z, h⟩
  obtain ⟨Φ, hΦ, hcont, hre, hre0⟩ := GlobalTheory.ThetaPosIso.exists_theta_re_nonneg F B.ψ hstd κ S hiso hspan
  refine ⟨Φ, hΦ, ?_⟩
  have hI : ∀ u : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) = thetaSum F (schr B.ψ (Lm u) Φ) :=
    fun u => rfl
  show ∫ u in 𝓕, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) ∂ν ≠ 0
  simp_rw [hI]
  refine GlobalTheory.PeriodicPositiveIntegral.integral_ne_zero F E nS nT (fun u => thetaSum F (schr B.ψ (Lm u) Φ)) ?_ ?_ ?_ ?_ ν 𝓕 hν h𝓕
  · exact hcont.comp (IsModuleTopology.continuous_of_linearMap Lm)
  · rintro _ ⟨γ₀, rfl⟩ u
    obtain ⟨y, z, h⟩ := hrat γ₀
    have e1 : Lm (((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS)) γ₀ + u) = Lm (incM F γ₀) + Lm u := by
      rw [map_add (f := _)]; rfl
    have hr : Lm (incM F γ₀) ∈ S := ⟨incM F γ₀, rfl⟩
    have hw : Lm u ∈ S := ⟨u, rfl⟩
    have hi := hiso _ hw _ hr
    rw [h] at hi
    show thetaSum F (schr B.ψ (Lm (_ + u)) Φ) = _
    rw [e1, h, GlobalTheory.ThetaRatInv.thetaSum_schr_rat_add B.ψ hstd.2.1 Φ y z (Lm u), hi, sub_self, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro u; exact hre _ ⟨u, rfl⟩
  · show 0 < (thetaSum F (schr B.ψ (Lm 0) Φ)).re
    rw [map_zero]; exact hre0
theorem lagr_invariant_unique_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσξ₀ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 l hl hinv
  have hstd : IsStd B.ψ := hB.std
  obtain ⟨L, hiso, hdim, hL⟩ := GlobalTheory.WeilSchrodinger.DiagLagr.exists_diag_lagrangian F E σ nS nT JT JB ξ κ co hco
  obtain ⟨l₂, hl₂, he⟩ := _root_.GlobalTheory.LagrThetaAdm.exists_admissible_eq_lagrangian_integral F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  obtain ⟨φ₀, hφ₀, hne⟩ := _root_.GlobalTheory.LagrUniq.exists_lagrInt_ne_zero_k F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  have hrho : ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ),
      (GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (uᵀ * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ = co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ := by
    intro u φ
    rw [GlobalTheory.WeilSchrodinger.transD_rho, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hmem : ∀ w, ∀ φ ∈ schA F κ, co.rho B.ψ w φ ∈ schA F κ := fun w φ hφ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ
  have key : ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ, l' (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ) = l' φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
        l' (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    intro l' h t w hw φ hφ
    obtain ⟨u, hu⟩ := hL t w hw
    rw [← hu]
    exact h u φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.AdelicSvN.main F B.ψ hstd κ L hiso hdim l hl l₂ hl₂
    (key l (fun u φ hφ => by rw [← hrho]; exact hinv _ φ hφ))
    (key l₂ (fun u φ hφ => by
      rw [he _ (hmem _ φ hφ), he φ hφ]
      exact _root_.GlobalTheory.LagrThetaInv.lagrInt_rho_inv_k F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕 u φ hφ))
    ⟨φ₀, hφ₀, by rw [he φ₀ hφ₀]; exact hne⟩
  exact ⟨c, fun Φ hΦ => by rw [hc Φ hΦ, he Φ hΦ]⟩
end GlobalTheory.LagrUniq
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsStandardHermitianSpace
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_standard_hermitian_space {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Y₀ : Spc F E n) (b₀ : GL (Fin n ⊕ Fin n) E) (K₀ : Subgroup (G2 σ Y₀)) (a₀ : G2 σ Y₀ → ℝ),
      IsFrame2 σ Y₀ b₀ ∧ b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n 1 ∧
      IsStdK (σ := σ) (Y := Y₀) B b₀ K₀ ∧ IsHgt K₀ a₀ := by
  obtain ⟨b, K, a, hb, hK, ha, -, -⟩ :=
    _root_.GlobalTheory.ThK.Dbl.stdEx_of_k _root_.GlobalTheory.ThK.Dbl.frameConj_k _root_.GlobalTheory.ThK.Dbl.hgtEx_k F E σ B n (UnitHermitianSpace.unitSpc F E n) n 0 hB (Or.inl (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n))
  refine ⟨UnitHermitianSpace.unitSpc F E n, b, K, a, hb, ?_, hK, ha⟩
  obtain ⟨ε, hε⟩ := hb.1
  have hc : ∀ z : E, σ (σ z) = z := (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n).herm |> fun _ => by
    intro z
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have h1 := eps_one hn hc (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n).herm hε
  rw [hε, eps_unit h1]
  simp [Ald.jeps]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsThetaFunctionalSplitIdempotent
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
theorem _root_.GlobalTheory.T.exists_theta_functional_split_idempotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  first | exact @_root_.GlobalTheory.SplitInvFormF.exists_invForm_split_k | exact _root_.GlobalTheory.SplitInvFormF.exists_invForm_split_k | (intros; apply _root_.GlobalTheory.SplitInvFormF.exists_invForm_split_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FundamentalDomainHaarParseval
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.fundamental_domain_haar_parseval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle,
        (∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f) →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f₀ ≠ 0 →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) → α t = χS (Matrix.GeneralLinearGroup.det t) := by
  first | exact @_root_.PositivityTheory.ThKW.fundamental_domain_parseval_global | exact _root_.PositivityTheory.ThKW.fundamental_domain_parseval_global | (intros; apply _root_.PositivityTheory.ThKW.fundamental_domain_parseval_global <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzLeftInvK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem phz_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ rat2 σ d.Y) (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  intro p hp g
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp.1
  obtain ⟨T, hT⟩ := par_rat ht hp.2
  obtain ⟨u, hu⟩ := det_rat hT
  have ha : d.a (p * g) = d.a g := by
    rw [IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]; simp
  have hfp : f (p * g) = f g := Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha, hfp]
theorem eis_leftInv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    ∀ γ ∈ rat2 σ d.Y, ∀ g, d.eis f s₁ z (γ * g) = d.eis f s₁ z g :=
  GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z)
theorem fc_dom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 𝓖₀ : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (h₀ : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀)
    (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T g = fc d.B.ψ d.b nb lam 𝓖₀ φ T g := by
  unfold fc
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  refine h.2.2.1.setIntegral_eq h₀.2.2.1 fun β₀ β => ?_
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

