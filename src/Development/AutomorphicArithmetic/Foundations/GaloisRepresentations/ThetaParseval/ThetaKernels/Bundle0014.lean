module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsTraceZeroElement
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_zero_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  first | exact @_root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k | exact _root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k | (intros; apply _root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExtendCharacterToNormGroup
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_character_to_norm_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  first | exact @_root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | exact _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | (intros; apply _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaInvariant
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_theta_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  first | exact @_root_.UpperTheory.TP.W.IsLatRepL.real_triv | exact _root_.UpperTheory.TP.W.IsLatRepL.real_triv | (intros; apply _root_.UpperTheory.TP.W.IsLatRepL.real_triv <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaLevel
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_theta_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  first | exact @_root_.GlobalTheory.FinLatF.latRepF_cont_k | exact _root_.GlobalTheory.FinLatF.latRepF_cont_k | (intros; apply _root_.GlobalTheory.FinLatF.latRepF_cont_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaSupport
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_theta_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  first | exact @_root_.GlobalTheory.FinLatHeis.isLatRepF_heis_k | exact _root_.GlobalTheory.FinLatHeis.isLatRepF_heis_k | (intros; apply _root_.GlobalTheory.FinLatHeis.isLatRepF_heis_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeckeCharacterTrivialOfSplit
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.hecke_character_trivial_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 →
        ν x = 1) → ∀ x, ν x = 1 := by
  first | exact @_root_.GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split_k | exact _root_.GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split_k | (intros; apply _root_.GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisOFDblGDeltaTK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblHeis
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heisOF_dblG_deltaT_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ w f₁ f₂
  have hn : ∀ x, ‖B.ψ x‖ = 1 := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1.2.1
  funext x
  have ht : topR (x + w) = topR x + topR w := rfl
  have hb : -botR (x + w) = -botR x + -botR w := by
    rw [← neg_add]; rfl
  simp only [heisOF, deltaT_apply, ht, hb, symplOHF_dblG, map_mul, conj_psi hn, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring
end GlobalTheory.DblHeis
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HermitianFormMatrixSelfadjoint
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  first | exact @_root_.GlobalTheory.RealWeilF.HMF_herm_det_k | exact _root_.GlobalTheory.RealWeilF.HMF_herm_det_k | (intros; apply _root_.GlobalTheory.RealWeilF.HMF_herm_det_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.InertCompletionIsField
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_completion_isField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  first | exact @_root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k | exact _root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k | (intros; apply _root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.InertofProofK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThK
open NumberField IsDedekindDomain GlobalTheory.AdelicU
theorem inertof_proof_k : _root_.PositivityTheory.ThK.InertOf_k := by
  intro F E _ _ _ _ _ σ B hB v he
  haveI := hB.unram
  haveI := v.isMaximal
  have h1 := ncard_primesOver_le_two hB.cm v
  have h2 : (v.asIdeal.primesOver (𝓞 E)).ncard ≠ 2 := fun h =>
    not_nonempty_iff.2 he ((nonempty_split_iff hB.cm).2 h)
  have h3 : 0 < (v.asIdeal.primesOver (𝓞 E)).ncard := Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)
  exact map_eq_of_ncard_eq_one v (by omega)
end PositivityTheory.ThK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsCompactStandardMaximalCompact
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_standard_maximal_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  first | exact @_root_.GlobalTheory.CompanionTheory.StdK.isCompact_K_k | exact _root_.GlobalTheory.CompanionTheory.StdK.isCompact_K_k | (intros; apply _root_.GlobalTheory.CompanionTheory.StdK.isCompact_K_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ItemsThkhLocrep
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKH.Locrep
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem locRepEx_k : _root_.PositivityTheory.ThK.LocRepEx_k := by
  intro F E _ _ _ _ _ σ n d B X W M om hP v
  obtain ⟨χX, χW, hw⟩ := hP.weil
  have hs := IsUWeilPair.isUSplitting hw
  have hstd := hP.base.std
  have hne : B.ψ ≠ 1 := fun h => GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hstd v (by rw [h]; rfl)
  have hH := (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F (Fin n × Fin d) B.ψ hstd.1 hne hstd.2.1).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ) → Module.End ℂ (Fn F n d v) := fun T =>
    res v x₀ ∘ₗ T ∘ₗ tensL v r₀
  have hloc : ∀ T φ, loc T φ = res v x₀ (T (tens (evFin F v) φ r₀)) := fun _ _ => rfl
  have pres : ∀ p, ∀ φ ∈ SB _, loc (om p) φ ∈ SB _ := fun p φ hφ => res_mem v x₀ (hs.pres p _ (h₀ φ hφ).2)
  have presH : ∀ u, ∀ φ ∈ SB _, loc (schrL B.ψ (M.co.e u)) φ ∈ SB _ := fun u φ hφ => res_mem v x₀ (hH _ _ (h₀ φ hφ).2)
  have acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      Acts (evFin F v) (om (g, h)) φ (loc (om (g, h)) φ) := by
    intro g hg h hh φ hφ
    refine acts_res v hstd.1 hne hstd.2.1 (hs.pres _) (hs.adm _) (fun w h1 h2 Φ hΦ => ?_) h₁ hφ (h₀ φ hφ)
    obtain ⟨u, rfl⟩ := M.co.e.surjective w
    have hu : atPlace v (1 : Fv F v) • u = 0 := by
      apply M.co.e.injective
      rw [map_smul, map_zero]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · change atPlace v 1 * (M.co.e u).1 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).1 i) = 0 from congrFun h1 i, mul_zero, map_zero]
      · change atPlace v 1 * (M.co.e u).2 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).2 i) = 0 from congrFun h2 i, mul_zero, map_zero]
    have := hs.impl (g, h) u Φ hΦ
    rwa [show actAB (cA σ) (g, h) u = u from act_away hg hh hu] at this
  have actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
      Acts (evFin F v) (M.co.rho B.ψ u) φ (loc (schrL B.ψ (M.co.e u)) φ) := by
    intro u hu φ hφ
    have e : ∀ a, evFin F v a = 0 → a • M.co.e u = 0 := fun a ha => by rw [← map_smul, hu a ha, map_zero]
    have A : Acts (evFin F v) (M.co.rho B.ψ u) φ _ := fun r hr =>
      GlobalTheory.SchrLoc.schr_tens_of_at B.ψ v (M.co.e u) (fun i a ha => congrFun (congrArg Prod.fst (e a ha)) i)
        (fun i a ha => congrFun (congrArg Prod.snd (e a ha)) i) φ r hr.1
    have := eq_of_acts v h₁ (h₀ φ hφ) A
    rw [this] at A
    exact A
  have one : ∀ φ ∈ SB _, loc (om 1) φ = φ := fun φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm
  have mul : ∀ p : UA σ X.J × UA σ W.J, ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      loc (om (p * (g', h'))) φ = loc (om p) (loc (om (g', h')) φ) := fun p g' hg' h' hh' φ hφ => by
    rw [hloc, hloc (om p), ← acts g' hg' h' hh' φ hφ r₀ (h₀ φ hφ), map_mul]
    rfl
  refine ⟨fun p => loc (om p), fun u => loc (schrL B.ψ (M.co.e u)), fun g _ h _ => pres _,
    fun g hg h hh φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ acts g hg h hh φ hφ⟩, one,
    fun g _ h _ => mul (g, h), fun φ hφ => ?_, fun u _ => presH u,
    fun u hu φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ actsH u hu φ hφ⟩,
    fun g hg h hh u hu φ hφ => ?_⟩
  · obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ W v
    obtain ⟨m, hm⟩ := smooth_of_weak (SB _) K hK1 hK2 (fun h => loc (om (1, h))) (fun h _ => pres _) one
      (fun h _ h' hh' φ hφ => by
        have := mul (1, h) 1 (one_mem_UAt X v) h' (hK3 0 hh') φ hφ
        rwa [Prod.mk_mul_mk, one_mul] at this)
      (fun l φ hφ => (hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2).comp (continuous_const.prodMk continuous_id)) φ hφ
    obtain ⟨U, hU, hUK⟩ := hK4 m
    exact ⟨U, hU, fun h hh hv => hm h (hUK h hh hv)⟩
  · change loc (om (g, h)) (loc (schrL B.ψ (M.co.e u)) φ) = loc (schrL B.ψ (M.co.e _)) (loc (om (g, h)) φ)
    rw [hloc (om (g, h)), hloc _ (loc (om (g, h)) φ), ← actsH u hu φ hφ r₀ (h₀ φ hφ),
      ← acts g hg h hh φ hφ r₀ (h₀ φ hφ), hs.impl _ _ _ (h₀ φ hφ).2]
    rfl
end PositivityTheory.ThKH.Locrep
end
end
end

