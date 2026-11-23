module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivRestrictsRealLinearEquivArchimed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilAdm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infPart (w : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1

theorem infPart_infE (z : κ → mixedEmbedding.mixedSpace F) : infPart (infE F z) = z := by
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem infE_infPart (w : κ → AdeleRing (𝓞 F) F) (h : ∀ i, (w i).2 = 0) : infE F (infPart w) = w := by
  funext i
  refine Prod.ext ?_ (h i).symm
  exact RingEquiv.symm_apply_apply _ _

def eInf : AdeleRing (𝓞 F) F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem eInf_smul_snd (w : κ → AdeleRing (𝓞 F) F) (i : κ) : ((eInf (F := F) • w) i).2 = 0 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = 0
  exact zero_mul _

theorem eInf_smul_infE (z : κ → mixedEmbedding.mixedSpace F) : eInf (F := F) • infE F z = infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (1 : InfiniteAdeleRing F) * _ = _
    exact one_mul _
  · show (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    exact zero_mul _

theorem infE_add (z z' : κ → mixedEmbedding.mixedSpace F) : infE F (z + z') = infE F z + infE F z' := by
  funext i
  refine Prod.ext ?_ ?_
  · exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 + 0
    exact (add_zero _).symm

theorem infPart_add (w w' : κ → AdeleRing (𝓞 F) F) : infPart (w + w') = infPart w + infPart w' := by
  funext i
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (w i).1 (w' i).1

def rAd (t : ℝ) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)), 0)

theorem infE_smul (t : ℝ) (z : κ → mixedEmbedding.mixedSpace F) : infE F (t • z) = rAd (F := F) t • infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • z i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i)
    rw [← map_mul, smul_mul_assoc, one_mul]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    exact (zero_mul _).symm

theorem infPart_smul (t : ℝ) (w : κ → AdeleRing (𝓞 F) F) : infPart (rAd (F := F) t • w) = t • infPart w := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)) * (w i).1) =
    t • InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1
  rw [map_mul, RingEquiv.apply_symm_apply, smul_mul_assoc, one_mul]

def infPart2 (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) := (infPart w.1, infPart w.2)

theorem archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    infPart2 (mixedSpaceVecPairAsAdeles F v) = v := by
  simp only [infPart2, mixedSpaceVecPairAsAdeles, infPart_infE]

theorem archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    eInf (F := F) • mixedSpaceVecPairAsAdeles F v = mixedSpaceVecPairAsAdeles F v := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.smul_mk, eInf_smul_infE]

theorem mixedSpaceVecPair_archimedeanPart_idempotent_smul (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (eInf (F := F) • w)) = eInf (F := F) • w := by
  show (infE F (infPart (eInf (F := F) • w.1)), infE F (infPart (eInf (F := F) • w.2))) =
    (eInf (F := F) • w.1, eInf (F := F) • w.2)
  rw [infE_infPart _ (eInf_smul_snd w.1), infE_infPart _ (eInf_smul_snd w.2)]

theorem mixedSpaceVecPair_archimedeanPart_linearMap_apply (f : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) →ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (f (mixedSpaceVecPairAsAdeles F v))) = f (mixedSpaceVecPairAsAdeles F v) := by
  rw [← archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles v, map_smul]
  exact mixedSpaceVecPair_archimedeanPart_idempotent_smul _

theorem mixedSpaceVecPairAsAdeles_add (v v' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (v + v') = mixedSpaceVecPairAsAdeles F v + mixedSpaceVecPairAsAdeles F v' := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.fst_add, Prod.snd_add, infE_add, Prod.mk_add_mk]

theorem mixedSpaceVecPairAsAdeles_real_smul (t : ℝ) (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (t • v) = rAd (F := F) t • mixedSpaceVecPairAsAdeles F v := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.smul_fst, Prod.smul_snd, infE_smul, Prod.smul_mk]

theorem infPart2_add (w w' : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (w + w') = infPart2 w + infPart2 w' := by
  simp only [infPart2, Prod.fst_add, Prod.snd_add, infPart_add, Prod.mk_add_mk]

theorem infPart2_smul (t : ℝ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (rAd (F := F) t • w) = t • infPart2 w := by
  simp only [infPart2, Prod.smul_fst, Prod.smul_snd, infPart_smul, Prod.smul_mk]

theorem exists_infLin (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∀ v, B (mixedSpaceVecPairAsAdeles F v) = mixedSpaceVecPairAsAdeles F (L v) := by
  refine ⟨{ toFun := fun v => infPart2 (B (mixedSpaceVecPairAsAdeles F v))
            invFun := fun v => infPart2 (B.symm (mixedSpaceVecPairAsAdeles F v))
            map_add' := fun v v' => by simp only [mixedSpaceVecPairAsAdeles_add, map_add (f := _), infPart2_add]
            map_smul' := fun t v => by simp only [mixedSpaceVecPairAsAdeles_real_smul, map_smul, infPart2_smul, RingHom.id_apply]
            left_inv := fun v => by
              show infPart2 (B.symm (mixedSpaceVecPairAsAdeles F (infPart2 (B.toLinearMap (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [mixedSpaceVecPair_archimedeanPart_linearMap_apply]
              simp [archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
            right_inv := fun v => by
              show infPart2 (B (mixedSpaceVecPairAsAdeles F (infPart2 (B.symm.toLinearMap (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [mixedSpaceVecPair_archimedeanPart_linearMap_apply]
              simp [archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles] }, fun v => ?_⟩
  exact (mixedSpaceVecPair_archimedeanPart_linearMap_apply B.toLinearMap v).symm

theorem infLin_main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))),
      ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
        ∀ v, B (GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F v) = GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F (L v) :=
  fun _ _ _ _ _ B => exists_infLin B

end GlobalTheory.WeilAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousFiniteRealPoint
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section
namespace GlobalTheory.AdelicCoordF

open GlobalTheory.AdelicCoord (incF incI incF_sndA incI_fstA pairA_mul_eq_zero_iff_snd pairA_mul_eq_zero_iff_fst)

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secF : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incF F) LinearMap.id

def secI : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incI F) LinearMap.id

theorem secF_finPart (z : AF F ⊗[F] E) :
    secF F E (Formalism.IndefR.DatumF.finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem secI_infPart (z : AF F ⊗[F] E) :
    secI F E (Formalism.IndefR.DatumF.infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E (pairA F 0 1 • z) = Formalism.IndefR.DatumF.finPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E (pairA F 1 0 • z) = Formalism.IndefR.DatumF.infPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, map_zero]
  · intro h; rw [← finPartF_smul, h, map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, map_zero]
  · intro h; rw [← infPartF_smul, h, map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF F) (w : GlobalTheory.ThetaTransform.VA F N) :
    c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    Continuous e ∧ Continuous e.symm ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔
        GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔
        GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  intro F E _ _ _ _ _ nS nT N e
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI hA : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin nS → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoordF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLin
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SchLine

theorem continuous_pureA (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : Continuous (pureA F f g) := by
  unfold pureA
  refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_)) (hg.1.continuous.comp (continuous_pi fun i => ?_))
  · exact (continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  · exact continuous_snd.comp (continuous_apply i)

theorem continuous_of_mem (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact continuous_pureA F f g hg
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact h.const_smul a

theorem line_shift (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t s : ℝ) :
    x + (fun i => infAd F (s • v i)) = (x + fun i => infAd F (t • v i)) + fun i => infAd F ((s - t) • v i) := by
  funext i
  simp only [Pi.add_apply]
  rw [add_assoc, ← infAd_add, ← add_smul, add_sub_cancel]

theorem schline : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  intro F _ _ κ _ g hg
  refine ⟨continuous_of_mem F hg, fun v x t => ?_⟩
  set y : κ → AF F := x + fun i => infAd F (t • v i)
  have h0 : HasDerivAt (fun u : ℝ => g (y + fun i => infAd F (u • v i))) (dD F v g y) (t - t) := by
    rw [sub_self]
    exact ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hg).1 y).hasDerivAt
  have h1 := h0.comp_sub_const t t
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show g (x + fun i => infAd F (s • v i)) = g (y + fun i => infAd F ((s - t) • v i))
  rw [line_shift F x v t s]

end GlobalTheory.ArchDecay.SchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCoordsMovedStaySupportedAndRecovered
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem at_mul_of_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n d : ℕ} (G : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (H : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (L : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hL : At (evI F) L) : At (evI F) (G * L * Hᵀ) := by
  intro u hu
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hL u hu, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_infAd_of_evI {F : Type} [Field F] [NumberField F] (u : AF F) (hu : evI F u = 0)
    (α : mixedEmbedding.mixedSpace F) : u * infAd F α = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
  refine Prod.ext ?_ ?_
  · show u.1 * _ = 0
    rw [h1, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem eq_infAd_of_ann {F : Type} [Field F] [NumberField F] (z : AF F)
    (hz : ∀ a : AF F, evI F a = 0 → a * z = 0) : z = infAd F (evI F z) := by
  obtain ⟨a, ha1, ha2⟩ : ∃ a : AF F, a.1 = 0 ∧ a.2 = 1 := ⟨(0, 1), rfl, rfl⟩
  have h0 : evI F a = 0 := by
    have e : evI F a = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 := rfl
    rw [e, ha1, map_zero]
  have h2 : z.2 = 0 := by
    have h3 := congrArg Prod.snd (hz a h0)
    have h4 : (a * z).2 = a.2 * z.2 := rfl
    rw [h4, ha2, one_mul] at h3
    exact h3
  refine Prod.ext ?_ ?_
  · show z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F z.1)
    rw [RingEquiv.symm_apply_apply]
  · show z.2 = 0
    exact h2

theorem liftI_at_movI : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (p : UA σ X.J × UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), At (evI F) (liftI M ζ) ∧ liftI M (movI M p ζ) = actAB (cA σ) p⁻¹ (liftI M ζ) := by
  intro F E _ _ _ _ _ σ n d X W M p ζ
  have hL : At (evI F) (liftI M ζ) := by
    intro u hu
    unfold liftI
    rw [← LinearEquiv.map_smul]
    convert (M.co.e.symm).map_zero using 2
    refine Prod.ext ?_ ?_
    · funext i
      exact mul_infAd_of_evI u hu _
    · funext i
      exact mul_infAd_of_evI u hu _
  refine ⟨hL, ?_⟩
  have hw : At (evI F) (actAB (cA σ) p⁻¹ (liftI M ζ)) := at_mul_of_at _ _ _ hL
  set w := actAB (cA σ) p⁻¹ (liftI M ζ) with hwdef
  have hc : ∀ u : AF F, evI F u = 0 → u • M.co.e w = 0 := by
    intro u hu
    rw [← LinearEquiv.map_smul, hw u hu, LinearEquiv.map_zero]
  unfold liftI movI arch
  conv_rhs => rw [← M.co.e.symm_apply_apply w]
  congr 1
  refine Prod.ext ?_ ?_
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.fst (hc a ha)) i).symm
  · funext i
    exact (eq_infAd_of_ann _ fun a ha => congrFun (congrArg Prod.snd (hc a ha)) i).symm

end GlobalTheory.ArchDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.PsiInfLinear

theorem continuous_ringEquiv_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem psiInf_eq_exp_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F,
      psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  intro D ψ h
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := h
  have hform := hall θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
  let c : ℂ := 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℂ :=
    { toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  have hg : Continuous g := by
    show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
    refine continuous_const.mul (continuous_finsetSum _ fun ρ _ => ?_)
    exact (hθ ρ).2.comp (continuous_ringEquiv_mixedSpace_symm D.host.F)
  refine ⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩
  rw [hform x]
  congr 1
  show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [e.symm_apply_apply]

end GlobalTheory.PsiInfLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiInvariantTestFunctionSum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bi_invariant_test_function_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 := by
  first | (exact @GlobalTheory.LKDef.Regroup.regroup) | (exact GlobalTheory.LKDef.Regroup.regroup) | (intros; apply GlobalTheory.LKDef.Regroup.regroup <;> assumption)
end

