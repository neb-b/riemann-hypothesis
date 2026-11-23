module

public import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolHOfPerf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds

@[expose] public section

noncomputable section

namespace PI.OmLocU.Done

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F))

attribute [local instance] LocMassOrdSF.isModTop_tens in
private theorem fullLattice_of_isSDLoc (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hSD : IsSDLoc σ J v (L : Set (Fin n → E))) :
    Submodule.IsFullLattice E L := by
  classical
  refine { toIsLattice := hL, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro x _
  by_contra hx
  obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_le_ker_of_notMem hx
  let A := Fv F v ⊗[F] E
  let ι : E →+* A := inclR (F := F) (Fv F v)
  let f : (Fin n → A) →ₗ[A] A :=
    ∑ i : Fin n, ι (φ (Pi.single i 1)) • LinearMap.proj i
  have hf (y : Fin n → E) : f (ratV (F := F) (Fv F v) y) = ι (φ y) := by
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, ratV,
      smul_eq_mul]
    change (∑ i : Fin n, ι (φ (Pi.single i 1)) * ι (y i)) = _
    simp_rw [← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  let fF := f.restrictScalars (Fv F v)
  let fO := fF.restrictScalars (v.adicCompletionIntegers F)
  have hfL : latLoc (E := E) v (L : Set (Fin n → E)) ≤ LinearMap.ker fO := by
    rw [latLoc, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change f (ratV (F := F) (Fv F v) y) = 0
    rw [hf, LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy)), map_zero]
  have hOpen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hSD (basLat_fg v L hL)
  obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v (hOpen.mem_nhds (Submodule.zero_mem _))
    (fun _ : Unit => ratV (F := F) (Fv F v) x)
  have hz := LinearMap.mem_ker.mp (hfL (htx ()))
  change fF (t • ratV (F := F) (Fv F v) x) = 0 at hz
  rw [map_smul] at hz
  change t • f (ratV (F := F) (Fv F v) x) = 0 at hz
  rw [hf] at hz
  exact ((map_ne_zero ι).2 hφx) ((smul_eq_zero.mp hz).resolve_left ht)

theorem local_omega_volume_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧
      ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν)
    (hOm : OmUnique σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hUN := UnN.unitNorm_of_res σ J ψ v Λ hR
  have hP : SdB.TrPerf σ J ψ v := SdB.trPerf_of_res σ J ψ v hR
  intro hS hLat hSD
  have hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ := by
    obtain ⟨L, hL, rfl⟩ := hLat
    exact ⟨L, fullLattice_of_isSDLoc σ J v L hL hSD, rfl⟩
  exact omLocU_of_tr σ J ψ v Λ a Y hSd hOm (UnitaryOrbitCounting.orbAll_of_res σ J ψ v Λ a Y hR hUN)
    (gramInvO_holds σ J v Λ ψ a Y) (Red.trOnto_holds σ J ψ v hS) hFull
    (UnitaryOrbitCounting.countU_of_res' σ J ψ v Λ a Y hR hUN)
    (SdB.sdVolW_of_perf σ J ψ v Λ a hP) (SdB.sdVolH_of_perf σ J ψ v a hP) hS hLat hSD

theorem omLocU_closed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  local_omega_volume_unique σ J ψ v Λ a Y
    (fun hS => ⟨(PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).1,
      (PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).2.1⟩)
    (omUnique σ J ψ v a)

end PI.OmLocU.Done
