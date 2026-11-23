module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct

section Order

variable {F : Type} [Field F] [NumberField F]

end Order

section LocInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] 𝔸
local notation "𝒮" => tensInt (F := F) 𝔸 (intOE E) (intAd F)

variable (E) in
def trV (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₗ[F] v.adicCompletion F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ (Algebra.trace F E).rTensor _

theorem trV_tmul (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : v.adicCompletion F) :
    trV E v (e ⊗ₜ a) = algebraMap F _ (Algebra.trace F E e) * a := by
  simp [trV, Algebra.smul_def]

theorem trV_prV (v : HeightOneSpectrum (𝓞 F)) (z : 𝒜) :
    trV E v (prV (E := E) v z) = (adelstabT F E z) v := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul e a => rw [afsplit_prV_tmul, trV_tmul, adelstabT_tmul]; rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]; rfl

theorem trV_int (v : HeightOneSpectrum (𝓞 F)) (y : E ⊗[F] v.adicCompletion F) (hy : y ∈ intV E v) :
    trV E v y ∈ v.adicCompletionIntegers F := by
  obtain ⟨a, rfl⟩ := levelv_S_le_range v y hy
  show trV E v (∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
    ((a i : v.adicCompletionIntegers F) : v.adicCompletion F)) ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine sum_mem fun i _ => ?_
  rw [trV_tmul]
  obtain ⟨t, ht⟩ := adelstab_trace_int (F := F) (RingOfIntegers.basis E i)
  rw [← ht, ← IsScalarTower.algebraMap_apply]
  exact mul_mem (levelaf_int_mem_v v t) (a i).2

theorem adele_expand {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (x : 𝒜) :
    x = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E (x * (β i ⊗ₜ[F] (1 : 𝔸))) := by
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    have h : ∀ i, β' i ⊗ₜ[F] adelstabT F E ((e ⊗ₜ[F] a) * (β i ⊗ₜ[F] (1 : 𝔸))) =
        (Algebra.trace F E (e * β i) • β' i) ⊗ₜ[F] a := by
      intro i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, adelstabT_tmul, ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    simp_rw [h]
    rw [← TensorProduct.sum_tmul]
    congr 1
    conv_lhs => rw [← β'.sum_repr e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  | add x y hx hy =>
    simp only [add_mul, map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hx hy


variable (F E) in
theorem loc_int_bound : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x : 𝒜, (∀ w, prV (E := E) w x ∈ intV E w) →
    levelafC E c * x ∈ 𝒮 := by
  classical
  set β := Module.finBasis F E
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β with hβ'
  obtain ⟨N, hN, hNi⟩ := adelstabL_den (fun i => β i)
  obtain ⟨M, hM, hMi⟩ := adelstabL_den (fun i => β' i)
  refine ⟨((M * N : ℤ) : 𝓞 F), by exact_mod_cast (mul_ne_zero hM hN), fun x hx => ?_⟩
  have key : levelafC E ((M * N : ℤ) : 𝓞 F) * x =
      ∑ i, ((M : E) * β' i) ⊗ₜ[F] adelstabT F E (x * (((N : E) * β i) ⊗ₜ[F] (1 : 𝔸))) := by
    conv_lhs => rw [adele_expand β x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ((N : E) * β i) = (N : F) • β i := by rw [Algebra.smul_def, map_intCast]
    have h2 : ((M : E) * β' i) = (M : F) • β' i := by rw [Algebra.smul_def, map_intCast]
    have h3 : ((N : F) • β i) ⊗ₜ[F] (1 : 𝔸) = (N : F) • (β i ⊗ₜ[F] (1 : 𝔸)) :=
      (TensorProduct.smul_tmul' _ _ _).symm
    rw [h1, h2, h3, mul_smul_comm, map_smul, TensorProduct.smul_tmul, levelafC,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    simp [Algebra.smul_def, mul_assoc]
  rw [key]
  refine sum_mem fun i _ => ?_
  refine levelaf_tmul_mem (⟨(M : E) * β' i, hMi i⟩ : 𝓞 E) ?_
  intro w
  rw [← trV_prV, map_mul]
  refine trV_int w _ (mul_mem (hx w) ?_)
  rw [afsplit_prV_tmul]
  exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨(⟨(N : E) * β i, hNi i⟩ : 𝓞 E), rfl⟩⟩, rfl⟩)

end LocInt

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace Par

variable {k : ℕ} (P : Par F E k)

end Par

namespace Par

variable {k : ℕ} (P : Par F E k)

end Par

end Fin

section Lb

variable {E : Type} [Field E] [NumberField E]

end Lb

end Formalism.MainNotions.Gaps.LG

end
