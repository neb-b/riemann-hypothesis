module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0023
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.GlRelTau
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0012
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0007

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaMinor
section
open Finset

namespace GlobalTheory.CompanionTheory.HeckeCapelli

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry capelliExpand)

theorem capelli_entry_apply {n : ℕ} (X : GMod n) (x : ℂ) (d b : Fin n) (v : X.V) :
    capEntry X.E x d b v = X.E d b v + if d = b then x • v else 0 := by
  unfold capEntry
  split_ifs <;> simp [Module.algebraMap_end_apply]

theorem capelli_component {m : ℕ} (X : GMod (m + 1)) (x : ℂ) (f : Fin (m + 1) → X.V) (b : Fin (m + 1)) :
    ∑ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) = capelliC X.E x (f b) := by
  have key := (capelliExpand (Module.End ℂ X.V) m X.E x X.gl).1 b
  have h : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) =
      if b = c then capelliC X.E x (f c) else 0 := by
    intro c
    have := LinearMap.congr_fun (key c) (f c)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    rw [this]
    split_ifs <;> simp
  simp only [h]
  simp

theorem omMinor : OmMinor := by
  intro m X x
  rw [GlobalTheory.T.QuantumDeterminantEquality (m + 1) X.V X.E x]
  refine LinearMap.ext fun f => funext fun b => ?_
  have h := capelli_component X x f b
  simp only [capelli_entry_apply, smul_add, sum_add_distrib] at h
  simp only [LinearMap.compLeft_apply, Function.comp_apply, ← h]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Pi.add_apply, Pi.smul_apply, om_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [minorOp, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  refine (add_comm _ _).trans ?_
  congr 1
  · exact sum_comm
  · rw [sum_comm]
    simp [smul_sum, smul_comm x]

end GlobalTheory.CompanionTheory.HeckeCapelli
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTau
section
noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliTwist

open Formalism.REAL (qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open CompanionTheory.RgExh.Hk

theorem qdetTau : QdetTau := by
  intro n X u
  have hgl : GlRelR X.E := X.gl
  have hrow : capelliC X.E (-u + ((n : ℂ) - 1)) = rminor X.E id id ((n : ℂ) - 1 - u) := by
    rw [show -u + ((n : ℂ) - 1) = (n : ℂ) - 1 - u by ring]
    exact cminor_eq_rminor X.E hgl id id _
  rw [GlobalTheory.CompanionTheory.RgExhHecke.qdet_eq_capelliC, GlobalTheory.CompanionTheory.RgExhHecke.qdet_eq_capelliC, hrow]
  show capelliC (fun a b => -X.E b a) u = _
  rw [ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.capelliC_negT]
  rw [show ((-1 : Module.End ℂ X.V)) ^ n = algebraMap ℂ _ ((-1 : ℂ) ^ n) by simp,
    Algebra.smul_def]

end GlobalTheory.CompanionTheory.CapelliTwist
end
end

