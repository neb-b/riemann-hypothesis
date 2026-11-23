module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023
public import Formalism.PeriodIntegrals.Bundle0019
public import Mathlib
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassSteps
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL5.PClassItems
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_sig_ne (D : D7) : ∃ θ : D.host.E, D.sp.cm.sig θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.host.E)
  obtain ⟨θ, t, e, h⟩ := D.sp.cm.cmUnram.2.2 P hP
  refine ⟨algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ, fun h' => h ?_⟩
  have h'' : star (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ) =
      algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ := h'
  rw [h''] at e
  have : t = θ := NumberField.RingOfIntegers.coe_injective e
  rw [this, sub_self]
  exact P.zero_mem

theorem classFin_of_UJ (hF : PI.UJClassFin.UJClassFin) (D : D7) : ClassFin D := by
  intro W hW hsig
  exact hF D.host.F D.host.E D.sp.cm.sig W.rank W.gram (L0c D W) (fun _ => rfl)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1)
    (StabFin.crd_up (F := D.host.F) W) (StabFin.crd_low (F := D.host.F) W)

theorem class_number_finite (D : D7) : ClassFin D := classFin_of_UJ unitary_class_set_finite D

theorem class_number_finite_rank (D : D7) (n : ℕ) : ClassFinAt D n := classFinAt_of D (class_number_finite D) n

theorem class_mass_of_genus_classes (hM : PI.UJClassMass2.UJClassMass) (D : D7) : ClassMass D := by
  intro W hW hsig n g hcov hdisj
  classical
  have hL : Submodule.IsFullLattice D.host.E W.L0 := by
    refine { toIsLattice := W.standardTuple_isLattice, span_eq_top := ?_ }
    obtain ⟨c, hc, hlow⟩ := StabFin.crd_low (F := D.host.F) W
    let a : D.host.E := (c : D.host.F) • (1 : D.host.E)
    have ha : a ≠ 0 := by
      change (c : D.host.F) • (1 : D.host.E) ≠ 0
      rw [Algebra.smul_def, mul_one]
      exact (algebraMap D.host.F D.host.E).injective.ne (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hc)
    rw [eq_top_iff, ← W.frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : a • W.frame i ∈ W.L0 := by
      have h := hlow i 1 isIntegral_one
      change ∑ j, (Pi.single i a : Fin W.rank → D.host.E) j • W.frame j ∈ W.L0 at h
      rwa [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same] at h
    have hframe : W.frame i = a⁻¹ • (a • W.frame i) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hframe]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hi)
  exact hM D.host.F D.host.E D.sp.cm.sig W.V W.hT W.rank W.frame W.L0 (fun _ => rfl) (exists_sig_ne D)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) W.herm W.nondeg hL
    (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1) n g hcov hdisj



end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def VolSigIndep (D : D7) : Prop :=
  ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) →
    (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank →
    ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
      (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram))
      (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)),
      IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
      IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ →
      μ 𝓕 = μ₀ 𝓕₀

def stdPos (D : D7) (n : ℕ) : HSpace D.host.E :=
  Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) n


def band (m a b : ℕ) : Fin m → Bool := fun i => decide (a ≤ (i : ℕ) ∧ (i : ℕ) < b)

theorem card_band (m a b : ℕ) (hb : b ≤ m) :
    (Finset.univ.filter (fun i : Fin m => band m a b i = true)).card = b - a := by
  first | exact UpperTheory.Reformulated.B.CardinalityOfBand.card_band .. | (apply UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (apply @UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (apply @UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m a b hb | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m a b | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m a | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m

theorem hasSig_diag_sgn {N : ℕ} (d : Fin N → Bool) (q : ℕ)
    (hq : (Finset.univ.filter (fun i => d i = true)).card = q) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i : Fin N => (Formalism.BasicNotions.Examples₂.sgn (d i) : ℂ)) (N - q) q := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (p := fun i => d i = true)
  rw [hq, Finset.card_univ, Fintype.card_fin] at hsum
  have hp : Fintype.card {i // d i = false} = N - q := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter (fun i : Fin N => d i = false)) =
        (Finset.univ.filter (fun i : Fin N => ¬ d i = true)) := by
      ext i; simp
    rw [this]; omega
  have hq' : Fintype.card {i // ¬ d i = false} = q := by
    rw [Fintype.card_subtype, ← hq]
    congr 1; ext i; simp
  let e1 : {i // d i = false} ≃ Fin (N - q) := Fintype.equivFinOfCardEq hp
  let e2 : {i // ¬ d i = false} ≃ Fin q := Fintype.equivFinOfCardEq hq'
  let e : Fin N ≃ Fin (N - q) ⊕ Fin q :=
    (Equiv.sumCompl (fun i => d i = false)).symm.trans (Equiv.sumCongr e1 e2)
  have hl : ∀ a, e.symm (Sum.inl a) = (e1.symm a).1 := fun a => rfl
  have hr : ∀ a, e.symm (Sum.inr a) = (e2.symm a).1 := fun a => rfl
  refine ⟨e, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hl, hl, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp [(e1.symm a).2, Formalism.BasicNotions.Examples₂.sgn]
    · have h' : (e1.symm a).1 ≠ (e1.symm b).1 := fun h' => h (e1.symm.injective (Subtype.val_injective h'))
      simp [h, h']
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hl, hr, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    have h' : (e1.symm a).1 ≠ (e2.symm b).1 := fun h => (e2.symm b).2 (h ▸ (e1.symm a).2)
    simp [h']
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hr, hl, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    have h' : (e2.symm a).1 ≠ (e1.symm b).1 := fun h => (e2.symm a).2 (h ▸ (e1.symm b).2)
    simp [h']
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hr, hr, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply]
    have hd : d (e2.symm a).1 = true := by simpa using (e2.symm a).2
    by_cases h : a = b
    · subst h; simp [hd, Formalism.BasicNotions.Examples₂.sgn]
    · have h' : (e2.symm a).1 ≠ (e2.symm b).1 := fun h' => h (e2.symm.injective (Subtype.val_injective h'))
      simp [h, h']

def bandSpace (D : D7) (m a b : ℕ) : HSpace D.host.E :=
  Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) m (band m a b)
    (m - (b - a)) (b - a)

theorem bandSpace_sigOK (D : D7) (m a b : ℕ) (hb : b ≤ m) : (bandSpace D m a b).SigOK := by
  intro τ
  have hg : (bandSpace D m a b).gram.map τ =
      Matrix.diagonal fun i : Fin m => (Formalism.BasicNotions.Examples₂.sgn (band m a b i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E)
      (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) m (band m a b) (m - (b - a)) (b - a) i j)).trans ?_
    change τ (if i = j then (Formalism.BasicNotions.Examples₂.sgn (band m a b i) : D.host.E) else 0) =
      if i = j then (Formalism.BasicNotions.Examples₂.sgn (band m a b i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.map_sgn]
  rw [hg]
  exact hasSig_diag_sgn (band m a b) (b - a) (card_band m a b hb)



end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
end

