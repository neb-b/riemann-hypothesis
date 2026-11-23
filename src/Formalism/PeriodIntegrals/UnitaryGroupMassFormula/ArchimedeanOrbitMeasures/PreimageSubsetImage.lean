module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousAdelicGL2Det

@[expose] public section

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

instance instT2SpaceUnitaryPQ (P Q : ℕ) : T2Space (UpqT P Q) := (isClosedEmbedding_mat P Q).isEmbedding.t2Space

section SlopeTestRemainingChoices

variable {P Q : ℕ}

theorem continuousOn_cayInv : ContinuousOn (cayInv P Q) (cayS (D0 P Q)) := by
  have e : cayInv P Q = fun g => ⟨cayCand P Q g, cayCand_mem P Q g⟩ :=
    funext (cayInv_eq P Q)
  rw [e]
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  show ContinuousOn (cayCand P Q) (cayS (D0 P Q))
  intro g hg
  have hdet : IsUnit (g.mat + 1).det := by
    rw [cayley_domain_eq] at hg
    exact hg
  unfold cayCand
  have hc : ContinuousAt (fun g : UpqT P Q => g.mat) g := continuous_mat.continuousAt
  have hinv : ContinuousAt (fun g : UpqT P Q => (g.mat + 1)⁻¹) g := by
    have hdet_cont : ContinuousAt Ring.inverse (g.mat + 1).det := by
      obtain ⟨u, hu⟩ := hdet
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    have hadd : ContinuousAt (fun x : UpqT P Q => x.mat + 1) g :=
      hc.add continuousAt_const
    exact (continuousAt_matrix_inv (g.mat + 1) hdet_cont).comp
      (f := fun x : UpqT P Q => x.mat + 1) (x := g) hadd
  exact ((continuousAt_const.mul hinv).mul (hc.sub continuousAt_const)).continuousWithinAt

theorem betaH_apply (lam : Measure (lieU P Q)) (S : Set (UpqT P Q)) (hS : MeasurableSet S) :
    betaH P Q lam S = ∫⁻ X in cayF P Q ⁻¹' S ∩ D0 P Q, rhoH P Q X ∂lam := by
  unfold betaH
  rw [Measure.map_apply measurable_cayF hS, withDensity_apply _ (measurable_cayF hS),
    Measure.restrict_restrict (measurable_cayF hS)]

theorem preimage_subset_image (S : Set (UpqT P Q)) :
    cayF P Q ⁻¹' S ∩ D0 P Q ⊆ cayInv P Q '' S := by
  rintro X ⟨hXS, hXD⟩
  exact ⟨cayF P Q X, hXS, cayInv_cayF X hXD⟩

end SlopeTestRemainingChoices

end HcInf
