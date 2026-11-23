module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndep
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS
open Matrix

theorem cayleyIndep : CayleyIndepStatement := by
  intro k r ε lam H _ _ _ σ P₀ P h0 h1 hDS
  set σ₁ : Mat k r → (H →L[ℂ] H) := fun g => σ (P₀⁻¹ * g * P₀) with hσ₁
  have e0 : star P₀ * P₀ = 1 := Matrix.mem_unitaryGroup_iff'.mp h0.2
  have e0' : P₀ * star P₀ = 1 := Matrix.mem_unitaryGroup_iff.mp h0.2
  have e1 : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp h1.2
  have e1' : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp h1.2
  have hinv0 : P₀⁻¹ = star P₀ := Matrix.inv_eq_left_inv e0
  have hinv1 : P⁻¹ = star P := Matrix.inv_eq_left_inv e1
  have hH0 := h0.1.2
  have hH1 := h1.1.2
  have hJ : star P₀ * Formalism.REAL.Jm ε * P₀ = star P * Formalism.REAL.Jm ε * P := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hH0, hH1]
  have hbK : P₀ * star P ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h0.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e1)), ?_⟩
    calc P₀ * star P * Formalism.REAL.Jm ε = P₀ * (star P * Formalism.REAL.Jm ε * P) * star P := by
          rw [Matrix.mul_assoc P₀ _ (star P), Matrix.mul_assoc (star P * _) P (star P), e1', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P₀ * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P₀ * star P) := by
          simp only [← Matrix.mul_assoc]
          rw [e0', Matrix.one_mul]
  have haK : P * star P₀ ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h1.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e0)), ?_⟩
    calc P * star P₀ * Formalism.REAL.Jm ε = P * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P₀ := by
          rw [Matrix.mul_assoc P _ (star P₀), Matrix.mul_assoc (star P₀ * _) P₀ (star P₀), e0', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P * (star P * Formalism.REAL.Jm ε * P) * star P₀ := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P * star P₀) := by
          simp only [← Matrix.mul_assoc]
          rw [e1', Matrix.one_mul]
  have hbU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj hbK
  have haU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj haK
  have hab : P * star P₀ * (P₀ * star P) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P₀), e0, Matrix.one_mul, e1']
  have hba : P₀ * star P * (P * star P₀) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P), e1, Matrix.one_mul, e0']
  have hfun : (fun g => σ (P⁻¹ * g * P)) = fun g => σ₁ (P₀ * star P * g * (P * star P₀)) := by
    funext g
    rw [hσ₁]
    congr 1
    rw [hinv0, hinv1]
    simp only [← Matrix.mul_assoc]
    rw [e0, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [e0, Matrix.mul_one]
  obtain ⟨hc, hnt, hU, hI, hS, ⟨S0, hS0⟩, hmin⟩ := hDS
  rw [hfun]
  refine ⟨⟨hc, hnt, ?_, ?_, ?_, ⟨S0, ?_⟩, fun μ S hS' => hmin μ S ?_⟩, ?_⟩
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.urep_conj
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.irred_conj (hirr := hI)
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.sqint_conj (hsq := hS)
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    · exact hS0
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff] at hS'
    · exact hS'
    all_goals first | assumption | exact hU
  · unfold Formalism.MainNotions.S.lowKSub
    refine congrArg sSup (Set.ext fun S => ?_)
    simp only [Set.mem_setOf_eq]
    rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    all_goals first | assumption | exact hU

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Groups
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

theorem groups_invL {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hH]

theorem groups_invR {k r : ℕ} {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    g * (Hpk k r * gᴴ * Hpk k r) = 1 :=
  mul_eq_one_comm.mp (groups_invL hg)

theorem groups_sset_closed (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hK : IsCompact (UWset k r z)) :
    IsClosed (Sset k r z) := by
  have hN : IsClosed (Nset k r) := (Formalism.FourierDecayAlt.P.B2x2.closedN k r).closed
  have : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK
  have hc : Continuous fun p : UWset k r z × Mat k r =>
      Hpk k r * ((p.1 : Mat k r))ᴴ * Hpk k r * p.2 := by
    refine Continuous.matrix_mul ?_ continuous_snd
    refine Continuous.matrix_mul ?_ continuous_const
    refine Continuous.matrix_mul continuous_const ?_
    exact (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose
  have e : Sset k r z = Prod.snd '' {p : UWset k r z × Mat k r |
      Hpk k r * ((p.1 : Mat k r))ᴴ * Hpk k r * p.2 ∈ Nset k r} := by
    ext s
    constructor
    · rintro ⟨h, hh, m, hm, rfl⟩
      refine ⟨(⟨h, hh⟩, h * m), ?_, rfl⟩
      show Hpk k r * hᴴ * Hpk k r * (h * m) ∈ Nset k r
      rw [← Matrix.mul_assoc, groups_invL hh.1, Matrix.one_mul]
      exact hm
    · rintro ⟨⟨⟨h, hh⟩, s'⟩, hp, rfl⟩
      refine ⟨h, hh, _, hp, ?_⟩
      show s' = h * (Hpk k r * hᴴ * Hpk k r * s')
      rw [← Matrix.mul_assoc, groups_invR hh.1, Matrix.one_mul]
  rw [e]
  exact isClosedMap_snd_of_compactSpace _ (hN.preimage hc)

theorem closedSubgroups : ClosedSubgroupsStatement := by
  intro k r z
  refine ⟨Formalism.FourierDecayAlt.P.B2x2.closedG k r, Formalism.FourierDecayAlt.P.B2x2.closedN k r, fun hz hT => ⟨Formalism.FourierDecayAlt.P.B2x3.closedW k r z, ?_⟩⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  refine ⟨h1, hmul, hinv, ?_, groups_sset_closed k r z (Formalism.FourierDecayAlt.P.B2x3.compactW k r z hz hT)⟩
  rintro s ⟨h, hh, m, hm, rfl⟩
  rw [Matrix.det_mul]
  exact ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit h hh).mul ((Formalism.FourierDecayAlt.P.B2x2.closedN k r).unit m hm)

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.HaarMap
section
noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace ConjugationHaarMap

variable {k r : ℕ}

theorem conj_closedEmb (P : Mat k r) (hP : IsUnit P.det) :
    IsClosedEmbedding (fun x : Mat k r => ((P⁻¹ * x * P : Mat k r) : Mt k r)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hc1 : Continuous (fun x : Mat k r => ((P⁻¹ * x * P : Mat k r) : Mt k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hc2 : Continuous (fun y : Mt k r => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let e : Mat k r ≃ Mt k r :=
    { toFun := fun x => ((P⁻¹ * x * P : Mat k r) : Mt k r)
      invFun := fun y => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r)
      left_inv := fun x => by
        show P * (P⁻¹ * x * P) * P⁻¹ = x
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
      right_inv := fun y => by
        show P⁻¹ * (P * (show Mat k r from y) * P⁻¹) * P = (show Mat k r from y)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one] }
  exact (Homeomorph.mk e hc1 hc2).isClosedEmbedding

private theorem det_unit_of_inUJ_lemma {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Formalism.REAL.inUJ ε M) : IsUnit M.det := by
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by split_ifs <;> norm_num)
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := congrArg Matrix.det (show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε from hM)
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
  exact hJ h.symm

theorem phi_closedEmb (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hP : IsUnit P.det) :
    IsClosedEmbedding
      (fun g : Formalism.REAL.UJ ε => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)) := by
  have hinvc : ContinuousOn (fun A : Mat k r => A⁻¹) {A : Mat k r | IsUnit A} := by
    have he : (fun A : Mat k r => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
      funext A
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [he]
    have hid : Continuous fun A : Mat k r => A := continuous_id
    exact (ContinuousOn.inv₀ hid.matrix_det.continuousOn
      (fun A hA => ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero)).smul hid.matrix_adjugate.continuousOn
  have hval : IsEmbedding (Units.val : (Mat k r)ˣ → Mat k r) :=
    Units.isEmbedding_val_mk' hinvc (fun u => (Matrix.coe_units_inv u).symm)
  have hU : IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := by
    refine ⟨hval.comp IsEmbedding.subtypeVal, ?_⟩
    have hr : Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) =
        {M : Mat k r | Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε} := by
      ext M
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hM
        exact ⟨⟨M.nonsingInvUnit (det_unit_of_inUJ_lemma ε M hM), hM⟩, rfl⟩
    rw [hr]
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  exact (conj_closedEmb P hP).comp hU

theorem phi_mem (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hC : Formalism.MainNotions.S.IsCayley k r ε P)
    (g : Mat k r) (hg : Formalism.REAL.inUJ ε g) : P⁻¹ * g * P ∈ UH (Hpk k r) := by
  obtain ⟨hPu, hPJ⟩ := hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
  rw [← hPJ]
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * ((gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g)) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hg', Matrix.mul_assoc]

theorem conj_mem (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hC : Formalism.MainNotions.S.IsCayley k r ε P)
    (s : Mat k r) (hs : s ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * s * P⁻¹) := by
  obtain ⟨hPu, hPJ⟩ := hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  show (P * s * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * s * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * s * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * s * P⁻¹)
      = (P⁻¹)ᴴ * (sᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * s) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPJ, hs']
    _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end ConjugationHaarMap

theorem haarMap : HaarMapStatement := by
  intro k r ε P hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hC.1
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have h2' : ∀ X : Mat k r, P⁻¹ * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  let φ : Formalism.REAL.UJ ε → Mt k r := fun g => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)
  have hφ : IsClosedEmbedding φ := ConjugationHaarMap.phi_closedEmb ε P hd
  have hme : MeasurableEmbedding φ := hφ.measurableEmbedding
  show Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ((Measure.haar : Measure (Formalism.REAL.UJ ε)).map φ)
  unfold Formalism.MainNotions.S.IsHaarOn
  refine ⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩
  · rw [Ne, Measure.map_eq_zero_iff hme.measurable.aemeasurable]
    exact Measure.measure_univ_pos.mp (isOpen_univ.measure_pos _ Set.univ_nonempty)
  · rw [hme.map_apply]
    have hE : φ ⁻¹' {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} = ∅ := by
      refine Set.subset_empty_iff.mp ?_
      intro g hg
      exact absurd (ConjugationHaarMap.phi_mem ε P hC (Formalism.MainNotions.S.umat g) g.2) hg
    rw [hE, measure_empty]
  · intro s hs
    have hsJ := ConjugationHaarMap.conj_mem ε P hC s hs
    let g₀ : Formalism.REAL.UJ ε := ⟨(P * s * P⁻¹).nonsingInvUnit (ConjugationHaarMap.det_unit_of_inUJ_lemma ε _ hsJ), hsJ⟩
    have hcl : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := continuous_const.matrix_mul continuous_id
    have hcomp : Formalism.QuantumDeterminants.lmulM s ∘ φ = φ ∘ (fun g => g₀ * g) := by
      funext g
      show s * (P⁻¹ * Formalism.MainNotions.S.umat g * P) = P⁻¹ * ((P * s * P⁻¹) * Formalism.MainNotions.S.umat g) * P
      simp only [Matrix.mul_assoc, h2']
    rw [Measure.map_map hcl.measurable hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_const_mul g₀).measurable, map_mul_left_eq_self]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.HaarUniq
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS.Mult1

theorem haarUniq2 : HaarUniq2Statement := by
  intro k r U μ ν hU hμ hν
  haveI : Fact (Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hμs, hμ0, hμc, hμl⟩ := hμ
  obtain ⟨hνs, hν0, hνc, hνl⟩ := hν
  have hμc' : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hμc
  have hνc' : ν (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hνc
  haveI := hμs
  haveI := hνs
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) ν
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap μ hμc' hμl
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap ν hνc' hνl
  have hμ0' : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hμ0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val μ hμc', h, Measure.map_zero]
  have hν0' : ν.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hν0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', h, Measure.map_zero]
  obtain ⟨c, hc, hcE⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hν0' hμ0'
  refine ⟨c, pos_iff_ne_zero.mpr hc, ?_⟩
  have hval : AEMeasurable (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r)
      (μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r)) :=
    (HaarSigmaFiniteUniqueness.mEmb (U := U)).measurable.aemeasurable
  rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', hcE, Measure.map_smul _ hval,
    HaarSigmaFiniteUniqueness.map_comap_val μ hμc']

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

