module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorHermitianBlockLiftLastBasisOfNormLe
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem forall_full_entries_iff {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) (P : k → Prop) :
    (∀ i j, P (full Y i j)) ↔
      (∀ i j, P (Y.1 i j)) ∧ (∀ i, P (Y.2.1 i)) ∧ (∀ j, P (Y.2.2.1 j)) ∧ P Y.2.2.2 := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
  · rintro ⟨h1, h2, h3, h4⟩ i j
    simp only [full, Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
    · simpa using h1 a b
    · simpa using h2 a
    · simpa using h3 b
    · simpa using h4

theorem unitU_liftH_of_norm_le_one {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ ≤ 1) :
    unitU (r + 1) F E (liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  classical
  have hA : (∀ i j, ‖full X.toGl i j‖ ≤ 1) ↔
      (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 := by
    rw [forall_full_entries_iff X.toGl (fun x => ‖x‖ ≤ 1)]
    simp only [Hn.toGl, Pi.star_apply, Unram.norm_star (F := F), norm_algebraMap']
    tauto
  have hb : ∀ i, ‖(ν • eL r E) i‖ ≤ 1 := by
    intro i
    by_cases hi : i = Fin.last r
    · subst hi; simpa [eL] using hν
    · simp [eL, Pi.single_eq_of_ne hi]
  unfold unitU
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have e : ((∀ i j, ‖(liftH X ν l).1.1 i j‖ ≤ 1) ∧ (∀ i, ‖(liftH X ν l).2.1 i‖ ≤ 1) ∧ ‖(liftH X ν l).2.2‖ ≤ 1) ↔
      (‖l‖ ≤ 1 ∧ (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1) := by
    change ((∀ i j, ‖full X.toGl i j‖ ≤ 1) ∧ (∀ i, ‖(ν • eL r E) i‖ ≤ 1) ∧ ‖l‖ ≤ 1) ↔ _
    rw [hA]
    exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hb, h.1⟩⟩
  simp only [e]
  by_cases h1 : ‖l‖ ≤ 1 <;>
    by_cases h2 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 <;>
    simp only [h1, h2, if_true, if_false, true_and, false_and, and_self, mul_one, mul_zero, zero_mul, implies_true]

end GlobalTheory.JR.Step
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorsMatchAtOfOneLtNormFirstMoment
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.BigMoment

theorem norm_dot_le_one {n : ℕ} {k : Type} [NormedField k] [IsUltrametricDist k] (c b : Fin n → k)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) : ‖c ⬝ᵥ b‖ ≤ 1 := by
  unfold dotProduct
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro i _
  rw [norm_mul]
  exact mul_le_one₀ (hc i) (norm_nonneg _) (hb i)

theorem dot_act {n : ℕ} {k : Type} [CommRing k] (g : GL (Fin n) k) (Y : Gl n k) :
    (act g Y).2.2.1 ⬝ᵥ (act g Y).2.1 = Y.2.2.1 ⬝ᵥ Y.2.1 := by
  simp only [act]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem dot_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv (r + 1) k) :
    (sec a).2.2.1 ⬝ᵥ (sec a).2.1 = a.2.1 0 := by
  simp [sec, dotProduct, Fin.sum_univ_succ]

theorem dot_actU {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (b : Fin n → E) : star (g.1 *ᵥ b) ⬝ᵥ (g.1 *ᵥ b) = star b ⬝ᵥ b := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp g.2, Matrix.one_mulVec]

theorem matchAt_unit_of_one_lt_norm :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ →
      MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  intro F E _ _ _ _ hU r M a ha
  haveI := hU.ultraF
  haveI := hU.ultraE
  have hG : orbG M (unitG (r + 1) F) (sec a) = 0 := by
    have h : ∀ g, unitG (r + 1) F (act g (sec a)) = 0 := by
      intro g
      unfold unitG
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨-, hb, hc, -⟩
      have := norm_dot_le_one _ _ hc hb
      rw [dot_act, dot_sec] at this
      exact absurd ha (not_lt.mpr this)
    simp [orbG, h]
  refine ⟨fun X hX => ?_, fun _ => hG⟩
  rw [hG]
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun t : Inv (r + 1) E => t.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have h : ∀ g, unitU (r + 1) F E (actU g X) = 0 := by
    intro g
    unfold unitU
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨-, hb, -⟩
    have := norm_dot_le_one (star (actU g X).2.1) (actU g X).2.1
      (fun i => by rw [Pi.star_apply, hU.norm_star]; exact hb i) hb
    simp only [actU] at this
    rw [dot_actU, h0, norm_algebraMap'] at this
    exact absurd ha (not_lt.mpr this)
  simp [orbU, h]

end GlobalTheory.JR.BigMoment
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitPrescribedResidueReducedFiniteAlgebra
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory

theorem UnitLemma.exists_unit_residue (K : UQ) (B : InvAlg K) (hB : IsReduced B.A) (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal) (hz : z ≠ 0) :
    ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  classical
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  let e := IsArtinianRing.equivPi B.A
  let v : (I : MaximalSpectrum B.A) → B.A ⧸ I.asIdeal := fun I =>
    if h : I = m then h ▸ z else 1
  have hv : IsUnit v := by
    rw [Pi.isUnit_iff]
    intro I
    letI := Ideal.Quotient.field I.asIdeal
    rw [isUnit_iff_ne_zero]
    by_cases h : I = m
    · subst h; simpa [v] using hz
    · simp [v, h]
  have hy : IsUnit (e.symm v) := hv.map e.symm
  refine ⟨hy.unit, ?_, ?_⟩
  · have := IsArtinianRing.equivPi_apply B.A (e.symm v) m
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v]
  · intro m' hm'
    have := IsArtinianRing.equivPi_apply B.A (e.symm v) m'
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v, hm']

theorem UnitLemma.unit_prescribed_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 :=
  fun K B hB m z hz => UnitLemma.exists_unit_residue K B hB m z hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActHermitianBlockDiagOneLiftLastBasis
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem actU_uEmb_liftH {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F) :
    actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by
  have hs : star (embHom r E s.1) = embHom r E (star s.1) := by
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · apply Subtype.ext
    show embHom r E s.1 * full X.toGl * star (embHom r E s.1) = full (actU s X).toGl
    rw [hs]
    simp only [embHom, full, Hn.toGl, actU, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    congr 2
    all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMul, Finset.sum_apply, star_sum, mul_comm, Matrix.star_apply])
  · show embHom r E s.1 *ᵥ (ν • eL r E) = ν • eL r E
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [embHom, eL, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Fin.sum_univ_castSucc]
    · simp [embHom, eL, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Fin.sum_univ_castSucc]

end GlobalTheory.JR.Step
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitProperOfInvertibleKrylovColumns
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OrbProper

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem continuous_bm : Continuous (fun X : Hn r F E => Bm X.toGl) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((((continuous_subtype_val.comp continuous_fst).pow (j : ℕ))).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem continuous_actU :
    Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU q.1 q.2) := by
  haveI := ImgSec.continuousStar (E := E) F
  have hg : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact ((hg.mul hA).mul hg.star).subtype_mk _
  · exact hg.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))
  · exact continuous_snd.comp (continuous_snd.comp continuous_snd)

theorem continuousOn_inv {X : Type} [TopologicalSpace X] {Ω : Set X} {h : X → Matrix (Fin r) (Fin r) E}
    (hh : ContinuousOn h Ω) (hu : ∀ a ∈ Ω, IsUnit (h a).det) : ContinuousOn (fun a => (h a)⁻¹) Ω := by
  have : (fun a => (h a)⁻¹) = fun a => ((h a).det)⁻¹ • (h a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  refine ContinuousOn.smul (f := fun a => ((h a).det)⁻¹) (g := fun a => (h a).adjugate) ?_ ?_
  · exact (continuous_id.matrix_det.comp_continuousOn hh).inv₀ fun a ha => (hu a ha).ne_zero
  · exact continuous_id.matrix_adjugate.comp_continuousOn hh

theorem isCompact_orbit (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E)
    (h : Inv r F → Matrix (Fin r) (Fin r) E) (hΩ : IsCompact Ω) (hs : ContinuousOn s Ω) (hhc : ContinuousOn h Ω)
    (hb : ∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) (C : Set (Hn r F E)) (hC : IsCompact C) :
    IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
  haveI := ImgSec.continuousStar (E := E) F
  set Φ : Hn r F E × Inv r F → Matrix (Fin r) (Fin r) E := fun q => Bm q.1.toGl * (h q.2)⁻¹ with hΦ
  have hΦc : ContinuousOn Φ (C ×ˢ Ω) := by
    refine (continuous_bm.comp continuous_fst).continuousOn.mul ?_
    exact (continuousOn_inv hhc fun a ha => (hb a ha).1).comp continuous_snd.continuousOn
      (fun q hq => hq.2)
  have hM : IsCompact (Φ '' (C ×ˢ Ω)) := (hC.prod hΩ).image_of_continuousOn hΦc
  have hU : IsClosed ((Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E))) := isClosed_unitary
  have hK : IsCompact (((↑) : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    (hU.isClosedEmbedding_subtypeVal).isCompact_preimage hM
  have hcl : IsClosed {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
    have hf : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2))
        (Set.univ ×ˢ Ω) := by
      have h1 : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => (p.1, s p.2)) (Set.univ ×ˢ Ω) :=
        continuous_fst.continuousOn.prodMk (hs.comp continuous_snd.continuousOn (fun q hq => hq.2))
      have h2 := (continuous_actU (F := F) (E := E) (r := r)).comp_continuousOn h1
      exact h2
    have hC2 : IsClosed C := hC.isClosed
    have hO2 : IsClosed (Set.univ ×ˢ Ω : Set (Matrix.unitaryGroup (Fin r) E × Inv r F)) := isClosed_univ.prod hΩ.isClosed
    have h3 := hf.preimage_isClosed_of_isClosed hO2 hC2
    have heq : {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} =
        (Set.univ ×ˢ Ω) ∩ (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2)) ⁻¹' C := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage]
    rw [heq]; exact h3
  refine (hK.prod hΩ).of_isClosed_subset hcl ?_
  rintro ⟨g, a⟩ ⟨ha, hC'⟩
  refine ⟨⟨(actU g (s a), a), ⟨hC', ha⟩, ?_⟩, ha⟩
  simp only [hΦ]
  rw [ImgSec.bm_actU, (hb a ha).2, Matrix.mul_nonsing_inv_cancel_right _ _ (hb a ha).1]

end GlobalTheory.JR.OrbProper

theorem GlobalTheory.JR.orbit_proper_of_columns : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} :=
  fun _ _ _ _ _ _ _ r Ω s h hΩ hs hh hb C hC => GlobalTheory.JR.OrbProper.isCompact_orbit r Ω s h hΩ hs hh hb C hC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedInvolutionExtMapsIntegersToIntegers
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem valuation_le_one_of_val_nonneg (K : UQ) (e : K.E) (he : e ≠ 0) (h : 0 ≤ val K.O e) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≤ 1 := by
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≠ 0 := by simpa using he
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem val_nonneg_of_int (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · rw [hx]; unfold val; simp
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem map_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (x : K.O) :
    ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
  have hφ : φ (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  have hv : 0 ≤ val K'.O (φ (algebraMap K.O K.E x)) := by
    rw [hU.2.2.1]; exact val_nonneg_of_int K x
  exact IsDiscreteValuationRing.exists_lift_of_le_one (valuation_le_one_of_val_nonneg K' _ hφ hv)

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticTraceEqAddStar
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  intro F E _ _ _ _ hU y
  classical
  have hfr : Module.finrank F E = 2 := hU.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut E)) (fun x => hU.star_fix x)
  have hσ : ∀ z, σ z = star z := fun z => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro h
    obtain ⟨z, hz⟩ := hU.star_ne
    apply hz
    rw [← hσ, ← h]; rfl
  have hle : Nat.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hfr]
    exact (Nat.card_le_card_of_injective _ AlgEquiv.coe_algHom_injective).trans (card_algHom_le_finrank F E E)
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    refine le_antisymm hle ?_
    have : Fintype.card (E ≃ₐ[F] E) ≥ 2 := by
      have h2 : (({1, σ} : Finset (E ≃ₐ[F] E))).card = 2 := Finset.card_pair hne
      rw [← h2]; exact Finset.card_le_univ _
    rwa [Nat.card_eq_fintype_card]
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfr])
  rw [trace_eq_sum_automorphisms]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} := by
    symm
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  rw [huniv, Finset.sum_pair hne]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def cc (A : Et F E) (e : A.L) (p : A.K × A.K) : A.L :=
  algebraMap A.K A.L p.1 * e + algebraMap A.K A.L p.2 * (1 - e)

def ci (A : Et F E) (e : A.L) (y : A.L) : A.K × A.K :=
  (Algebra.trace A.K A.L (y * e), Algebra.trace A.K A.L (y * (1 - e)))

def kx (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (u b : A.K) : ℂ := A.psiK ψ (x * u * b)

def pt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  fourB ν (kx A ψ x) (fun b => Φ (p.1, b)) p.2

def rg (A : Et F E) (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  Φ (p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 0 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 0,
    p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 1 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 1)

def wHyp (A : Et F E) (e : A.L) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K)
    (g : SpecialLinearGroup (Fin 2) A.K) (φ : A.L → ℂ) (y : A.L) : ℂ :=
  pt A ν ψ x (pt A ν ψ x (pt A ν ψ x (rg A g (pt A ν ψ x (fun p => φ (cc A e p)))))) (ci A e y)

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeylNumeratorLaplace
section
open Polynomial

namespace GlobalTheory

theorem weylNumerator_laplace : ∀ (a b : ℕ) (α : Fin a → ℂˣ) (β : Fin b → ℂˣ) (l : Fin (a + b) → ℤ), (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α β i : ℂˣ) ^ l j : ℂˣ) : ℂ)).det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * (Matrix.of fun i k : Fin a => ((α i ^ l (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det * (Matrix.of fun i k : Fin b => ((β i ^ l (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det := by
  intro a b α β l
  rw [Formalism.ResultantValuation.laplaceExpansionRows ℂ a b]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [Nat.add_comm (a * (a - 1) / 2)]
  congr 2
  · congr 1
    ext i k
    simp [Matrix.submatrix]
  · congr 1
    ext i k
    simp [Matrix.submatrix]

end GlobalTheory
end

