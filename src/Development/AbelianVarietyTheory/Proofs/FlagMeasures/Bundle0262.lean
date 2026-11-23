module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRep
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRepStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudes_relevant_cell_monomial_rep : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₀ : LocS W) (hA : GoodS D lam0 A₀) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'), 0 < θ → 0 < D.host.ka / gg D → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ' : ℝ, 0 < θ' → ∀ νR, RMeas D W γ θ' νR → ∃ (g₀ : MatKR D.R.k D.R.rS) (μR ν₀ : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)) (s : ℂ), CellData (toBessel D τ w w' θ W lam0 A₀ hW hA hT hT') W.μG g₀ μR ν₀ ν ∧ ν₀ {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 ∧ (∀ l, DminN W.z W.z' γ l = DminN W.z W.z' g₀ l) ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → A.J νR γ = s • A.J ν₀ g₀ := by
  first | exact @GlobalTheory.CellRed.amp_at_monomial | exact GlobalTheory.CellRed.amp_at_monomial | (intros; apply GlobalTheory.CellRed.amp_at_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupportStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_data_support : Hyps → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbInt.orbInt_integrable | exact GlobalTheory.CellOrbInt.orbInt_integrable | (intros; apply GlobalTheory.CellOrbInt.orbInt_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramFibreOfHaar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.GramFibreRescale

theorem isFibreFamily_smul {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν B fib)
    (c d : ℝ≥0) (hd : d ≠ 0) :
    IsFibreFamily (c • μ) f ι U (d • ν) B (fun b => (c / d) • fib b) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc hU => ⟨fun b hb => ?_, ?_⟩⟩
  · rw [Measure.smul_apply, h1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_div_cancel₀ _ hd, h2 φ hφ]
  · exact ((h3 φ hφ hc hU).1 b hb).smul_measure_nnreal
  · simp only [integral_smul_nnreal_measure]
    exact (h3 φ hφ hc hU).2.const_smul (c / d)

end GlobalTheory.GramFibreRescale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsotropicOrthHyp
section
open Formalism.BasicNotions Formalism.MainNotions.S
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoOrthHyp

open Matrix

theorem exists_norm_one {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (n : ℕ) (h : S.rank = n)
    (hn : 0 < n) (C : GL (Fin n) E)
    (hC : (C.1.map (starRingEnd E))ᵀ * C.1 = S.gram.reindex (finCongr h) (finCongr h)) :
    ∃ x : S.V, S.hT x x = 1 := by
  classical
  set e : Fin S.rank ≃ Fin n := finCongr h with he
  set M : Matrix (Fin n) (Fin n) E := ((C⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hM
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  refine ⟨∑ j : Fin n, M j i₀ • S.frame (e.symm j), ?_⟩
  have hCM : C.1 * M = 1 := by
    rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstar : (C.1.map (starRingEnd E))ᵀ = C.1ᴴ := rfl
  have hprod : Mᴴ * S.gram.reindex e e * M = (C.1 * M)ᴴ * (C.1 * M) := by
    rw [← hC, hstar, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have key : (Mᴴ * S.gram.reindex e e * M) i₀ i₀ = 1 := by
    rw [hprod, hCM]
    simp
  rw [← key]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem star_eq_hostConj (D : D7) (x : D.host.E) : starRingEnd D.host.E x = D.host.conj x := by
  have := D.host.isCMField_hostE
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  apply ψ.injective
  have h1 : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  rw [h1]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ x

theorem exists_isotropic_orth_hyp : ∀ (D : D7), Formalism.L2.Forms.Forms0 D D.u₀ → ∃ w : (VS D).V, w ≠ 0 ∧ (VS D).hT w w = 0 ∧ ∀ i, (VS D).hT (D.sp.hypE i) w = 0 ∧ (VS D).hT (D.sp.hypF i) w = 0 := by
  intro D hF
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hi : (0 : ℕ) ≤ D.R.m := Nat.zero_le _
  obtain ⟨C, hC, -⟩ := hF.val0.de
  have hN : 0 < D.R.N 0 := by
    show 0 < D.R.k + 0 * (D.R.t + 1)
    have := D.R.m_add_three_le_k
    omega
  have hC' : (C.1.map (starRingEnd D.host.E))ᵀ * C.1 =
      (D.sp.X 0).gram.reindex (finCongr (Formalism.L2.Forms.rankN D 0 hi))
        (finCongr (Formalism.L2.Forms.rankN D 0 hi)) := hC
  obtain ⟨x, hx⟩ := exists_norm_one (D.sp.X 0) (D.R.N 0) (Formalism.L2.Forms.rankN D 0 hi) hN C hC'
  have hπ : (hF.atT.piU : D.host.E) * D.host.conj (hF.atT.piU : D.host.E) =
      ((D.mem D.u₀).A.T : D.host.E) := hF.atT.piU_norm
  have hT0 : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
    rw [← D.sp_T]
    exact_mod_cast D.sp.T_prime.ne_zero
  have hsym : ∀ a b : (VS D).V, (VS D).hT a b = 0 → (VS D).hT b a = 0 := by
    intro a b hab
    rw [← (VS D).herm.eq a b, hab, map_zero]
  have hvv : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x))
      (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) = ((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.iXY_isom 0 hm]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hx, mul_one, RingHom.id_apply,
      star_eq_hostConj]
    linear_combination hπ
  have hvz : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) D.sp.zm = 0 := D.sp.zm_orth _
  have hzv := hsym _ _ hvz
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.zm_norm, D.sp_T]
  refine ⟨D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm, ?_, ?_, ?_⟩
  · intro h0
    have h1 : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm) D.sp.zm = 0 := by
      rw [h0, map_zero, LinearMap.zero_apply]
    rw [map_add (f := _), LinearMap.add_apply, hvz, hzz, zero_add, neg_eq_zero] at h1
    exact hT0 h1
  · simp only [map_add (f := _), LinearMap.add_apply, hvv, hvz, hzv, hzz]
    ring
  · intro i
    constructor
    · rw [map_add (f := _), hsym _ _ (D.sp.hyp_orthX i _).1, hsym _ _ (D.sp.hyp_orthz i).1, add_zero]
    · rw [map_add (f := _), hsym _ _ (D.sp.hyp_orthX i _).2, hsym _ _ (D.sp.hyp_orthz i).2, add_zero]

end GlobalTheory.IsoOrthHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DatumOf

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul_iff (g : S.GLV) (P : Submodule L.O S.V) (x : S.V) :
    x ∈ g • P ↔ ∃ b ∈ P, g b = x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem inner_le_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O ≤
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine sup_le ?_ le_sup_right
  rintro z ⟨hz1, hz2⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff S n Λ z).1 hz1
  have hyP : y ∈ perp L S.Hm Y := (hn.1 y).1 hz2
  have e : n y = y + (n y - y) := by abel
  rw [e]
  exact Submodule.add_mem_sup ⟨hy, hyP⟩ (hn.2 y hyP)

theorem inner_eq_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine le_antisymm (inner_le_of_unip S Y n hn Λ) ?_
  have h1 := inner_le_of_unip S Y n⁻¹ (inv_mem hn) (n • Λ)
  rwa [inv_smul_smul] at h1

theorem complementGroup_fixes_frameSpan {g : S.GLV} (hg : g ∈ S.H0) {x : S.V} (hx : x ∈ S.ME) : g x = x :=
  sub_eq_zero.1 ((Submodule.mem_bot E).1 (hg.2.2 x hx))

theorem X_le : S.X ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_left
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem X'_le : S.X' ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_right
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0) {y : S.V}
    (hy : y ∈ perp L S.Hm Y) : g y ∈ perp L S.Hm Y := by
  intro w hw
  have e := hg.1 y w
  rw [complementGroup_fixes_frameSpan S hg (hY hw)] at e
  rw [e]
  exact hy w hw

theorem inTh_smul (g : S.GLV) (Λ : Submodule L.O S.V) {v : S.V} (hv : S.InTh Λ v) :
    S.InTh (g • Λ) (g v) := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩, map_smul g _ y⟩

theorem smul_inner_lattice_le_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) ≤
      ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_smul_iff S g _ z).1 hz
  obtain ⟨y, ⟨hy1, hy2⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hb
  rw [map_add (f := _), complementGroup_fixes_frameSpan S hg (hY hx)]
  exact Submodule.add_mem_sup ⟨(mem_smul_iff S g Λ _).2 ⟨y, hy1, rfl⟩, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S Y hY hg hy2⟩ hx

theorem smul_inner_lattice_eq_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) := by
  refine le_antisymm ?_ (smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY hg Λ)
  have h1 := smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY (inv_mem hg) (g • Λ)
  rw [inv_smul_smul] at h1
  intro z hz
  have h2 := Submodule.smul_mem_pointwise_smul _ g _ (h1 (Submodule.smul_mem_pointwise_smul z g⁻¹ _ hz))
  rwa [smul_inv_smul] at h2

theorem smul_graphOf_subset_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    g • S.graphOf Λ ⊆ S.graphOf (g • Λ) := by
  rintro _ ⟨p, ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩, rfl⟩
  refine ⟨g y', (mem_smul_iff S g Λ _).2 ⟨y', hy', rfl⟩, g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩,
    hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X'_le S) hg h1, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X_le S) hg h2, ?_, ?_, ?_⟩
  · show g y' - g p.1 ∈ S.X'
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X'_le S h3)]
    exact h3
  · show g y - g p.2 ∈ S.X
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X_le S h4)]
    exact h4
  · rw [← map_sub]
    exact inTh_smul S g Λ h5

theorem graphOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.graphOf (g • Λ) = g • S.graphOf Λ := by
  refine subset_antisymm ?_ (smul_graphOf_subset_of_mem_hermitianStabilizer S hg Λ)
  intro p hp
  have h1 := smul_graphOf_subset_of_mem_hermitianStabilizer S (inv_mem hg) (g • Λ) ⟨p, hp, rfl⟩
  rw [inv_smul_smul] at h1
  exact ⟨g⁻¹ • p, h1, smul_inv_smul g p⟩

theorem datOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.datOf (g • Λ) = g • S.datOf Λ :=
  Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X (X_le S) hg Λ)
    (Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X' (X'_le S) hg Λ) (graphOf_smul_eq_of_mem_hermitianStabilizer S hg Λ))

theorem std_inner [IsNonarchimedeanLocalField F] [CharZero F] (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hgs : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    (S.stdLat g gs A ⊓ (perp L S.Hm (S.spanTo g r)).restrictScalars L.O) ⊔
      (S.spanTo g r).restrictScalars L.O = A := by
  have h3 := (StdLat.stdLat_spec L r k S g gs hgs A hA).2.2
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro y ⟨hy1, hy2⟩
      exact (h3 y).2 ⟨y, hy1, hy2, by simp⟩
    · intro x hx
      exact hA.1 x hx
  · intro x hx
    obtain ⟨y, hy, hyp, hyx⟩ := (h3 x).1 hx
    have e : x = y - (y - x) := by abel
    rw [e]
    exact Submodule.sub_mem_sup ⟨hy, hyp⟩ hyx

theorem datOf_term [IsNonarchimedeanLocalField F] [CharZero F] {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) : d = S.datOf Λ := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛ, hΛ', -, hg⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ hg)
  · show d.1 = (Λ ⊓ (perp L S.Hm S.X).restrictScalars L.O) ⊔ S.X.restrictScalars L.O
    rw [hΛ, inner_eq_of_unip S S.X n hn.2]
    exact (std_inner S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).symm
  · show d.2.1 = (Λ ⊓ (perp L S.Hm S.X').restrictScalars L.O) ⊔ S.X'.restrictScalars L.O
    rw [hΛ', inner_eq_of_unip S S.X' n' hn'.2]
    exact (std_inner S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').symm

theorem exists_unitri (g : Fin (r + 1) → S.V) (φ : S.GLV) (h : ∀ b : Fin (r + 1), φ (g b) - g b ∈ S.spanTo g b) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, φ (g j) = ∑ i, s i j • g i := by
  choose c hc0 hc using fun b : Fin (r + 1) => StdLat.exists_coef g {i | (i : ℕ) < b} (h b)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := (ne_of_lt hij).symm
    have h0 : c j i = 0 := hc0 j i fun hi => by
      have := Fin.lt_def.1 hij
      simp only [Set.mem_setOf_eq] at hi
      omega
    simp [h0, hne]
  · have h0 : c i i = 0 := hc0 i i fun hi => lt_irrefl (i : ℕ) hi
    simp [h0]
  · have e1 : ∑ i, (c j i + if i = j then (1 : E) else 0) • g i = ∑ i, c j i • g i + g j := by
      simp [add_smul, Finset.sum_add_distrib, ite_smul]
    rw [e1, ← hc j]
    abel

theorem mem_hermitianStabilizer_of_preserves_both_flags [IsNonarchimedeanLocalField F] [CharZero F] (φ : S.GLV) (hφ : φ ∈ isomG L S.Hm)
    (h1 : ∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b)
    (h2 : ∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) :
    ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨s, hs, hsφ⟩ := exists_unitri S S.f φ h1
  obtain ⟨s', hs', hsφ'⟩ := exists_unitri S S.f' φ h2
  have hz : cT L s * S.Zh * s' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S s s' a b, ← hsφ, ← hsφ']
    exact hφ _ _
  obtain ⟨h, hh, hf, hf'⟩ := ((FrameStab.stab_eq L r k S).2 s s' hs hs').1 hz
  have k1 : ∀ (g : Fin (r + 1) → S.V) (m : ℕ), (∀ i, φ (g i) = h (g i)) → ∀ v ∈ S.spanTo g m, φ v = h v := by
    intro g m hg v hv
    have hle : S.spanTo g m ≤ LinearMap.eqLocus (φ : S.V →ₗ[E] S.V) (h : S.V →ₗ[E] S.V) := by
      rw [Frames.spanTo, Submodule.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact hg i
    exact hle hv
  have hfix : ∀ v ∈ S.ME, φ v = h v := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _), map_add (f := _), k1 S.f _ (fun i => by rw [hsφ, hf]) a ha,
      k1 S.f' _ (fun i => by rw [hsφ', hf']) b hb]
  have hiso : h ∈ isomG L S.Hm := hh.1.1.1
  refine ⟨h, hh, h⁻¹ * φ, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hiso) hφ, ?_⟩, (mul_inv_cancel_left h φ).symm⟩
  refine FrameStab.mem_unipOn' bot_le _ fun v hv => ?_
  show h.symm (φ v) - v ∈ (⊥ : Submodule E S.V)
  rw [hfix v hv, LinearEquiv.symm_apply_apply, sub_self]
  exact zero_mem _

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨fun d Λ h => datOf_term S h, fun g hg Λ => datOf_smul_eq_of_mem_hermitianStabilizer S hg Λ,
    fun n hn Λ => inner_eq_of_unip S S.X n hn.2 Λ, fun n hn Λ => inner_eq_of_unip S S.X' n hn.2 Λ,
    fun φ hφ h1 h2 => mem_hermitianStabilizer_of_preserves_both_flags S φ hφ h1 h2⟩

end GlobalTheory.HL.DatumOf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLevelLocalDualQuotientLengthOne
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tidx_arith {ι : Type} (s : Finset ι) (r : ι → ℕ) (T f : ℕ) (hT : T.Prime) (hcard : s.card = f)
    (hdvd : ∏ i ∈ s, r i ∣ T ^ (2 * f)) (hlow : ∀ i ∈ s, r i ≠ 0 → T ^ 2 ≤ r i) : ∀ i ∈ s, r i = T ^ 2 := by
  have hT0 : 0 < T := hT.pos
  have hpow0 : T ^ (2 * f) ≠ 0 := pow_ne_zero _ hT.ne_zero

  have hprod0 : ∏ i ∈ s, r i ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact hpow0 (zero_dvd_iff.mp hdvd)
  have hge : ∀ i ∈ s, T ^ 2 ≤ r i := fun i hi =>
    hlow i hi (fun h => hprod0 (Finset.prod_eq_zero hi h))

  have hle : ∏ i ∈ s, r i ≤ ∏ _i ∈ s, T ^ 2 := by
    rw [Finset.prod_const, hcard, ← pow_mul]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpow0) hdvd
  intro i hi
  by_contra hne
  have hlt : ∏ _i ∈ s, T ^ 2 < ∏ i ∈ s, r i :=
    Finset.prod_lt_prod₀ (fun j _ => pow_pos hT0 2) hge ⟨i, hi, lt_of_le_of_ne (hge i hi) (Ne.symm hne)⟩
  exact absurd hle (not_le.mpr hlt)

theorem tLat_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hs hdeg hL v hv
  obtain ⟨hncard, hloc⟩ := GlobalTheory.St.G.SplitPrime.split_place F E cm T hT hs

  have hF : Module.finrank ℚ F = f := by
    have h := Module.finrank_mul_finrank ℚ F E
    rw [cm.deg2, hdeg] at h
    omega
  have hfin : {w : HeightOneSpectrum (𝓞 F) | (T : 𝓞 F) ∈ w.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [hncard]; exact Module.finrank_pos)
  have hcard : hfin.toFinset.card = f := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hncard, hF]

  have hlow : ∀ w ∈ hfin.toFinset,
      (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup ≠ 0 →
      T ^ 2 ≤ (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup := by
    intro w hw h0
    have hw' : (T : 𝓞 F) ∈ w.asIdeal := (Set.Finite.mem_toFinset hfin).mp hw
    obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc w hw'
    exact _root_.GlobalTheory.St.G.IdxLower.sq_le_local_index F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2
      (_root_.GlobalTheory.St.G.dual_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2) h0

  have hdvd := _root_.GlobalTheory.St.G.GlobIdx.prod_loc_relIndex_dvd F E cm n J hJ hdet T f L hT hs hdeg hL hfin.toFinset
    (fun w hw => (Set.Finite.mem_toFinset hfin).mp hw)
  rw [hL.2.2.2.1] at hdvd
  have heq := tidx_arith hfin.toFinset
    (fun w => (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup)
    T f hT hcard hdvd hlow v ((Set.Finite.mem_toFinset hfin).mpr hv)
  refine ⟨heq, ?_⟩
  obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc v hv
  exact _root_.GlobalTheory.St.G.CyclicQuot.local_dual_cyclic F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2
    (_root_.GlobalTheory.St.G.dual_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2) heq

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiUnipotentModelMeasurableFullMeasure
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem nset_closed (k r : ℕ) : IsClosed {y : Mt k r | Matrix.of y ∈ Nset k r} := by
  simp only [Nset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · have hc : Continuous fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y := by
      have h0 : Continuous fun y : Mt k r => (Matrix.of y : Matrix _ _ ℂ) := continuous_id
      exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  · refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const

theorem pi_nset_full : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  intro ι _ k r
  have hS : MeasurableSet {y : Mt k r | Matrix.of y ∈ Nset k r} := (nset_closed k r).measurableSet
  have hH := (_root_.GlobalTheory.SnMass.NEntry.haarLie_entries k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hset : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
      ⋂ w, Function.eval w ⁻¹' {y : Mt k r | Matrix.of y ∈ Nset k r} := by
    ext x; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact MeasurableSet.iInter fun w => measurable_pi_apply w hS
  · rw [hset, Set.compl_iInter]
    refine measure_iUnion_null fun w => ?_
    rw [← Set.preimage_compl]
    exact Measure.pi_eval_preimage_null _ (by simpa [Set.compl_setOf] using hH.2.2.1)

end GlobalTheory.SnMass.VolN
end

