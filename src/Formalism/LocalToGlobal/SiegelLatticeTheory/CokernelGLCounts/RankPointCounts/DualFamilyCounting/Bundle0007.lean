module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXSig
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitSk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSBoxVolSk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXN
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem inN_indep {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
    (hz' : ∀ a, hJ ε (e a) z' = 0) {g : Matrix (Fin n) (Fin n) ℂ} (h : InN ε e z g) : InN ε e z' g :=
  ⟨⟨h.1.1, h.2 z' hz'⟩, h.2⟩

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem Qm_mulVec_eq_sum (w : Fin (2 * r + k + 1) → ℂ) : Qm e f wf z0 *ᵥ w = ∑ j, w j • colQ e f wf z0 j := by
  funext i
  simp only [mulVec, dotProduct, Qm, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem Qm_mem_spanLt {a : ℕ} (ha : a ≤ r) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → w i = 0) : Qm e f wf z0 *ᵥ w ∈ spanLt e a := by
  rw [Qm_mulVec_eq_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j.val < a
  · have hjr : j.val < r := lt_of_lt_of_le hj ha
    have hc : colQ e f wf z0 j = e ⟨j.val, hjr⟩ := by simp [colQ, hjr]
    rw [hc]
    unfold spanLt
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, hjr⟩, hj, rfl⟩)
  · rw [hw j (not_lt.mp hj), zero_smul]
    exact Submodule.zero_mem _

theorem sub_one_eI {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) (a : Fin r)
    (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : ((m - 1) *ᵥ bvec (eI k r a)) i = 0 := by
  rw [bvec, mulVec_single_one, col_apply, Matrix.sub_apply, hm.2.1 a i hi, Matrix.one_apply, sub_self]

theorem sub_one_mulVec_apply_eq_zero_of_mem_Nset {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ j : Fin (2 * r + k + 1), r + k < j.val → w j = 0)
    (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : ((m - 1) *ᵥ w) i = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases lt_or_ge (r + k) j.val with hj | hj
  · rw [hw j hj, mul_zero]
  · rcases lt_or_ge j.val r with hj' | hj'
    · have h1 := hm.2.1 ⟨j.val, hj'⟩ i (by show j.val ≤ i.val; omega)
      have he : eI k r ⟨j.val, hj'⟩ = j := Fin.ext rfl
      rw [he] at h1
      rw [Matrix.sub_apply, h1, Matrix.one_apply, sub_self, zero_mul]
    · rw [Matrix.sub_apply, hm.2.2 i j hj' hj hi, Matrix.one_apply, sub_self, zero_mul]

theorem Qi_perp (y : Fin (2 * r + k + 1) → ℂ) (hy : ∀ a, hJ ε (e a) y = 0) (j : Fin (2 * r + k + 1))
    (hj : r + k < j.val) : (Qi ε e f wf z0 *ᵥ y) j = 0 := by
  have hv : ∀ l : Fin (2 * r + k + 1), l.val < r → ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0 := by
    intro l hl
    have hc : colQ e f wf z0 l = e ⟨l.val, hl⟩ := by simp [colQ, hl]
    have h1 := hy ⟨l.val, hl⟩
    rw [← hc] at h1
    rw [← h1]
    simp only [hJ, mulVec, dotProduct, conjTranspose_apply, Qm, of_apply, Pi.star_apply]
  unfold Qi
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change ∑ l, Hpk k r j l * ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hv l hl, mul_zero]
  · have h0 : Hpk k r j l = 0 := by
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> first | rfl | omega
    rw [h0, zero_mul]

theorem inN_of_conj (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : Qi ε e f wf z0 * g * Qm e f wf z0 ∈ Nset k r) :
    InN ε e (Qm e f wf z0 *ᵥ zB) g := by
  have hg : Qm e f wf z0 * (Qi ε e f wf z0 * g * Qm e f wf z0) * Qi ε e f wf z0 = g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul, Matrix.mul_assoc,
      Qm_mul_Qi hF, Matrix.mul_one]
  have key : ∀ v, (g - 1) *ᵥ v
      = Qm e f wf z0 *ᵥ ((Qi ε e f wf z0 * g * Qm e f wf z0 - 1) *ᵥ (Qi ε e f wf z0 *ᵥ v)) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, hg, Matrix.mul_one, Qm_mul_Qi hF]
  have hz : Qi ε e f wf z0 *ᵥ (Qm e f wf z0 *ᵥ zB) = zB := by
    rw [mulVec_mulVec, Qi_mul_Qm hF, one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, Qi_e hF]
    exact Qm_mem_spanLt (le_of_lt a.isLt) _ (fun i hi => sub_one_eI hm a i hi)
  · rw [key, hz]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm zB (fun j hj => hzB j (Or.inr hj)) i hi)
  · rw [key]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm _ (fun j hj => Qi_perp y hy j hj) i hi)

theorem refN_map (hF : IsFrameJ ε e f wf z0) :
    (refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) = Jac.N1 k r := by
  have h := measN_of hF 1
  rwa [ENNReal.ofReal_one, one_smul] at h

theorem refN_isHaarLoc (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    (hz0 : ∃ t : ℂ, z0 = t • (Qm e f wf z0 *ᵥ zB)) :
    IsHaarLoc (NLoc ε e (Qm e f wf z0 *ᵥ zB)) (refN ε e f wf z0) := by
  set C := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hC
  have hE : MeasurableEmbedding C := embQ hF
  have hmap : Measure.map C (refN ε e f wf z0) = Jac.N1 k r := refN_map hF
  have hH := Jac.nilradical_measure_is_haar (k := k) (r := r)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : SigmaFinite (Measure.map C (refN ε e f wf z0)) := by
      rw [hmap]
      exact hH.1
    exact SigmaFinite.of_map _ hE.measurable.aemeasurable hs
  · intro h0
    apply hH.2.1
    rw [← hmap, h0, Measure.map_zero]
  · refine measure_mono_null (t := C ⁻¹' {x : Mt k r | of x ∉ Nset k r}) ?_ ?_
    · intro g hg
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro hm
      exact hg (inN_of_conj hF hzB hm)
    · rw [← hE.map_apply, hmap]
      exact hH.2.2.1
  · intro s hs
    have hsN := conj_mem_Nset hF hz0 (uMat_mem s) hs
    have hcomp : C ∘ (fun x => s * x) = lmulM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) ∘ C := by
      funext x
      simp only [Function.comp_apply, hC]
      rw [lmulM_cM]
      show Qi ε e f wf z0 * uMat (s * x) * Qm e f wf z0
        = Qi ε e f wf z0 * uMat s * Qm e f wf z0 * Qi ε e f wf z0 * uMat x * Qm e f wf z0
      rw [uMat_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.one_mul]
    have hms : Measurable (fun x : ↥(REAL.UJ ε) => s * x) := by
      rw [← hE.measurable_comp_iff, hcomp]
      exact (measurable_lmulM _).comp hE.measurable
    have hmm : Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))
        = Measure.map C (refN ε e f wf z0) := by
      rw [Measure.map_map hE.measurable hms, hcomp, ← Measure.map_map (measurable_lmulM _) hE.measurable,
        hmap, hH.2.2.2 _ hsN]
    calc Measure.map (fun x => s * x) (refN ε e f wf z0)
        = Measure.comap C (Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))) :=
          (hE.comap_map _).symm
      _ = Measure.comap C (Measure.map C (refN ε e f wf z0)) := by rw [hmm]
      _ = refN ε e f wf z0 := hE.comap_map _

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSAdTup
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.AdTupPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.L2.SG.Pf.NcS.SplitSk
open scoped TensorProduct

open scoped Pointwise in
private theorem compact_open_of_haar_pos_finite {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure]
    [μ.InnerRegularCompactLTTop] (hpos : 0 < μ H) (hfin : μ H < ⊤) :
    IsCompact (H : Set G) ∧ IsOpen (H : Set G) := by
  have hopen : IsOpen (H : Set G) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    simpa only [coe_div_coe H] using
      Measure.div_mem_nhds_one_of_haar_pos_ne_top μ (H : Set G) hH.measurableSet hpos hfin.ne
  have hhalf := ENNReal.half_lt_self hpos.ne' hfin.ne
  obtain ⟨K, hKH, hKc, hKm⟩ := hH.measurableSet.exists_lt_isCompact_of_ne_top hfin.ne hhalf
  have hmass : μ H < μ K + μ K := calc
    μ H = μ H / 2 + μ H / 2 := (ENNReal.add_halves _).symm
    _ < μ K + μ K := ENNReal.add_lt_add_of_le_of_lt (hhalf.trans hfin).ne hKm.le hKm
  -- Every translate of K by an element of H meets K, since K has more than half the mass of H.
  have hdiv : Continuous (fun p : G × G => p.1 / p.2) := continuous_fst.div' continuous_snd
  refine ⟨((hKc.prod hKc).image hdiv).of_isClosed_subset hH ?_, hopen⟩
  intro g hg
  have htranslate : g • K ⊆ (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem hg (hKH hx)
  have hmeet : ¬ Disjoint (g • K) K := by
    intro hd
    have hle := measure_mono (μ := μ) (Set.union_subset htranslate hKH)
    rw [measure_union hd hKc.isClosed.measurableSet, measure_smul] at hle
    exact hmass.not_ge hle
  obtain ⟨y, hy, hyK⟩ := Set.not_disjoint_iff.mp hmeet
  obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hy
  exact ⟨(g * x, x), ⟨hyK, hx⟩, div_eq_iff_eq_mul.mpr rfl⟩

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in
private theorem kf_eq_preimage_stabGLHat (Λ : Set (Fin n → E)) :
    (Kf σ J Λ : Set (HA (Af F) σ J)) = incAf σ J ⁻¹' MassDataMassesW.KCptW.stabGLHat (F := F) Λ :=
  Set.ext fun g => MassDataMassesW.KCptW.kf_iff σ J Λ g

private theorem isClosed_kf [FiniteDimensional F E] (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    IsClosed (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
  let M := MassDataMassesW.KCptW.latHat (F := F) (L : Set (Fin n → E))
  have hM : IsClosed M := by
    have hEq : M = ⋂ v, MassDataMassesW.KCptW.pv v ⁻¹'
        (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [M, MassDataMassesW.KCptW.latHat]
    rw [hEq]
    refine isClosed_iInter fun v => ?_
    have : T2Space (Fv F v ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Fv F v)
    exact (MassDataLevelSSteps.LatTop.isCompact_latLoc v L hfg).isClosed.preimage
      (MassDataMassesW.KCptW.continuous_pv v)
  have hS := MassDataLevelSSteps.LatTop.isClosed_matStab hM
  rw [kf_eq_preimage_stabGLHat]
  exact ((hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)).preimage
    (continuous_subtype_val : Continuous (incAf σ J))

theorem kf_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    IsCompact (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) ∧
      IsOpen (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hO : MassDataMassesW.KCptW.LatHatOpen :=
    MassDataMassesW.KCptW.latHatOpen_of @MassDataMassesW.KCptW.stdHatOpen_holds
  have hC : MassDataMassesW.KCptW.LatHatCompact :=
    MassDataMassesW.KCptW.latHatCompact_of @MassDataMassesW.KCptW.stdHatCompact_holds
  letI : Submodule.IsFullLattice E L := hL
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ :=
    Submodule.IsFullLattice.span_eq_top
  have hMo := hO (F := F) L hspan hL.fg
  have hMc := hC (F := F) L hspan hL.fg
  have hinc : Continuous (incAf σ J) := continuous_subtype_val
  rw [kf_eq_preimage_stabGLHat]
  refine ⟨?_, (MassDataMassesW.KCptW.isOpen_stabGLHat L hMc hMo).preimage hinc⟩
  exact (PI.AdicCompletionValuation.isClosed_HR (Af F) σ J).isClosedEmbedding_subtypeVal.isCompact_preimage
    (MassDataMassesW.KCptW.isCompact_stabGLHat L hspan hMc)

theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [FiniteDimensional F E] {a : ℕ} (X : Fin a → Fin n → E) :
    IsClosed (stabT R σ J X : Set (HA R σ J)) := by
  have : T2Space (R ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product R
  have hmat : Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hact : Continuous (fun g : HA R σ J => g • ratTup (F := F) R X) := by
    refine continuous_pi fun b => ?_
    show Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec
        (ratTup (F := F) R X b))
    exact hmat.matrix_mulVec continuous_const
  exact isClosed_eq hact continuous_const

end Gen

theorem admissible_tuple_holds : AdTup := by
  intro F E _ _ _ _ _ σ n J hCM hJ
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hmI : Measurable (haMap σ J (fstA F)) :=
    (PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (fstA F)
      (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (fstA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_fstA)).measurable
  have hmF : Measurable (haMap σ J (sndA F)) :=
    (PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (sndA F)
      (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (sndA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_sndA)).measurable
  have : SecondCountableTopology (HA (Ainf F) σ J) :=
    PI.VolStabS.TopoAF.secondCountable_HA_of (Ainf F) σ J
  have : SecondCountableTopology (HA (Af F) σ J) :=
    PI.VolStabS.TopoAF.secondCountable_HA_of (Af F) σ J
  have : SigmaCompactSpace (HA (Ainf F) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaCompactSpace (HA (Af F) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hsub : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
      [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] (r : ℕ) (P : Frame E n r)
      (μ : Measure (Hsub R σ J P)), μ.IsHaarMeasure → SFinite (amb μ) := by
    intro R _ _ _ _ _ _ _ r P μ hμ
    have : SecondCountableTopology (HA R σ J) := PI.VolStabS.TopoAF.secondCountable_HA_of R σ J
    have hcl : IsClosed (Hsub R σ J P : Set (HA R σ J)) := isClosed_stabT σ J R (tupH P)
    have : LocallyCompactSpace (Hsub R σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : SecondCountableTopology (Hsub R σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have : SigmaCompactSpace (Hsub R σ J P) := sigmaCompactSpace_of_locallyCompact_secondCountable
    have := hμ
    infer_instance
  refine ⟨hmI.prodMk hmF, fun g₁ g₂ => ⟨PI.UnitaryGroupMassFormula.MeasWCore.haPair σ J g₁ g₂,
      PI.UnitaryGroupMassFormula.MeasWCore.splitA_haPair σ J g₁ g₂⟩, ?_, ?_, ?_, fun g => (continuous_const_mul g).measurable,
    fun g => (continuous_const_mul g).measurable, fun μ hμ => by have := hμ; infer_instance,
    fun μ hμ => by have := hμ; infer_instance, fun r P μ hμ => hsub (Ainf F) r P μ hμ,
    fun r P μ hμ => hsub (Af F) r P μ hμ, ?_, ?_⟩
  · intro a g X
    constructor
    · funext x i
      change tensMap (E := E) (fstA F)
          (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) =
        ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
          (tensMap (E := E) (fstA F))).mulVec (fun j => tensMap (E := E) (fstA F) (X x j))) i
      rw [RingHom.map_mulVec]
      rfl
    · funext x i
      change tensMap (E := E) (sndA F)
          (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) =
        ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
          (tensMap (E := E) (sndA F))).mulVec (fun j => tensMap (E := E) (sndA F) (X x j))) i
      rw [RingHom.map_mulVec]
      rfl
  · intro a X0
    exact ⟨funext fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (fstA F) (X0 x i),
      funext fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (sndA F) (X0 x i)⟩
  · intro a X Y h1 h2
    funext x i
    have e : PI.UnitaryGroupMassFormula.MeasWCore.splT (X x i) = PI.UnitaryGroupMassFormula.MeasWCore.splT (Y x i) :=
      Prod.ext (congrFun (congrFun h1 x) i) (congrFun (congrFun h2 x) i)
    have := congrArg PI.UnitaryGroupMassFormula.MeasWCore.splInv e
    rwa [PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT, PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT] at this
  · rintro Λ ⟨L, hL, rfl⟩
    exact (isClosed_kf σ J L hL.fg).measurableSet
  · rintro Λ μf ⟨L, hL, rfl⟩ hμf hpos hfin r P μ hμ
    have : T2Space (Af F ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Af F)
    obtain ⟨hKc, hKo⟩ := compact_open_of_haar_pos_finite _ (isClosed_kf σ J L hL.fg) μf hpos hfin
    have hcl : IsClosed (Hsub (Af F) σ J P : Set (HA (Af F) σ J)) := isClosed_stabT σ J (Af F) (tupH P)
    have := hμ
    refine ⟨hKo.preimage continuous_subtype_val |>.measure_pos μ ⟨1, (Kf σ J _).one_mem⟩, ?_⟩
    exact (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top

end Formalism.L2.SG.Pf.NcS.AdTupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSBoxSteps
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.BoxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open Formalism.L2.SG.Pf.NcS.BoxVolSk
open scoped TensorProduct

theorem finite_integral_holds : FinInt := by
  intro F E _ _ _ _ _ n a d b x
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact PI.VolStabS.AdmissibleCompactSupport.eventually_mem_latV b x

theorem box_measurable_holds : BoxMeas := by
  intro F E _ _ _ _ _ n a C hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  have e : {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} = ⋂ v, projV v ⁻¹' C v := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter fun v =>
    (PI.VolStabS.TopoMeas.continuous_projV b v).measurable (hC v)

theorem gram_measurable_holds : GramMeas := by
  intro F E _ _ _ _ _ σ n J a T
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨?_, fun y hy => ?_, fun x hx v => ?_⟩
  · have : T2Space (Af F ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Af F)
    have : T2Space (Matrix (Fin a) (Fin a) (Af F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Af F ⊗[F] E))
    exact (isClosed_singleton.preimage
      (PI.VolStabS.continuous_gramR (Af F) σ J)).isOpen_compl.measurableSet
  · funext i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
      (congrFun (congrFun hy i) j)
    rw [PI.VolStabS.RestrProdG.map_gramR, Matrix.map_apply,
      PI.VolStabS.RestrProdG.map_inclR] at h
    rw [Matrix.map_apply]
    exact h
  · funext i j
    have h := congrArg (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
      (congrFun (congrFun hx i) j)
    rw [PI.VolStabS.RestrProdG.map_gramR, Matrix.map_apply,
      PI.VolStabS.RestrProdG.map_inclR] at h
    rw [Matrix.map_apply]
    exact h

theorem positivity_test_holds : PosTest := by
  intro F E _ _ _ _ _ σ n J a μ ν fib t hfib hne
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  set V := Fin a → Fin n → Ainf F ⊗[F] E
  set U : Set V := {X | LinearIndependent (Ainf F ⊗[F] E) X} with hUdef
  have hUo : IsOpen U := PI.VolStabS.TensAllW.isOpen_linIndep b (Ainf F)
    (PI.VolStabS.isOpen_units_Ainf F) (PI.VolStabS.lip_ainf F)
  have : LocallyCompactSpace (Ainf F ⊗[F] E) := PI.AdicCompletionValuation.locallyCompactSpace_tens (Ainf F)
  have : T2Space (Ainf F ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Ainf F)
  have : SecondCountableTopology (Ainf F ⊗[F] E) := PI.VolStabS.secondCountable_tens (Ainf F)

  have hcU : fib t Uᶜ = 0 := measure_mono_null
    (Set.compl_subset_compl.2 Set.inter_subset_right) (hfib.1 t)
  have hUpos : 0 < fib t U := by
    rcases eq_or_ne (fib t U) 0 with h | h
    · exfalso; apply hne
      rw [← Measure.measure_univ_eq_zero]
      have := measure_union_null h hcU
      rwa [Set.union_compl_self] at this
    · exact pos_iff_ne_zero.2 h

  have : LocallyCompactSpace U := hUo.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hUeq : U = ⋃ m, Subtype.val '' compactCovering U m := by
    ext x; constructor
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ((iUnion_compactCovering U).symm ▸ Set.mem_univ (⟨x, hx⟩ : U))
      exact Set.mem_iUnion.2 ⟨m, ⟨⟨x, hx⟩, hm, rfl⟩⟩
    · intro hx
      obtain ⟨m, y, _, rfl⟩ := Set.mem_iUnion.1 hx
      exact y.2
  obtain ⟨m, hm⟩ : ∃ m, 0 < fib t (Subtype.val '' compactCovering U m) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : fib t U = 0 := by
      rw [hUeq]
      exact measure_iUnion_null fun m => nonpos_iff_eq_zero.1 (hcon m)
    exact hUpos.ne' this
  set K : Set V := Subtype.val '' compactCovering U m
  have hK : IsCompact K := (isCompact_compactCovering U m).image continuous_subtype_val
  have hKU : K ⊆ U := by rintro _ ⟨y, _, rfl⟩; exact y.2
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hUo hKU
  have hint : Integrable f (fib t) :=
    ((hfib.2.2 f f.continuous hfc hfU).1 t (Set.mem_univ _))
  refine ⟨f, f.continuous, hfc, fun x => (hf01 x).1, hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun x => (hf01 x).1) hint]
  refine lt_of_lt_of_le hm (measure_mono fun x hx => ?_)
  rw [Function.mem_support, hf1 hx]
  exact one_ne_zero

end Formalism.L2.SG.Pf.NcS.BoxSteps
end
end

