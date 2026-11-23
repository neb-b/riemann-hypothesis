module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMeasureEqSmulAddHaarLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormNonNormCancel
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.Cancel

open ValuativeRel
open scoped Topology NNReal

theorem compact_subset_cball {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {K : Set F} (hK : IsCompact K) :
    ∃ s : Fˣ, K ⊆ GlobalTheory.SplitWeil.cball s := by
  refine hK.elim_directed_cover (fun s : Fˣ => GlobalTheory.SplitWeil.cball s) GlobalTheory.SplitWeil.isOpen_cball ?_ ?_
  · intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [GlobalTheory.SplitWeil.cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩
  · intro a b
    rcases le_total (valuation F (a : F)) (valuation F (b : F)) with h | h
    · exact ⟨b, fun x hx => le_trans (show valuation F x ≤ _ from hx) h, fun x hx => hx⟩
    · exact ⟨a, fun x hx => hx, fun x hx => le_trans (show valuation F x ≤ _ from hx) h⟩

theorem punctured_neBot (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : (𝓝[≠] (0 : F)).NeBot := by
  by_contra h
  rw [Filter.not_neBot, ← isOpen_singleton_iff_punctured_nhds] at h
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (h.mem_nhds rfl)
  exact s.ne_zero (hs (by simp [GlobalTheory.SplitWeil.cball]))

theorem mul_mem_cball_iff {F : Type} [Field F] [ValuativeRel F] (a s : Fˣ) (x : F) :
    valuation F ((a : F) * x) ≤ valuation F (s : F) ↔ valuation F x ≤ valuation F ((a⁻¹ * s : Fˣ) : F) := by
  rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    le_inv_mul_iff₀ (by simp [zero_lt_iff])]

theorem gauss_cancel : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → (∫ z in {z : E | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ (Algebra.norm F z) ∂μ) + (nabs F t : ℂ) * ∫ z in {z : E | (t : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _ t ht
  borelize F
  obtain ⟨hfd, hring, -, ht2, -, hN, -, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  haveI := GlobalTheory.SplitWeil.t2Space F
  haveI := punctured_neBot F
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  haveI : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot F E 0
  haveI : LocallyCompactSpace E := by
    obtain ⟨L, -, h1, h2⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1
    exact h1.locallyCompactSpace_of_mem_nhds_of_addGroup (h2.mem_nhds L.zero_mem)
  have hμ0 : μ {0} = 0 := measure_singleton 0
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.SplitWeil.exists_isUnitVol F
  obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.KSp.exists_integral_cball_char_eq_zero F lam ψ hψ hψ1 hψ0
  have hm : ∀ a : F, Measurable fun z : E => a * Algebra.norm F z := fun a =>
    (continuous_const.mul hN).measurable
  let m : Fˣ → Measure F := fun a => μ.map fun z : E => (a : F) * Algebra.norm F z
  let n : Fˣ → Measure F := fun a => distribHaarChar F a • m a
  have hmc : ∀ a, IsFiniteMeasureOnCompacts (m a) := fun a => ⟨fun K hK => by
    obtain ⟨s, hs⟩ := compact_subset_cball hK
    obtain ⟨L, hL, h1, -⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (a⁻¹ * s)
    rw [Measure.map_apply (hm a) hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (h1.measure_lt_top (μ := μ))
    intro z hz
    rw [hL]
    exact (mul_mem_cball_iff a s _).mp (hs hz)⟩
  have hnc : ∀ a, IsFiniteMeasureOnCompacts (n a) := fun a => by
    haveI := hmc a
    exact IsFiniteMeasureOnCompacts.smul_nnreal (m a) _
  have hn0 : ∀ a, n a {0} = 0 := fun a => by
    have : (fun z : E => (a : F) * Algebra.norm F z) ⁻¹' {0} = {0} := by
      ext z; simp [Algebra.norm_eq_zero_iff]
    simp only [n, m, Measure.smul_apply]
    rw [Measure.map_apply (hm a) (measurableSet_singleton 0), this, hμ0, smul_zero]
  have hn1 : ∀ (a : Fˣ) (b : Fˣ), b ∈ (Units.map (Algebra.norm F : E →* F)).range → n (b * a) = n a := by
    rintro a _ ⟨w, rfl⟩
    have h1 := _root_.GlobalTheory.KSp.map_mul_left_eq_norm_smul F E c δ hE μ w
    have h2 : m (Units.map (Algebra.norm F : E →* F) w * a) =
        (μ.map fun x => (w : E) * x).map fun z : E => (a : F) * Algebra.norm F z := by
      rw [Measure.map_map (hm a) (measurable_const_mul _)]
      simp only [m]
      congr 1
      funext z
      simp [map_mul, mul_comm, mul_left_comm, mul_assoc]
    simp only [n]
    rw [h2, h1, Measure.map_smul _ (hm a).aemeasurable, smul_smul, map_mul, mul_right_comm,
      mul_inv_cancel₀ (distribHaarChar_pos).ne', one_mul]
  have hn2 : ∀ a u : Fˣ, (n a).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n (u * a) := by
    intro a u
    simp only [n, m]
    rw [Measure.map_smul _ (measurable_const_mul _).aemeasurable,
      Measure.map_map (measurable_const_mul _) (hm a), smul_smul, map_mul,
      inv_mul_cancel_left₀ (distribHaarChar_pos).ne']
    congr 2
    funext z
    simp [mul_assoc]
  have hhom : ∀ u : Fˣ, (n 1 + n t).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • (n 1 + n t) := by
    intro u
    rw [Measure.map_add _ _ (measurable_const_mul _), hn2, hn2, ← smul_add]
    congr 1
    by_cases hu : u ∈ (Units.map (Algebra.norm F : E →* F)).range
    · rw [hn1 _ _ hu, hn1 _ _ hu]
    · have h1 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE u t hu ht
      have h2 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE t t ht ht
      have h3 := hn1 1 _ h1
      have h4 := hn1 t _ (mul_mem h1 (inv_mem h2))
      rw [mul_one] at h3
      have h5 : u * t * (t * t)⁻¹ * t = u * 1 := by group
      rw [h5] at h4
      rw [h3, h4, add_comm]
  haveI := hnc 1
  haveI := hnc t
  haveI : IsFiniteMeasureOnCompacts (n 1 + n t) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.KSp.Homog.eq_smul_haar_of_homog F lam (n 1 + n t) (by rw [Measure.add_apply, hn0, hn0, add_zero]) hhom
  refine ⟨s₀, fun s hs => ?_⟩
  have hB := GlobalTheory.SplitWeil.isCompact_cball s
  have hint : ∀ a : Fˣ, ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n a) = (nabs F a : ℂ) *
      ∫ z in {z : E | (a : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((a : F) * Algebra.norm F z) ∂μ := by
    intro a
    simp only [n, m]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      setIntegral_map hB.measurableSet hψ.aestronglyMeasurable (hm a).aemeasurable]
    rfl
  have h1 : ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n 1 + n t) = 0 := by
    rw [hr, Measure.restrict_smul, integral_smul_nnreal_measure, hs₀ s hs, smul_zero]
  rw [Measure.restrict_add, integral_add_measure (hψ.continuousOn.integrableOn_compact hB)
    (hψ.continuousOn.integrableOn_compact hB), hint, hint] at h1
  simpa [GlobalTheory.SplitWeil.nabs_one] using h1

end GlobalTheory.KSp.Cancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
section
namespace GlobalTheory.HookDiagram

theorem hookProd_eq_of_mem (μ : YoungDiagram) (n : ℕ) (a : ℕ → ℕ)
    (h : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i) :
    Formalism.LatticeIndexTer.hookProd μ = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hrow : ∀ r, r < n → μ.rowLen r = a r := by
    intro r hr
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, a r) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hlt
      exact lt_irrefl _ ((h r (a r)).mp hm).2
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, μ.rowLen r) ∈ μ := (h r _).mpr ⟨hr, hlt⟩
      exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)
  have hcol : ∀ r c, Finset.filter (fun r' => c < a r') (Finset.Ioo r n) =
      Finset.Ioo r (μ.colLen c) := by
    intro r c
    ext r'
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, YoungDiagram.mem_iff_lt_colLen.mp ((h r' c).mpr ⟨h2, h3⟩)⟩
    · rintro ⟨h1, h2⟩
      have hm := (h r' c).mp (YoungDiagram.mem_iff_lt_colLen.mpr h2)
      exact ⟨⟨h1, hm.1⟩, hm.2⟩
  have hrc : ∀ r c, r < n → c < a r → r < μ.colLen c := fun r c hr hc =>
    YoungDiagram.mem_iff_lt_colLen.mp ((h r c).mpr ⟨hr, hc⟩)
  unfold Formalism.LatticeIndexTer.hookProd GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd
  rw [Finset.prod_finset_product μ.cells (Finset.range n) (fun r => Finset.range (a r))]
  · apply Finset.prod_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    apply Finset.prod_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    dsimp only
    rw [hcol r c, Nat.card_Ioo, hrow r hr]
    have := hrc r c hr hc
    omega
  · rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_range]
    exact h i j

theorem hookOf_eq (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hsort : ((List.range n).map a).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem
      (fun {x y} _ hy hxy => ha x y hxy.le (List.mem_range.mp hy))
  have hL : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a :=
    hsort.insertionSort_eq
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf
  apply hookProd_eq_of_mem
  intro i j
  rw [YoungDiagram.mem_ofRowLens]
  simp only [hL, List.length_map, List.length_range, List.getElem_map, List.getElem_range,
    exists_prop]

theorem hookOf_pos_log (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a ∧
      Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) = Formalism.BasicNotions.DV.logHook n (fun k => (a k : ℝ)) := by
  rw [hookOf_eq n a ha]
  have hm := GlobalTheory.LiftSizeCompare.hookProd_mul n a ha
  have hinner : ∀ r ∈ Finset.range n,
      0 < ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) := by
    intro r _
    apply Finset.prod_pos
    intro l hl
    rw [Finset.mem_Ioo] at hl
    omega
  have hPpos : 0 < ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) :=
    Finset.prod_pos hinner
  have hHpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
    rcases Nat.eq_zero_or_pos (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a) with h0 | h0
    · have hF : 0 < ∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial :=
        Finset.prod_pos fun r _ => Nat.factorial_pos _
      rw [h0, zero_mul] at hm
      omega
    · exact h0
  refine ⟨hHpos, ?_⟩
  have hmR : (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a : ℝ) =
      ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) /
        ((∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) : ℕ) : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hPpos.ne'), ← Nat.cast_mul, hm]
  have hFpos : (0 : ℝ) < ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun r _ => Nat.factorial_pos _
  rw [hmR, Real.log_div hFpos.ne' (by exact_mod_cast hPpos.ne')]
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      have hg : (a r : ℝ) + n - r = ((a r + n - 1 - r : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (show r ≤ a r + n - 1 by omega), Nat.cast_sub (show 1 ≤ a r + n by omega)]
        push_cast
        ring
      rw [hg, Real.Gamma_nat_eq_factorial]
    · intro r _
      exact_mod_cast (Nat.factorial_pos _).ne'
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.cast_prod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mem_Ioo] at hl
        have hal : a l ≤ a r := ha r l hl.1.le hl.2
        congr 1
        rw [Nat.cast_add, Nat.cast_sub hal, Nat.cast_sub hl.1.le]
        ring
      · intro l hl
        rw [Finset.mem_Ioo] at hl
        have hpos : 0 < a r - a l + (l - r) := by omega
        exact_mod_cast hpos.ne'
    · intro r hr
      exact_mod_cast (hinner r hr).ne'

end GlobalTheory.HookDiagram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharUnramVal

theorem locK_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (m : ℤ) (hk : Q.valuation L (k : L) = WithZero.exp (-m)) :
    χ.locK Q k = χ.val Q ^ m := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-m) :=
    (GlobalTheory.CharLocProd.val_algebraMap Q (k : L)).trans hk
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * atFin Q (unif Q) ^ (-m)) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h1, h2, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h4 := hu _ h3
  rw [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at h4
  exact h4

theorem char_eq_prod_val_zpow : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (m : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ Q ∈ S, χ.UnrAt Q ∧ Valued.v (ι (finPart D (x : AE D)) Q) = WithZero.exp (-m Q)) → (∀ Q, Q ∉ S → ι (finPart D (x : AE D)) Q = 1) → ((c x : Circle) : ℂ) = ((∏ Q ∈ S, χ.val Q ^ m Q : ℂˣ) : ℂ) := by
  classical
  intro D ι h1 h2 h3 c χ hc x hx S m hS hoff
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h3 c χ hc
  obtain ⟨S', k₀, -, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hx0 : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h
    by_cases hP : P ∈ S
    · have := (hS P hP).2
      rw [h, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    · exact zero_ne_one (h.symm.trans (hoff P hP))
  choose k hk using fun P => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hx0 P)
  have key := hprod x hx (S ∪ S') (fun P => if P ∈ S then k P else 1) (fun P _ => by
    by_cases hP : P ∈ S
    · simp only [if_pos hP]
      exact ⟨(hk P).1, (hk P).2.1⟩
    · simp only [if_neg hP, hoff P hP, Units.val_one, map_one, sub_self, map_zero, zero_le, and_self])
    (fun P hP => hS' P fun h => hP (Finset.mem_union_right _ h))
  rw [key, Units.coe_prod, ← Finset.prod_subset (Finset.subset_union_left (s₁ := S) (s₂ := S'))]
  · refine Finset.prod_congr rfl fun P hP => ?_
    simp only [if_pos hP]
    rw [locK_eq_val_zpow χ P (hS P hP).1 (k P) (m P) ((hk P).1.symm.trans (hS P hP).2)]
  · intro P _ hP
    simp only [if_neg hP, map_one, Units.val_one]

end GlobalTheory.CharUnramVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisAltLast
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CasimirPull

open GlobalTheory.CechPic

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (act : O → (A ⟶ A)), IsRAct A act → Adj A Q bar act → ∀ (G : Over S) [GrpObj G] (pr : Fin r → (G ⟶ A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → ∀ Φ : A ⟶ G, (∀ u, Φ ≫ pr u = act (e u)) → LBIso ((LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)).pull Φ.left) (LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ))) := by
  intro S A _ _ Q hA hQ h₁ h₂ _ hamp O _ bar r e W d _ _ _ _ hsum act hact hadj G _ pr _ _ Φ hΦ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A
    (Q.pull (lift (𝟙 A) (𝟙 A)).left) hA (pull_isLB hQ _) hamp Q hQ h₁ h₂

  have add2 : ∀ (T : Over S) (y x x' : T ⟶ A), pull (lift y (x * x')).left (cls Q hQ) =
      pull (lift y x).left (cls Q hQ) + pull (lift y x').left (cls Q hQ) := by
    intro T y x x'
    have z := (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).2 (hbi T x x' y).2
    rw [cls_linComb hQ, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    rw [← sub_eq_zero, ← z]
    abel

  have adjB : ∀ (T : Over S) (x y : T ⟶ A) (a : O), pull (lift (x ≫ act a) y).left (cls Q hQ) =
      pull (lift x (y ≫ act (bar a))).left (cls Q hQ) := by
    intro T x y a
    have h := (cls_eq_iff (pull_isLB hQ _) (pull_isLB hQ _)).2 (hadj a)
    rw [cls_pull hQ, cls_pull hQ] at h
    have k₁ : (lift x y).left ≫ (lift (fst A A ≫ act a) (snd A A)).left = (lift (x ≫ act a) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd]
    have k₂ : (lift x y).left ≫ (lift (fst A A) (snd A A ≫ act (bar a))).left = (lift x (y ≫ act (bar a))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    rw [← k₁, ← k₂, pull_comp, pull_comp, h]
  let f : O →+ Pic A.left := AddMonoidHom.mk' (fun a => pull (lift (𝟙 A) (act a)).left (cls Q hQ))
    (fun a b => by simp only [hact.2.2.2 a b]; exact add2 A (𝟙 A) _ _)
  have term : ∀ i j : Fin r, pull Φ.left (pull (lift (pr i) (pr j)).left (cls Q hQ)) =
      f (e j * bar (e i)) := by
    intro i j
    rw [← pull_comp, ← Over.comp_left, comp_lift, hΦ, hΦ]
    have := adjB A (𝟙 A) (act (e j)) (e i)
    rw [Category.id_comp] at this
    rw [this, ← hact.2.2.1]
    rfl
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hQ _ _) _) (LB.isLB_linComb hQ _ _)).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_pull (LB.isLB_linComb hQ _ _), cls_linComb hQ, cls_linComb hQ, map_sum, Fin.sum_univ_one]
  simp only [map_zsmul, term]
  rw [Fintype.sum_prod_type]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_zsmul, ← map_sum, hsum]
  rw [← nsmul_one, map_nsmul, natCast_zsmul]
  rw [map_nsmul]
  show d • pull (lift (𝟙 A) (act 1)).left (cls Q hQ) = _
  rw [hact.2.1]

end GlobalTheory.CasimirPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFineModuliAtComplexEmbeddingComplexBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem spMap_id_complex : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
  simp [spMap]

theorem fineAt_of_isBC (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type)
    [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop)
    (F' : Fam ℂ O Λ g) (hBC : IsBC F' F σ) (hF : FineAt F σ ρ N C) : FineAt F' (RingHom.id ℂ) ρ N C := by
  obtain ⟨f, φ, pb, gp, hact, hL, heta⟩ := hBC
  have M := _root_.GlobalTheory.unifAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ gp hact hL heta
  have base : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' hy
    rw [Category.assoc, pb.w, ← Category.assoc, hy, spMap_id_complex, Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · intro y' hy
    obtain ⟨D', t, P, e, hC, hU⟩ := hF.pts (y' ≫ f) (base y' hy)
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy (base y' hy)).2 e hU
    exact ⟨D', t, P, e', hC, hU'⟩
  · intro D' t P hC hP
    obtain ⟨y, e, hU⟩ := hF.occ D' t P hC hP
    have w : y ≫ F.s = spMap (RingHom.id ℂ) ≫ spMap σ := by
      rw [hU.1, spMap_id_complex, Category.id_comp]
    obtain ⟨y', rfl, hy'⟩ : ∃ y', y' ≫ f = y ∧ y' ≫ F'.s = spMap (RingHom.id ℂ) :=
      ⟨pb.lift y _ w, pb.lift_fst _ _ w, pb.lift_snd _ _ w⟩
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy' (base y' hy')).2 e hU
    exact ⟨y', e', hU'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w h hw hP
    obtain ⟨e₁, hU₁, -⟩ := (M D' t P y hU.1 (base y hU.1)).1 e hU
    obtain ⟨e₂, hU₂, -⟩ := (M D'' t' P' y' hU'.1 (base y' hU'.1)).1 e' hU'
    have hf : y ≫ f = y' ≫ f := hF.sep D' D'' t t' P P' _ _ e₁ e₂ hU₁ hU₂ w h hw hP
    exact pb.hom_ext hf (hU.1.trans hU'.1.symm)

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.IsModel (L := L) A G → ∀ (A' : Over (Sp L)) [GrpObj A'] (ψ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap K L)) ψ → ∃ φ : A'.left ⟶ G.left, IsGrpPullback A' G (spMap (algebraMap W L)) φ := by
  first | exact @GlobalTheory.SS.exists_isGrpPullback_of_isModel | exact GlobalTheory.SS.exists_isGrpPullback_of_isModel | (intros; apply GlobalTheory.SS.exists_isGrpPullback_of_isModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinearStatement
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPeriodMap_comp_injective_realLinear : ∀ {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → Function.Injective R → (∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) → M.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) → (∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) → IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  first | exact @GlobalTheory.PELU.isPeriod_comp_realLinear | exact GlobalTheory.PELU.isPeriod_comp_realLinear | (intros; apply GlobalTheory.PELU.isPeriod_comp_realLinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffineStatement
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_relation_converse_conjAffine : ∀ {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ), M₀ᴴ = M₀ → M₀.det ≠ 0 → (Cᵀ * M₀)ᵀ = Cᵀ * M₀ → (1 - C.map star * C).det ≠ 0 → (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧ ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im = (hermForm M₀ z w).im := by
  first | exact @GlobalTheory.PeriodCoord.riemann_converse | exact GlobalTheory.PeriodCoord.riemann_converse | (intros; apply GlobalTheory.PeriodCoord.riemann_converse; all_goals assumption)
end

