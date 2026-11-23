module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectHaar
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

theorem SemidirectHaar.proof (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] :
    SemidirectHaar.Statement G T := by
  intro P H hP hH hHP τ β δ hτ hβ hδc hτP _ hτH hβH μ _ ν _ ρ _ hδ
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology (H : Set G))
  have : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hUo : IsOpen (interior K) := isOpen_interior
  have hU1 : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.2 hK1
  set f : G → ℝ≥0∞ := (interior K).indicator 1 with hf_def
  have hfm : Measurable f := measurable_one.indicator hUo.measurableSet
  have hI : ∫⁻ x : H, f x ∂ν = ν (Subtype.val ⁻¹' interior K) := by
    rw [← lintegral_indicator_one (hUo.preimage continuous_subtype_val).measurableSet]
    congr 1
  have hI0 : ∫⁻ x : H, f x ∂ν ≠ 0 := by
    rw [hI]
    exact ((hUo.preimage continuous_subtype_val).measure_pos ν ⟨1, hU1⟩).ne'
  have hItop : ∫⁻ x : H, f x ∂ν ≠ ∞ := by
    rw [hI]
    exact ((measure_mono (Set.preimage_mono interior_subset)).trans_lt
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top).ne

  have hmul : ∀ s t, δ (s * t) = δ s * δ t := by
    intro s t
    have e1 := hδ (s * t) f hfm
    have e2 : ∫⁻ x : H, f (τ s * (τ t * x * (τ t)⁻¹) * (τ s)⁻¹) ∂ν =
        δ t * ∫⁻ x : H, f (τ s * x * (τ s)⁻¹) ∂ν :=
      hδ t (fun z => f (τ s * z * (τ s)⁻¹))
        (hfm.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable)
    have e3 := hδ s f hfm
    have e : ∫⁻ x : H, f (τ (s * t) * x * (τ (s * t))⁻¹) ∂ν =
        ∫⁻ x : H, f (τ s * (τ t * x * (τ t)⁻¹) * (τ s)⁻¹) ∂ν := by
      congr 1
      funext x
      simp only [map_mul, mul_inv_rev]
      group
    rw [e, e2, e3, ← mul_assoc] at e1
    have h := (ENNReal.mul_left_inj hI0 hItop).1 e1
    exact (ENNReal.coe_injective (by rw [ENNReal.coe_mul]; exact h)).symm.trans (mul_comm _ _)
  have hone : δ 1 = 1 := by
    have e := hδ 1 f hfm
    simp only [map_one, one_mul, inv_one, mul_one] at e
    have h := (ENNReal.mul_left_inj hI0 hItop).1 (e.symm.trans (one_mul _).symm)
    exact_mod_cast h
  have hpos : ∀ t, δ t ≠ 0 := fun t h => by
    have e := hmul t t⁻¹
    rw [mul_inv_cancel, hone, h, zero_mul] at e
    exact one_ne_zero e

  let Φ : T × H → P := fun q => ⟨(q.2 : G) * τ q.1, P.mul_mem (hHP q.2.2) (hτP q.1)⟩
  have hΦc : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hτ.comp continuous_fst)).subtype_mk _
  have hΦm : Measurable Φ := hΦc.measurable
  have hδm : Measurable fun t => (δ t : ℝ≥0∞) := (ENNReal.continuous_coe.comp hδc).measurable
  let m : Measure P := Measure.map Φ ((ρ.withDensity fun t => (δ t : ℝ≥0∞)).prod ν)
  have hm : ∀ ψ : P → ℝ≥0∞, Measurable ψ →
      ∫⁻ p, ψ p ∂m = ∫⁻ t, δ t * ∫⁻ x : H, ψ (Φ (t, x)) ∂ν ∂ρ := by
    intro ψ hψ
    rw [lintegral_map hψ hΦm, lintegral_prod (fun z => ψ (Φ z)) (hψ.comp hΦm).aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hδm]
    · rfl
    · exact (hψ.comp hΦm).lintegral_prod_right'

  have hinv : ∀ (p₀ : P) (ψ : P → ℝ≥0∞), Measurable ψ →
      ∫⁻ p, ψ (p₀ * p) ∂m = ∫⁻ p, ψ p ∂m := by
    intro p₀ ψ hψ
    rw [hm (fun p => ψ (p₀ * p)) (hψ.comp (measurable_const_mul p₀)), hm _ hψ]
    set s := β p₀ with hs
    let y : H := ⟨(p₀ : G) * (τ s)⁻¹, hβH p₀⟩
    let ψ' : G → ℝ≥0∞ := Function.extend Subtype.val ψ 0
    have hψ' : Measurable ψ' :=
      (MeasurableEmbedding.subtype_coe hP.measurableSet).measurable_extend hψ measurable_const
    have hψ'e : ∀ p : P, ψ' p = ψ p := fun p => Subtype.val_injective.extend_apply ψ 0 p
    have inner : ∀ t, ∫⁻ x : H, ψ (p₀ * Φ (t, x)) ∂ν =
        δ s * ∫⁻ x : H, ψ (Φ (s * t, x)) ∂ν := by
      intro t
      have h1 : ∫⁻ x : H, ψ' ((y : G) * (τ s * x * (τ s)⁻¹) * τ (s * t)) ∂ν =
          δ s * ∫⁻ x : H, ψ' ((y : G) * x * τ (s * t)) ∂ν :=
        hδ s (fun z => ψ' ((y : G) * z * τ (s * t)))
          (hψ'.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable)
      have h2 : ∫⁻ x : H, ψ' ((y : G) * x * τ (s * t)) ∂ν = ∫⁻ x : H, ψ (Φ (s * t, x)) ∂ν := by
        rw [← lintegral_mul_left_eq_self (μ := ν) (fun x : H => ψ (Φ (s * t, x))) y]
        congr 1
        funext x
        rw [← hψ'e]
        rfl
      rw [← h2, ← h1]
      congr 1
      funext x
      rw [← hψ'e]
      congr 1
      simp only [Φ, y, Subgroup.coe_mul, map_mul]
      group
    refine Eq.trans ?_ (lintegral_mul_left_eq_self (μ := ρ)
      (fun u => (δ u : ℝ≥0∞) * ∫⁻ x : H, ψ (Φ (u, x)) ∂ν) s)
    congr 1
    funext t
    rw [inner, hmul, ENNReal.coe_mul]
    ring
  have : Measure.IsMulLeftInvariant m := by
    constructor
    intro p₀
    ext S hS
    rw [Measure.map_apply (measurable_const_mul p₀) hS, ← lintegral_indicator_one hS,
      ← lintegral_indicator_one (measurable_const_mul p₀ hS)]
    exact hinv p₀ _ (measurable_one.indicator hS)

  have hβΦ : ∀ t (x : H), β (Φ (t, x)) = t := by
    intro t x
    have h := H.mul_mem (H.inv_mem x.2) (hβH (Φ (t, x)))
    have h' : τ (t * (β (Φ (t, x)))⁻¹) ∈ H := by
      simpa [Φ, map_mul, map_inv, mul_assoc] using h
    exact (mul_inv_eq_one.1 (hτH _ h')).symm
  let α : P → H := fun p => ⟨(p : G) * (τ (β p))⁻¹, hβH p⟩
  have hα : Continuous α :=
    (continuous_subtype_val.mul (hτ.comp hβ).inv).subtype_mk _
  have hαΦ : ∀ t (x : H), α (Φ (t, x)) = x := by
    intro t x
    apply Subtype.ext
    simp only [α, hβΦ]
    simp [Φ]
  have : IsFiniteMeasureOnCompacts m := by
    constructor
    intro K hK
    have hL : IsCompact (closure K) := hK.closure
    refine (measure_mono subset_closure).trans_lt ?_
    have hLm : MeasurableSet (closure K) := isClosed_closure.measurableSet
    obtain ⟨C, hC⟩ := (hL.image hβ).bddAbove_image hδc.continuousOn
    rw [← lintegral_indicator_one hLm, hm _ (measurable_one.indicator hLm)]
    calc ∫⁻ t, δ t * ∫⁻ x : H, (closure K).indicator 1 (Φ (t, x)) ∂ν ∂ρ
        ≤ ∫⁻ t, (β '' closure K).indicator (fun _ => (C : ℝ≥0∞) * ν (α '' closure K)) t ∂ρ := by
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ β '' closure K
          · rw [Set.indicator_of_mem ht]
            gcongr
            · exact_mod_cast hC ⟨t, ht, rfl⟩
            · calc ∫⁻ x : H, (closure K).indicator 1 (Φ (t, x)) ∂ν
                  ≤ ∫⁻ x : H, (α '' closure K).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν := by
                    refine lintegral_mono fun x => ?_
                    by_cases hx : Φ (t, x) ∈ closure K
                    · rw [Set.indicator_of_mem hx,
                        Set.indicator_of_mem (show x ∈ α '' closure K from ⟨Φ (t, x), hx, hαΦ t x⟩)]
                      rfl
                    · rw [Set.indicator_of_notMem hx]
                      exact bot_le
                _ ≤ 1 * ν (α '' closure K) := lintegral_indicator_const_le _ _
                _ = ν (α '' closure K) := one_mul _
          · have h0 : ∀ x : H, (closure K).indicator (1 : P → ℝ≥0∞) (Φ (t, x)) = 0 :=
              fun x => Set.indicator_of_notMem (fun hx => ht ⟨Φ (t, x), hx, hβΦ t x⟩) _
            simp [h0]
      _ ≤ (C : ℝ≥0∞) * ν (α '' closure K) * ρ (β '' closure K) :=
          lintegral_indicator_const_le _ _
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
          (hL.image hα).measure_lt_top) (hL.image hβ).measure_lt_top

  have hm0 : m ≠ 0 := by
    intro h0
    have e := hm (fun _ => 1) measurable_const
    rw [h0, lintegral_zero_measure] at e
    simp only [lintegral_const, one_mul] at e
    rw [lintegral_mul_const _ hδm] at e
    have hν : ν Set.univ ≠ 0 := isOpen_univ.measure_ne_zero ν Set.univ_nonempty
    have hρ : ∫⁻ t, (δ t : ℝ≥0∞) ∂ρ ≠ 0 := by
      rw [Ne, lintegral_eq_zero_iff hδm]
      intro h
      have hF : ∀ᵐ _t ∂ρ, False := h.mono fun t ht => hpos t (by simpa using ht)
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hF
      exact isOpen_univ.measure_ne_zero ρ Set.univ_nonempty (by rw [hF]; rfl)
    exact mul_ne_zero hρ hν e.symm

  have hsc := Measure.isMulLeftInvariant_eq_smul m μ
  set c₀ := Measure.haarScalarFactor m μ with hc₀
  have hc0 : c₀ ≠ 0 := by
    intro h
    apply hm0
    rw [hsc, h, zero_smul]
  refine ⟨c₀⁻¹, inv_ne_zero hc0, fun φ hφ => ?_⟩
  have key : ∫⁻ p, φ p ∂m = ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ :=
    hm _ (hφ.comp continuous_subtype_val.measurable)
  rw [hsc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul] at key
  rw [← key, ENNReal.coe_inv hc0, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hc0) ENNReal.coe_ne_top, one_mul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerCovolume
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

universe u

theorem exists_covering_of_relIndex_ne_zero {G K : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [Group K] (μ : Measure G) [μ.IsMulLeftInvariant] (f : K →* G)
    (A B : Subgroup K) (hidx : A.relIndex B ≠ 0) (FD : Set G)
    (hFD : IsFundamentalDomain (B.map f) FD μ) (hfin : μ FD < ⊤) :
    ∃ T : Set G, MeasurableSet T ∧ μ T < ⊤ ∧ ∀ l, ∃ a ∈ A, f a * l ∈ T := by
  classical
  have : (A.subgroupOf B).FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (B ⧸ A.subgroupOf B)
  set bad := {l : G | ¬ ∃ γ : B.map f, γ • l ∈ FD} with hbad_def
  have hbad : μ bad = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hFD.ae_covers.mono fun x hx hx' => hx' hx)
  refine ⟨(⋃ k : B ⧸ A.subgroupOf B, (fun x => f ((Quotient.out k : B) : K) * x) ⁻¹'
    toMeasurable μ FD) ∪ toMeasurable μ bad, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun k => (measurableSet_toMeasurable μ FD).preimage
      (measurable_const_mul _)).union (measurableSet_toMeasurable μ bad)
  · refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [measure_toMeasurable, hbad, add_zero]
    refine lt_of_le_of_lt (measure_iUnion_fintype_le μ _) ?_
    simp only [measure_preimage_mul, measure_toMeasurable]
    exact ENNReal.sum_lt_top.2 fun _ _ => hfin
  · intro l
    by_cases hl : l ∈ bad
    · exact ⟨1, one_mem _, Or.inr (subset_toMeasurable μ bad (by simpa using hl))⟩
    · rw [hbad_def, Set.mem_ofPred_eq, not_not] at hl
      obtain ⟨⟨γ, hγ⟩, hγl⟩ := hl
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hγ
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
      set k : B ⧸ A.subgroupOf B := QuotientGroup.mk (⟨b, hb⟩ : B)
      have hcA : (((c : B) : K)) ∈ A := c.2
      refine ⟨((c : B) : K)⁻¹, inv_mem hcA, Or.inl (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      apply subset_toMeasurable
      have e : ((Quotient.out k : B) : K) = b * ((c : B) : K) := by
        rw [hc]; rfl
      simp only [e, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      simpa [Subgroup.smul_def] using hγl

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem StabilizerCovolumeFinite.proof [FiniteDimensional E W] (h : HermitianForm F E W)
    (v : Basis ι E W) (h₁ : CovolumeFiniteBelow.{u} F E (finrank E W))
    (h₂ : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (h₃ : StabilizerLevi.Statement h v) (h₄ : UnipotentModulus.Statement h v)
    (h₅ : UnipotentCocompact.Statement h v) (h₆ : CongruenceLift.Statement h) :
    StabilizerCovolumeFinite.Statement h v := by
  classical
  intro D La x₀ hLa hx₀ hne hiso ν hν

  obtain ⟨w₀, hxw, hww⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨h', hh'⟩ := ComplementForm.proof h x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  have hlt : finrank E (hypComplement h x₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hmem : w₀ ∈ hypComplement h x₀ w₀ := htop ▸ Submodule.mem_top
    rw [mem_hypComplement, hxw] at hmem
    exact one_ne_zero hmem.1

  obtain ⟨i, q, hi, hq, hqi, hker, hiw, hcompat⟩ := h₃ x₀ w₀ hp h' hh' _ v'

  obtain ⟨D', La', G'', hLa', hG'', hidx, hlift⟩ := h₆ D La x₀ w₀ hLa hx₀ hp h' hh'
  let μL : Measure (archUnitary h' v') := Measure.haar
  obtain ⟨FD', hFD', hFD'fin⟩ :=
    h₁ (hypComplement h x₀ w₀) h' _ v' hlt μL D' La' hLa'
  obtain ⟨T, hTm, hTfin, hT⟩ := exists_covering_of_relIndex_ne_zero μL (archEmbed h' v') G''
    (latticeStab h' La') hidx FD' hFD' hFD'fin
  set Γ := (vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀) with hΓ
  have hcovL : ∀ l, ∃ γ ∈ Γ, q γ * l ∈ T := by
    intro l
    obtain ⟨m, hm, hml⟩ := hT l
    obtain ⟨γ₀, hγx, hγw, hγm⟩ := ComplementExtension.proof h x₀ w₀ hp h' hh' m
    have hγ₀ : γ₀ ∈ latticeStab h La := hlift m hm γ₀ hγx hγw hγm
    refine ⟨i (archEmbed h' v' m), ?_, by rw [hqi]; exact hml⟩
    rw [hΓ, Subgroup.mem_subgroupOf, hcompat γ₀ m hγx hγw hγm]
    exact ⟨⟨γ₀, hγ₀⟩, hγx, rfl⟩

  obtain ⟨C, hC, hcovN⟩ := h₅ D La x₀ hLa hx₀ hne hiso
  let j : unipRadical h v x₀ →* vecFixGroup h v x₀ :=
    Subgroup.inclusion (unipRadical_le_vecFixGroup h v x₀)
  have hjc : Continuous j := (continuous_subtype_val.subtype_mk _)
  have hj : IsClosedEmbedding j := by
    refine ⟨IsEmbedding.of_comp hjc continuous_subtype_val IsEmbedding.subtypeVal, ?_⟩
    have : Set.range j = Subtype.val ⁻¹' (unipRadical h v x₀ : Set (archUnitary h v)) := by
      ext g
      exact ⟨by rintro ⟨n, rfl⟩; exact n.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    rw [this]
    exact (isClosed_unipRadical h v x₀).preimage continuous_subtype_val
  have hjr : ∀ g, q g = 1 ↔ g ∈ j.range := fun g => (hker g).trans
    ⟨fun hg => ⟨⟨g, hg⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩
  let μN : Measure (unipRadical h v x₀) := Measure.haar
  have hemb : MeasurableEmbedding (Subtype.val : vecFixGroup h v x₀ → archUnitary h v) :=
    (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.measurableEmbedding
  have hconj : ∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j := by
    intro l
    have key := h₄ x₀ w₀ hp μN ((i l : vecFixGroup h v x₀) : archUnitary h v) ⟨(i l).2, hiw l⟩
    have hf : Continuous fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹ :=
      (continuous_const.mul hjc).mul continuous_const
    rw [← hemb.comap_map (μN.map _), ← hemb.comap_map (μN.map j),
      Measure.map_map hemb.measurable hf.measurable,
      Measure.map_map hemb.measurable hjc.measurable]
    have e1 : (Subtype.val ∘ fun n : unipRadical h v x₀ => i l * j n * (i l)⁻¹) =
        fun n : unipRadical h v x₀ =>
          ((i l : vecFixGroup h v x₀) : archUnitary h v) * (n : archUnitary h v) *
            ((i l : vecFixGroup h v x₀) : archUnitary h v)⁻¹ := by
      funext n
      simp [j]
    have e2 : (Subtype.val ∘ j) = (Subtype.val : unipRadical h v x₀ → archUnitary h v) := by
      funext n
      rfl
    rw [e1, e2, key]
  have hcovN' : ∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C := fun n => by
    obtain ⟨δ, hδ, hδn⟩ := hcovN n
    exact ⟨δ, hδ, hδn⟩

  obtain ⟨S, -, hSfin, hScov⟩ :=
    h₂ x₀ w₀ h' _ v' i q j hi hq hj hqi hjr μL μN hconj Γ C T hC hTm hTfin hcovN' hcovL ν

  have hdG : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨((x : vecFixGroup h v x₀) : archUnitary h v), x.2⟩ :
        vecStabGroup h v La x₀))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨FD, -, hFD⟩ := DiscreteFundamentalDomain.proof (vecFixGroup h v x₀) ν Γ hdisc

  have hle : ν FD ≤ ν S := by
    rw [hFD.measure_eq_tsum S]
    refine (measure_mono fun x hx => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, hγx⟩ := hScov x
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγx
  have hν0 : ν ≠ 0 := fun h0 => (isOpen_univ.measure_ne_zero ν Set.univ_nonempty) (by simp [h0])
  exact ⟨FD, hFD, pos_iff_ne_zero.2 (hFD.measure_ne_zero hν0), hle.trans_lt hSfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipRadicalOfRational
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipRadicalOfRational.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipRadicalOfRational.Statement h v := by
  classical
  intro x₀ γ hx hz
  have hγ : ∀ u : W, γ • u = (γ : W ≃ₗ[E] W) u := fun _ => rfl

  have key : ∃ y : W, ∀ u : W, ∃ a : E,
      γ • u = u + h.toSesq x₀ u • (γ • y - y) + a • x₀ := by
    by_cases hy : ∃ y, h.toSesq x₀ y = 1
    · obtain ⟨y, hy⟩ := hy
      refine ⟨y, fun u => ?_⟩
      obtain ⟨a, ha⟩ := hz (u - h.toSesq x₀ u • y)
        (by rw [map_sub, map_smul, smul_eq_mul, hy, mul_one, sub_self])
      have hs : γ • (u - h.toSesq x₀ u • y) = γ • u - h.toSesq x₀ u • (γ • y) := by
        simp only [hγ, map_sub, map_smul]
      rw [hs] at ha
      refine ⟨a, ?_⟩
      rw [smul_sub, sub_eq_iff_eq_add.mp ha]
      abel
    · refine ⟨0, fun u => ?_⟩
      have h0 : h.toSesq x₀ u = 0 := by
        by_contra hu
        exact hy ⟨(h.toSesq x₀ u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
      obtain ⟨a, ha⟩ := hz u h0
      exact ⟨a, by simp [ha]⟩
  obtain ⟨y, hy⟩ := key
  choose a ha using fun j => hy (v j)
  rw [mem_unipRadical]
  intro w
  set M : Matrix ι ι ℂ := (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
    Matrix ι ι ℂ) with hM
  have hvec : ∀ x : W, M *ᵥ vecAt v x w = vecAt v (γ • x) w := fun x =>
    congrFun (archEmbed_smul_vecAt h v γ x) w

  have hcol : ∀ i j, M i j = w.embedding (v.repr (γ • v j) i) := by
    intro i j
    have := congrFun (hvec (v j)) i
    simpa [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite,
      eq_comm] using this
  refine ⟨by rw [hvec, hx], fun z hz0 => ?_⟩

  have hℓ : ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j = 0 := by
    rw [← hz0]
    have hH : ∀ j, w.embedding (h.toSesq x₀ (v j)) =
        ∑ i, star (vecAt v x₀ w i) * gramAt h v w i j := by
      intro j
      rw [HermAtPlace.proof h v w x₀ (v j)]
      simp [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite]
    simp only [hH, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∑ j, w.embedding (a j) * z j, ?_⟩
  funext i
  have hrow : (M *ᵥ z) i = ∑ j, (w.embedding (if i = j then 1 else 0) +
      w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) +
      w.embedding (a j) * w.embedding (v.repr x₀ i)) * z j := by
    simp only [mulVec, dotProduct, hcol]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]
    simp [Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  have e1 : ∑ j, w.embedding (if i = j then 1 else 0) * z j = z i := by
    simp [apply_ite]
  have e2 : ∑ j, w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) * z j =
      w.embedding (v.repr (γ • y - y) i) * ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, w.embedding (a j) * w.embedding (v.repr x₀ i) * z j =
      (∑ j, w.embedding (a j) * z j) * w.embedding (v.repr x₀ i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, hℓ]
  simp [vecAt]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

