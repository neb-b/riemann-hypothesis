module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureVanishingLatticeEqRowLatticeMatrices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFil
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRowsFil

theorem isKSRow_of_isKSValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  intro E _ _ _ H Dw K _ A _ A' _ i h hA ψ ub hb n e θ s htan hθ hKS τ a₀ hrow
  obtain ⟨w₀, f, hfF, hf, -⟩ := hrow
  haveI : IsCommMonObj A := hA.comm
  have hcc : ∀ σ : E →+* ℂ, conjEmb (conjEmb σ) = σ := fun σ ↦ RingHom.ext fun x ↦ Complex.conj_conj _
  have hc : ∀ a, s * ∑ b, θ a b * ψ f (hb (e.symm b)) = s * θ a (e ⟨conjEmb τ, a₀⟩) := by
    intro a
    congr 1
    rw [Finset.sum_eq_single (e ⟨conjEmb τ, a₀⟩)]
    · rw [hf, Equiv.symm_apply_apply, if_pos rfl, mul_one]
    · intro b _ hb'
      rw [hf, if_neg, mul_zero]
      intro hq
      exact hb' (by rw [← hq, Equiv.apply_symm_apply])
    · intro hn; exact absurd (Finset.mem_univ _) hn
  refine ⟨GlobalTheory.SqZero.tanExp (ub τ) (fun b ↦ s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)),
    (GlobalTheory.LieComb.isLieComb_iff_tanExp _ _).2 rfl, f, hfF, hf, hKS f hfF _ ?_⟩
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp]
  symm
  simp only [GlobalTheory.SqZero.tanExp, GlobalTheory.SqZero.lieExp, hc]
  rw [Fintype.prod_equiv e.symm _ (fun p : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) ↦
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (TrivSqZeroExt.inr (s * θ (e p) (e ⟨conjEmb τ, a₀⟩)) : DualNumber K)
        (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ ub p.1 p.2) (fun a ↦ by simp only [Equiv.apply_symm_apply]),
    Fintype.prod_sigma, Finset.prod_eq_single τ]
  · intro σ _ hσ
    refine Finset.prod_eq_one fun k _ ↦ GlobalTheory.SqZero.epsTo_zero_comp ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (htan σ k)) _ ?_ _
    rw [hθ _ _ (by simpa [hcc] using hσ), mul_zero, TrivSqZeroExt.inr_zero]
  · intro hn; exact absurd (Finset.mem_univ _) hn

end GlobalTheory.KSRowsFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue

namespace GlobalTheory.GlueCoverNull

open Set Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.GlueCover
open scoped ENNReal

variable {n : ℕ}

theorem glueMeas_null {X ι : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞)
    {F : Set X} (hF : MeasurableSet F) (h0 : ∀ i, volume ((e i) '' ((e i).source ∩ F)) = 0) :
    glueMeas e ρ F = 0 := by
  have hc : ∀ i, chartMeas (e i) (ρ i) F = 0 := fun i => by
    rw [chartMeas_apply (e i) (ρ i) hF]
    exact setLIntegral_measure_zero _ _ (h0 i)
  have hle : glueMeas e ρ ≤ (glueMeas e ρ).restrict Fᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB]
    calc chartMeas (e i) (ρ i) B ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
          measure_mono fun y hy => by
            by_cases h : y ∈ F
            · exact Or.inr h
            · exact Or.inl ⟨hy, h⟩
      _ ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ) + chartMeas (e i) (ρ i) F := measure_union_le _ _
      _ = chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [hc i, add_zero]
      _ ≤ glueMeas e ρ (B ∩ Fᶜ) :=
          Measure.le_iff'.1 (le_iSup (fun i => chartMeas (e i) (ρ i)) i) _
  have h := Measure.le_iff'.1 hle F
  rw [Measure.restrict_apply hF, inter_compl_self, measure_empty] at h
  exact nonpos_iff_eq_zero.1 h

section Cover

variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}

theorem exists_evenly_covered_closed
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : IsClosed T) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {x : A} (hx : x ∉ T) :
    ∃ W : Set A, IsOpen W ∧ x ∈ W ∧ ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
      glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := by
  classical
  have hfin : ∀ y ∉ T, (m ⁻¹' {y}).Finite := fun y hy => finite_of_encard_eq_coe (hfib y hy)
  have hcard : ∀ y (hy : y ∉ T), (hfin y hy).toFinset.card = d := fun y hy => by
    have h := hfib y hy
    rw [← (hfin y hy).coe_toFinset, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  obtain ⟨U, hU, hUd⟩ := (hfin x hx).t2_separation
  have hFc := hcard x hx
  have hFm : ∀ z, z ∈ (hfin x hx).toFinset ↔ m z = x := fun z => by simp
  generalize (hfin x hx).toFinset = F at hFc hFm
  have hzF : ∀ z ∈ F, m z = x := fun z hz => (hFm z).1 hz
  have hzT : ∀ z ∈ F, m z ∉ T := fun z hz => by rwa [hzF z hz]
  have hsheet : ∀ z, z ∈ F → ∃ M : Set B, M ⊆ U z ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        glueMeas e' ρ' (M ∩ m ⁻¹' Q) = glueMeas e ρ Q := fun z hz =>
    exists_sheet hd hρ hd' hρ' hm (hch z (hzT z hz)) (hU z).2 (hU z).1
  choose! M hMU hMo hzM hMi hMQ using hsheet
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ Tᶜ, (isOpen_biInter_finset hMi).inter hT.isOpen_compl,
    ⟨mem_iInter₂.2 fun z hz => ⟨z, hzM z hz, hzF z hz⟩, hx⟩, fun Q hQ hQW => ?_⟩
  have hdisj : ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ → Disjoint (M z₁) (M z₂) := fun z₁ h₁ z₂ h₂ hne =>
    Disjoint.mono (hMU z₁ h₁) (hMU z₂ h₂) (hUd (hzF z₁ h₁) (hzF z₂ h₂) hne)
  have key : m ⁻¹' Q = ⋃ z ∈ F, (M z ∩ m ⁻¹' Q) := by
    ext w
    constructor
    · intro hw
      have hWx := hQW hw
      have hpre : ∀ z ∈ F, ∃ z', z' ∈ M z ∧ m z' = m w := fun z hz => by
        obtain ⟨z', h₁, h₂⟩ := mem_iInter₂.1 hWx.1 z hz
        exact ⟨z', h₁, h₂⟩
      haveI : Nonempty B := ⟨w⟩
      choose! f hfM hfm using hpre
      have hinj : InjOn f F := fun z₁ h₁ z₂ h₂ h12 => by
        by_contra hne
        exact disjoint_left.1 (hdisj z₁ h₁ z₂ h₂ hne) (hfM z₁ h₁) (h12 ▸ hfM z₂ h₂)
      have hsub : F.image f ⊆ (hfin (m w) hWx.2).toFinset := fun v hv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
        simpa using hfm z hz
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hinj, hcard _ hWx.2, hFc])
      have hwm : w ∈ F.image f := by
        rw [heq]
        simp
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hwm
      exact mem_iUnion₂.2 ⟨z, hz, hzw ▸ hfM z hz, hw⟩
    · intro hw
      obtain ⟨z, _, _, h⟩ := mem_iUnion₂.1 hw
      exact h
  rw [key, measure_biUnion_finset
    (fun z₁ h₁ z₂ h₂ hne => Disjoint.mono inter_subset_left inter_subset_left
      (hdisj z₁ h₁ z₂ h₂ hne))
    (fun z hz => (hMo z hz).measurableSet.inter (hm.measurable hQ)),
    Finset.sum_congr rfl fun z hz => hMQ z hz Q hQ
      fun y hy => mem_iInter₂.1 (hQW hy).1 z hz,
    Finset.sum_const, nsmul_eq_mul, hFc]

theorem map_glueMeas_closed
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : IsClosed T)
    (hT0 : ∀ i, volume ((e i) '' ((e i).source ∩ T)) = 0)
    (hT0' : ∀ j, volume ((e' j) '' ((e' j).source ∩ m ⁻¹' T)) = 0) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) :
    Measure.map m (glueMeas e' ρ') = (d : ℝ≥0∞) • glueMeas e ρ := by
  have hW : ∀ x : {x // x ∉ T}, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered_closed hd hρ hd' hρ' hm hT hfib hch x.2
  choose W hWo hxW hWQ using hW
  obtain ⟨C, hC, hCW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  haveI : Countable C := hC.to_subtype
  refine Measure.ext_of_iUnion_eq_univ
    (s := fun o : Option C => o.elim T fun c => W c.1) ?_ fun o => ?_
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ T
    · exact mem_iUnion.2 ⟨none, hx⟩
    · have hmem : x ∈ ⋃ i ∈ C, W i := by
        rw [hCW]
        exact mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hmem
      exact mem_iUnion.2 ⟨some ⟨c, hc⟩, hxc⟩
  · cases o with
    | none =>
      show (Measure.map m (glueMeas e' ρ')).restrict T = ((d : ℝ≥0∞) • glueMeas e ρ).restrict T
      rw [Measure.restrict_eq_zero.2, Measure.restrict_eq_zero.2]
      · simp [glueMeas_null e ρ hT.measurableSet hT0]
      · rw [Measure.map_apply hm.measurable hT.measurableSet]
        exact glueMeas_null e' ρ' (hT.preimage hm).measurableSet hT0'
    | some c =>
      show (Measure.map m (glueMeas e' ρ')).restrict (W c.1) =
        ((d : ℝ≥0∞) • glueMeas e ρ).restrict (W c.1)
      ext Q hQ
      have hQW := hQ.inter (hWo c.1).measurableSet
      rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ,
        Measure.map_apply hm.measurable hQW, hWQ c.1 _ hQW inter_subset_right]
      simp

end Cover

theorem map_glueMeas_of_cover : ∀ (n : ℕ) (A B ι κ : Type) [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ENNReal) (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ENNReal), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) → (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source → ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) → ∀ (m : B → A), Continuous m → ∀ T : Set A, IsClosed T → (∀ i, MeasureTheory.volume ((e i) '' ((e i).source ∩ T)) = 0) → (∀ j, MeasureTheory.volume ((e' j) '' ((e' j).source ∩ m ⁻¹' T)) = 0) → ∀ d : ℕ, (∀ x ∉ T, (m ⁻¹' {x}).encard = d) → (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source, m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) → MeasureTheory.Measure.map m (GlobalTheory.ChartGlue.glueMeas e' ρ') = (d : ENNReal) • GlobalTheory.ChartGlue.glueMeas e ρ := by
  intro n A B ι κ _ _ _ _ _ _ _ _ _ _ e ρ e' ρ' hd hρ hd' hρ' m hm T hT hT0 hT0' d hfib hch
  exact map_glueMeas_closed hd hρ hd' hρ' hm hT hT0 hT0' hfib hch

end GlobalTheory.GlueCoverNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamTrivOfMemKL
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lam_triv_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → ∀ (T : Over S) (x : T ⟶ A), GlobalTheory.MemKL A L x → Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) := by
  intro S A _ hA L hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (fst A T) (snd A T ≫ x))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (fst A T) (snd A T ≫ x)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd A T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hA T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, e, lift_fst, lift_snd_assoc, Category.id_comp, lam_one_left]
  · intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    obtain ⟨W, hW, hw⟩ := exists_pull_eq_zero
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
    refine ⟨V ⊓ W, ⟨hV, hW⟩, ?_⟩
    let U := (snd A T).left ⁻¹ᵁ (V ⊓ W)
    let Y : Over S := Over.mk (U.ι ≫ (A ⊗ T).hom)
    let i : Y ⟶ A ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, e]
    have ht : ∀ z, (i ≫ snd A T).left z ∈ V := fun z ↦ z.2.1
    have h1 := pull_mul_eq hL hTV (i ≫ snd A T) ht (i ≫ fst A T)
    have h2 : CechPic.pull (i ≫ snd A T).left
        (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) = 0 :=
      pull_eq_zero_of_mem W (i ≫ snd A T).left (fun z ↦ z.2.2) hw
    rw [map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      Category.assoc] at h2
    rw [lam, mul_comm (i ≫ fst A T), ← Category.assoc i (snd A T) x, h1, Category.assoc, sub_self, zero_sub,
      neg_add_eq_zero]
    exact (sub_eq_zero.1 h2)

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVacuumEqSmulIndicatorSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

theorem vacuum_eq_smul_indicator : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ))
      (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)) (c : ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧ ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ φ₀ h0 hne hfix huniq
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.LinBarExist.exists_isLinBar Bs Γ X om om' hTr
  have hfSB : ι φ₀ ∈ GlobalTheory.WeilM.SB _ := hι.bij.mapsTo h0
  have hf0 : ι φ₀ ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn h0 (zero_mem _) ?_
    rw [h, map_zero]
  have hinv : ∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, ι φ₀ (Y + s) = ι φ₀ Y := by
    rintro _ ⟨u, hu, hu0, rfl⟩ Y
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hA := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inl hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hA
    exact (hι.trans u hat hu0 φ₀ h0 φ₀ h0 hA Y).symm
  have hsupp : ∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, ι φ₀ Y = 0 := by
    intro Y hY
    simp only [GlobalTheory.VacShape.Bd, Set.mem_setOf_eq, not_forall] at hY
    obtain ⟨x, hx, hx0, rfl, u, hu, hu0, hne1⟩ := hY
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hB := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inr hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hB
    have hm := hι.mult u hat hu0 φ₀ h0 φ₀ h0 hB x hx hx0
    by_contra h
    exact hne1 ((mul_eq_right₀ h).mp hm.symm)
  obtain ⟨c, hc, hop, hcp⟩ := _root_.GlobalTheory.SBClosure.main Bs.v₁ _ _ (_root_.GlobalTheory.VacShapeBd.bd_sub Bs Γ X om om' hTr L₁ L₂) (ι φ₀) hfSB hf0 hinv hsupp
    (GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq)
  obtain ⟨P, Λ, hPΛ⟩ := _root_.GlobalTheory.VacShapeCl.closure_Sa_eq_matLat Bs Γ X om om' hTr L₁ L₂ hop hcp
  refine ⟨ι, P, Λ, c, hι, fun Y => ?_⟩
  have hY := congrFun hc Y
  rw [Pi.smul_apply, smul_eq_mul] at hY
  rw [hY]
  congr 1
  by_cases h : Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set _)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show P.val * Y ∈ (matLat (Fin a') Λ : Set _) from (hPΛ Y).1 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show P.val * Y ∉ (matLat (Fin a') Λ : Set _) from fun h' => h ((hPΛ Y).2 h'))]

end GlobalTheory.VacShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismIntegralMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

theorem exists_isGrpPullback_extend : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X' V : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → ∀ (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ] (σ : V ⟶ V) (σ' : X' ⟶ X'), σ ≫ ℓ = ℓ ≫ σ' → ∀ (G' : Over X') [GrpObj G'], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' → ∀ (A : Over V) [GrpObj A] (κ : A.left ⟶ G'.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A G' ℓ κ → ∀ ν : A.left ⟶ A.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A σ ν → ∃ M : G'.left ⟶ G'.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G' σ' M ∧ κ ≫ M = ν ≫ κ := by
  intro hext X' V _ hS ℓ _ _ σ σ' hσ G' _ hG A _ κ hκ ν hν
  have hGσ : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian ((Over.pullback σ').obj G') := IsSemiAbelian.pullback _ _ hG
  have h1 : IsGrpPullback A G' (ℓ ≫ σ') (ν ≫ κ) := (hν.comp hκ).congr hσ rfl
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor σ' ℓ h1
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  obtain ⟨e, ⟨he, he'⟩, -⟩ := hext.existsUnique_iso_of_isGrpPullback hS hG hGσ hκ h2 (Iso.refl A)
  haveI := he
  refine ⟨e.hom.left ≫ pullback.fst _ _, ?_, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' σ')).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, ← he']
    exact pullback.lift_fst _ _ _

theorem eq_of_comp_eq_of_isGrpPullback {X' V : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X']
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ]
    (G' : Over X') [GrpObj G'] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G') (A : Over V) [GrpObj A]
    (κ : A.left ⟶ G'.left) (hκ : IsGrpPullback A G' ℓ κ) (f g : G'.left ⟶ G'.left)
    (h : f ≫ G'.hom = g ≫ G'.hom) (hfg : κ ≫ f = κ ≫ g) : f = g := by
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS ℓ
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G' hG
  have : IsSchemeTheoreticallyDominant κ := .of_isPullback hκ.1.flip
  exact GlobalTheory.ExtUnique.hom_ext_of_dominant G'.hom h κ hfg

end GlobalTheory.EqvAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeBijectiveLinearEquivSquareUniv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' h
  have hsq : ∀ x : R' ⊗[R] M, e' (liftSemi f x) = liftSemi g (e.lTensor R' x) := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, h]
  have hb : Function.Bijective (e.lTensor R') := by
    have := (TensorProduct.congr (LinearEquiv.refl R R') (LinearEquiv.ofBijective e he)).bijective
    convert this using 1
    funext x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => rfl
  have hcomp : (⇑e') ∘ (⇑(liftSemi f)) = (⇑(liftSemi g)) ∘ (⇑(e.lTensor R')) := funext hsq
  constructor
  · intro hf
    have h1 : Function.Bijective ((⇑e') ∘ (⇑(liftSemi f))) := he'.comp hf
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff _ hb).mp h1
  · intro hg
    have h1 : Function.Bijective ((⇑(liftSemi g)) ∘ (⇑(e.lTensor R'))) := hg.comp hb
    rw [← hcomp] at h1
    exact (Function.Bijective.of_comp_iff' he' _).mp h1

end GlobalTheory.BaseChangeIso
end

