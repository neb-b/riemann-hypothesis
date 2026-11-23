module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProduct
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CommProd

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def mulEquiv (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) : (B × A) ≃ₜ* G where
  toFun p := (p.1 : G) * p.2
  invFun g := ((e.symm g).2, (e.symm g).1)
  left_inv p := by
    have : e.symm ((p.1 : G) * p.2) = (p.2, p.1) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ p.2.2 _ p.1.2]
    simp [this]
  right_inv g := by
    change ((e.symm g).2 : G) * (e.symm g).1 = g
    rw [← hc _ (e.symm g).1.2 _ (e.symm g).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    change ((p.1 * q.1 : B) : G) * ((p.2 * q.2 : A) : G) = ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (p.2 : G), hc _ p.2.2 _ q.1.2]
    simp only [mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (e.symm.continuous.snd).prodMk (e.symm.continuous.fst)

@[simp] theorem mulEquiv_apply (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (p : B × A) : mulEquiv A B hc e he p = (p.1 : G) * p.2 := rfl

def mulEquivSub (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    (R.subgroupOf B × R.subgroupOf A) ≃ₜ* R where
  toFun p := ⟨((p.1 : B) : G) * ((p.2 : A) : G), R.mul_mem (Subgroup.mem_subgroupOf.1 p.1.2) (Subgroup.mem_subgroupOf.1 p.2.2)⟩
  invFun r :=
    have h := hR _ (e.symm r).1.2 _ (e.symm r).2.2 (by rw [← he, e.apply_symm_apply]; exact r.2)
    (⟨(e.symm r).2, Subgroup.mem_subgroupOf.2 h.2⟩, ⟨(e.symm r).1, Subgroup.mem_subgroupOf.2 h.1⟩)
  left_inv p := by
    have : e.symm (((p.1 : B) : G) * ((p.2 : A) : G)) = ((p.2 : A), (p.1 : B)) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ (p.2 : A).2 _ (p.1 : B).2]
    ext <;> simp [this]
  right_inv r := by
    apply Subtype.ext
    change ((e.symm r).2 : G) * (e.symm r).1 = r
    rw [← hc _ (e.symm r).1.2 _ (e.symm r).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    apply Subtype.ext
    change (((p.1 * q.1 : R.subgroupOf B) : B) : G) * (((p.2 * q.2 : R.subgroupOf A) : A) : G) =
      (((p.1 : B) : G) * ((p.2 : A) : G)) * (((q.1 : B) : G) * ((q.2 : A) : G))
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc ((p.2 : A) : G), hc _ (p.2 : A).2 _ (q.1 : B).2]
    simp only [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hs : Continuous fun r : R => e.symm r := e.symm.continuous.comp continuous_subtype_val
    exact ((hs.snd).subtype_mk _).prodMk ((hs.fst).subtype_mk _)

@[simp] theorem mulEquivSub_apply (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (p : R.subgroupOf B × R.subgroupOf A) :
    (mulEquivSub A B R hc e he hR p : G) = ((p.1 : B) : G) * ((p.2 : A) : G) := rfl

end GlobalTheory.CommProd

namespace GlobalTheory.CommProd

theorem invInv : ∀ {X Y H : Type} [Group X] [Group Y] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace H] [IsTopologicalGroup X] [IsTopologicalGroup Y] [IsTopologicalGroup H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace H] [BorelSpace X] [BorelSpace Y] [BorelSpace H] [LocallyCompactSpace X]
    [LocallyCompactSpace Y] [LocallyCompactSpace H] [SecondCountableTopology X] [SecondCountableTopology Y]
    [SecondCountableTopology H] (e : (Y × X) ≃ₜ* H) (ρ : Measure Y) (ν : Measure X) (μH : Measure H),
    ρ.IsHaarMeasure → ρ.IsInvInvariant → ν.IsHaarMeasure → μH.IsInvInvariant → (ρ.prod ν).map e = μH →
    ν.IsInvInvariant := by
  intro X Y H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e ρ ν μH _ _ _ _ h
  have he : Measurable e := e.continuous.measurable
  have h1 : (ρ.prod ν.inv).map e = μH := by
    have hp : ρ.prod ν.inv = (ρ.prod ν).map (fun p => p⁻¹) := by
      rw [show (fun p : Y × X => p⁻¹) = Prod.map (·⁻¹) (·⁻¹) from rfl,
        ← Measure.map_prod_map _ _ measurable_inv measurable_inv]
      change ρ.prod ν.inv = ρ.inv.prod ν.inv
      rw [Measure.inv_eq_self ρ]
    have hc : (e ∘ fun p : Y × X => p⁻¹) = (fun q : H => q⁻¹) ∘ e := funext fun p => map_inv e p
    rw [hp, Measure.map_map he measurable_inv, hc, ← Measure.map_map measurable_inv he, h]
    exact Measure.inv_eq_self μH
  have h2 : ρ.prod ν.inv = ρ.prod ν := by
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : (E : Y × X → H) = e := rfl
    rw [← E.map_symm_map (μ := ρ.prod ν.inv), ← E.map_symm_map (μ := ρ.prod ν), hE, h1, h]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : Y)
  have hK0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := ρ) hK1).ne'
  have hKt : ρ K ≠ ⊤ := hK.measure_lt_top.ne
  refine ⟨Measure.ext fun S hS => ?_⟩
  have := congrArg (fun m : Measure (Y × X) => m (K ×ˢ S)) h2
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_right_inj hK0 hKt).1 this

theorem cutProd : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G) (he : ∀ p, e p = p.1 * p.2)
    (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (μR : Measure R) (ρ : Measure (R.subgroupOf B))
    (ν : Measure (R.subgroupOf A)) (βB : B → NNReal) (βA : A → NNReal), SFinite ρ → SFinite ν →
    (ρ.prod ν).map (mulEquivSub A B R hc e he hR) = μR →
    GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf B) ρ βB → GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf A) ν βA →
    GlobalTheory.Tw.IsCosetCutoff R μR (fun g => βB (e.symm g).2 * βA (e.symm g).1) := by
  intro G _ _ _ _ _ _ _ _ A B R hc e he hR μR ρ ν βB βA _ _ hm hB hA
  have hs : Measurable fun g : G => e.symm g := e.symm.continuous.measurable
  have hmeas : Measurable fun g : G => βB (e.symm g).2 * βA (e.symm g).1 :=
    (hB.1.comp (measurable_snd.comp hs)).mul (hA.1.comp (measurable_fst.comp hs))
  refine ⟨hmeas, fun x => ?_⟩
  set ψ := mulEquivSub A B R hc e he hR
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hmx : Measurable fun r : R => ((βB (e.symm ((r : G) * x)).2 * βA (e.symm ((r : G) * x)).1 : NNReal) : ℝ≥0∞) :=
    (hmeas.comp (measurable_subtype_coe.mul_const x)).coe_nnreal_ennreal
  rw [← hm, lintegral_map hmx hψ]
  have key : ∀ p : R.subgroupOf B × R.subgroupOf A, e.symm ((ψ p : G) * x) = ((p.2 : A) * (e.symm x).1, (p.1 : B) * (e.symm x).2) := by
    intro p
    rw [Homeomorph.symm_apply_eq, he, mulEquivSub_apply]
    have hx : x = ((e.symm x).1 : G) * (e.symm x).2 := by rw [← he, e.apply_symm_apply]
    have h1 : ((p.1 : B) : G) * ((p.2 : A) : G) = ((p.2 : A) : G) * ((p.1 : B) : G) :=
      (hc _ (p.2 : A).2 _ (p.1 : B).2).symm
    have h2 : ((p.1 : B) : G) * ((e.symm x).1 : G) = ((e.symm x).1 : G) * ((p.1 : B) : G) :=
      (hc _ (e.symm x).1.2 _ (p.1 : B).2).symm
    calc ((p.1 : B) : G) * ((p.2 : A) : G) * x
        = ((p.2 : A) : G) * (((p.1 : B) : G) * ((e.symm x).1 : G)) * (e.symm x).2 := by
          rw [h1]; conv_lhs => rw [hx]
          simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [Subgroup.coe_mul, mul_assoc]
  simp only [key, ENNReal.coe_mul]
  refine (lintegral_prod _ ((hB.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_fst).mul_const _)).mul
    (hA.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_snd).mul_const _))).aemeasurable).trans ?_
  simp only [Pi.mul_apply, Function.comp_apply, lintegral_const_mul' _ _ ENNReal.coe_ne_top, hA.2, mul_one, hB.2]

end GlobalTheory.CommProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CommProd in
theorem GlobalTheory.CommProd.quot_vanish_of_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (R : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → (∃ e : (A × B) ≃ₜ G, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) → ∀ (μR : Measure R) (μG : Measure G) (ρ : Measure (R.subgroupOf B)) (μ : Measure B), μR.IsHaarMeasure → μR.IsInvInvariant → μG.IsHaarMeasure → ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ a ∈ A, IsQuotIntL1 ρ μ (fun b => f (a * b.1)) 0) → z = 0 := by
  intro G _ _ _ _ _ _ _ _ A B R hA hB hR hc ⟨e, he⟩ hdec μR μG ρ μ _ _ _ _ _ _ f z hf hz
  have : LocallyCompactSpace A := hA.locallyCompactSpace
  have : LocallyCompactSpace B := hB.locallyCompactSpace
  have hRA : IsClosed ((R.subgroupOf A : Subgroup A) : Set A) := hR.preimage continuous_subtype_val
  have hRB : IsClosed ((R.subgroupOf B : Subgroup B) : Set B) := hR.preimage continuous_subtype_val
  have : LocallyCompactSpace (R.subgroupOf A) := hRA.locallyCompactSpace
  have : LocallyCompactSpace (R.subgroupOf B) := hRB.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  let φ := mulEquiv A B hc e he
  let ψ := mulEquivSub A B R hc e he hdec
  obtain ⟨μA, hμA, hG⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq φ μ μG
  obtain ⟨ν, hν, hRm⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq ψ ρ μR
  have : ν.IsInvInvariant := invInv ψ ρ ν μR inferInstance inferInstance hν inferInstance hRm
  obtain ⟨βB, -, hβB⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ρ) hRB
  obtain ⟨βA, -, hβA⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ν) hRA
  have hβ := cutProd G A B R hc e he hdec μR ρ ν βB βA inferInstance inferInstance hRm hβB hβA
  obtain ⟨hi, rfl⟩ := hf.cutoff hβ
  have hφs : ∀ p : B × A, e.symm (φ p) = (p.2, p.1) := fun p => by
    rw [Homeomorph.symm_apply_eq, he, mulEquiv_apply, hc _ p.2.2 _ p.1.2]
  have hme : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [← hG] at hi ⊢
  rw [hme.integral_map]
  rw [hme.integrable_map_iff] at hi
  refine (integral_prod_symm _ hi).trans ?_
  have hin : ∀ a : A, ∫ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) ∂μ = 0 := by
    intro a
    obtain ⟨-, h0⟩ := (hz a a.2).cutoff hβB
    have e1 : ∀ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) =
        (βA a : ℝ) • ((βB b : ℝ) • f (a * b)) := fun b => by
      simp only [Function.comp_apply, hφs, mulEquiv_apply, NNReal.coe_mul, smul_smul]
      rw [show φ (b, a) = (b : G) * a from rfl, hc _ a.2 _ b.2, mul_comm (βB b : ℝ)]
    simp only [e1, integral_smul, ← h0, smul_zero]
  exact (integral_congr_ae (Filter.Eventually.of_forall hin)).trans (integral_zero _ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem ginfC_facts (V : HSp D) : IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
    SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ LocallyCompactSpace (GinfC V) ∧
    SecondCountableTopology (GinfC V) ∧ BorelSpace (GinfC V) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  exact ⟨i1, i2, i3, i4, i5, i6.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsInducing.subtypeVal.secondCountableTopology, Subtype.borelSpace _⟩

theorem eq_map_of_lev {V : HSp D} (K : Subgroup (GA D V)) (hK : K ≤ GfC V) (A : Set (GA D V)) (ν : Measure (GA D V))
    (mR : Measure (GinfC V)) (hH : mR.IsHaarMeasure)
    (h : ∀ (f : GinfC V → ℂ) (F : GA D V → ℂ), Integrable f mR → (∀ b : GinfC V, ∀ κ ∈ K, F ((b : GA D V) * κ) = f b) →
      IntegrableOn F A ν ∧ ∫ g in A, F g ∂ν = ∫ b, f b ∂mR) :
    mR = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable

  have hfin : ∀ G : Set (GinfC V), MeasurableSet G → mR G < ⊤ →
      mR G = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) G := by
    intro G hG hGf
    have hS : MeasurableSet (GlobalTheory.AutMult.toInf V ⁻¹' G) := hmeas hG
    have hf : Integrable (G.indicator fun _ => (1 : ℂ)) mR :=
      (integrable_indicator_iff hG).2 ((integrableOn_const_iff (by simp)).2 (Or.inr hGf))
    obtain ⟨hi, he⟩ := h (G.indicator fun _ => (1 : ℂ)) ((GlobalTheory.AutMult.toInf V ⁻¹' G).indicator fun _ => (1 : ℂ)) hf
      (fun b κ hκ => by
        have h1 : GlobalTheory.AutMult.toInf V ((b : GA D V) * κ) = b := by
          rw [map_mul, GlobalTheory.AutMult.toInf_coe, (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V κ).2 (hK hκ), mul_one]
        classical
        rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, h1])
    have hi' : ν.restrict A (GlobalTheory.AutMult.toInf V ⁻¹' G) < ⊤ := by
      have := ((integrable_indicator_iff hS).1 hi)
      rcases (integrableOn_const_iff (by simp)).1 this with h0 | h0
      · simp at h0
      · exact h0
    rw [integral_indicator_const _ hS, integral_indicator_const _ hG] at he
    have he' : (ν.restrict A).real (GlobalTheory.AutMult.toInf V ⁻¹' G) = mR.real G := by
      simpa using he
    rw [Measure.map_apply hmeas hG]
    exact ((ENNReal.toReal_eq_toReal_iff' hGf.ne hi'.ne).1 he'.symm)
  refine Measure.ext fun G hG => ?_
  have hU : ⋃ n, G ∩ spanningSets mR n = G := by rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hmono : Monotone fun n => G ∩ spanningSets mR n := fun a b hab =>
    Set.inter_subset_inter_right _ (monotone_spanningSets mR hab)
  rw [← hU, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => hfin _ (hG.inter (measurableSet_spanningSets mR n)) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top mR n)

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem infMat_toInf (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram φ (GlobalTheory.AutMult.toInf V g : GA D V) = infMat D.sp.cm.sig V.gram φ g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.TensRep.infMat_of_mem_fin V φ (GlobalTheory.AutMult.toFin V g).2, Matrix.mul_one]

theorem eq_of_measLevW {V : HSp D}
    {good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop}
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure)
    {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {ν₁ ν₂ : Measure (GA D V)}
    (h₁ : Lev.IsMeasLevW V K₁ good ν₁) (h₂ : Lev.IsMeasLevW V K₂ good ν₂)
    (m₁ m₂ : Measure (GinfC V)) (hH₁ : m₁.IsHaarMeasure) (hH₂ : m₂.IsHaarMeasure)
    (e₁ : m₁ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₁.restrict {g | Lev.finE V g ∈ K₁}))
    (e₂ : m₂ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₂.restrict {g | Lev.finE V g ∈ K₂})) : m₁ = m₂ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH₁
  haveI := hH₂
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, ⟨θ, hθ⟩, h1⟩ := h₁
  obtain ⟨⟨A, hA⟩, h1⟩ := h1 θ hθ
  obtain ⟨⟨m, hm⟩, h1⟩ := h1 A hA
  obtain ⟨-, -, h2⟩ := h₂
  obtain ⟨-, h2⟩ := h2 θ hθ
  obtain ⟨-, h2⟩ := h2 A hA
  have h2 := h2 m hm
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, infMat_toInf]
  have hval : ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)),
      Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict {g | Lev.finE V g ∈ K}) E =
        ν {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K ν
    rw [Measure.map_apply (GlobalTheory.AutMult.continuous_toInf V).measurable hE, hpre, Measure.restrict_apply hS]
    congr 1
    ext h
    exact and_comm
  have v1 : m₁ E = ∏ ρ, m ρ (B ρ) := by rw [e₁, hval]; exact h1 m hm (fun ρ => B ρ) hB
  have v2 : m₂ E = ∏ ρ, m ρ (B ρ) := by rw [e₂, hval]; exact h2 (fun ρ => B ρ) hB
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  have e : m₂ = ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) • m₁ := Measure.isMulLeftInvariant_eq_smul m₂ m₁
  have e' := v2
  rw [e, Measure.smul_apply, v1, smul_eq_mul] at e'
  have hc : ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (e'.trans (one_mul _).symm)
  rw [e, hc, one_smul]

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

theorem models_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (j : ℕ)
    (hj : j < D.R.m) :
    ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D j).sig (tauE D ρ)).1 ((Yc D j).sig (tauE D ρ)).2) → Prop,
      (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧
      ∀ t, Lev.IsMeasLevW (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) good (R.νY t j) := by
  rcases Nat.lt_or_ge (j + 1) D.R.m with h | h
  · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ hm => hm.1, fun t => (hM.νY t j h).1⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ hm => hm.1, fun t => (hM.νY' t).1⟩

theorem one_real_measure : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RMeas R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR j hj
  by_cases hT : Nonempty T
  swap
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩
  obtain ⟨t₀⟩ := hT
  have hlev : ∀ t, ∃ mR, IsLevMeas (stY R t j) mR := fun t =>
    (_root_.GlobalTheory.ChainTw.LevLoc.levLoc D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) ((hC hR t).2.1 j hj)).2.2.2.2.2
  choose mR hmR using hlev
  obtain ⟨good, hgood, hW⟩ := models_good R hG.core.models j hj
  have hmap : ∀ t, mR t = Measure.map (GlobalTheory.AutMult.toInf (Yc D j))
      ((R.νY t j).restrict {g | Lev.finE (Yc D j) g ∈ lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)}) := fun t => by
    exact eq_map_of_lev (Lev.levG (Yc D j) (R.βY j) (R.datYt t j R.triv)) inf_le_left _ _ (mR t) (hmR t).1 (hmR t).2
  refine ⟨mR t₀, fun t => ?_⟩
  have e : mR t = mR t₀ := by
    exact eq_of_measLevW hgood (hW t) (hW t₀) (mR t) (mR t₀) (hmR t).1 (hmR t₀).1 (hmap t) (hmap t₀)
  rw [← e]
  exact hmR t

end GlobalTheory.RealMeasOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionHasDerivAtRealLineDoubledPai
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchLine

theorem sch_hasDerivAt_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ M : ℝ →+ Mx D B.rank A.rank, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ f', IsThetaFunO ψ (dblSp A) B f' ∧ ∀ x, HasDerivAt (fun t : ℝ => sch ψ A B ν 𝓨 f (x + M t)) (sch ψ A B ν 𝓨 f' x) 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf M hM hMf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let v : GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  let L : ℝ →+ WO (dblSp A) B := ((dblDec A).extX B).comp M
  have hLc : Continuous L := (continuous_id.matrix_mul continuous_const).comp hM
  have hLf : ∀ t, (L t).map (finPart D) = 0 := by
    intro t
    show (((dblDec A).extX B) (M t)).map (finPart D) = 0
    rw [HypDec.extX_apply, Matrix.map_mul, hMf t, Matrix.zero_mul]
  obtain ⟨_, hT⟩ := GlobalTheory.HeisTaylor.heisO_taylor D ψ hψ θ hθ (dblSp A) B 0 f hf
  obtain ⟨hf', hlim⟩ := hT L hLc hLf
  refine ⟨_, hf', fun x => ?_⟩
  set f' := fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (L t) f p) 0 with hf'def
  obtain ⟨C, hC⟩ := GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank (dblDec A) v 0
  have hS := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) v f hf).1
  have hth : ∀ t, IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B (L t) f) := fun t =>
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _
  have lin := GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hν

  have htr : ∀ t : ℝ, sch ψ A B ν 𝓨 f (x + M t) = sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x := by
    intro t
    exact (congrFun (hS x (M t)) 0).symm

  have key : ∀ t : ℝ, IsThetaFunO ψ (dblSp A) B ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') ∧
      sch ψ A B ν 𝓨 ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') x =
        (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) - sch ψ A B ν 𝓨 f' x := by
    intro t
    have e : (t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f' =
        ((t⁻¹ : ℂ) • heisO ψ (dblSp A) B (L t) f + (-(t⁻¹ : ℂ)) • f) + (-1 : ℂ) • f' := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h1 := lin _ _ (hth t) hf (t⁻¹ : ℂ)
    have h2 := lin _ _ hf hf (-(t⁻¹ : ℂ))
    have ha := GlobalTheory.OrientedHeis.theta_smul (t⁻¹ : ℂ) (hth t)
    have hb := GlobalTheory.OrientedHeis.theta_smul (-(t⁻¹ : ℂ)) hf
    have hc := GlobalTheory.OrientedHeis.theta_smul (-1 : ℂ) hf'
    have hab := GlobalTheory.OrientedHeis.theta_add ha hb
    rw [e]
    refine ⟨GlobalTheory.OrientedHeis.theta_add hab hc, ?_⟩
    rw [(lin _ _ hab hc 1).2.2.1, (lin _ _ ha hb 1).2.2.1, (lin _ _ (hth t) hf (t⁻¹ : ℂ)).2.2.2,
      (lin _ _ hf hf (-(t⁻¹ : ℂ))).2.2.2, (lin _ _ hf' hf' (-1 : ℂ)).2.2.2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_edist_tendsto_0]
  have hup : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ 0
      ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f')) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => by simp) (fun t => ?_)
  have hb := hC _ (key t).1 x 0
  rw [pow_zero, ENNReal.ofReal_one, mul_one] at hb
  have e2 : t⁻¹ • (sch ψ A B ν 𝓨 f (x + M (0 + t)) - sch ψ A B ν 𝓨 f (x + M 0)) =
      (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) := by
    rw [zero_add, htr t, map_zero, add_zero, Complex.real_smul, Complex.ofReal_inv]
  simp only
  rw [e2, edist_eq_enorm_sub, ← (key t).2]
  exact hb

end GlobalTheory.SchLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSourceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_commutes_superposition_slices_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  first | exact @GlobalTheory.WeilSuperpos.weil_comm_superpos | exact GlobalTheory.WeilSuperpos.weil_comm_superpos | (intros; apply GlobalTheory.WeilSuperpos.weil_comm_superpos <;> assumption)
end

