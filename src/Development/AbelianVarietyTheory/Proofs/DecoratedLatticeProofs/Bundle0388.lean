module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarFiniteOnCompacts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR
namespace RDecomp

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem blocks_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃ x : GL n k, r.val.toBlocks₁₁ = x.val ∧ (r⁻¹).val.toBlocks₁₁ = (x⁻¹).val := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  refine ⟨x, GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu, ?_⟩
  have e : (embX c x * u)⁻¹ = embX c x⁻¹ * (embX c x * u⁻¹ * (embX c x)⁻¹) := by
    rw [map_inv]; group
  rw [e]
  exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x⁻¹ (GlobalTheory.RootEx.Radical.conj_mem x (inv_mem hu))

def gpart (r : R k n c p) : GL n k :=
  ⟨(r : GL (n ⊕ Fin c) k).val.toBlocks₁₁, ((r : GL (n ⊕ Fin c) k)⁻¹).val.toBlocks₁₁,
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.mul_inv],
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.inv_mul]⟩

theorem gpart_prodR (q : GL n k × N k n c p) : gpart (prodR p q) = q.1 :=
  Units.ext (GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul q.1 q.2.2)

theorem mem_N_of_mem_R (r : R k n c p) : (embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k) ∈ N k n c p := by
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R r.2
  have : gpart r = x := Units.ext (by
    change (r : GL (n ⊕ Fin c) k).val.toBlocks₁₁ = _
    rw [e]; exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu)
  rw [this, e, inv_mul_cancel_left]
  exact hu

def upart (r : R k n c p) : N k n c p := ⟨(embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k), mem_N_of_mem_R r⟩

end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_gpart (p : ℕ) : Continuous (gpart (k := k) (n := n) (c := c) (p := p)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp continuous_subtype_val
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp (continuous_subtype_val.inv)

def prodRHomeo (p : ℕ) : GL n k × N k n c p ≃ₜ R k n c p where
  toFun := prodR p
  invFun r := (gpart r, upart r)
  left_inv q := by
    have h := gpart_prodR (c := c) q
    refine Prod.ext h (Subtype.ext ?_)
    change (embX c (gpart (prodR p q)))⁻¹ * (embX c q.1 * (q.2 : GL (n ⊕ Fin c) k)) = _
    rw [h, inv_mul_cancel_left]
  right_inv r := Subtype.ext (by
    change embX c (gpart r) * ((embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k)) = _
    rw [mul_inv_cancel_left])
  continuous_toFun := Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun := (continuous_gpart p).prodMk (Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_gpart p)).inv.mul continuous_subtype_val) _)

end

end RDecomp
open RDecomp

theorem finite_r : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts ((m.prod (volN ν n c p)).map (prodR p)) := by
  intro k _ _ _ _ _ _ n _ _ c p _ _ ν hν m hm
  haveI := hν
  haveI := hm
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL n k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : (volN ν n c p).IsHaarMeasure := GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν p
  haveI : LocallyCompactSpace (N k n c p) := (GlobalTheory.RootEx.VolN.isClosed_N p).locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  have e : ⇑(prodRHomeo (k := k) (n := n) (c := c) p) = prodR p := rfl
  rw [← e]
  exact Measure.IsFiniteMeasureOnCompacts.map _ (prodRHomeo p)

end GlobalTheory.HaarR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarIsMulLeftInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

theorem GlobalTheory.HaarR.map_prodR_isMulLeftInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → ((m.prod (volN ν n c p)).map (prodR p)).IsMulLeftInvariant := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hp ν hν m hm
  haveI := hν
  haveI := hm
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  obtain ⟨hNc, -, hH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c p h1 hp ν
  haveI := hH
  haveI : LocallyCompactSpace (N k n c p) := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite m := inferInstance
  haveI : SigmaFinite (volN ν n c p) := inferInstance
  have hE : Continuous (embX c : GL n k → GL (n ⊕ Fin c) k) := GlobalTheory.RootEx.QuotStep.continuous_embX
  have hφ : Measurable (prodR (k := k) (n := n) (c := c) p) :=
    (Continuous.subtype_mk ((hE.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _).measurable
  have hmulJ : ∀ g : R k n c p, Measurable (fun y : R k n c p => g * y) :=
    fun g => (continuous_const_mul g).measurable
  have hmulH : ∀ g : GL n k, Measurable (fun y : GL n k => g * y) := fun g => (continuous_const_mul g).measurable
  let μR : Measure (R k n c p) := (m.prod (volN ν n c p)).map (prodR p)
  let K : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {x | ∃ hx : x ∈ R k n c p,
        μR.map (fun y => (⟨x, hx⟩ : R k n c p) * y) = μR}
      one_mem' := ⟨one_mem _, by
        simp only [show (⟨1, one_mem _⟩ : R k n c p) = 1 from rfl, one_mul]
        exact Measure.map_id'⟩
      mul_mem' := by
        rintro a b ⟨ha, Ha⟩ ⟨hb, Hb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have : (fun y : R k n c p => (⟨a * b, mul_mem ha hb⟩ : R k n c p) * y)
            = (fun y => (⟨a, ha⟩ : R k n c p) * y) ∘ (fun y => (⟨b, hb⟩ : R k n c p) * y) :=
          funext fun y => mul_assoc (⟨a, ha⟩ : R k n c p) ⟨b, hb⟩ y
        rw [this, ← Measure.map_map (hmulJ _) (hmulJ _), Hb, Ha]
      inv_mem' := by
        rintro a ⟨ha, Ha⟩
        refine ⟨inv_mem ha, ?_⟩
        conv_lhs => rw [← Ha]
        rw [Measure.map_map (hmulJ _) (hmulJ _)]
        have : (fun y : R k n c p => (⟨a⁻¹, inv_mem ha⟩ : R k n c p) * y) ∘
            (fun y => (⟨a, ha⟩ : R k n c p) * y) = id :=
          funext fun y => inv_mul_cancel_left (⟨a, ha⟩ : R k n c p) y
        rw [this, Measure.map_id] }
  have hXK : (embX c : GL n k →* GL (n ⊕ Fin c) k).range ≤ K := by
    rintro _ ⟨g₀, rfl⟩
    refine ⟨Subgroup.mem_sup_left ⟨g₀, rfl⟩, ?_⟩
    show Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map (hmulJ _) hφ]
    have : (fun y : R k n c p => (⟨embX c g₀, Subgroup.mem_sup_left ⟨g₀, rfl⟩⟩ : R k n c p) * y) ∘ prodR p
        = prodR p ∘ Prod.map (fun y : GL n k => g₀ * y) id := by
      funext q; apply Subtype.ext; simp [mul_assoc]
    rw [this, ← Measure.map_map hφ ((hmulH _).prodMap measurable_id),
      ← Measure.map_prod_map m (volN ν n c p) (hmulH _) measurable_id, map_mul_left_eq_self, Measure.map_id]
  have hNK : N k n c p ≤ K := by
    intro u₀ hu₀
    refine ⟨Subgroup.mem_sup_right hu₀, ?_⟩
    show Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map (hmulJ _) hφ]
    let cg : GL n k → N k n c p := fun g => ⟨(embX c g)⁻¹ * u₀ * embX c g, GlobalTheory.RootEx.Model.conj_mem hu₀ g⟩
    have hcg : Continuous cg :=
      Continuous.subtype_mk (((hE.inv).mul continuous_const).mul hE) _
    let F : GL n k → N k n c p → N k n c p := fun g u => cg g * u
    have hF : Measurable (Function.uncurry F) :=
      (((hcg.comp continuous_fst).mul continuous_snd)).measurable
    have hFm : ∀ g, Measure.map (F g) (volN ν n c p) = volN ν n c p := fun g => map_mul_left_eq_self _ _
    have hmp := (MeasurePreserving.id m).skew_product hF (Filter.Eventually.of_forall hFm)
    have : (fun y : R k n c p => (⟨u₀, Subgroup.mem_sup_right hu₀⟩ : R k n c p) * y) ∘ prodR p
        = prodR p ∘ (fun q : GL n k × N k n c p => (id q.1, F q.1 q.2)) := by
      funext q; apply Subtype.ext; simp [F, cg, mul_assoc]
    rw [this, ← Measure.map_map hφ hmp.measurable, hmp.map_eq]
  refine ⟨fun g => ?_⟩
  obtain ⟨hx, H⟩ := (sup_le hXK hNK) g.2
  exact H
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapToFourierJacobiPreimageIntegralGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarFJInt

open GlobalTheory.RootEx.Radical

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (c ρ : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * ρ + 1) (fun i => 2 * (i.val + 1))

theorem uni_of_mem_N {ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c (ρ + 1)) :
    Uni (midLev c ρ) u.val := by
  rw [mem_N_iff] at hu
  intro r s hrs
  refine hu r s ?_
  rcases r with r | r <;> rcases s with s | s <;> simp only [midLev, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

theorem uni_colE (ρ : ℕ) (β : n → k) : Uni (midLev c ρ) (colE c (ρ + 1) β).val := by
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [colE, upU, Matrix.one_apply]
  · simp only [midLev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : s.val ≠ ρ := by omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem uni_inl_inl {ρ : ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Uni (midLev c ρ) M) (i j : n) :
    M (Sum.inl i) (Sum.inl j) = (1 : Matrix n n k) i j := by
  rw [h _ _ (by simp [midLev])]
  simp [Matrix.one_apply]

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  have one_int : ∀ (i j : Fin c), (1 : Matrix (Fin c) (Fin c) k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.1 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j
  · rw [← map_inv, embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.2 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j

theorem colE_mem_KO (p : ℕ) {β : n → k} (hβ : ∀ i, β i ∈ 𝒪[k]) : colE c p β ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  have one_int : ∀ {m : Type} [DecidableEq m] (i j : m), (1 : Matrix m m k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · simp only [colE, upU, fromBlocks_apply₁₂, Matrix.of_apply]
      split_ifs
      · exact hβ i
      · exact zero_mem _
    · simp only [colE, upU, fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · exact one_int i j
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
      split_ifs
      · exact neg_mem (hβ i)
      · rw [neg_zero]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₂]; exact one_int i j

theorem embX_mul_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (embX c g * w).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem mul_embX_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (w * embX c g).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem col_eq {ρ : ℕ} (hρ : ρ < c) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1)) (β : n → k) (t : n) :
    (u * colE c (ρ + 1) β).val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = β t := by
  have h1 := uni_inl_inl (uni_of_mem_N hu)
  have h0 : u.val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = 0 := by
    rw [mem_N_iff] at hu
    rw [hu _ _ (by simp [lev])]
    simp
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [colE, upU, h1, Matrix.one_apply, h0]

theorem mem_KO_iff_prod {ρ : ℕ} (hρ : ρ < c) (g : GL n k) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1))
    (β : n → k) :
    embX c g * u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) ↔
      g ∈ KO k n ∧ u ∈ KO k (n ⊕ Fin c) ∧ ∀ i, β i ∈ 𝒪[k] := by
  constructor
  · intro hr
    have hw : Uni (midLev c ρ) (u * colE c (ρ + 1) β).val :=
      Uni.mul (uni_of_mem_N hu) (uni_colE ρ β)
    have hwi : Uni (midLev c ρ) ((u * colE c (ρ + 1) β)⁻¹).val := Uni.inv hw
    have hr' := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hr
    have hg : g ∈ KO k n := by
      rw [GlobalTheory.SplitFlip.mem_KO_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have := hr'.1 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, embX_mul_inl g _ hw] at this
      · have := hr'.2 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, _root_.mul_inv_rev, ← map_inv, mul_embX_inl g⁻¹ _ hwi] at this
    have hwK : u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) := by
      have := mul_mem (inv_mem (embX_mem_KO (c := c) hg)) hr
      rwa [mul_assoc, inv_mul_cancel_left] at this
    have hβ : ∀ i, β i ∈ 𝒪[k] := fun i => by
      have := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hwK).1 (Sum.inl i) (Sum.inr ⟨ρ, hρ⟩)
      rwa [col_eq hρ u hu β i] at this
    refine ⟨hg, ?_, hβ⟩
    have := mul_mem hwK (inv_mem (colE_mem_KO (c := c) (ρ + 1) hβ))
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨hg, huK, hβ⟩
    exact mul_mem (mul_mem (embX_mem_KO hg) huK) (colE_mem_KO _ hβ)

end GlobalTheory.HaarFJInt

open GlobalTheory.HaarFJInt in
theorem GlobalTheory.HaarFJInt.prodRFJ_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), ρ < c → prodRFJ (k := k) (n := n) (c := c) ρ ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = ((KO k n : Set (GL n k)) ×ˢ {u : N k n c (ρ + 1) | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)}) ×ˢ {β : n → k | ∀ i, β i ∈ 𝒪[k]} := by
  intro k _ _ _ _ n _ _ c ρ hρ
  ext ⟨⟨g, u⟩, β⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodRFJ_coe, Set.mem_prod, SetLike.mem_coe]
  rw [mem_KO_iff_prod hρ g u u.2 β, and_assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContrLocProof
open GlobalTheory.ContractionLocal

theorem contrLoc : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  have hH := _root_.GlobalTheory.Unf.ContrHeis.contr_heisO
  have hC := _root_.GlobalTheory.LineRowFrame.line_row
  have hD := _root_.GlobalTheory.ContrFrameCol.frame_col
  have hL := _root_.GlobalTheory.ContrModL.contr_isModel
  have hR := _root_.GlobalTheory.ContrModR.contr_isModel
  intro D hCF k _ _ _ _ _ _ p ν hν ψ hψ ψk hk ρ σ B B' l S vL s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' hF hF' T₁ T₂ hT₁ hT₂
  obtain ⟨-, hψk, -, -, -⟩ := _root_.GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hψkc, hψk1⟩ := hψk ψk hk
  let Bm := contrBil hψ l S vL T₁ T₂ hT₁.theta hT₂.theta
  have inv1 : ∀ (u₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = (ψk (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) * Ψ₁.1 x) →
      (∀ x, Ψ₂'.1 x = Ψ₂.1 (x + fromRows 0 (Matrix.of fun _ => u₀))) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro u₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hC D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' u₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) :=
      hT₁.modul _ hx2 Ψ₁ Ψ₁' fun t => by rw [h1, hx3]
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) := by
      rw [← hx1]; exact hT₂.trans _ Ψ₂ Ψ₂' h2
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  have inv2 : ∀ (y₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = Ψ₁.1 (x + fromCols 0 (Matrix.of fun r _ => y₀ r))) →
      (∀ x, Ψ₂'.1 x = (ψk (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) * Ψ₂.1 x) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro y₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hD D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' y₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) := by
      rw [← hx1]; exact hT₁.trans _ Ψ₁ Ψ₁' h1
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) :=
      hT₂.modul _ hx2 Ψ₂ Ψ₂' fun t => by rw [h2, hx3]
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  obtain ⟨Λ, hΛ⟩ := hCF k ψk ν hψkc hψk1 hν n n' n'' (WO B.A S → WO S B'.A → ℂ) Bm inv1 inv2
  obtain ⟨φ₀, φ₀', hφ⟩ := exists_normPair ψk ν hψkc hν n
  have hval : ∀ Ξ₁ Ξ₂ (Ξ : SB (Matrix n n' k × Matrix n'' n k)), (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) →
      Λ Ξ = Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) := by
    intro Ξ₁ Ξ₂ Ξ hq
    obtain ⟨Ξ', hΞ'1, hΞ'2⟩ := hΛ (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂)
    have : Ξ' = Ξ := Subtype.ext (funext fun q => by rw [hΞ'1, contr_tens, hφ, mul_one, hq])
    rw [← this, hΞ'2]
  refine ⟨Λ, ⟨fun Ξ₂ v => ?_, fun Ξ₁ u => ?_⟩, hΛ⟩
  · let T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
      { toFun := fun Ξ₁ u => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext u; simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
        map_smul' := fun c a => by funext u; simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hL D k p ψ hψ ρ σ B B' l S vL s hs n n' FA F₀ FS hF T₁ hT₁ φ₀ _ (hT₂.theta _) v T fun Ξ₁ u => rfl,
      fun Ξ₁ Ξ hq u => ?_⟩
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
  · let T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ) :=
      { toFun := fun Ξ₂ v => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext v; simp only [map_add (f := _), Pi.add_apply]
        map_smul' := fun c a => by funext v; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hR D k p ψ hψ ρ σ B B' l S vL (s * p.xi) ?_ n n'' FS FA' F₀' hF' T₂ hT₂ φ₀' _ (hT₁.theta _) u T
      fun Ξ₂ v => rfl, fun Ξ₂ Ξ hq v => ?_⟩
    · obtain ⟨-, -, hxi, -, -⟩ := _root_.GlobalTheory.LocChar.weil_char_split D k p ψ hψ
      exact mul_ne_zero hs hxi
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
end GlobalTheory.ContrLocProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapWittEmbeddingZeroRankIsHaarMeasure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HaarEmb

theorem map_wittEmbedding_zero_rank_isHaarMeasure : ∀ (D : D7) (S S₀ : HSp D) (d : HypDec S S₀ 0) (μ : Measure (GA D S₀)), μ.IsHaarMeasure → (Measure.map d.emb0 μ).IsHaarMeasure := by
  intro D S S₀ d μ hμ
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (GA D S₀) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D S₀) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hbkc : Continuous (GlobalTheory.WeilSrc.Zero.back d) := continuous_of_mt S₀ (by
    simp only [GlobalTheory.WeilSrc.Zero.back, mt_ofMat]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)
  have hli : ∀ g, GlobalTheory.WeilSrc.Zero.back d (d.emb0 g) = g := fun g =>
    d.wittDecomp_anisotropicEmbedding_injective (GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d _)
  let e : GA D S₀ ≃* GA D S :=
    { toFun := d.emb0, invFun := GlobalTheory.WeilSrc.Zero.back d, left_inv := hli,
      right_inv := GlobalTheory.WeilSrc.Zero.witt_decomposition_zero_embedding_left_inverse d, map_mul' := fun x y => map_mul d.emb0 x y }
  exact MulEquiv.isHaarMeasure_map μ e d.continuous_embed hbkc

end GlobalTheory.HaarEmb
end
end

