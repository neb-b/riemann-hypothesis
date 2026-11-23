module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralVanishOfInnerVanish
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CellVanishing

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]

def extPt (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) : ∀ i, H i :=
  fun i => if hp : p i then g ⟨i, hp⟩ else h₀ i

lemma extPt_update (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p)
    (x : H j.1) : extPt p h₀ (Function.update g j x) = Function.update (extPt p h₀ g) j.1 x := by
  funext i
  by_cases hi : i = j.1
  · subst hi
    simp [extPt, j.2]
  · have hne : ∀ hp : p i, (⟨i, hp⟩ : Subtype p) ≠ j := fun hp h => hi (by rw [← h])
    rw [Function.update_of_ne hi]
    unfold extPt
    split_ifs with hp
    · rw [Function.update_of_ne (hne hp)]
    · rfl

lemma extPt_at (p : ι → Prop) [DecidablePred p] (h₀ : ∀ i, H i) (g : ∀ j : Subtype p, H j.1) (j : Subtype p) :
    extPt p h₀ g j.1 = g j := by
  simp [extPt, j.2]

lemma niter_sub (p : ι → Prop) [DecidablePred p] {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i))
    (μ : ∀ i, Measure (H i)) (f : (∀ i, H i) → ℂ) (h₀ : ∀ i, H i) :
    ∀ (l : List (Subtype p)) (g : ∀ j : Subtype p, H j.1) (z : ℂ),
      NIter (R := fun j : Subtype p => R j.1) (fun j => ρ j.1) (fun j => μ j.1) (fun g => f (extPt p h₀ g)) l g z →
      NIter ρ μ f (l.map Subtype.val) (extPt p h₀ g) z := by
  intro l
  induction l with
  | nil =>
    intro g z hz
    simpa [NIter] using hz
  | cons j l ih =>
    intro g z hz
    simp only [List.map_cons, NIter.eq_2] at hz ⊢
    obtain ⟨F, hF, hF'⟩ := hz
    refine ⟨F, hF, fun x => ?_⟩
    rw [← extPt_update]
    exact ih _ _ (hF' x)

end GlobalTheory.CellVanishing

namespace GlobalTheory.RowVal


open GlobalTheory.CellVanishing in
theorem cellVan_holds : CellVan := by
  intro ι _ H _ _ _ _ _ _ _ _ A B R K l hl hS ρ μ ρ' μ' hM X S b w q z α hw hdist hinv hsupp hz hrel
  haveI := Classical.decEq (∀ i, H i)
  have hQ := (_root_.GlobalTheory.RowVal.niter_lin_congr ι H R ρ μ l 1).1 (Fin 2) Finset.univ α z q (fun n _ => hz n)
  refine _root_.GlobalTheory.NestVan.nested_vanish ι H A B R K l hl hS ρ μ ρ' μ' hM
    ((S 0).image (b 0) ∪ (S 1).image (b 1)) (fun g => ∑ n ∈ Finset.univ, α n * q n g) _ ?_ ?_ ?_ hQ ?_
  · intro c hc i
    rcases Finset.mem_union.1 hc with hc | hc <;>
    · obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨_, hb, _⟩ := hw _ β hβ
      exact hb i
  · intro i hi h
    constructor
    · intro r hr
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).1 r hr]
    · intro k hk
      exact Finset.sum_congr rfl fun n _ => by rw [(hinv n i hi h).2 k hk]
  · intro h h1 hne
    obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨β, hβ, hc⟩ := hsupp n h h1 (right_ne_zero_of_mul hn)
    refine ⟨b n β, ?_, hc⟩
    fin_cases n
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hβ)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hβ)
  · intro a ha ha1
    let p : ι → Prop := fun i => i ∈ l
    haveI : ∀ j : Subtype p, LocallyCompactSpace (B j.1) := fun j =>
      (hS j.1 j.2).clB.isClosedEmbedding_subtypeVal.locallyCompactSpace

    haveI : ∀ n (β : X n) i, Decidable (b n β i ∈ B i) := fun _ _ _ => Classical.dec _
    let bb : ∀ n, X n → ∀ i, B i := fun n β i => if h : b n β i ∈ B i then ⟨b n β i, h⟩ else 1
    have hbb : ∀ n β (hβ : β ∈ S n), bb n β = fun i => ⟨b n β i, (hw n β hβ).2.1 i⟩ := by
      intro n β hβ
      funext i
      exact dif_pos _
    let qn : Fin 2 → (∀ j : Subtype p, B j.1) → ℂ := fun n g => q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1
    have hg1 : ∀ (g : ∀ j : Subtype p, B j.1) i, i ∉ l → a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1 = 1 := by
      intro g i hi
      simp [extPt, p, hi, ha1 i hi]
    have hmeas : ∀ j ∈ l.attach, IsClosed (((R j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsCompact (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧
        IsOpen (((K j.1).subgroupOf (B j.1) : Subgroup (B j.1)) : Set (B j.1)) ∧ (ρ' j.1).IsHaarMeasure ∧
        (ρ' j.1).IsInvInvariant ∧ (μ' j.1).IsHaarMeasure ∧ (μ' j.1).IsMulRightInvariant := by
      intro j _
      have hs := hS j.1 j.2
      obtain ⟨-, -, h3, h4⟩ := hM j.1 j.2
      exact ⟨hs.clR.preimage continuous_subtype_val, hs.clB.isClosedEmbedding_subtypeVal.isCompact_preimage hs.cpt,
        hs.opn, h3, hs.uniRB _ h3, h4, hs.uniB _ h4⟩
    have hcell : ∀ n, NIter (R := fun j : Subtype p => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1) (fun j => μ' j.1)
        (qn n) l.attach 1 (∑ β ∈ S n, w n β * q n (a * b n β)) := by
      intro n
      have hv : ∀ β (hβ : β ∈ S n) i, ((bb n β i : B i) : H i) = b n β i := fun β hβ i => by rw [hbb n β hβ]
      have key := _root_.GlobalTheory.RowVal.niter_cellSum (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1))
        (fun j => (K j.1).subgroupOf (B j.1)) l.attach (List.nodup_attach.2 hl) (fun j => ρ' j.1) (fun j => μ' j.1) hmeas
        (X n) (S n) (fun β j => bb n β j.1) (qn n) (fun β _ j hj => absurd (List.mem_attach l j) hj) ?_ ?_ ?_
      · convert key using 1
        refine Finset.sum_congr rfl fun β hβ => ?_
        obtain ⟨h1, hb, hwβ⟩ := hw n β hβ
        rw [hwβ, hbb n β hβ]
        congr 1
        · exact congrArg List.prod (List.attach_map_val (f := fun i => cellWt (ρ' i) (μ' i) ((K i).subgroupOf (B i)) ⟨b n β i, hb i⟩)).symm
        · show q n (a * b n β) = q n fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (fun j => (⟨b n β j.1, hb j.1⟩ : B j.1)) i).1
          congr 1
          funext i
          by_cases hi : i ∈ l
          · simp [extPt, p, hi]
          · simp [extPt, p, hi, ha1 i hi, h1 i hi]
      · intro β hβ β' hβ' hc
        apply hdist n β hβ β' hβ'
        intro i hi
        obtain ⟨r, hr, a0, ha0, k, hk, e⟩ := hc ⟨i, hi⟩ (List.mem_attach _ _)
        rw [Subgroup.mem_bot] at ha0
        subst ha0
        refine ⟨r.1, Subgroup.mem_subgroupOf.1 hr, 1, (A i).one_mem, k.1, Subgroup.mem_subgroupOf.1 hk, ?_⟩
        have e' := congrArg Subtype.val e
        dsimp only at e'
        simp only [Subgroup.coe_mul, OneMemClass.coe_one, mul_one] at e'
        rw [hv β' hβ', hv β hβ] at e'
        rw [mul_one]
        exact e'
      · intro j _ g
        have hgj : ∀ x : B j.1, (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 (Function.update g j x) i).1) =
            Function.update (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1) j.1 (a j.1 * x.1) := by
          intro x
          rw [extPt_update]
          funext i
          by_cases hi : i = j.1
          · subst hi; simp
          · simp [Function.update_of_ne hi]
        have hj1 : (extPt (H := fun i => ↥(B i)) p 1 g j.1) = g j := extPt_at _ _ _ _
        constructor
        · intro r hr
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).1 r.1
            (Subgroup.mem_subgroupOf.1 hr)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (r * g j).1 = r.1 * (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) := by
            rw [hj1, Subgroup.coe_mul, ← mul_assoc, ← mul_assoc, (hS j.1 j.2).comm _ (ha j.1) _ r.2]
          rw [hx]
          exact this
        · intro k hk
          have := (hinv n j.1 j.2 (fun i => a i * (extPt (H := fun i => ↥(B i)) p 1 g i).1)).2 k.1
            (Subgroup.mem_subgroupOf.1 hk)
          show q n _ = q n _
          rw [hgj]
          have hx : a j.1 * (g j * k).1 = (a j.1 * (extPt (H := fun i => ↥(B i)) p 1 g j.1).1) * k.1 := by
            rw [hj1, Subgroup.coe_mul, mul_assoc]
          rw [hx]
          exact this
      · intro g _ hne
        obtain ⟨β, hβ, hc⟩ := hsupp n _ (hg1 g) hne
        refine ⟨β, hβ, fun j _ => ?_⟩
        obtain ⟨r, hr, a', ha', k, hk, e⟩ := hc j.1 j.2
        have hs := hS j.1 j.2
        have hbB : b n β j.1 ∈ B j.1 := (hw n β hβ).2.1 j.1
        have hkB : k ∈ B j.1 := hs.le hk
        have hgB : (g j).1 ∈ B j.1 := (g j).2
        dsimp only at e
        rw [extPt_at] at e
        obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = (g j).1 * k⁻¹ * (b n β j.1)⁻¹ := ⟨_, rfl⟩
        have hr₀B : r₀ ∈ B j.1 := hr₀ ▸ mul_mem (mul_mem hgB (inv_mem hkB)) (inv_mem hbB)
        have hrr : r = (a j.1 * a'⁻¹) * r₀ := by
          have hc' : a'⁻¹ * r₀ = r₀ * a'⁻¹ := hs.comm _ (inv_mem ha') _ hr₀B
          calc r = (r * a' * b n β j.1 * k) * k⁻¹ * (b n β j.1)⁻¹ * a'⁻¹ := by group
            _ = a j.1 * r₀ * a'⁻¹ := by rw [← e, hr₀]; group
            _ = a j.1 * (a'⁻¹ * r₀) := by rw [hc']; group
            _ = (a j.1 * a'⁻¹) * r₀ := by group
        have hr₀R : r₀ ∈ R j.1 := (hs.split _ (mul_mem (ha j.1) (inv_mem ha')) _ hr₀B (by rw [← hrr]; exact hr)).2
        refine ⟨⟨r₀, hr₀B⟩, Subgroup.mem_subgroupOf.2 hr₀R, 1, Subgroup.one_mem _, ⟨k, hkB⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
        apply Subtype.ext
        show (g j).1 = r₀ * 1 * (bb n β j.1).1 * k
        rw [hv β hβ, hr₀]
        group
    have hlin := (_root_.GlobalTheory.RowVal.niter_lin_congr (Subtype p) (fun j => B j.1) (fun j => (R j.1).subgroupOf (B j.1)) (fun j => ρ' j.1)
      (fun j => μ' j.1) l.attach 1).1 (Fin 2) Finset.univ α (fun n => ∑ β ∈ S n, w n β * q n (a * b n β)) qn
      (fun n _ => hcell n)
    rw [hrel a ha ha1] at hlin
    have ht := niter_sub p ρ' μ' (fun bb : ∀ i, B i => ∑ n ∈ Finset.univ, α n * q n fun i => a i * (bb i).1) 1 l.attach 1 0 hlin
    have e1 : extPt p (1 : ∀ i, B i) (1 : ∀ j : Subtype p, B j.1) = 1 := by
      funext i; simp [extPt]
    rw [e1, List.attach_map_subtype_val] at ht
    exact ht

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CosSupport

theorem isHalf_actO_one {D : D7} (S T : HSp D) (c : AE D) (h : GA D T) (y : WO S T) (hy : IsHalf c y) :
    IsHalf c (actO S T 1 h y) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hy k l]
  ring

theorem cosSupp : CosSupp := by
  classical
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ Φ hΦ m X hm g hg hne
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hw := W.om_is (.core i) (by show Node.InRange D.R.m (.core (i + 1)); simp [Node.InRange]; omega)
  have hth : IsThetaFunO W.ψ _ _ Φ := hΦ.1.1
  have hchar : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y)) := by
    intro y h1 h2 h3
    by_contra hne'
    exact hne (_root_.GlobalTheory.TargetCoef.coef_zero_of_target_eigen D W.ψ _ _ _ _ (W.om (.core i)) hw m X hm Φ hth g y _ _ (hΦ.2 e he y h1 h2)
      (hΦ.2 e he _ (isHalf_actO_one _ _ _ _ y h1) h3) hne')
  have hloc := GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hchar
  refine GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent D (G.V (.core i)) (G.Λ (.core i)) (G.sp.P_is i (by omega)).sd G.pl.W0 e he G.modul ?_ g ?_ hloc
  · intro PP hPP
    have hprime : PP.asIdeal.IsPrime := PP.isPrime
    obtain ⟨v, hv, hle⟩ := hprime.prod_le.1 hPP
    have hle' : (G.pl.w v).asIdeal ≤ PP.asIdeal := hprime.le_of_pow_le hle
    have heq : G.pl.w v = PP := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hprime.ne_top hle')
    unfold Places.W0
    exact Finset.mem_image.2 ⟨v, hv, heq⟩
  · intro v hv
    apply hg v
    intro hvS
    exact hv _ (by unfold Places.W0; exact Finset.mem_image.2 ⟨v, hvS, rfl⟩) (G.pl.under_w hvS)

end GlobalTheory.CosSupport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorRowFactorLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_rowFactor_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 u) 0 * ∏ i : Fin D.R.m, φ (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((y i).map fun a => cpt w.1 (toEAf D a))) := by
  first | exact @GlobalTheory.LocAsm.flatTensor_rowFactor | exact GlobalTheory.LocAsm.flatTensor_rowFactor | (intros; apply GlobalTheory.LocAsm.flatTensor_rowFactor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLocalIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensor_local_identity : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (Φ : ch.G.Datum) (e : AE D) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → (∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) → (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (n : locPl ch.G t → ℕ) (xw : ∀ w : locPl ch.G t, Fin (n w) → ℂ) (φw : ∀ w : locPl ch.G t, Fin (n w) → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ (w : locPl ch.G t) z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z) → ∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ Fintype.piFinset (fun w => (Finset.univ : Finset (Fin (n w)))), (∏ w, xw w (a w)) * (∏ i : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (x i)) * ∏ j : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (y j) := by
  first | exact @GlobalTheory.LocAsm.flipFin_local_identity | exact GlobalTheory.LocAsm.flipFin_local_identity | (intros; apply GlobalTheory.LocAsm.flipFin_local_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipVertexInv

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopLevelInv

theorem flips_isAdmissible {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ}
    {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → CanFlip St.path l →
      (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) → St.IsAdmissible .one ϖ e →
      (St.flips .one ψ ϖ e l).IsAdmissible .one ϖ e := by
  intro l
  induction l with
  | nil => intro St _ _ _ hT; exact hT
  | cons x l ih =>
    intro St hν hc hJ hT
    obtain _ | ⟨hp, hc'⟩ := hc
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (_root_.GlobalTheory.FlipAdm.isAdmissible_flip ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT)
    change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

theorem mem_flipOrder {m : ℕ} {x : ℕ × ℕ} (hx : x ∈ flipOrder m) : x.1 < m ∧ x.2 < m := by
  simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, j, hj, rfl⟩ := hx
  exact ⟨hi, hj⟩

theorem mem_inner_opposite {m j : ℕ} (hj : j + 1 < m) : (j + 1, m) ∈ innerVertices (oppositePath m) := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : Edge.ex (j + 1) m ∈ (oppositePath m).tail := by
    rw [oppositePath, hn, List.range_succ_eq_map, List.map_cons, List.cons_append, List.tail_cons]
    exact List.mem_append_left _ (List.mem_map.2 ⟨j + 1, List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩, rfl⟩)
  exact List.mem_map.2 ⟨_, h, rfl⟩

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (Φ : G.Datum), t ∈ U → ∀ {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ (w : Pl D.host.E), w ∈ locPl G t → ∀ (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w).rank (j + 1, D.R.m))) (Kw w)), κ ∈ givenLevel G t w (j + 1, D.R.m) →
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (j + 1, D.R.m) κ) (Tflip W S.B t Φ w) =
      Tflip W S.B t Φ w := by
  intro D T L sc G W U S t Φ _ μ₀ hL hde hc w hw j hj κ hκ
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    obtain ⟨hi, hj⟩ := mem_flipOrder hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square x.1 hi x.2 hj).condν
  have hfl : (flipStage t w S.B W Φ).IsAdmissible .one (unifAt w) (depthAt G w) :=
    flips_isAdmissible h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w S.B Φ) hν (canFlip_flipOrder _).1
      (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL S.B t Φ hw)
  obtain ⟨hp, hl⟩ := flipStage_path_level t w S.B W Φ
  have := hfl.invariant (j + 1, D.R.m) (hp ▸ mem_inner_opposite hj) κ (hl ▸ hκ)
  rw [hp] at this
  exact this

end GlobalTheory.FlipVertexInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPiecesMutualAnnihilators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

theorem pcFB_dualA : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₂ ∧ (∀ a, MxAt (fun _ => True) a → (a ∈ (pcFB W F σ h h').A₁ ↔ ∀ a' ∈ (pcFB W F σ h h').A₂, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) ∧ (∀ a', MxAt (fun _ => True) a' → (a' ∈ (pcFB W F σ h h').A₂ ↔ ∀ a ∈ (pcFB W F σ h h').A₁, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h'
  have hi : 2 * σ + 2 < D.R.m := by omega
  refine pieces_dualA (d := F.dJ (σ + 1) h) (ψ := W.ψ) (Γ := latRow G (2 * σ + 2)) (F.dB σ h') (latBig G (2 * σ + 2))
    (_root_.GlobalTheory.AscFin.SplitX.latRow_extX D hD T L μ0 hL sc G W M hM F hF σ h) (GlobalTheory.AscFin.RowAnn.annRow_isCompact D hD T L μ0 hL sc G W M hM _ hi) (GlobalTheory.AscFin.AnnOpen.latRow_ann_open D hD T L μ0 hL sc G W M hM _ hi)
    (fun u hu hb => _root_.GlobalTheory.AscFin.LatticeBidual.latRow_bidual D hD T L μ0 hL sc G W M hM _ hi u hu fun u' hu' hv => hb u' ⟨hu', hv⟩)

end GlobalTheory.AscFin.AnnPieces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_row_column_product_data_have_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  first | exact @GlobalTheory.VecsLast.vecs_last | exact GlobalTheory.VecsLast.vecs_last | (intros; apply GlobalTheory.VecsLast.vecs_last <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowData_localPureTensors_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  first | exact @GlobalTheory.RowSingle.rowData | exact GlobalTheory.RowSingle.rowData | (intros; apply GlobalTheory.RowSingle.rowData <;> assumption)
end

