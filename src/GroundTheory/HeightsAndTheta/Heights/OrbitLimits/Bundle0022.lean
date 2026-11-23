module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ContractMixedField

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [Fintype K'] in
theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRingOver F ι} {a : K → ℕ} (ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _


omit [Fintype K] [Fintype K'] in
theorem isMultiProjPrime_imageVar {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRingOver F ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageVar F v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := F) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

theorem exists_dim {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver F ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem mem_divSupp_of_ne_zero {P : Ideal (MRingOver F ι)} {s : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) : W ∈ divSupp P s := by
  classical
  by_contra hW
  apply h
  simp [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem component [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {V' : Ideal (MRingOver F ι')} {n d₀ : ℕ} (hV' : IsProjVarF V' (n + 1))
    (hI : IsProjVarF (imageVar F v V') d₀) {t : MRingOver F ι} {a : K → ℕ} (ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a)
    (htV : t ∉ imageVar F v V') {W : Ideal (MRingOver F ι')} (hW : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v t) W ≠ 0) :
    IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
  classical
  have hWs := mem_divSupp_of_ne_zero hW
  have hVW : V' ≤ W := le_sup_left.trans hWs.1.1.2
  have htW : rename v t ∈ W := hWs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hrel : FieldNumbers.relDim V' = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    NumbersDVR.relDim_eq_of_ringKrullDim V' (n + 1) hV'.2
  have hW' : NumbersDVR.divCycle V' (rename v t) W ≠ 0 := by
    rw [← NumbersDVR.VocabDivCycle.proof F K' ι' V' (rename v t) W]
    exact_mod_cast hW
  obtain ⟨hWm, hWd⟩ := FieldNumbers.DivCycleSupport.full F K' ι' V' ((Bridge.isMultiProjPrime_iff V').mpr hV'.1)
    n hrel (Function.extend κ a 0) (rename v t)
    ((Bridge.isMultiHomog_iff _ _).mpr (isMultiHomog_rename hv ht)) (fun h => htV h) W hW'
  have hWm' := (Bridge.isMultiProjPrime_iff W).mp hWm
  refine ⟨⟨hWm', NumbersDVR.Numbers.ringKrullDim_eq_of_relDim W n hWd⟩, ?_⟩
  have hIm := isMultiProjPrime_imageVar hv hWm'
  obtain ⟨D, hKD, hD⟩ := exists_dim hIm
  have hle : imageVar F v V' ≤ imageVar F v W := Ideal.comap_mono hVW
  have : (imageVar F v V').IsPrime := hI.1.1
  have hdim := Inter.krullDim_quot_add_one_le hle (show t ∈ imageVar F v W from htW) htV
  rw [hD, hI.2] at hdim
  have hD' : D + 1 ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
  refine ⟨D - Fintype.card K, by omega, hIm, ?_⟩
  rw [hD, Nat.sub_add_cancel hKD]


open Classical in
theorem intNum_eq_zero [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (V' : Ideal (MRingOver F ι')) (d₀ : ℕ) (bs : Fin n → K' → ℤ),
      IsProjVarF V' n → IsProjVarF (imageVar F v V') d₀ →
      d₀ < (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) →
      NumbersDVR.intNum F V' bs = 0 := by
  intro n
  induction n with
  | zero =>
    intro V' d₀ bs _ _ h
    simp at h
  | succ n ih =>
    intro V' d₀ bs hV' hI hcount
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_gt (lt_of_le_of_lt (Nat.zero_le d₀) hcount))
    obtain ⟨a, ha⟩ : ∃ a : K → ℤ, bs i = pullDeg κ a := by
      by_contra h
      exact hi (if_neg h)
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = i :=
      ⟨Equiv.swap i (Fin.last n), Equiv.swap_apply_right _ _⟩
    rw [← FieldNumbers.IntNumSymm.full F K' ι' V' (n + 1) bs σ]
    have hlast : (bs ∘ σ) (Fin.last n) = pullDeg κ a := by
      show bs (σ (Fin.last n)) = _
      rw [hσ, ha]
    have e : bs ∘ σ = Fin.snoc (α := fun _ => K' → ℤ) (Fin.init (bs ∘ σ)) (pullDeg κ a) := by
      rw [← hlast]
      exact (Fin.snoc_init_self _).symm

    have hsum : (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) =
        (∑ j : Fin n, if ∃ a : K → ℤ, Fin.init (bs ∘ σ) j = pullDeg κ a then 1 else 0) + 1 := by
      rw [← Equiv.sum_comp σ (fun j => if ∃ a : K → ℤ, bs j = pullDeg κ a then 1 else 0),
        Fin.sum_univ_castSucc, hσ, if_pos ⟨a, ha⟩]
      rfl

    classical
    obtain ⟨bf, bg, f, g, hf, hg, hfI, hgI, hfg⟩ :=
      FieldNumbers.ExistsForm.full F K ι _ ((Bridge.isMultiProjPrime_iff _).mpr hI.1) a
    have hf' := (Bridge.isMultiHomog_iff f bf).mp hf
    have hg' := (Bridge.isMultiHomog_iff g bg).mp hg
    have hsec : IsRatSection V' (pullDeg κ a) (rename v f) (rename v g) := by
      refine ⟨Function.extend κ bf 0, Function.extend κ bg 0, isMultiHomog_rename hv hf',
        isMultiHomog_rename hv hg', fun h => hfI h, fun h => hgI h, fun k' => ?_⟩
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, hv.1.extend_apply, ← hfg]
      · simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, Function.extend_apply' _ _ _ hk, Pi.zero_apply,
          Nat.cast_zero, sub_zero]
    have key := (NumbersDVR.IntNumIsFieldIntersection.full F K' ι').2 V' n (Fin.init (bs ∘ σ)) _ _ _ hV' hsec
    dsimp only at key
    rw [e, key]
    unfold cycEval Finsupp.sum
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.mem_support_iff] at hW
    suffices h0 : NumbersDVR.intNum F W (Fin.init (bs ∘ σ)) = 0 by simp only [h0, mul_zero]
    have hcases : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v f) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v g) W ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hW
      simp [ratDiv, hc.1, hc.2]
    have hpair : IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
      rcases hcases with hc | hc
      · exact component hv hV' hI hf' (fun h => hfI h) hc
      · exact component hv hV' hI hg' (fun h => hgI h) hc
    obtain ⟨hWn, d₁, hd₁, hWI⟩ := hpair
    exact ih W d₁ _ hWn hWI (by omega)

end ContractMixedField


open ContractMixedField in
theorem contractMixedField : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement := by
  unfold ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement
  intro F _ K _ ι _ K' _ ι' _ J' hJ' κ v V' d₀ d r L N hv hV' hI hd
  classical
  rw [NumbersDVR.Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full J' hJ' V' (d + r) _ hV']
  refine intNum_eq_zero hv (d + r) V' d₀ _ hV' hI ?_
  rw [Fin.sum_univ_add]
  have h1 : ∀ j : Fin d, (if ∃ a : K → ℤ, Fin.append (fun j => pullDeg κ (L j)) N (Fin.castAdd r j) =
      pullDeg κ a then 1 else 0) = 1 := fun j => if_pos ⟨L j, by rw [Fin.append_left]⟩
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArith
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageArith.of_found (hBT : BlockTrdeg.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' hK hbm hP'
  classical
  obtain ⟨-, hMP', hHor', hdim'⟩ := hP'

  have hMP : IsMultiProjPrime (imageZ v P') := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP' ⊢
    exact FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := κ) (g := v) hbm.2.2.1 hbm.1 hbm.2.1
      (fun w hw ↦ hbm.2.2.2 w hw |>.imp fun _ h ↦ h) hMP'

  have hHor : IsHorizontal (imageZ v P') := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor'
    simp only [imageZ, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]

  have : (P').IsPrime := hMP'.1
  set A' := MRing ι' ⧸ P'
  set L := FractionRing A'
  have hinj : Function.Injective (algebraMap ℤ A') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at ha
    have h' : a ∈ (P').comap (C : ℤ →+* MRing ι') := ha
    rw [show (P').comap (C : ℤ →+* MRing ι') = ⊥ from hHor'] at h'
    exact (Submodule.mem_bot ℤ).mp h'
  have : CharZero A' := charZero_of_injective_algebraMap hinj
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective A' L)
  set φ' : MRing ι' →+* L := (algebraMap A' L).comp (Ideal.Quotient.mk P')
  have hker' : RingHom.ker φ' = P' := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A' L),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  set φ : MRing ι →+* L := φ'.comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
  have hker : RingHom.ker φ = imageZ v P' := by
    rw [← RingHom.comap_ker, hker']
    rfl

  obtain ⟨s', hs', hd'⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ'
  obtain ⟨s, hs, hd⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ
  rw [hker'] at hd'
  rw [hker] at hd
  have hφX : (Set.range fun p : Σ k, ι k ↦ φ (X p)) = Set.range fun p ↦ φ' (X (v p)) := by
    simp [φ]
  rw [hφX] at hs

  have h1 := hBT K ι K' ι' κ v P' L φ' hbm hMP' hker'
  rw [hs, hs'] at h1
  have h2 := @hBT Empty _ (fun k ↦ k.elim) (fun k ↦ k.elim) K _ ι _ (fun k ↦ k.elim) (fun p ↦ p.1.elim)
    (imageZ v P') L _ _ φ
    ⟨fun a ↦ a.elim, fun p ↦ p.1.elim, fun p ↦ p.1.elim, fun q ⟨a, _⟩ ↦ a.elim⟩ hMP hker
  rw [hφX, hs] at h2
  simp only [Fintype.card_empty, Nat.sub_zero] at h2
  have h1' : s + (Fintype.card K' - Fintype.card K) ≤ s' := by exact_mod_cast h1
  have h2' : Fintype.card K ≤ s := by
    have := le_trans (self_le_add_left _ _) h2
    exact_mod_cast this
  have hKK : Fintype.card K ≤ Fintype.card K' := Fintype.card_le_of_injective κ hbm.1
  rw [hdim'] at hd'
  have h3 : d' + Fintype.card K' = s' + 1 := by exact_mod_cast hd'
  refine ⟨s + 1 - Fintype.card K, by omega, hK, hMP, hHor, ?_⟩
  rw [hd]
  have : s + 1 - Fintype.card K + Fintype.card K = s + 1 := by omega
  rw [this]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LiftBlockGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftBlockGraph

variable {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]

theorem generatesOn_liftCoords [Fintype K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω)
    (h : KH.GeneratesOn y n x') : KH.GeneratesOn y n (liftCoords x') := by
  intro c hc
  obtain ⟨u, hu, hs⟩ := h c hc
  refine ⟨fun j => u ((Fintype.equivFin ι').symm j), fun j => hu _, ?_⟩
  rw [← hs]
  exact Fintype.sum_equiv (Fintype.equivFin ι').symm _ _ (fun j => rfl)

theorem exists_ne_zero_of_generatesOn [Fintype K] {r : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (h : KH.GeneratesOn y n v) : ∃ j, v j ≠ 0 := by
  obtain ⟨u, -, hs⟩ := h c hc
  by_contra h0
  simp only [not_exists, not_not] at h0
  simp [h0] at hs

variable [CharZero Ω] [Fintype K] [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartRingZ_le_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingZ y c) :
    x ∈ blockFnField y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  | algebraMap m =>
    rw [eq_intCast]
    exact intCast_mem _ m
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem blockFnField_addBlock (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y n 1) :
    blockFnField (addBlock y v) = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨pk, pi⟩, ⟨qk, qi⟩, hpq, rfl⟩
    simp only at hpq
    subst hpq
    cases pk with
    | none =>
      set P : Ω := ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) with hP
      have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have h1 := chartRingZ_le_blockFnField y c (hv pi c hc)
      have h2 := chartRingZ_le_blockFnField y c (hv qi c hc)
      have : v pi / v qi = (v pi * P) / (v qi * P) := (mul_div_mul_right _ _ hP0).symm
      change v pi / v qi ∈ blockFnField y
      rw [this]
      exact div_mem h1 h2
    | some k =>
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, pi⟩, ⟨k, qi⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨⟨some p.1, p.2⟩, ⟨some q.1, q.2⟩, by simp [hpq], rfl⟩

theorem isArithVar_addBlock {D : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hv : ∀ j, v j ∈ chartLat y n 1) (hg : KH.GeneratesOn y n v) :
    IsArithVar (mCoordIdeal (addBlock y v)) (D + 1) := by
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hA.2.1.2.2
  refine CoordArithOfFnField.proof K ι (Option K) (addIdx ι r) Ω y (addBlock y v) (D + 1) ⟨none⟩ ?_
    (blockFnField_addBlock y n v c hc hv).symm hA
  rintro (_ | k)
  · obtain ⟨j, hj⟩ := exists_ne_zero_of_generatesOn y n v c hc hg
    exact ⟨j, hj⟩
  · exact ⟨c k, hc k⟩


omit [CharZero Ω] in
theorem isMultiHomog_rename_none [DecidableEq K] {ι' : Type} [Fintype ι'] {g : MRing (fun _ : Unit => ι')} {e : Unit → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (fun p : Σ _ : Unit, ι' =>
      (⟨none, Fintype.equivFin ι' p.2⟩ : Σ k, addIdx ι (Fintype.card ι') k)) g)
      (blockDeg (none : Option K) (e ())) := by
  classical
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    obtain ⟨-, h2⟩ := Sigma.mk.inj h
    exact congrArg (Sigma.mk ()) ((Fintype.equivFin ι').injective (eq_of_heq h2))
  intro m hm k
  rw [support_rename_of_injective hinj] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  cases k with
  | none =>
    have hterm : ∀ i : Fin (Fintype.card ι'),
        (Finsupp.mapDomain φ m0) ⟨none, i⟩ = m0 ⟨(), (Fintype.equivFin ι').symm i⟩ := by
      intro i
      have : (⟨none, i⟩ : Σ k, addIdx ι (Fintype.card ι') k) = φ ⟨(), (Fintype.equivFin ι').symm i⟩ := by
        simp [hφ]
      rw [this, Finsupp.mapDomain_apply_of_injective hinj]
    change ∑ i : Fin (Fintype.card ι'), (Finsupp.mapDomain φ m0) ⟨none, i⟩ = _
    simp only [hterm]
    rw [Fintype.sum_equiv (Fintype.equivFin ι').symm (fun i => m0 ⟨(), (Fintype.equivFin ι').symm i⟩)
      (fun j => m0 ⟨(), j⟩) (fun _ => rfl)]
    have := hg m0 hm0 ()
    simp only [blockDeg, if_true]
    rw [← this]
  | some k =>
    have hterm : ∀ i, (Finsupp.mapDomain φ m0) ⟨some k, i⟩ = 0 := by
      intro i
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨p, hp⟩
      simp only [hφ] at hp
      exact absurd (congrArg Sigma.fst hp) (by simp)
    simp [hterm, blockDeg]


omit [CharZero Ω] in
theorem blockBirational_addBlock [DecidableEq K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (x' : ι' → Ω)
    (hb : Birational (fun p : Σ _ : Unit, ι' => x' p.2)) :
    BlockBirational (addBlock y (liftCoords x')) (none : Option K) := by
  intro d g h hg hh hne
  obtain ⟨e, g', h', hg', hh', hne', hs⟩ :=
    hb (aeval (addBlock y (liftCoords x')) g / aeval (addBlock y (liftCoords x')) h)
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hev : ∀ f : MRing (fun _ : Unit => ι'), aeval (addBlock y (liftCoords x')) (rename φ f) =
      aeval (fun p : Σ _ : Unit, ι' => x' p.2) f := by
    intro f
    have hc : addBlock y (liftCoords x') ∘ φ = fun p => x' p.2 := by
      funext p
      simp [hφ, addBlock, liftCoords]
    rw [aeval_rename, hc]
  refine ⟨e (), rename φ g', rename φ h', isMultiHomog_rename_none hg', isMultiHomog_rename_none hh', ?_, ?_⟩
  · rw [hev]
    exact hne'
  · rw [hev, hev, hs]
    field_simp


omit [CharZero Ω] in
theorem isMultiHomogIdeal_top : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
  ⟨{1}, fun f hf => ⟨0, by rw [Set.mem_singleton_iff.mp hf]; exact Inter.AvoidRing.isMultiHomog_one⟩,
    Ideal.span_singleton_one.symm⟩

end LiftBlockGraph

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn divSupp IsHorizontal multAt mcPts)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents localMult mem_segreChartComponents)

variable {K : Type*} [Fintype K] {ι : K → Type*}

theorem segreChartIdeal_isRadical (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    (segreChartIdeal P σ i).IsRadical := by
  rintro f ⟨e, he⟩
  rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff] at he ⊢
  intro x hx
  have h := he x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

theorem segreChartIdeal_mono {P W : Ideal (MRing ι)} (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : segreChartIdeal P σ i ≤ segreChartIdeal W σ i := by
  apply MvPolynomial.vanishingIdeal_anti_mono
  rintro x ⟨z, ⟨hz0, hz⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz0, fun f hf => hz f (h hf)⟩, hzi, rfl⟩

theorem ChartDivisorLength.proof (hNotMem : ChartSectionNotMem.Statement) (hComp : ChartDivisorComponents.Statement)
    (hLen : ChartSectionLength.Statement) : ChartDivisorLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hcomp := (hComp K ι P n m σ i A s hP hs).1
  have hnot := hNotMem K ι P (n + 1) m σ i A s hP hs
  have hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes := mem_segreChartComponents.1 hW'
  have hW'p : W'.IsPrime := hW'min.1.1
  have hIW' : segreChartIdeal P σ i ≤ W' :=
    (segreChartIdeal_mono (le_sup_left.trans hW.1.1.2) σ i).trans hW'min.1.2
  have hJW : ∀ J ∈ (segreChartIdeal P σ i).minimalPrimes, J ≤ W' →
      W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := fun J hJ hJW' =>
    (hcomp J (mem_segreChartComponents.2 hJ) W').2 ⟨hJW', W, ⟨hW, hWh⟩, hW'⟩
  have hmin : W' ∈ (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := by
    refine ⟨⟨hW'p, sup_le hIW' ?_⟩, fun Q hQ hQW' => ?_⟩
    · obtain ⟨J, hJ, hJW'⟩ := Ideal.exists_minimalPrimes_le hIW'
      exact le_sup_right.trans (hJW J hJ hJW').1.2
    · have := hQ.1
      obtain ⟨J, hJ, hJQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.2)
      exact (hJW J hJ (hJQ.trans hQW')).2 ⟨hQ.1, sup_le hJQ (le_sup_right.trans hQ.2)⟩ hQW'
  have key := GroundTheory.Heights₂.Heights.SectionLengthSum.proof
    (GroundTheory.Heights₂.Heights.LocalSectionLengthSum.proof GroundTheory.Heights₂.Heights.PiQuotCokerFiniteLength.proof)
    (MvPolynomial (Fin m) ℂ) (segreChartIdeal P σ i) W' (chartSection σ i s) (segreChartIdeal_isRadical P σ i)
    (fun J hJ => hnot J (mem_segreChartComponents.2 hJ)) hmin hJW
  rw [← hLen K ι P n m σ i A s hP hs W hW hWh W' hW', key]
  rfl

end GroundTheory.Heights₂.Heights.Targets
end

