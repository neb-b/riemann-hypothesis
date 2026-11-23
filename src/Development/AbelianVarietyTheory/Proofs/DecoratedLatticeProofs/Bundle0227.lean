module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.SBTwist

theorem viaRed_mem_SB {D : D7} {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ}
    (r : v.adicCompletionIntegers D.host.F →+* k)
    (hr : ∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) :
    GlobalTheory.StepVec.viaRed r ω ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  classical
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : ∀ᶠ y in nhds x, ∀ i j, Valued.v (y i j - x i j) < 1 := by
      rw [Filter.eventually_all]; intro i
      rw [Filter.eventually_all]; intro j
      have hc : Continuous fun y : Matrix (Fin b) (Fin a) (Fv D.host.F v) => y i j :=
        continuous_id.matrix_elem i j
      have hn : {z : Fv D.host.F v | Valued.v (z - x i j) < 1} ∈ nhds (x i j) :=
        Valued.mem_nhds.2 ⟨1, fun z hz => by simpa using hz⟩
      exact hc.continuousAt.preimage_mem_nhds hn
    filter_upwards [hU] with y hy
    have hint : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F ↔ x i j ∈ v.adicCompletionIntegers D.host.F := by
      intro i j
      simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 := hy i j
      constructor
      · intro h
        have : x i j = y i j - (y i j - x i j) := by ring
        rw [this]
        refine le_trans (Valuation.map_sub _ _ _) (max_le h (le_of_lt h1))
      · intro h
        have : y i j = (y i j - x i j) + x i j := by ring
        rw [this]
        exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt h1) h)
    unfold GlobalTheory.StepVec.viaRed
    by_cases hx : ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F
    · have hy' : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun i j => (hint i j).2 (hx i j)
      rw [dite_eq_left hy', dite_eq_left hx]
      congr 1
      ext i j
      simp only [Matrix.of_apply]
      have hs : (⟨y i j, hy' i j⟩ : v.adicCompletionIntegers D.host.F) - ⟨x i j, hx i j⟩ =
          ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩ := rfl
      have h0 := (hr ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩).2 (hy i j)
      rw [← hs, map_sub, sub_eq_zero] at h0
      exact h0
    · have hy' : ¬ ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun h => hx fun i j => (hint i j).1 (h i j)
      rw [dif_neg hy', dif_neg hx]
  · haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers D.host.F v
    have hK : IsCompact {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} := by
      have he : {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} =
          Set.pi Set.univ (fun _ : Fin b => Set.pi Set.univ (fun _ : Fin a => (v.adicCompletionIntegers D.host.F : Set (Fv D.host.F v)))) := by
        ext Y
        exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
      rw [he]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 ‹_›
    refine HasCompactSupport.intro hK ?_
    intro Y hY
    have hY' : ¬ ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F := hY
    unfold GlobalTheory.StepVec.viaRed
    exact dif_neg hY'

theorem phiQ_mem_SB : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hφ a b r ξ mu hmu
  obtain ⟨⟨rr, hrr⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hred : GlobalTheory.StepVec.IsRedMap φ PP rr := hrr
  have hmu' : LiftsChar φ PP mu ξ⁻¹⁻¹ := by rwa [inv_inv]
  have heq : phiQ (a := a) (b := b) v r mu = GlobalTheory.StepVec.viaRed rr (GlobalTheory.StepVec.qLoc r PP ξ⁻¹) :=
    funext fun Y => GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc D v φ PP rr hred a b r mu ξ⁻¹ hmu' Y
  rw [heq]
  exact viaRed_mem_SB rr hred.2.1 _

end GlobalTheory.SBTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumMulConjEqIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_mul_conj_eq_indicator : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v r mu x * (starRingEnd ℂ) (phiQ v r mu x) = (GlobalTheory.NrmVol.suppQ v r).indicator (fun _ => (1 : ℂ)) x := by
  intro D PP v φ hP a b r ξ mu hL x
  by_cases hx : x ∈ GlobalTheory.NrmVol.suppQ v r
  · rw [Set.indicator_of_mem hx]
    have h : IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧
        (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1 := hx
    unfold phiQ
    rw [dite_eq_left h]
    obtain ⟨⟨red, -, -, hrel, -⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hP
    set u := h.1.unit with hu
    have hv : Valued.v (u : Fv D.host.F v) = 1 := by rw [hu, IsUnit.unit_spec]; exact h.2.1
    have hvi : Valued.v ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have hint : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv.le
    have hint' : ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hvi.le
    have hunit : IsUnit (⟨(u : Fv D.host.F v), hint⟩ : v.adicCompletionIntegers D.host.F) :=
      ⟨⟨⟨_, hint⟩, ⟨_, hint'⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
    haveI : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot
    set k := (hunit.map red).unit with hk
    have hR : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) :=
      (hrel _ _).2 ⟨hint, (IsUnit.unit_spec (hunit.map red)).symm⟩
    have hmu : mu u = ξ k := hL u k hR
    haveI : Finite (kP PP)ˣ := Finite.of_injective _ Units.val_injective
    obtain ⟨n, hn0, hn⟩ := (ξ.isOfFinOrder (isOfFinOrder_of_finite k)).exists_pow_eq_one
    have hpow : ((mu u : ℂˣ) : ℂ) ^ n = 1 := by
      rw [hmu, ← Units.val_pow_eq_pow_val, hn, Units.val_one]
    have hnorm : ‖((mu u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hn0.ne'
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inv, hnorm]
    norm_num
  · rw [Set.indicator_of_notMem hx, phiQ_eq_zero_of_not_mem v r mu x hx, zero_mul]

end GlobalTheory.NrmVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceChainStepDatumSupportEqValuative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.NrmVol

theorem suppQ_eq_valuative : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r = {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin r) : Set (GL (Fin r) (Fv D.host.F v))) ∧ (∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation (Fv D.host.F v) (x i j) < 1} ∧ {y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ 1} = {x | ∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1} := by
  intro D v a b r
  have hC : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE : (ValuativeRel.valuation (Fv D.host.F v)).IsEquiv
      (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have hle : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z ≤ 1 ↔ Valued.v z ≤ 1 :=
    fun z => hE.le_one_iff_le_one
  have hlt : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z < 1 ↔ Valued.v z < 1 :=
    fun z => hE.lt_one_iff_lt_one
  have heq : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z = 1 ↔ Valued.v z = 1 :=
    fun z => hE.eq_one_iff_eq_one
  have htop : ∀ (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (i j : Fin r),
      topL r x i j = 0 ∨ ∃ i' j', topL r x i j = x i' j' := by
    intro x i j
    unfold topL
    split_ifs with h
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl rfl
  refine ⟨?_, ?_⟩
  · ext x
    simp only [suppQ, Set.mem_setOf_eq, GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · rintro ⟨-, hdet, hint, hlow⟩
      refine ⟨⟨fun i j => ?_, (heq _).2 hdet⟩, fun i j => (hle _).2 (hint i j),
        fun i j hi hj => (hlt _).2 (hlow i j hi hj)⟩
      rcases htop x i j with h | ⟨i', j', h⟩
      · rw [h, map_zero]; exact zero_le_one
      · rw [h]; exact (hle _).2 (hint i' j')
    · rintro ⟨⟨-, hdet⟩, hint, hlow⟩
      have hd : Valued.v (topL r x).det = 1 := (heq _).1 hdet
      refine ⟨?_, hd, fun i j => (hle _).1 (hint i j), fun i j hi hj => (hlt _).1 (hlow i j hi hj)⟩
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      rw [h0, map_zero] at hd
      exact zero_ne_one hd
  · ext y
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => (hle _).symm

end GlobalTheory.NrmVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw
variable {D : D7}

theorem t_fd {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (hFD : FiniteDimensional ℂ ((flat c w j s hr).CC c)) :
    FiniteDimensional ℂ (s.CC c) := by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  exact @FiniteDimensional.of_injective ℂ _ _ _ _ _ _ _ ι (Submodule.inclusion_injective hle) hFD

theorem t_met {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (h : ∃ ipD ip, IsMet c (flat c w j s hr) ipD ip) :
    ∃ ipD ip, IsMet c s ipD ip := by
  obtain ⟨ipD, ipF, hm⟩ := h
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ := (ipF.comp ι).compl₂ ι
  have hι : ∀ x : s.CC c, ι x ≠ 0 ↔ x ≠ 0 := fun x => (Submodule.inclusion_injective hle).ne_iff' (map_zero ι)
  exact ⟨ipD, ip, hm.pure, hm.hermD, hm.posD, fun x y => hm.herm (ι x) (ι y),
      fun x hx => hm.pos (ι x) ((hι x).2 hx), fun x y v v' => hm.integ (ι x) (ι y) v v',
      fun x y v v' => hm.schur (ι x) (ι y) v v'⟩

theorem t_van {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0) :
    ∀ (x : s.CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0 := by
  intro x v hv h0
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  by_contra hx
  exact (Submodule.inclusion_injective hle).ne_iff' (map_zero ι) |>.2 hx (h (ι x) v hv h0)

theorem t_par {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c (flat c w j s hr) (PiLocalization₂.val x v) B → IsPar x B) :
    ∀ (x : s.CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c s (PiLocalization₂.val x v) B → IsPar x B := fun x v B hv hP => by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  have h' := h (ι x) v B hv hP
  exact ⟨fun h0 => h'.1 (by rw [h0]; exact map_zero ι), fun v' hv' => h'.2 v' hv'⟩

theorem softQ_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := by
  intro hHC hCR D c w hw j hj s hs
  obtain ⟨hr, hL, hf⟩ := hs
  have hle : s.CC c ≤ (flat c w j s hr).CC c := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw j hj s ⟨hr, hL, hf⟩ hr
  have hMet : MetEx D := GlobalTheory.ChainMetric.metEx hCR D
  have hLev : LevFacts D := LevelFacts.levFacts D
  exact ⟨t_fd hle (finDim_of_levFacts hHC D hLev c hw.com j hj _ hf), t_met hle (hMet c hw.com j hj _ hf),
    t_van hle (val_eq_zero_imp D hMet c hw.com j hj _ hf), t_par hle (_root_.GlobalTheory.ChainOnto.parOfVal_of_parts hCR D hMet hLev c hw.com j hj _ hf)⟩

end GlobalTheory.ChainTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainLValueQuotientFactorization
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem lFull_holds : ∀ D : D7, LFull D := by
  intro D c hc B hB k hk
  set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
  have hrt : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast hrt
  have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.Icc 1 k → Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
    intro i
    by_cases hi : i ∈ Finset.Icc 1 k
    · have h1 := (Finset.mem_Icc.1 hi).1
      have h2 := (Finset.mem_Icc.1 hi).2
      obtain ⟨Λ, h⟩ := GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero D c hc i (k + 1) h1 (by omega) (by omega)
      exact ⟨Λ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Λ hΛ using hΛ
  set A := GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ with hA
  have hAb : GlobalTheory.LFun.Bounded T A D.R.r ((D.R.r : ℝ) / 2) :=
    hB.twist fun w _ => by simp [GlobalTheory.LFun.norm_val]
  let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)
  have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
    (GlobalTheory.ChainOnto.bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
  let G : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
    ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l)
  have hEq : ∀ x : ℂ, ((D.R.r : ℝ) + D.R.t + 2) < x.re →
      G x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.chT (k + 1)) (x + 1 / 2) := by
    intro x hx
    have hre : ∀ l : ℕ, l < D.R.t → 1 < (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l).re := by
      intro l hl
      have : (l : ℝ) + 1 ≤ D.R.t := by exact_mod_cast hl
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      simp
      linarith
    show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
      (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹) (x + 1 / 2)
    rw [GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char D c B k, ← hA, GlobalTheory.ChainOnto.eulerProd_add_segFam T A (Finset.Icc 1 k) z D.R.t (x + 1 / 2)
      (hAb.converges (by have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _; simp; linarith))
      (fun i _ l hl => hzc i _ (hre l hl))]
    refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun l hl => ?_)
    exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
  have hU : IsOpen (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
  have hD : DifferentiableOn ℂ G (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := by
    refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
    · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
      simp only [GlobalTheory.Cont.mem_rightOf] at hx
      simp
      linarith
    · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
        (hΛ i hi).1.comp (by fun_prop)
  have hAn := hD.analyticOnNhd hU
  have hmem : ((D.R.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2) := by
    simp only [GlobalTheory.Cont.mem_rightOf]
    simp
    linarith
  have hA0 : GlobalTheory.LFun.Converges T A ((1 + (D.R.t : ℂ)) / 2) := by
    refine hAb.converges ?_
    simp
    linarith
  have hLS : GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2) = GlobalTheory.LFun.eulerProd T A ((1 + (D.R.t : ℂ)) / 2) := rfl
  have hreidx : ∀ i, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l) =
      ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n := by
    intro i
    refine Finset.prod_nbij' (fun l => D.R.t - l) (fun n => D.R.t - n) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl ⊢
      omega
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn ⊢
      omega
    · intro l hl
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl
      omega
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn
      omega
    · intro l hl
      have hl' := Finset.mem_range.1 hl
      congr 1
      rw [Nat.cast_sub hl'.le]
      ring
  refine ⟨∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n, ?_,
    ⟨Λ, fun i hi => ⟨(hΛ i hi).1, (hΛ i hi).2.1⟩, rfl⟩, hA0, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun n hn => ?_
    have hn' := Finset.mem_Icc.1 hn
    exact (hΛ i hi).2.2 n hn'.1 hn'.2
  · rw [hLS]
    exact hA0.ne_zero
  · refine ⟨G, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
      (D.R.r : ℝ) + D.R.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, ?_⟩
    show GlobalTheory.LFun.eulerProd T A ((D.R.t : ℂ) / 2 + 1 / 2) *
      ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l) = _
    rw [hLS, Finset.prod_congr rfl fun i _ => hreidx i]
    congr 2
    ring

end GlobalTheory.ChainTw

end
end

