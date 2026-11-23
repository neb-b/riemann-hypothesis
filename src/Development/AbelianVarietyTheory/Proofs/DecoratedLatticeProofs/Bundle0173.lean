module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegment
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem esymm_cons_succ_C (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add_C (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ_C]

theorem esymm_add_C (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add_C, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add_C]

theorem esymm_map_mul_C (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  have h := Multiset.pow_smul_esymm c k s
  simpa [smul_eq_mul] using h.symm

theorem esymm_eq_zero_of_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem natCast_cpow_half (Q : ℕ) (m : ℤ) :
    (Q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt Q : ℝ) : ℂ) ^ m := by
  have h1 : ((Real.sqrt Q : ℝ) : ℂ) = (Q : ℂ) ^ ((1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [h1, ← Complex.cpow_int_mul]
  congr 1
  ring

theorem sqrt_sq_C (Q : ℕ) : ((Real.sqrt Q : ℝ) : ℂ) ^ 2 = (Q : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

theorem esymm_string (Q : ℕ) (s z : ℂ) (hs : s ≠ 0) (hQ : s ^ 2 = (Q : ℂ)) (t : ℕ) :
    ∀ l : ℕ, ((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).esymm l =
      z ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) * (Formalism.L2.Col.gaussBin Q t l : ℂ) := by
  induction t with
  | zero =>
    intro l
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l => simp [Multiset.esymm, Formalism.L2.Col.gaussBin, Multiset.powersetCard_zero_right]
  | succ t ih =>
    intro l
    have hm : ((Finset.range (t + 1)).val.map fun i : ℕ => z * s ^ (((t + 1 : ℕ) : ℤ) - 1 - 2 * i)) =
        (z * s ^ (-(t : ℤ))) ::ₘ (((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).map
          fun x => s * x) := by
      rw [Finset.range_val, Finset.range_val, Multiset.range_succ, Multiset.map_cons, Multiset.map_map]
      congr 1
      · congr 1; congr 1; push_cast; ring
      · refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp_apply]
        rw [mul_left_comm]
        congr 1
        rw [show (((t + 1 : ℕ) : ℤ) - 1 - 2 * i) = 1 + ((t : ℤ) - 1 - 2 * i) by push_cast; ring,
          zpow_add₀ hs, zpow_one]
    rw [hm]
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l =>
      rw [esymm_cons_succ_C, esymm_map_mul_C, esymm_map_mul_C, ih, ih, Formalism.L2.Col.gaussBin]
      push_cast
      rw [← hQ]
      have h1 : s ^ (l + 1) * s ^ (-(((l : ℤ) + 1) * ((t : ℤ) - ((l : ℤ) + 1)))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) * (s ^ 2) ^ (l + 1) := by
        rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      have h2 : s ^ (-(t : ℤ)) * s ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) := by
        rw [← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      linear_combination (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t (l + 1) : ℂ)) * h1 +
        (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t l : ℂ)) * h2

theorem map_coe_seg (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (z : ℂˣ) (t : ℕ) :
    (seg w z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (qV E w) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [seg, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul, coe_npowU, npow]
  congr 1
  rw [← natCast_cpow_half]
  show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
  congr 1
  push_cast
  ring

theorem satEig_map_add_seg : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  intro E _ _ w a t k B z y hB _
  have hsQ := sqrt_sq_C (qV E w)
  have hs : ((Real.sqrt (qV E w) : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < qV E w := one_lt_absNorm w
    have : ((qV E w : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : qV E w ≠ 0) (by exact_mod_cast this)
  have hA : (B.map (z * y⁻¹ * ·)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((z : ℂ) * (y : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by simp [hB]
  set Q := qV E w with hQdef
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  set F : ℕ → ℂ := fun j => (if j ≤ k then (Q : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) *
    ((z : ℂ) * (s ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * s ^ (a + t)) ^ j else 0) * satEig Q a B j with hF
  have hFa : ∀ j, a < j → F j = 0 := by
    intro j hj
    simp only [hF, satEig, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, k < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ k by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (a + 1), F j = ∑ j ∈ Finset.range (k + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show a + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show k + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, satEig, Multiset.map_add (f := _), esymm_add_C, Finset.mul_sum, hA, map_coe_seg]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s z hs hsQ t]
  by_cases hja : j ≤ a
  · simp only [hF, if_pos hjk, satEig]
    have c1 : (Q : ℂ) ^ (((k : ℂ) * (((a + t : ℕ) : ℂ) - k)) / 2) = s ^ ((k : ℤ) * ((a : ℤ) + t - k)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    have c2 : (Q : ℂ) ^ (((j : ℂ) * ((a : ℂ) - j)) / 2) = s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    rw [c1, c2]
    have hz : ((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j) = (z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j := by
      rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk]
    have hsI : s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ)))) =
        (s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      simp only [← pow_mul, inv_pow, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_mul, ← zpow_add₀ hs]
      congr 1
      push_cast [Nat.cast_sub hja, Nat.cast_sub hjk]
      ring
    calc _ = (s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ))))) *
          (((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j)) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
      _ = ((s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j))) *
          ((z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
      _ = _ := by rw [hsQ]; ring
  · rw [esymm_eq_zero_of_lt _ (by omega), hFa j (by omega)]
    ring

end GlobalTheory.ChainOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeStringGivesSimplePoleHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.StringPole

theorem good_of_not_mem_above {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    GlobalTheory.Hk3.Good R t w := by
  intro PP hPP
  have hmem : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
    exact Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hw hmem
  · intro hc
    have e := GlobalTheory.GoodPrimes.isConjPl_iff.1 hc
    apply hw
    show w.under (𝓞 D.host.F) ∈ (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))
    rw [e, GlobalTheory.TwistTypePlaces.under_conjPl]
    exact hmem

end GlobalTheory.Core.Rk.StringPole


open GlobalTheory.Core.Rk.StringPole in
theorem GlobalTheory.Core.Rk.StringPole.string_pole_hyp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t s, HasString R i t s → ∃ B c : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧ GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))) D.R.r D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i t s hs
  classical
  obtain ⟨B, hB, hstr⟩ := hs
  set x := GlobalTheory.LFun.val (F := D.host.F) (chiV R i t) with hx
  let c : GlobalTheory.LFun.Fam D.host.E := fun w => B w - GlobalTheory.LFun.segFam x D.R.t w
  refine ⟨B, c, hB, (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t).finite_toSet, D.R.rank_add_five_le, fun w hw => ?_⟩
  have hg := good_of_not_mem_above R t w hw
  obtain ⟨B', hB', hbd⟩ := hstr w hg
  have hcard : (B w).card = (Vc D i).rank := by
    rcases hB (w.under (𝓞 D.host.F)) (fun h => hw h) w rfl with ⟨_, h2, _⟩ | ⟨_, τ, ϖ, α, _, _, h3, _⟩
    · exact h2
    · rw [h3]
      simp [GlobalTheory.LGrp.bcParam]
      omega
  have hrank : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hseg : (GlobalTheory.LFun.segFam x D.R.t w).map (fun a : ℂˣ => (a : ℂ)) =
      str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t := by
    unfold GlobalTheory.LFun.segFam GlobalTheory.LFun.seg str
    rw [Multiset.map_map]
    rfl
  have hle : GlobalTheory.LFun.segFam x D.R.t w ≤ B w := by
    refine (Multiset.map_le_map_iff (f := fun a : ℂˣ => (a : ℂ)) Units.val_injective).1 ?_
    rw [hB', hseg]
    exact Multiset.le_add_left _ _
  have hsplit : B w = c w + GlobalTheory.LFun.segFam x D.R.t w := (tsub_add_cancel_of_le hle).symm
  have hc' : (c w).map (fun a : ℂˣ => (a : ℂ)) = B' := by
    have := congrArg (Multiset.map fun a : ℂˣ => (a : ℂ)) hsplit
    rw [Multiset.map_add (f := _), hB', hseg] at this
    exact (add_right_cancel this).symm
  refine ⟨?_, ?_, GlobalTheory.LFun.norm_val _ _, GlobalTheory.LFun.norm_val _ _, ?_⟩
  · have := congrArg Multiset.card hsplit
    rw [Multiset.card_add, hcard, hrank] at this
    simp only [GlobalTheory.LFun.segFam, GlobalTheory.LFun.card_seg] at this
    omega
  · intro b hb
    have hb' : (b : ℂ) ∈ B' := hc' ▸ Multiset.mem_map_of_mem _ hb
    exact hbd _ hb'
  · show B w = GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam c x x D.R.t w
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam
    rw [mul_inv_cancel, GlobalTheory.LFun.twist_one]
    exact hsplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.SatInv


open GlobalTheory.LFun.ConjPlace in
theorem Tj_inv_eq_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (u : (w.adicCompletion E)ˣ) (j : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) (u : w.adicCompletion E) j g⁻¹ =
      Tj ℂ n (Ov E w) (u : w.adicCompletion E) j (invT (RingEquiv.refl (w.adicCompletion E)) n g) := by
  classical
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  have hd : invT (RingEquiv.refl (w.adicCompletion E)) n (dGL n u j)⁻¹ = dGL n u j :=
    (invT_dGL _ u j).trans (congrArg (fun v => dGL n v j) (Units.ext rfl))
  rw [Tj_apply, Tj_apply]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    refine ⟨_, (hK _).1 (inv_mem hb), _, (hK _).1 (inv_mem ha), ?_⟩
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq, ← inv_inv g, H]
    group
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective a
    obtain ⟨b, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective b
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq] at H
    refine ⟨_, inv_mem ((hK b).2 hb), _, inv_mem ((hK a).2 ha), ?_⟩
    rw [H]
    group


open GlobalTheory.LFun.ConjPlace in
theorem invT_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) :
    invT (RingEquiv.refl (w.adicCompletion E)) n (invT (RingEquiv.refl (w.adicCompletion E)) n g) = g :=
  Units.ext (Matrix.ext fun i j => by
    rw [invT_val, ← map_inv, invT_val, inv_inv]; rfl)


open GlobalTheory.LFun.ConjPlace in
theorem heckeVec_inv_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (hx : x ∈ fixed ρ (KGL w (n := n))) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x =
      heckeVec (ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom) (KGL w (n := n))
        (Tj ℂ n (Ov E w) ϖ j) x := by
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ j).1 hx]
  obtain ⟨u, rfl⟩ : ∃ u : (w.adicCompletion E)ˣ, (u : w.adicCompletion E) = ϖ :=
    ⟨Units.mk0 ϖ fun e => by simp [IsUnifV, e] at hϖ, rfl⟩
  congr 1
  funext g
  exact Tj_inv_eq_invT w n u j g

open GlobalTheory.LFun.ConjPlace in
theorem satVec_iff_inv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  intro E _ _ w n V _ _ ρ x B h0 hx hB
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  let ρ' := ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom
  have hx' : x ∈ fixed ρ' (KGL w (n := n)) := (mem_fixed_comp_symm _ hK).2 hx
  have hs : ∀ g, (invT (RingEquiv.refl (w.adicCompletion E)) n).symm g =
      invT (RingEquiv.refl (w.adicCompletion E)) n g := fun g =>
    (MulEquiv.symm_apply_eq _).2 (invT_invT w n g).symm
  have hρ : ρ'.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom = ρ := MonoidHom.ext fun g => by
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs, invT_invT]
  constructor
  · intro h ϖ hϖ j hj
    rw [heckeVec_inv_eq w n V ρ x hx hϖ j]
    exact (isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h).2.2.2 ϖ hϖ j hj
  · intro h
    have h1 : IsSatVecGL w ρ' x (B.map (·⁻¹)) :=
      ⟨h0, hx', by simpa using hB, fun ϖ hϖ j hj => (heckeVec_inv_eq w n V ρ x hx hϖ j).symm.trans (h ϖ hϖ j hj)⟩
    have h2 := isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h1
    rw [hρ, Multiset.map_map] at h2
    simpa using h2

end GlobalTheory.ChainOnto.SatInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem setIntegral_fd_mul_right : ∀ (D : D7) (S : HSp D) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ F : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) → ∀ a : GA D S, ∫ g in 𝓕, F (g * a) ∂ν = ∫ g in 𝓕, F g ∂ν := by
  intro D S ν 𝓕 hν h𝓕 F hF a
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
  haveI : ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds S ν hν
  exact GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 a F hF

end GlobalTheory.ChainOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallEntriesAndStringsAvoidExcludedNormPowers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RkNs

theorem small_entries_and_strings_avoid_excluded : ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r t : ℕ), r + 2 ≤ t → ∀ k ∈ ({(t : ℤ) - 1, 1 - (t : ℤ), (t : ℤ) + 1, -((t : ℤ) + 1)} : Set ℤ), (∀ β : ℂ, β ≠ 0 → ‖β‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → ‖β⁻¹‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → β ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2)) ∧ ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → x ≠ 1 → ∀ β ∈ GlobalTheory.LFun.seg w x t, (β : ℂ) ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2) := by
  intro K _ _ w r t hrt k hk
  have hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast GlobalTheory.LFun.one_lt_absNorm w
  have hN0 : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by linarith
  have hkabs : (r : ℤ) < k ∨ k < -(r : ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h | h <;> subst h <;> omega
  refine ⟨?_, ?_⟩
  · intro β hβ0 h1 h2 heq
    have hn : ‖β‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
      rw [heq, GlobalTheory.LFun.norm_npow]
      congr 1
      simp
    rcases hkabs with hk' | hk'
    · have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (r : ℝ) < (k : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
    · have hinv : ‖β⁻¹‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        rw [norm_inv, hn, Real.rpow_neg hN0.le]
      have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (k : ℝ) < -(r : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
  · intro x hx1 hxne β hβ heq
    simp only [GlobalTheory.LFun.seg, Multiset.mem_map, Finset.mem_range] at hβ
    obtain ⟨i, -, rfl⟩ := hβ
    set c : ℂ := (k : ℂ) / 2 - (((t : ℂ) - 1) / 2 - (i : ℂ)) with hc
    have hsplit : GlobalTheory.LFun.npow w ((k : ℂ) / 2) =
        GlobalTheory.LFun.npow w (((t : ℂ) - 1) / 2 - (i : ℂ)) * GlobalTheory.LFun.npow w c := by
      rw [← GlobalTheory.LFun.npow_add]
      congr 1
      rw [hc]; ring
    rw [Units.val_mul, GlobalTheory.LFun.coe_npowU, hsplit, mul_comm] at heq
    have hx : (x : ℂ) = GlobalTheory.LFun.npow w c :=
      mul_left_cancel₀ (GlobalTheory.LFun.npow_ne_zero w _) heq
    have him : c.im = 0 := by
      rw [hc]; simp
    have hre : c.re = 0 := by
      have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ c.re = 1 := by
        rw [← GlobalTheory.LFun.norm_npow, ← hx, hx1]
      rcases lt_trichotomy c.re 0 with h | h | h
      · have := Real.rpow_lt_one_of_one_lt_of_neg hN h
        linarith
      · exact h
      · have := Real.one_lt_rpow hN h
        linarith
    have hc0 : c = 0 := Complex.ext hre him
    apply hxne
    ext
    rw [hx, hc0, GlobalTheory.LFun.npow, Complex.cpow_zero, Units.val_one]

end GlobalTheory.RkNs
end

