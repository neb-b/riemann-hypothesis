module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenValAddSegL
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHecke.StringEig

open GlobalTheory.ChainOnto (esymm_add_C esymm_map_mul_C esymm_string esymm_eq_zero_of_lt sqrt_sq_C natCast_cpow_half)

theorem map_coe_segL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (z : ℂˣ) (t : ℕ) :
    (segL ϖ z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [segL, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  congr 1
  rw [GlobalTheory.MellinPoly.absPow_eq_zpow, ord_eq_one hϖ, zpow_one, ← natCast_cpow_half]
  congr 1
  push_cast
  ring

theorem genVal_add_segL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r N t n₀ : ℕ) (B : Multiset ℂˣ) (zS zT : ℂˣ), B.card = N → n₀ ≤ N + t → genVal (resCard k) r (N + t) (B.map (· * (zS * zT⁻¹)) + segL ϖ zS t) n₀ = (zS : ℂ) ^ n₀ * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n₀ * (r + N)) * ∑ n ∈ Finset.range (N + 1), (if n ≤ n₀ then ((resCard k ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin (resCard k) t (n₀ - n) : ℕ) : ℂ) else 0) * (((zT : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (r + N + t)))⁻¹ * genVal (resCard k) r N B n) := by
  intro k _ _ _ _ ϖ hϖ r N t n₀ B zS zT hB hn₀
  set Q := resCard k with hQdef
  have hsQ := sqrt_sq_C Q
  have hs : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < Q := one_lt_resCard k
    have : ((Q : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : Q ≠ 0) (by exact_mod_cast this)
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  have hA : (B.map (· * (zS * zT⁻¹))).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((zS : ℂ) * (zT : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def, mul_comm]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = N := by simp [hB]
  set F : ℕ → ℂ := fun n => (if n ≤ n₀ then ((Q ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin Q t (n₀ - n) : ℕ) : ℂ) else 0) *
    (((zT : ℂ) ^ n * s ^ (n * (r + N + t)))⁻¹ * genVal Q r N B n) with hF
  have hFa : ∀ j, N < j → F j = 0 := by
    intro j hj
    simp only [hF, genVal, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, n₀ < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ n₀ by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (N + 1), F j = ∑ j ∈ Finset.range (n₀ + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show N + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show n₀ + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, genVal, Multiset.map_add (f := _), esymm_add_C, Finset.mul_sum, Finset.mul_sum, hA, map_coe_segL k ϖ hϖ]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ n₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s zS hs hsQ t]
  simp only [hF, if_pos hjk, genVal]
  by_cases hjN : j ≤ N
  · by_cases hat : n₀ - j ≤ t
    · have hsI : s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ)))) =
          s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j)) := by
        rw [← pow_mul]
        simp only [← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hs]
        congr 1
        push_cast [Nat.cast_sub hjN, Nat.cast_sub hjk, Nat.cast_sub hat, Nat.cast_sub hn₀]
        ring
      have hz : ((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j) = (zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹ := by
        rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk, inv_pow]
      calc _ = (s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ))))) *
            (((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j)) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
        _ = (s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j))) *
            ((zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
        _ = _ := by rw [hsQ]; push_cast; rw [mul_inv]; ring
    · rw [Formalism.L2.Col.gaussBin_eq_zero Q (show t < n₀ - j by omega)]
      simp
  · rw [esymm_eq_zero_of_lt _ (by omega)]
    simp

end GlobalTheory.ParHecke.StringEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugate
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem typePlaces_noConj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg →
    ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg hT PP hP PP' hP' hc
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hFfix : ∀ r : 𝓞 D.host.F,
      D.host.conj ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) :=
    fun r => (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2

  have hle : PP.asIdeal.under (𝓞 D.host.F) ≤ PP'.asIdeal.under (𝓞 D.host.F) := by
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap] at hr ⊢
    obtain ⟨c', hc', he⟩ := hc _ hr
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
      apply RingOfIntegers.ext
      rw [he, hstar, hFfix]
    rwa [← this]
  have hmax : (PP.asIdeal.under (𝓞 D.host.F)).IsMaximal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP).isMaximal
  have hne : PP'.asIdeal.under (𝓞 D.host.F) ≠ ⊤ := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP').isPrime.ne_top
  have hund : HeightOneSpectrum.under (𝓞 D.host.F) PP' = HeightOneSpectrum.under (𝓞 D.host.F) PP := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    exact (hmax.eq_of_le hne hle).symm
  have hgP := hT.1 PP hP
  have hgv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hgP
  obtain ⟨W, _, hW⟩ := hT.2 _ hgv
  have e1 : PP = W := hW PP ⟨hP, rfl⟩
  have e2 : PP' = W := hW PP' ⟨hP', hund⟩
  have e : PP' = PP := e2.trans e1.symm
  subst e

  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    rw [Nat.cast_mul] at hgP
    rcases PP'.isPrime.mem_or_mem hgP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨x, hx, hxn⟩ :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP' hk).2.2.1
  obtain ⟨c', hc', he⟩ := hc x hx
  exact hxn c' (he.trans (hstar _)) hc'

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientUnramifiedAtTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.ChainTw.QuotUnr

theorem loc_eq_of_isRes {D : D7} {H H' : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ}
    (h : IsRes H PP a) (h' : IsRes H' PP a) (x : (PP.adicCompletion D.host.E)ˣ) (hx : Formalism.L2.Host.IsUnitAt PP x) :
    H.loc PP x = H'.loc PP x := by
  have ht := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H PP a h
  have ht' := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H' PP a h'
  obtain ⟨b, hb⟩ := GlobalTheory.GaussModulus.exists_int_approx PP (x := (x : PP.adicCompletion D.host.E)) (le_of_eq hx) 1
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hbv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = 1 := by
    have hx1 : Valued.v (x : PP.adicCompletion D.host.E) = 1 := hx
    have e : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = Valued.v (x : PP.adicCompletion D.host.E) :=
      Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, hx1]; exact lt_of_le_of_lt hb hlt)
    rw [e, hx1]
  have hbP : b ∉ PP.asIdeal := by
    intro hm
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) < 1 := (PP.valuation_lt_one_iff_mem b).2 hm
    have h2 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) = 1 := by
      rw [← GlobalTheory.GaussModulus.valued_algebraMap]; exact hbv
    exact (ne_of_lt h1) h2
  have hb0 : (b : D.host.E) ≠ 0 := fun h0 => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  let kb : D.host.Eˣ := Units.mk0 _ hb0
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hu0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun h0 => hbP (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let u : (kP PP)ˣ := Units.mk0 _ hu0
  have e1 := h b kb u rfl rfl
  have e2 := h' b kb u rfl rfl

  obtain ⟨y, hy⟩ : ∃ y : (PP.adicCompletion D.host.E)ˣ, y = x * (Formalism.L2.Host.atFin PP kb)⁻¹ := ⟨_, rfl⟩
  have hkv : Valued.v ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1 := hbv
  have hyu : Formalism.L2.Host.IsUnitAt PP y := by
    show Valued.v ((y : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hkv, inv_one, mul_one]
    exact hx
  have hy1 : Valued.v ((y : PP.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have hk0 : ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) =
        algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) := rfl
    have e : (y : PP.adicCompletion D.host.E) - 1 =
        ((x : PP.adicCompletion D.host.E) - algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) *
          (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E))⁻¹ := by
      have hne : algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) ≠ 0 := by
        rw [← hk0]; exact Units.ne_zero _
      rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, hk0, sub_mul, mul_inv_cancel₀ hne]
    rw [e, map_mul, map_inv₀, hbv, inv_one, mul_one]
    exact hb
  have hxy : x = Formalism.L2.Host.atFin PP kb * y := by rw [hy, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hxy, map_mul, map_mul, ht y hyu hy1, ht' y hyu hy1, mul_one, mul_one]
  exact e1.symm.trans e2

end GlobalTheory.ChainTw.QuotUnr


open GlobalTheory.ChainTw.QuotUnr in
theorem GlobalTheory.ChainTw.quot_unrAt_twist : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  intro D c w hw PP hPP i j hi1 him hj1 hjm
  have hPg : PP ∈ c.Pg := by classical rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨Hi, hci, hri⟩ := hw.com.res ⟨i - 1, by omega⟩
  obtain ⟨Hj, hcj, hrj⟩ := hw.com.res ⟨j - 1, by omega⟩
  simp only [Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1] at hci hri hcj hrj
  have ri := hri PP hPg
  have rj := hrj PP hPg
  rw [hw.chiQ i PP hPP] at ri
  rw [hw.chiQ j PP hPP] at rj
  intro x hx
  have li := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hci PP) x
  have lj := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hcj PP) x
  have split : GlobalTheory.LFun.locChar (c.μ i * (c.μ j)⁻¹) PP x =
      GlobalTheory.LFun.locChar (c.μ i) PP x * (GlobalTheory.LFun.locChar (c.μ j) PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [split, li, lj, loc_eq_of_isRes ri rj x hx, mul_inv_cancel]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorInverseCosetConjEigenvalue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeAdjEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.FinZeta (bddAut bddRep coe_bddRep)

theorem exists_dual_rep (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (α : GA D V)
    (hS : OffS D Sb P) (hef : IsPrimeIdem P e f) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : d.Pairwise (fun a b => b ≤ a)) (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅))
    (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1) (hα : SuppF V f α) (hdiv : DivAt V e (ϖ : D.host.E) d α)
    (hrep : IsCosetRep V {k | k ∈ J ∧ SuppF V f k} α R) :
    ∃ R' : Finset (GA D V), Hecke₂ V J χ Sb P (dualLab d) R' ∧ R'.card = R.card ∧
      ∀ γ ∈ R', ∃ k₁ ∈ {k | k ∈ J ∧ SuppF V f k}, ∃ k₂ ∈ {k | k ∈ J ∧ SuppF V f k}, γ = k₁ * α⁻¹ * k₂ := by
  obtain ⟨he, v, hf⟩ := GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HeckeDual.exists_skew D
  haveI := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ J ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (hJ g h2).1 h1
      obtain ⟨k, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h2 := (GlobalTheory.HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩
      refine ⟨(hJ _ h2).2 ?_, h2⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := GlobalTheory.HeckeDual.exists_rep_inv
    (GlobalTheory.HeckeDual.modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h]
    exact zero_mem _)
  refine ⟨R', ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, ?_, hJ, hχ, (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he hϖ0 hdiv).1, fun γ hγ => (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1,
    fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3, fun γ hγ => (h1 γ hγ).2⟩
  · rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact hd.imp fun h => neg_le_neg h
  · obtain ⟨x, rfl⟩ := (h1 γ hγ).1
    exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem form_sum (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (K : Set (GA D V)) (F : bddAut V)
    (hF : ∀ k ∈ K, bddRep V k F = F) (α : GA D V) (R : Finset (GA D V))
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) :
    B (∑ γ ∈ R, bddRep V γ F) F = (R.card : ℂ) * B (bddRep V α F) F := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (g := fun _ => B (bddRep V α F) F), Finset.sum_const, nsmul_eq_mul]
  intro γ hγ
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR γ hγ
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hF k₂ hk₂]
  have h := hinv k₁ (bddRep V α F) F
  rwa [hF k₁ hk₁] at h

theorem form_inv (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (F : bddAut V) (α : GA D V) :
    B (bddRep V α⁻¹ F) F = starRingEnd ℂ (B (bddRep V α F) F) := by
  have h := hinv α⁻¹ F (bddRep V α F)
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
  rw [h, hsym]

theorem coe_sum_bddRep (f : GA D V → ℂ) (hf : f ∈ bddAut V) (R : Finset (GA D V)) :
    ((∑ γ ∈ R, bddRep V γ ⟨f, hf⟩ : bddAut V) : GA D V → ℂ) = heckeLin V R f := by
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply, heckeLin_apply]
  rfl

theorem heckeLin_eq_conj_of_dualLab : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ GlobalTheory.FinZeta.bddAut V, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = e P (dualLab d) • f) → ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = conj (e P d) • f := by
  intro D V J χ Sb _ f hf hJχ ev heig P d R hR
  obtain ⟨e, f', ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, -, hrep⟩ := id hR
  obtain ⟨R', hR', hcard, hR're⟩ := exists_dual_rep J χ Sb P d R e f' ϖ α hS hef hϖ hϖ2 hd hJ hχ hα hdiv hrep
  obtain ⟨B, hsym, hpos, hinv⟩ := (GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded D V).1
  set F : bddAut V := ⟨f, hf⟩ with hFdef
  have hFK : ∀ k ∈ {k | k ∈ J ∧ SuppF V f' k}, bddRep V k F = F := fun k hk => by
    refine Subtype.ext (funext fun g => ?_)
    rw [coe_bddRep]
    show f (g * k) = f g
    rw [hJχ k hk.1, hχ k hk.1 hk.2, one_mul]
  have e1 := heig P d R hR
  have e2 := heig P (dualLab d) R' hR'
  rw [show dualLab (dualLab d) = d by simp [dualLab, List.map_reverse]] at e2
  have s1 : (∑ γ ∈ R, bddRep V γ F) = ev P (dualLab d) • F := Subtype.ext (by
    rw [coe_sum_bddRep, e1]; rfl)
  have s2 : (∑ γ ∈ R', bddRep V γ F) = ev P d • F := Subtype.ext (by
    rw [coe_sum_bddRep, e2]; rfl)
  have t1 := form_sum B hinv _ F hFK α R (fun γ hγ => (hrep.1 γ hγ).2)
  have t2 := form_sum B hinv _ F hFK α⁻¹ R' hR're
  rw [form_inv B hsym hinv, s2, hcard, map_smul, LinearMap.smul_apply, smul_eq_mul] at t2
  rw [s1, map_smul, LinearMap.smul_apply, smul_eq_mul] at t1
  by_cases h0 : F = 0
  · have : f = 0 := congrArg Subtype.val h0
    subst this
    rw [map_zero, smul_zero]
  · have hb : B F F ≠ 0 := fun h => by
      have := hpos F h0
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hbr : starRingEnd ℂ (B F F) = B F F := (hsym F F).symm
    have key : ev P (dualLab d) = starRingEnd ℂ (ev P d) := by
      apply mul_right_cancel₀ hb
      rw [t1, ← hbr, ← map_mul, t2, map_mul, map_natCast, Complex.conj_conj]
    rw [e1, key]

end GlobalTheory.HeckeAdjEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverse
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem secW_cA (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : secW hw h (c z) = cA D (secW hw h z) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.LFun.InertChart.complEquiv hw h).surjective z
  have e1 : c (GlobalTheory.LFun.InertChart.complEquiv hw h y) =
      GlobalTheory.LFun.InertChart.complEquiv hw h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig y) := hc y
  rw [e1]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) =
    cA D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact (GlobalTheory.EmbChart.sigR_tensAt v _ y).symm

theorem thW_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  intro D ψ v w hw h c k hc hcc z
  have h1 : secW hw h (k * c k * c z) = cA D (secW hw h (k * c k * z)) := by
    rw [← secW_cA D hw h c hc]
    congr 1
    rw [map_mul c, map_mul c, hcc, mul_comm k (c k)]
  rw [thW_apply, thW_apply, h1, ← GlobalTheory.DualPairCheck.trace_cA (_ * cA D _), RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, neg_mul, LinearMap.map_neg,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymmStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w (n := n)) ∧ CosetSym (KGL w (n := n)) := by
  first | exact @GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | exact GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | (intros; apply GlobalTheory.ChainOnto.kGL_commensurated_cosetSym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormsMatrixStepsCoupledFactorBoundedAnyLevelPrimStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_matrixSteps_coupledFactor_bounded_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  first | exact @GlobalTheory.Core.Ht2.factors_leS | exact GlobalTheory.Core.Ht2.factors_leS | (intros; apply GlobalTheory.Core.Ht2.factors_leS <;> assumption)
end

