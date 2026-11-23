module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeHeightMulMass
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NoCancellation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop) (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ i ∈ s, Q i Λ) :
    S.mass d P ≤ ∑ i ∈ s, S.mass d (Q i) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases hP : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨i, hi, hQ⟩ := h _ hP.1 hP.2
    rw [if_pos hP]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => if S.IsTerm d o.out ∧ Q i o.out then
      ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => zero_le) hi)
    exact (if_pos ⟨hP.1, hQ⟩).ge
  · rw [if_neg hP]
    exact zero_le


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  simpa using mass_le_sum S {()} d P (fun _ => Q) (fun Λ h1 h2 => ⟨(), by simp, h Λ h1 h2⟩)


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem sumData_mass_le (P : S.Datum → Submodule L.O S.V → Prop) :
    (S.sumData fun d => S.mass d (P d)) ≤ S.nn := by
  unfold Frames.nn Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (mass_mono S _ _ _ fun _ _ _ => trivial) _

theorem ampSq_le_of_mass (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop) (B : ℝ)
    (hB : ∀ d, S.mass d (P d) ≤ ENNReal.ofReal B) :
    S.ampSq P ≤ ENNReal.ofReal B * S.sumData fun d => S.mass d (P d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk
  simpa using h2 P B 1 zero_le_one hB (fun d => by simpa using h1 d (P d))

theorem ampSq_le_of_zero (hk : 1 ≤ k) (P : S.Datum → Submodule L.O S.V → Prop)
    (hP : ∀ d Λ, S.IsTerm d Λ → P d Λ → S.BBzero d Λ) :
    S.ampSq P ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  refine (ampSq_le_of_mass S hk P _ fun d => ?_).trans
    (mul_le_mul_right (sumData_mass_le S P) _)
  by_cases hT : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hT
    have hH : 1 ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀).2.2.2.2.1
    have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    refine (mass_mono S d _ (fun Λ => S.cardI d Λ = 1) fun Λ h1 h2 => ?_).trans
      (((_root_.GlobalTheory.HL.MassGlue.mass_le_and_finite L r k S hk d).1 1).trans (ENNReal.ofReal_le_ofReal ?_))
    · have hb := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h1).2.2.2.2.2.2.1.1 (hP d Λ h1 h2)
      obtain ⟨⟨i, hi⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      have : 0 < S.q ^ i := by positivity
      omega
    · rw [Nat.cast_one, one_pow, mul_one]
      exact pow_le_pow_right₀ hH (by nlinarith)
  · refine (mass_le_sum S (∅ : Finset Unit) d _ (fun _ _ => True) fun Λ h1 _ =>
      (hT ⟨Λ, h1⟩).elim).trans ?_
    simp

theorem ampSq_defect_le (hk : 4 * r + 7 ≤ k) (hH : 0 ≤ S.Hp) (i : ℕ) :
    (S.ampSq fun d Λ => S.be d Λ = S.q ^ i) ≤
      ENNReal.ofReal ((i + 1) * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (4 * S.Hp ^ (4 * (r + 1)))) * S.nn := by
  have hk1 : 1 ≤ k := by omega
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hβ : 0 < S.q ^ i := by positivity
  have hβ' : (0 : ℝ) < ((S.q ^ i : ℕ) : ℝ) ^ (k - 1) := by positivity
  have hm : ∀ d, S.mass d (fun Λ => S.be d Λ = S.q ^ i) ≤ ENNReal.ofReal ((i + 1) *
      (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1))) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun j Λ => S.cardI d Λ = S.q ^ j)
      fun Λ h1 h2 => ?_).trans ?_
    · obtain ⟨⟨j, hj⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ h1
      refine ⟨j, Finset.mem_range.2 ?_, hj⟩
      rw [hj, h2] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      omega
    · refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal
        (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * ((S.q ^ i : ℕ) : ℝ) ^ (k - 1)))
        fun j hj => ?_).trans ?_
      · refine ((_root_.GlobalTheory.HL.MassGlue.mass_le_and_finite L r k S hk1 d).1 _).trans (ENNReal.ofReal_le_ofReal ?_)
        have hji : S.q ^ j ≤ S.q ^ i :=
          Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.1 hj; omega)
        gcongr
      · rw [Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ i + 1),
          ← ENNReal.ofReal_natCast, Nat.cast_succ]
  refine (ampSq_le_of_mass S hk1 _ _ hm).trans ?_
  refine (mul_le_mul_right (_root_.GlobalTheory.DefectShare.mass_defect_order_le L r k S hk _ hβ) _).trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem ampSq_le_height_mul_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.ampSq S.BBzero ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn ∧ (S.ampSq fun _ _ => True) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2)) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  have hk1 : 1 ≤ k := by omega
  refine ⟨ampSq_le_of_zero S hk1 _ fun _ _ _ h => h, ?_⟩
  by_cases hz : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ
  · exact ampSq_le_of_zero S hk1 _ fun d Λ h _ => hz d Λ h
  push_neg at hz
  obtain ⟨d₀, Λ₀, h₀, hn⟩ := hz
  obtain ⟨ha, -, -, hqa, hH, -, -, hqH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq' : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
  have h2 : (2 : ℝ) ≤ S.Hp := hq'.trans (hqH hn)
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le ha
  have hAH : (A : ℝ) + 1 ≤ S.Hp := by
    rw [hA, zpow_natCast] at hqa
    have h1 : A + 1 ≤ S.q ^ A := Nat.lt_pow_self (by omega)
    exact le_trans (by exact_mod_cast h1) hqa
  refine (GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (Finset.range (A + 1))
    (fun i d Λ => S.be d Λ = S.q ^ i) _ (fun d Λ h => ?_) (fun d Λ h i _ i' _ h1 h2 => ?_)).trans ?_
  · obtain ⟨i, hi, hb⟩ := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.1
    exact ⟨fun _ => ⟨i, Finset.mem_range.2 (by omega), hb⟩, fun _ => trivial⟩
  · exact Nat.pow_right_injective hq (h1.symm.trans h2)
  have hsum := Finset.sum_le_card_nsmul (Finset.range (A + 1))
    (fun i => S.ampSq fun d Λ => S.be d Λ = S.q ^ i)
    (ENNReal.ofReal (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
        (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) * S.nn) (fun i hi => by
      refine (ampSq_defect_le S hk (by linarith) i).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
      have hi' : (i : ℝ) ≤ A := by
        have := Finset.mem_range.1 hi
        exact_mod_cast (by omega : i ≤ A)
      have h4 : (4 : ℝ) ≤ S.Hp ^ 2 := by nlinarith
      have h5 : (i : ℝ) + 1 ≤ S.Hp := by linarith
      gcongr)
  refine (mul_le_mul_right hsum _).trans ?_
  have hc : ((A + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal S.Hp := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact hAH)
  rw [Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  refine (mul_le_mul_left (mul_le_mul' hc hc) _).trans ?_
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have he : S.Hp * S.Hp * (S.Hp * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) *
      (S.Hp ^ 2 * S.Hp ^ (4 * (r + 1)))) = S.Hp ^ (9 * (r + 1) ^ 2 + 16 * (r + 1) + 5) := by
    ring
  rw [he]
  exact pow_le_pow_right₀ hH (by nlinarith)

end GlobalTheory.HL.NoCancellation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLeMassSecondTypeFamily
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AmpCancel

theorem ofReal_tsum_ite {ι : Type} (p : ι → Prop) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfin : {i | p i}.Finite) :
    ENNReal.ofReal (∑' i, if p i then f i else 0) =
      ∑' i, if p i then ENNReal.ofReal (f i) else 0 := by
  have hs : ∀ i, i ∉ hfin.toFinset → ¬ p i := fun i hi h => hi (hfin.mem_toFinset.2 h)
  have hs' : ∀ i ∈ hfin.toFinset, p i := fun i hi => hfin.mem_toFinset.1 hi
  rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i)]

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (β J βJ : ℕ) (d : S.Datum) :
    ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤
      ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  have hk1 : 1 ≤ k := by omega
  have hc0 : 0 ≤ (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := zpow_nonneg (Nat.cast_nonneg _) _
  have hvol : ∀ K : Subgroup S.GLV, 0 ≤ invVol S.K0 K := fun K =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : Submodule L.O S.V → Prop, P = fun Λ => S.IsTerm d Λ ∧ S.InFF β J βJ d Λ :=
    ⟨_, rfl⟩
  have hPiff : ∀ Λ, P Λ ↔ S.IsTerm d Λ ∧ S.InFF β J βJ d Λ := fun Λ => by rw [hP]
  have hPfin : {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | P o.out}.Finite :=
    (_root_.GlobalTheory.HL.MassGlue.mass_le_and_finite L r k S hk1 d).2.subset fun o ho => ((hPiff _).1 ho).1
  have hmass : S.mass d (S.InFF β J βJ d) = ENNReal.ofReal (∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0) := by
    rw [ofReal_tsum_ite (ι := MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) (fun o => P o.out)
      (fun o => invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out)) (fun o => hvol _) hPfin]
    subst hP
    unfold Frames.mass Frames.mu
    exact tsum_congr fun o => by congr
  have hsum0 : 0 ≤ ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 :=
    tsum_nonneg fun o => by split_ifs <;> simp [hvol]
  have hamp : S.amp d (S.InFF β J βJ d) = ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then ((invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) : ℝ) : ℂ) * S.om d o.out
      else 0 := by
    subst hP
    unfold Frames.amp Frames.mu
    exact tsum_congr fun o => by congr
  have key : ‖S.amp d (S.InFF β J βJ d)‖ ≤ 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) *
      ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
        if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 := by
    by_cases hJ : 1 ≤ J ∧ J ≤ r
    · have hj : ((⟨J - 1, by omega⟩ : Fin r) : ℕ) + 1 = J := by simp only; omega
      obtain ⟨m, hm_inv, hm⟩ := _root_.GlobalTheory.HL.exists_symm_invariant_kernel L r k S hk ⟨J - 1, by omega⟩ β βJ d P
        (fun Λ => by rw [hj]; exact hPiff Λ)
      have hK0 : S.K0 ≤ S.St := fun g hg => hg.1.1
      have bound := GlobalTheory.HL.norm_orbit_sum_le_of_symm_kernel S.St S.K0 P (S.om d) m
        (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) hK0
        (fun h hh x hx => by
          obtain ⟨hT, hI⟩ := (hPiff x).1 hx
          have T := _root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d x hT h hh
          have hlat := (GlobalTheory.HL.TermBasic.term_basic L r k S d x hT).1.1
          exact ⟨(hPiff _).2 ⟨T.1, (T.2.2.2.2.2.2.2.2.2.1 β J βJ).2 hI⟩, T.2.1,
            ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hlat).2.2 h hh, fun y hy => hm_inv h hh x y hx hy⟩)
        (fun x hx => by
          have hb := GlobalTheory.HL.TermBasic.term_basic L r k S d x ((hPiff x).1 hx).1
          have A := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hb.1.1
          have W := (GlobalTheory.HL.WitIndep.witness_independence L r k S d x _ _ hb.2.1).2.2.2.2
          obtain ⟨h1, h2, h3, h4⟩ := hm x hx
          exact ⟨A.1, A.2.1, W, h1, h2, h3, h4⟩)
        hPfin
      rw [hamp]
      have h2 : 2 * (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ≤
          7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by linarith
      exact bound.trans (mul_le_mul_of_nonneg_right h2 hsum0)
    · have hempty : ∀ Λ, ¬ P Λ := by
        intro Λ hΛ
        obtain ⟨hT, hTB, -, hle, ⟨y, hy, hyJ⟩, -⟩ := (hPiff Λ).1 hΛ
        by_cases hJr : r < J
        · have := hTB.2.1 y hy
          omega
        · have hJ0 : J = 0 := by omega
          apply hTB.1
          refine le_antisymm (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1 fun z hz => ?_
          refine ((_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.2.2.1 z hz).1 ?_
          have := hle z hz
          omega
      rw [hamp]
      simp [hempty]
  rw [hmass, ← ENNReal.ofReal_mul (by linarith)]
  exact ENNReal.ofReal_le_ofReal key

end GlobalTheory.HL.AmpCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents
section
open NumberField Formalism.HermitianLattices.Ext.L3

namespace GlobalTheory.Mass


open NumberField in
theorem _root_.GlobalTheory.Mass.binary_hermitian_represents : _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram := by
  unfold _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram
  intro K _ _ _ hK a b n ha hb hn hpa hpb hpn
  obtain ⟨w, hw0, hw⟩ := _root_.Formalism.HermitianLattices.Ext.L3.exists_skew hK
  have memF : ∀ x : K, star x = x → x ∈ _root_.Formalism.HermitianLattices.Ext.L3.cmF K := fun x hx => (_root_.Formalism.HermitianLattices.Ext.L3.mem_cmF_iff K x).2 hx
  obtain ⟨ψ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ne_of_pos : ∀ x : K, _root_.Formalism.HermitianLattices.Ext.L3.TotPos x → x ≠ 0 := by
    intro x hx h
    have := hx ψ₀
    simp [h] at this
  let a' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨a, memF a ha⟩
  let b' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨b, memF b hb⟩
  let n' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨n, memF n hn⟩
  let δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨w * w, memF _ (by rw [star_mul, hw]; ring)⟩
  have hnegδ : _root_.Formalism.HermitianLattices.Ext.L3.TotPos ((-δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K) : K) := by
    unfold _root_.Formalism.HermitianLattices.Ext.L3.TotPos
    intro ψ
    have h1 : ψ (star w) = (starRingEnd ℂ) (ψ w) := hK.2.1 ψ w
    rw [hw, map_neg] at h1
    have hre : (ψ w).re = 0 := by
      have := congrArg Complex.re h1
      simp at this
      linarith
    have hne : ψ w ≠ 0 := (map_ne_zero ψ).2 hw0
    have him : (ψ w).im ≠ 0 := by
      intro him
      exact hne (Complex.ext hre him)
    simp [δ, Complex.mul_re, hre]
    positivity
  have hδneg : ∀ φ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K →+* ℝ, φ δ < 0 := by
    intro φ
    have := (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK (-δ)).1 hnegδ φ
    simpa using this
  have ha' : a' ≠ 0 := fun h => ne_of_pos a hpa (congrArg Subtype.val h)
  have hb' : b' ≠ 0 := fun h => ne_of_pos b hpb (congrArg Subtype.val h)
  have hn' : n' ≠ 0 := fun h => ne_of_pos n hpn (congrArg Subtype.val h)
  have hδ0 : δ ≠ 0 := fun h => hw0 (mul_self_eq_zero.1 (congrArg Subtype.val h))
  let c : Fin 5 → _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ![a', -(a' * δ), b', -(b' * δ), -n']
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, ha', hb', hn', hδ0]
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt
    (_root_.Formalism.HermitianLattices.Ext.L3.cmF K) c (by simp) hc (by
      intro σ
      refine ⟨4, 0, ?_, ?_⟩
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK n').1 hpn σ
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK a').1 hpa σ)
  obtain ⟨y, hy4, hy⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_zero_coord_ne_zero hc hx0 hx 4
  have h4 : (y 4 : K) ≠ 0 := fun h => hy4 (Subtype.ext h)
  have hy' := congrArg (fun z : _root_.Formalism.HermitianLattices.Ext.L3.cmF K => (z : K)) hy
  simp [Fin.sum_univ_five, c, a', b', n', δ] at hy'
  refine ⟨((y 0 : K) + (y 1 : K) * w) / (y 4 : K), ((y 2 : K) + (y 3 : K) * w) / (y 4 : K), ?_⟩
  simp only [star_div₀, star_add, star_mul, _root_.Formalism.HermitianLattices.Ext.L3.star_coe_cmF, hw]
  field_simp
  linear_combination hy'

end GlobalTheory.Mass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricRealisationOfSublattice
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.SubReal

theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  rw [Complex.ofReal_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem cnorm_mulVec_isometry {m k : Type} [Fintype m] [Fintype k] [DecidableEq k]
    (P : Matrix m k ℂ) (h : Pᴴ * P = 1) (u : k → ℂ) :
    cnorm (P *ᵥ u) = cnorm u := by
  have hsum : (∑ i, ‖(P *ᵥ u) i‖ ^ 2 : ℝ) = ∑ i, ‖u i‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      h, Matrix.vecMul_one]
  unfold cnorm
  rw [hsum]

theorem exists_isometry_factor {n j : ℕ} (Y : Matrix (Fin n) (Fin j) ℂ)
    (L : Matrix (Fin j) (Fin n) ℂ) (hL : L * Y = 1) :
    ∃ (Z : Matrix (Fin j) (Fin j) ℂ) (P : Matrix (Fin n) (Fin j) ℂ),
      IsUnit Z.det ∧ Pᴴ * P = 1 ∧ Y = P * Z⁻¹ := by
  classical
  have hG0 : (0 : Matrix (Fin j) (Fin j) ℂ) ≤ Yᴴ * Y := (Matrix.posSemidef_conjTranspose_mul_self Y).nonneg
  obtain ⟨S, hSS, hSh⟩ : ∃ S : Matrix (Fin j) (Fin j) ℂ, S * S = Yᴴ * Y ∧ Sᴴ = S :=
    ⟨CFC.sqrt (Yᴴ * Y), CFC.sqrt_mul_sqrt_self _ hG0, (CFC.sqrt_nonneg (Yᴴ * Y)).isSelfAdjoint⟩
  have hker : ∀ x : Fin j → ℂ, (Yᴴ * Y) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hYx : Y *ᵥ x = 0 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero Y x).mp hx
    have hback : L *ᵥ (Y *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
    rw [← hback, hYx, Matrix.mulVec_zero]
  have hGu : IsUnit (Yᴴ * Y).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv (hker v hv0)
  have hSu : IsUnit S.det := by
    have h2 : IsUnit (S * S).det := by rw [hSS]; exact hGu
    rw [Matrix.det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨S⁻¹, Y * S⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]
    exact hSu.ringInverse
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hSh, Matrix.mul_assoc,
      ← Matrix.mul_assoc Yᴴ, ← hSS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hSu]
  · rw [Matrix.nonsing_inv_nonsing_inv _ hSu, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu,
      Matrix.mul_one]

theorem fcoord_std {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (x : Fin d → K) :
    fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold fcoord vecAt
  simp only [Pi.basisFun_repr]

end GlobalTheory.SubReal


open GlobalTheory.SubReal in
theorem GlobalTheory.exists_isometric_realisation_of_sublattice : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  intro K _ _ _ _ n X R hX hR
  classical
  let bS := Module.finBasis K (Submodule.span K (R : Set (Fin n → K)))
  let ψ : (Fin (Module.finrank K (Submodule.span K (R : Set (Fin n → K)))) → K) →ₗ[K] (Fin n → K) :=
    (Submodule.span K (R : Set (Fin n → K))).subtype ∘ₗ bS.equivFun.symm.toLinearMap
  have hinj : Function.Injective ψ :=
    (Submodule.injective_subtype _).comp bS.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ψ (LinearMap.ker_eq_bot.mpr hinj)
  have hgψ : ∀ y, g (ψ y) = y := fun y => LinearMap.congr_fun hg y
  have hψS : ∀ y, ψ y ∈ Submodule.span K (R : Set (Fin n → K)) := fun y => Submodule.coe_mem _
  have hψg : ∀ r ∈ Submodule.span K (R : Set (Fin n → K)), ψ (g r) = r := by
    intro r hr
    obtain ⟨y, rfl⟩ : ∃ y, ψ y = r := ⟨bS.equivFun ⟨r, hr⟩, by simp [ψ]⟩
    rw [hgψ]
  have hψR : ∀ r ∈ R, ψ (g r) = r := fun r hr => hψg r (Submodule.subset_span hr)
  have hi : ∀ y, LinearMap.toMatrix' ψ *ᵥ y = ψ y := fun y => LinearMap.toMatrix'_mulVec ψ y
  have hLi : LinearMap.toMatrix' g * LinearMap.toMatrix' ψ = 1 := by
    rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hLY : ∀ w : InfinitePlace K,
      ((LinearMap.toMatrix' g).map w.embedding * X w) *
        ((X w)⁻¹ * (LinearMap.toMatrix' ψ).map w.embedding) = 1 := by
    intro w
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (X w), Matrix.mul_nonsing_inv _ (hX w), Matrix.one_mul,
      ← Matrix.map_mul, hLi, Matrix.map_one _ (map_zero _) (map_one _)]
  choose Z P hZ hP hY using fun w => exists_isometry_factor _ _ (hLY w)
  have hmap : (R.map (g.restrictScalars (𝓞 K))).map (ψ.restrictScalars (𝓞 K)) = R := by
    ext r
    constructor
    · rintro ⟨y, ⟨r', hr', rfl⟩, rfl⟩
      simpa [hψR r' hr'] using hr'
    · intro hr
      exact ⟨g r, ⟨r, hr, rfl⟩, hψR r hr⟩
  have hnorm : ∀ (v : InfinitePlace K) (x : Fin (Module.finrank K (Submodule.span K (R : Set (Fin n → K)))) → K),
      normAt (Pi.basisFun K (Fin n)) X v (ψ x) = normAt (Pi.basisFun K _) Z v x := by
    intro v x
    unfold normAt
    rw [fcoord_std, fcoord_std]
    have hcomp : (fun k => v.embedding (ψ x k)) =
        (LinearMap.toMatrix' ψ).map v.embedding *ᵥ fun k => v.embedding (x k) := by
      funext k
      rw [← hi x, RingHom.map_mulVec]
      rfl
    rw [hcomp, Matrix.mulVec_mulVec, hY v, ← Matrix.mulVec_mulVec, cnorm_mulVec_isometry _ (hP v)]
  have hRR := (Formalism.HN.rerealize K _ _ (Fin n → K) (Fin n) (Pi.basisFun K _) Z (Pi.basisFun K (Fin n)) X ψ
    hZ hX hinj hnorm (R.map (g.restrictScalars (𝓞 K))) (hR.map _)).2.2.2.2.2.2
  refine ⟨Module.finrank K (Submodule.span K (R : Set (Fin n → K))), LinearMap.toMatrix' ψ, Z, P,
    R.map (g.restrictScalars (𝓞 K)), rfl, hZ, hP, hY, hR.map _, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, eq_top_iff]
    intro y _
    exact ⟨ψ y, hψS y, hgψ y⟩
  · rintro y ⟨r, hr, rfl⟩
    rw [hi]
    simpa [hψR r hr] using hr
  · intro r hr
    exact ⟨g r, ⟨r, hr, rfl⟩, by rw [hi]; exact hψR r hr⟩
  · rw [← hRR, hmap]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapCompNegStatement
section
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) → ∀ v : V, GlobalTheory.RowStab.gen H J e ρ c (GlobalTheory.RowStab.gen H J e (-ρ) c' v) = v := by
  first | exact @GlobalTheory.RowStab.gen_comp_gen_neg | exact GlobalTheory.RowStab.gen_comp_gen_neg | (intros; apply GlobalTheory.RowStab.gen_comp_gen_neg <;> assumption)
end

