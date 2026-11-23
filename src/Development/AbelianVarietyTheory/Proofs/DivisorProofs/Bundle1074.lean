module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelHolomorphicOverReflexField
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨hA, q, hq, hS⟩ := h
  obtain ⟨hA', q', hq', hS'⟩ := h'
  have hqA : StrictAnti q := fun a b hab => by
    have := hA hab; rw [hq, hq] at this; exact_mod_cast this
  have hqA' : StrictAnti q' := fun a b hab => by
    have := hA' hab; rw [hq', hq'] at this; exact_mod_cast this
  have himg : Finset.univ.image q = Finset.univ.image q' := by
    have e := congrArg (Finset.image Prod.fst) (hS.symm.trans hS')
    simpa [Finset.image_image, Function.comp_def] using e
  have hr : Set.range q = Set.range q' := by
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) himg
    simpa [Finset.coe_image] using this
  have hqq : q = q' := (StrictAnti.range_inj hqA hqA').1 hr
  subst hqq
  refine ⟨funext fun a => by rw [hq, hq'], funext fun a => ?_⟩
  have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [hS'] at hm
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hm
  have hb1 : b = a := hqA.injective (congrArg Prod.fst hb)
  subst hb1
  exact (congrArg Prod.snd hb).symm

theorem parAt_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    parAt (Wc D i) σ ρ = parAt (Wc D i) (sg0 D A) (lab σ ρ) := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
    fun τ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hl := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  unfold parAt kapAt
  rw [if_pos hl, hs, GlobalTheory.ThetaFiresProbe.lab_fixed, if_pos (GlobalTheory.ThetaFiresProbe.labE_fixed _), hsig ρ, hsig (lab σ ρ)]

theorem model_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    (R.MW i σ).lam ρ = (R.MW i (sg0 D A)).lam (lab σ ρ) ∧ (R.MW i σ).ε ρ = (R.MW i (sg0 D A)).ε (lab σ ρ) := by
  have h1 := (R.MW i σ).enum ρ
  rw [parAt_overK R i σ hK ρ] at h1
  exact isEnum_unique h1 ((R.MW i (sg0 D A)).enum (lab σ ρ))

theorem holShape_overK : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F →
    ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i σ s hE
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hE.2
  obtain ⟨hH, w0, hw0⟩ := holShape_fixed D G Pl0 T A Ks R hc.models.order i
  have hm := model_overK R i σ hK
  refine ⟨fun ρ => ?_, fun ρ c => w0 (lab σ ρ) c, fun ρ c => ?_⟩
  · have h := hH (lab σ ρ)
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h
  · have h := hw0 (lab σ ρ) c
    unfold extWt at h ⊢
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelParameterDecreasingHalfIntegralWidth
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ParWidth

theorem mem_holPar_kapW {Rk : Ranks} (h : HCParam Rk) (p q : ℕ) (hpq : Odd (p + q)) {x : ℚ} {b : Bool}
    (hx : (x, b) ∈ Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    ∃ n < p + q, x = Formalism.L2.NTheta.lamAt h n := by
  unfold Formalism.L2.NTheta.holPar at hx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx
  have e := Formalism.L2.NTheta.holEnt_kapW h p q hpq a
  have hx' : x = Formalism.L2.NTheta.holEnt p q (Formalism.L2.NTheta.kapW h p q) a := (congrArg Prod.fst ha).symm
  rcases a with i | c
  · exact ⟨i, by omega, hx'.trans (by simpa using e)⟩
  · exact ⟨p + c, by omega, hx'.trans (by simpa using e)⟩

theorem lamAt_anti {Rk : Ranks} (h : HCParam Rk) {n n' : ℕ} (hnn : n ≤ n') (hn : n' < Rk.r) :
    Formalism.L2.NTheta.lamAt h n' ≤ Formalism.L2.NTheta.lamAt h n := by
  have mono : ∀ d : ℕ, n + d < Rk.r → Formalism.L2.NTheta.lamAt h (n + d) ≤ Formalism.L2.NTheta.lamAt h n := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (n + d) (by omega)).le.trans (ih (by omega))
  have := mono (n' - n) (by omega)
  rwa [show n + (n' - n) = n' by omega] at this

theorem lamAt_b {Rk : Ranks} (h : HCParam Rk) (c : ℕ) (hc : c < Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

theorem le_toNat_floor (x : ℚ) : x ≤ ((⌊x⌋.toNat : ℕ) : ℚ) + 1 := by
  have h1 := Int.lt_floor_add_one x
  have h2 : ((⌊x⌋ : ℤ) : ℚ) ≤ (((⌊x⌋.toNat : ℕ) : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
  rw [Int.cast_natCast] at h2
  linarith

end GlobalTheory.LowRow.ParWidth

namespace GlobalTheory.LowRow.ParWidth

theorem width_le (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) 0 - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) (D.R.r - 1) ≤
      (degAt D i σ ρ : ℚ) + D.R.nV + 1 := by
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hp : pW D i ρ = D.R.k + i := by simp only [pW, hsig, Ranks.sigW]; omega
  have hq : qW D i ρ = D.R.m - (i + 1) := by simp only [qW, hsig, Ranks.sigW]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  set h := D.hc (lab σ ρ) with hh
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hnV : (D.R.nV : ℚ) = (D.R.k : ℚ) + D.R.m - 1 + D.R.t := by
    simp only [Ranks.nV, Ranks.r]; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring

  have hP0 : (aPlAt D i σ ρ 0 : ℚ) + 1 ≥
      Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - (0 + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    have := le_toNat_floor (Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - ((0 : ℕ) + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2)
    unfold aPlAt aPl
    rw [hp, if_pos (by omega)]
    simpa using this
  have hdeg : (aPlAt D i σ ρ 0 : ℚ) + (if 0 < qW D i ρ then (aMiAt D i σ ρ 0 : ℚ) else 0) ≤ degAt D i σ ρ := by
    have e1 : aPlAt D i σ ρ 0 ≤ ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n :=
      Finset.single_le_sum (f := aPlAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    have e2 : (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) ≤ ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n := by
      split_ifs with hq0
      · exact Finset.single_le_sum (f := aMiAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hq0)
      · exact Nat.zero_le _
    have e3 := Nat.add_le_add e1 e2
    unfold degAt
    have : ((aPlAt D i σ ρ 0 + (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) : ℕ) : ℚ) ≤
        ((∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n : ℕ) : ℚ) := by
      exact_mod_cast e3
    push_cast at this
    split_ifs at this ⊢ <;> simpa using this
  by_cases hq0 : (i : ℕ) + 1 < D.R.m
  · have hqpos : 0 < qW D i ρ := by rw [hq]; omega
    rw [if_pos hqpos] at hdeg
    have hM0 : (aMiAt D i σ ρ 0 : ℚ) + 1 ≥
        -(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
      have := le_toNat_floor (-(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2))
      unfold aMiAt aMi
      rw [hp, hq, if_pos (by omega), show D.R.k + ↑i + (D.R.m - (↑i + 1) - 0) - 1 = D.R.r - 1 by omega]
      simpa using this
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    have c2 : (((D.R.m - (i + 1) : ℕ) : ℚ)) = D.R.m - (i : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [c1] at hP0
    rw [c2] at hM0
    rw [hnV]
    linarith
  · have him : (i : ℕ) = D.R.m - 1 := by omega
    rw [if_neg (by rw [hq]; omega), add_zero] at hdeg
    have hb : Formalism.L2.NTheta.lamAt h (D.R.r - 1) = -h.b i := by
      rw [show D.R.r - 1 = D.R.k - 1 + (i : ℕ) by omega, lamAt_b h i i.2]
    have hg := h.gap_be i
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    rw [c1] at hP0
    have hmi : (i : ℚ) = D.R.m - 1 := by
      rw [him, Nat.cast_sub (by omega)]; simp
    rw [hnV, hb]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith

end GlobalTheory.LowRow.ParWidth


open GlobalTheory.LowRow.ParWidth in
theorem GlobalTheory.LowRow.lam_par_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _hC i σ s hσ ρ
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hσ.2
  have hat : labE σ (lab σ ρ) = tauE D ρ := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  obtain ⟨hanti, qv, hqv, hS⟩ := (R.MW i σ).enum ρ
  have hpar : parAt (Wc D i) σ ρ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) := if_pos hat
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hr : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    rw [hsig]; simp only [Ranks.sigW, Ranks.r]; omega
  have hrodd : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hodd : Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := hr ▸ hrodd
  have hent : ∀ a, ∃ n < D.R.r, (R.MW i σ).lam ρ a = ((Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n : ℚ) : ℝ) := by
    intro a
    have hmem : (qv a, (R.MW i σ).ε ρ a) ∈ parAt (Wc D i) σ ρ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hpar] at hmem
    obtain ⟨n, hn, e⟩ := mem_holPar_kapW _ _ _ hodd hmem
    exact ⟨n, hr ▸ hn, by rw [hqv a, e]⟩
  have hrank : (Wc D i).rank = D.R.r := by
    rw [← hr]; exact (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _).symm
  refine ⟨hanti, fun a => ?_, fun a b => ?_⟩
  · obtain ⟨n, -, e⟩ := hent a
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) n
    obtain ⟨w, hw⟩ := hrodd
    refine ⟨z - w, ?_⟩
    rw [e, hz, hrank, hw]
    push_cast
    ring
  · obtain ⟨n, hn, ea⟩ := hent a
    obtain ⟨n', hn', eb⟩ := hent b
    have hW := width_le D i σ ρ
    have l1 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n) hn
    have l2 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n') hn'
    have u1 := lamAt_anti (D.hc (lab σ ρ)) (show n ≤ D.R.r - 1 by omega) (by omega)
    have u2 := lamAt_anti (D.hc (lab σ ρ)) (show n' ≤ D.R.r - 1 by omega) (by omega)
    have key : |Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n'| ≤
        (degAt D i σ ρ : ℚ) + D.R.nV + 3 := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    rw [ea, eb, ← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRank
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRowAnti

variable {D : D7}

theorem lam_step (τ : D.what₂.Tau) (n : ℕ) (hn : n + 1 < D.R.r) :
    Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1) + 1 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n := by
  have h := Formalism.L2.NTheta.lamAt_lt (D.hc τ) n hn
  obtain ⟨a, ha⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (n + 1)
  obtain ⟨b, hb⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  rw [ha, hb] at h ⊢
  have : a < b := by exact_mod_cast h
  have : a + 1 ≤ b := this
  exact_mod_cast this

theorem pq_eq (i : Fin D.R.m) (ρ : D.what₂.Tau) : pW D i ρ + qW D i ρ = D.R.r := by
  have h := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2] at h
  exact h

theorem aPl_anti (i : Fin D.R.m) (p : ℕ) (τ : D.what₂.Tau) (hp : p ≤ D.R.r) : Antitone (aPl D i p τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aPl
  by_cases h1 : n + 1 < p
  · rw [if_pos h1, if_pos (by omega : n < p)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have := lam_step τ n (by omega)
    push_cast
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

theorem aMi_anti (i : Fin D.R.m) (p q : ℕ) (τ : D.what₂.Tau) (hpq : p + q = D.R.r) : Antitone (aMi D i p q τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aMi
  by_cases h1 : n + 1 < q
  · rw [if_pos h1, if_pos (by omega : n < q)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have e1 : p + (q - n) - 1 = (p + (q - (n + 1)) - 1) + 1 := by omega
    have := lam_step τ (p + (q - (n + 1)) - 1) (by omega)
    rw [e1]
    have e2 : ((q - n : ℕ) : ℚ) = ((q - (n + 1) : ℕ) : ℚ) + 1 := by
      rw [show q - n = (q - (n + 1)) + 1 by omega]; push_cast; ring
    rw [e2]
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

end GlobalTheory.LowRowAnti

open GlobalTheory.LowRowAnti in
theorem GlobalTheory.LowRow.lift_rows_antitone : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau),
    Antitone (aPlAt D i σ ρ) ∧ Antitone (aMiAt D i σ ρ) ∧ pW D i ρ + qW D i ρ = (Wc D i).rank ∧
      (Wc D i).rank ≤ (Vc D i).rank := by
  intro D i σ ρ
  have hpq := pq_eq (D := D) i ρ
  refine ⟨?_, ?_, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ, ?_⟩
  · exact aPl_anti i _ _ (by omega)
  · exact aMi_anti i _ _ _ hpq
  · rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact r_le_V i
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.VB

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.coe_lt_top n))
    | coe m =>
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem suppDim_lt_of_genRank_eq_zero {n : ℕ} (hd : topologicalKrullDim Z ≤ (n : WithBot ℕ∞))
    {F : Z.Modules} [QCoh.IsFiniteQC F] (h : genRank F = 0) : QCoh.suppDim F < (n : WithBot ℕ∞) := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z := by
    rw [← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact lt_of_add_one_le_natCast (this.trans hd)

variable {κ : Type} [Field κ] [Algebra κ Γ(Z, ⊤)]

theorem interNum_of_genRank_eq (hp : IsProjOver (strHom κ (X := Z))) {ι : Type} [Fintype ι]
    (hd : topologicalKrullDim Z ≤ (Fintype.card ι : ℕ)) {P : ι → LB Z} (hP : ∀ i, (P i).IsLB)
    (r : ℕ) : ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    rw [interNum_eq_zero_of_isProjOver hf G hp (suppDim_lt_of_genRank_eq_zero hd h) hP]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := Fintype.card ι) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist le_rfl hP hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hP h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

end GlobalTheory.VB

theorem GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver : ∀ (κ : Type) [Field κ] (Z : Scheme.{0})
    [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → ∀ (ι : Type) [Fintype ι],
    topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G]
    (P : ι → LB Z), (∀ i, (P i).IsLB) →
    interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P :=
  fun _ _ _ _ _ hp _ _ hd G _ _ hP => GlobalTheory.VB.interNum_of_genRank_eq hp hd hP _ G rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfHeisenbergInvariantNorms
section
noncomputable section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem lintegral_rhoBF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ) (u : WOF F E nS nT)
    (G : BBF σ JS JT ξ₀ ψ) :
    ∫⁻ w in 𝓕, ‖(rhoBF σ JS JT ξ₀ ψ hψ u G).1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖G.1 w‖ₑ ^ 2 ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have key : ∀ H : BBF σ JS JT ξ₀ ψ, ∫⁻ w in 𝓕, ‖H.1 w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ w in 𝓕, ‖H.1 w‖ ^ 2 ∂μ) := by
    intro H
    rw [ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall fun w => by positivity)]
    · simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    · exact Integrable.of_bound (H.1.continuous.norm.pow 2).aestronglyMeasurable (‖H‖ ^ 2)
        (Filter.Eventually.of_forall fun w => by
          rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_ev_le w H) 2)
  rw [key, key, coe_rhoBF]
  simp only [norm_heisOF hψ]
  rw [GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕 (fun w => ‖G.1 w‖ ^ 2)
    (fun γ hγ w => by rw [BBF_norm_periodic hψ G γ hγ]) u]

theorem lintegral_eq_of_normsF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ), ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f f' : BBF σ JS JT ξ₀ ψ,
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BBF σ JS JT ξ₀ ψ →L[ℂ] H),
        (∀ w g, ‖Φ (rhoBF σ JS JT ξ₀ ψ hψ w g)‖ = ‖Φ g‖) → ‖Φ f'‖ = ‖Φ f‖) →
      ∫⁻ w in 𝓕, ‖f'.1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f.1 w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ μ 𝓕 hμ h𝓕 f f' hn
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hlt := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  rw [lintegral_norm_sq_eq_toL2, lintegral_norm_sq_eq_toL2, enorm_sq_inj]
  refine hn _ (toL2 _ _ (μ.restrict 𝓕)) fun v G => ?_
  rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
  exact lintegral_rhoBF hψ μ 𝓕 hμ h𝓕 _ G

end GlobalTheory.RealWeilF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFiniteFrameLatticeFormsStatement
section
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_frameLatticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  first | exact @GlobalTheory.ExpFrame.Frame.finite_latticeForms | exact GlobalTheory.ExpFrame.Frame.finite_latticeForms | (intros; apply GlobalTheory.ExpFrame.Frame.finite_latticeForms <;> assumption)
end

