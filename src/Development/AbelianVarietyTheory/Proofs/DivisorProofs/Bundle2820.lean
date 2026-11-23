module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AutomorphicArithmetic.LocalEmbeddings.StairDepth
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorIdempotentSumVacuumNormalisedSum
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjHalfCosetRepsScalarDilation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDepthConditionsAwayFromTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

private theorem val_nat_le_unif (w : Pl D.host.E) {p : ℕ} (hp : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    valuation (Kw w) (p : Kw w) ≤ valuation (Kw w) (unifAt w : Kw w) := by
  rw [isUnif_unifAt w]
  refine le_uniformizer_iff.2 ((Comparison₂.vEq w).lt_one_iff_lt_one.2 ?_)
  rw [← map_natCast (algebraMap D.host.E (Kw w)), Good.valued_alg, ← map_natCast (algebraMap (𝓞 D.host.E) D.host.E)]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hp

private theorem exists_depth (P : Finset (Pl D.host.E)) (n : Pl D.host.E → ℕ) : ∃ K : ℕ, 0 < K ∧
    (∀ l B : ℕ, l.Prime → (∀ w ∈ P, (l : 𝓞 D.host.E) ∈ w.asIdeal → n w ≤ B) → padicValNat l K ≤ B) ∧
    ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w) := by
  classical
  let N : ℕ → ℕ := fun p => (P.filter fun w => Formalism.EigenvalueLevelCeiling.plc w = p).sup n
  have hpr : ∀ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p.Prime := fun p hp => by
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
    exact Formalism.EigenvalueLevelCeiling.plc_prime w
  refine ⟨∏ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p ^ N p, Finset.prod_pos fun p hp => pow_pos (hpr p hp).pos _, fun l B hl hB => ?_,
    fun w hw => ?_⟩
  · have hN : N l ≤ B := Finset.sup_le fun w hw => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact hB w h1 (h2 ▸ Formalism.EigenvalueLevelCeiling.plc_mem w)
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ hl, Nat.factorization_prod fun p hp => pow_ne_zero _ (hpr p hp).ne_zero,
      Finset.sum_congr rfl fun p hp => (hpr p hp).factorization_pow, Finset.sum_apply']
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs
    · exact hN
    · exact Nat.zero_le _
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p => p ^ N p) (Finset.mem_image_of_mem Formalism.EigenvalueLevelCeiling.plc hw)
    have hn : n w ≤ N (Formalism.EigenvalueLevelCeiling.plc w) := Finset.le_sup (f := n) (Finset.mem_filter.2 ⟨hw, rfl⟩)
    have hc1 : valuation (Kw w) (c : Kw w) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (natCast_mem _ c)
    rw [hc, Nat.cast_mul, map_mul]
    refine (mul_le_mul' ?_ hc1).trans ((mul_one _).le.trans (val_pow_anti (isUnif_unifAt w) hn))
    rw [Nat.cast_pow, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_left' (val_nat_le_unif w (Formalism.EigenvalueLevelCeiling.plc_mem w)) _

private theorem frAt_nsmul (w : Pl D.host.E) {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (K : ℕ)
    (x : Mx D b a) (r : Fin b) (s : Fin a) : frAt w β' β (K • x) r s = (K : Kw w) * frAt w β' β x r s := by
  induction K with
  | zero => simp [frAt, Comparison₂.fr]
  | succ K ih => rw [succ_nsmul, frAt_add, Matrix.add_apply, ih, Nat.cast_succ, add_mul, one_mul]

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
  {P : Finset (Pl D.host.E)} {n : Pl D.host.E → ℕ} {K : ℕ}

private theorem nsmul_mem_lat (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {e : AE D} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)
    (hK : ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w)) {x : WO S T}
    (hx : IsHalf e x)
    (h : ∀ w ∈ P, ∀ r s, valuation (Kw w) (frAt w βT βS x r s) ≤ valuation (Kw w) (((unifAt w ^ n w)⁻¹ : (Kw w)ˣ) : Kw w)) :
    K • x ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  have hx' : IsHalf e (K • x) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he hAA hx' (GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hx' fun w hw r s => ?_)
  refine (Comparison₂.vEq w).le_one_iff_le_one.1 ?_
  change valuation (Kw w) (frAt w βT βS (K • x) r s) ≤ 1
  rw [frAt_nsmul, map_mul]
  refine (mul_le_mul' (hK w hw) (h w hw r s)).trans_eq ?_
  rw [← map_mul, Units.mul_inv, map_one]

private theorem nsmul_small (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {w : Pl D.host.E}
    (hAA : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) {c : ValueGroupWithZero (Kw w)}
    (hK : valuation (Kw w) (K : Kw w) ≤ c) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (r : Fin T.rank) (s : Fin S.rank) :
    valuation (Kw w) (frAt w βT βS (K • u) r s) ≤ c := by
  have h1 : valuation (Kw w) (frAt w βT βS u r s) ≤ 1 :=
    (Comparison₂.vEq w).le_one_iff_le_one.2 (GlobalTheory.RowLatChi.int_of_mem_latO hS hβS hβT w hAA hu r s)
  rw [frAt_nsmul, map_mul]
  exact (mul_le_mul' hK h1).trans_eq (mul_one _)

end Lat

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

private theorem isSBArgs_of_mem_good_places {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    IsSBArgs (locGrid G t P) (unifAt P) (depthAt G P) (S.term t Φ β ⟨P, hl⟩).datum := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by simpa [Places.W0] using hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT ⊢
  have hKO : ∀ j, 0 < j → j < (locGrid G t P).m → givenLevel G t P ((locGrid G t P).m, j) = KO (Kw P) _ := by
    intro j hj _
    have key : ∀ i, 0 < i → givenLevel G t P (i, j) = KO _ _ := by
      rintro (_ | i) hi
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rfl
    exact key _ hm
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT hKO
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have h := GlobalTheory.StairDepth.isSBArgs_stair hs (psiAt W P) (unitVol P) hm2 (isUnif_unifAt P) h00.cond hT (keepAt G P)
  rw [← GlobalTheory.StairDepth.elt_eq hs (givenLevel G t P) _ _ hm2, ← hβ'] at h
  exact h

private theorem depthOK_of {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (β : CosFam G t)
    {n : Pl D.host.E → ℕ} (hF : ∀ w : locPl G t, IsSBArgs (locGrid G t w.1) (unifAt w.1) (n w.1) (S.term t Φ β w).datum)
    {K : ℕ} (hK : ∀ w ∈ locPl G t, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w))
    {e : AE D} (he : IsIdemSum e (locPl G t)) : DepthOK S t Φ β e K := by
  have hAA : ∀ w ∈ locPl G t, (∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1 := by
    intro w hw
    have hb := Good.badInt_notMem hL hde hc hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [Good.valued_alg]
      exact Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [Good.valued_alg]
      exact Good.valuation_nat hN
  have sT : ∀ j : Fin D.R.m, IsSelfDualC (G.pS (.top t j)) (G.latS (.top t j)) := fun j =>
    (G.isV (X := .top j) j.2.le fun _ e => by cases e).sd
  have sC : ∀ i : Fin D.R.m, IsSelfDualC (G.pS (.chi i D.R.m : Pair T)) (G.latS (.chi i D.R.m : Pair T)) := fun i =>
    isSelfDualC_neg (G.isV (X := .grid (i + 1) D.R.m) ⟨i.2, le_rfl⟩ fun j e => by injection e with h1; omega).sd
  refine ⟨fun x y hx hy hne => ?_, fun x u y v _ _ hu hv => ?_⟩
  · have hw : ∀ w : locPl G t, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0 := fun w h0 =>
      hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
    refine ⟨fun j => nsmul_mem_lat (sT j) (S.βp_is j j.2.le) (S.βp_is (j + 1) j.2) he (fun w hw => (hAA w hw).2) hK (hx j)
        fun w hwP r s => ?_,
      fun i => nsmul_mem_lat (sC i) (S.B.isFrame_β hL i.2 le_rfl) (S.B.isFrame_β hL i.2.le le_rfl) he
        (fun w hw => (hAA w hw).2) hK (hy i) fun w hwP r s => ?_⟩
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).1 j j.2 (Fin.cast (topRank_eq G t w j.2).symm r)
        (Fin.cast (topRank_eq G t w j.2.le).symm s)
      rw [colAt_eq S t w x j.2] at this
      exact this
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).2 i i.2
        (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨i.2.le, le_rfl⟩).symm r)
        (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨i.2, le_rfl⟩).symm s)
      rw [rowAt_eq S t w y i.2] at this
      exact this
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [colAt_add, rowAt_add]
    refine (hF w).per _ _ _ _ (fun j hj r s => ?_) (fun i hi r s => ?_)
    · rw [colAt_eq S t w _ hj]
      exact nsmul_small (sT ⟨j, hj⟩) (S.βp_is j hj.le) (S.βp_is (j + 1) hj) (hAA w.1 w.2).1 (hK w.1 w.2) (hu ⟨j, hj⟩).2 _ _
    · rw [rowAt_eq S t w _ hi]
      exact nsmul_small (sC ⟨i, hi⟩) (S.B.isFrame_β hL hi le_rfl) (S.B.isFrame_β hL hi.le le_rfl) (hAA w.1 w.2).1
        (hK w.1 w.2) (hv ⟨i, hi⟩).2 _ _

private theorem depth_main {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w →
      padicValNat l K ≤ depL G l) ∧ ∀ e, IsIdemSum e (locPl G t) → DepthOK S t Φ β e K := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hSB : ∀ w : Pl D.host.E, ∃ n, (w ∈ G.pl.W0 → n = depthAt G w) ∧ ∀ hw : w ∈ locPl G t,
      IsSBArgs (locGrid G t w) (unifAt w) n (S.term t Φ β ⟨w, hw⟩).datum := fun w => by
    by_cases h0 : w ∈ G.pl.W0
    · exact ⟨_, fun _ => rfl, fun hw => isSBArgs_of_mem_good_places hL S t Φ hde hc h0 hw hβ⟩
    by_cases hw : w ∈ locPl G t
    · have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
      have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
      haveI := (isUnitVol_unitVol w).1
      obtain ⟨n, hn⟩ := exists_isSBArgs_flat (locGrid G t w) one_le_sLen (psiAt W w) (unitVol w) (unifAt w) (depthAt G w)
        (Tflip W S.B t Φ w) (keepAt G w) ((repsAt G t w).elt (β ⟨w, hw⟩)) hm h00.unif h00.cond
        (isTensor_Tflip hL W S.B t Φ hde hc hw)
      exact ⟨n, fun h => absurd h h0, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h h0, fun h => absurd h hw⟩
  choose n hn0 hn using hSB
  obtain ⟨K, hK0, hKl, hK⟩ := exists_depth (locPl G t) n
  refine ⟨K, hK0, fun w l hl hlw hA => hKl l _ hl fun P hP hlP => ?_,
    fun e he => depthOK_of hL S t Φ hde hc β (fun w => hn w.1 w.2) hK he⟩
  have hW : P ∈ G.pl.W0 := by
    rcases Good.locPl_cases hP with ⟨a, b⟩ | ⟨a, -, b⟩
    · rw [b]
      unfold Places.W0
      convert Finset.mem_image_of_mem _ a
    · exact absurd hlw ((hA P b).resolve_left a l hl hlP)
  rw [hn0 P hW]
  exact Finset.le_sup (f := depthAt G) (Finset.mem_filter.2 ⟨hW, hlP⟩)

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.flatTensor_depth_conditions_away_from_twist : BigC fun {D} _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ∀ (t : _) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w → padicValNat l K ≤ depL ch.G l) ∧ ∀ e, IsIdemSum e (locPl ch.G t) → DepthOK ch.S.toGridChoice t Φ β e K := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ t Φ β hβ => ?_⟩⟩⟩
  exact depth_main hS.core.lev ch.S.toGridChoice t Φ (GlobalTheory.RowClaim.Test.pde_ne_q hS) (GlobalTheory.RowClaim.Test.guard hS t) hβ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePart
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.PartFlat

open GlobalTheory.BaseCmp GlobalTheory.OnCmp Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas

theorem idem_mul_of_subset {D : D7} {P Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) (h : P ⊆ Q) : idem Q * idem P = idem P := by
  have k : ∀ l ∈ Q, idemAt l * idem Q = idemAt l := fun l hl =>
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hl
  conv_lhs => rw [show idem P = ∑ PP ∈ P, idemAt PP from rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l hl => by rw [mul_comm, k l (h hl)]

theorem isHalf_mono {D : D7} {m n : ℕ} {a b : AE D} (hab : b * a = a) {u : Mx D m n} (hu : IsHalf a u) : IsHalf b u := by
  intro k l
  rw [← hu k l, ← mul_assoc, hab]

theorem suppAt_mono {D : D7} {V : HSp D} {a b : AE D} (hab : b * a = a) (ha : a * cA D a = 0) (hb : b * cA D b = 0)
    {g : GA D V} (hg : SuppAt a V g) : SuppAt b V g := by
  intro k l
  have hc : cA D b * cA D a = cA D a := by rw [← map_mul, hab]
  have h1 : b * cA D a = 0 := by rw [← hc, ← mul_assoc, hb, zero_mul]
  have h2 : cA D b * a = 0 := by rw [← hab, ← mul_assoc, mul_comm (cA D b), hb, zero_mul]
  have e : (b + cA D b) * (a + cA D a) = a + cA D a := by linear_combination hab + hc + h1 + h2
  rw [← hg k l, ← mul_assoc, e]


open GlobalTheory.ChiUnit GlobalTheory.DilChi in
theorem chi_unitOff_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (i : Fin D.R.m) (t : T0) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eQ : AE D) (heQ : IsIdemSum eQ Q) (ϖ : 𝓞 D.host.E)
    (hϖ0 : (ϖ : D.host.E) ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) (z : GA D (Vc D i))
    (hz : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ))) (x : (AE D)ˣ) (hx : IsDetAt (cA D eQ) (Vc D i) z x) :
    UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  have hchr := hK.chr
  have hfin := hK.fin
  have hpl := fun P (hP : P ∈ Q) => hK.pl P (hQ hP)
  generalize R.xi t = χ at hchr ⊢
  generalize R.xiH t = ξ at hchr hfin
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hs0 with hu
  have hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E) := by
    rw [detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]; rfl
  have hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ →
      ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank := by
    intro c ψ hc
    rw [_root_.GlobalTheory.IdemSumChar.char_eq_prod D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
  have e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [e, hval _ _ (hlev.mu0 i), hval _ _ hchr, hval _ _ hlev.eta]
  have hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2 := fun P hP =>
    ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩
  have hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P) := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hpl P hP
    have hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
      rw [natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr (conjPl P) fun k hk =>
      not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk
  have hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E) := by rw [Formalism.L2.DIV.starO_coe]; rfl
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hfin
  refine unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)
    (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))
  · rw [locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    have h := LR ξ n hnx (conjPl P) u
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr (conjPl P)) (hNc P hP)

theorem splitSet_tuple {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (i : Fin D.R.m) (t : T0) : SplitSet (R.Q t) := by
  obtain ⟨-, e, he, -⟩ := (kerDat_tuple (i := i) hC.lev hC.thP t).vec
  exact SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)

theorem dil_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hQG : QGuard R) (i : Fin D.R.m) (t : T0) (hV : VStd D i) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ) (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ) (heg : IsIdemSum eg R.Pg)
    (heQ : IsIdemSum eQ Q) (hfg : IsTypeVec R i eg fg) (ϖ : 𝓞 D.host.E)
    (hϖ0 : (ϖ : D.host.E) ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) (z : GA D (Vc D i))
    (hz : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ))) :
    SuppAt eQ (Vc D i) z ∧ ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ,
      IsSBHalf eQ (lattice₂ R i) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  have hsp := splitSet_tuple hC i t
  have hsub : idem (R.Q t) * eQ = eQ := by rw [← idem_eq heQ]; exact idem_mul_of_subset hsp hQ
  have hsubc : cA D (idem (R.Q t)) * cA D eQ = cA D eQ := by rw [← map_mul, hsub]
  obtain ⟨hSV, hSW, hθ, hfix0⟩ := _root_.GlobalTheory.KerTypeVec.typeVec_fixed D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ hK ⟨t, subset_rfl⟩ eg
    (idem (R.Q t)) fg heg hsp.isIdemSum hfg
  have hfix : ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) →
      heisO R.ψ (Vc D i) (Wc D i) u fg = fg := fun u hu h =>
    hfix0 u hu (h.imp (isHalf_mono hsub) (isHalf_mono hsubc))
  have hW := hK.weil
  obtain ⟨hsupp, ⟨x, hx⟩, hpull, hsb, hlat⟩ :=
    _root_.GlobalTheory.DilScalar.scalar_dil_facts D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  obtain ⟨Rr, hR1, hR2, hR3, hRc⟩ :=
    _root_.GlobalTheory.ScalarReps.scalar_half_reps D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  have hchi := chi_unitOff_part hC i t Q hQ N hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  refine ⟨hsupp, (((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ), unitOff_mul' hchi hRc, fun Tm hTm Ψ hΨ => ?_⟩
  have hom := _root_.GlobalTheory.SumHecke.om_eq_sum_idemSum D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z x hsupp hx Rr hR1 hR2 hR3
    fg hθ hfix
  have hsum := _root_.GlobalTheory.HeisTranslSum.sum_heisO_base_eq D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z hlat Rr hR1 hR2 hR3 fg Tm hTm
  have hvac : R.ωP i t (z, 1) fg = (((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (actPull (z, (1 : GA D (Wc D i))) (halfInd eQ (latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i)))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_mul, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  have h := _root_.GlobalTheory.PullModelLaw.om_apply_eq_smul_pull D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ fg hθ hfix Tm hTm (z, 1) _ hsb hvac
    Ψ hΨ
  rw [h, hpull Ψ hΨ.1]

theorem lift_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hG : QGuard R) (i : Fin D.R.m) (t : T0) (hV : VStd D i) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ) (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ)
    (hq : IsIdemSum eQ Q) (ϖ : 𝓞 D.host.E) (hϖ0 : ϖ ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) ∧
      ∀ Tm, IsModel R i eQ fg Tm → ∀ φ, ThAt R i (cA D eQ) fg (adjDat R i Q (R.xiR t) (cA D eQ)) φ →
        φ = Tm (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  obtain ⟨Y, a, Gc, hU, hY, hΦ, hS⟩ := _root_.GlobalTheory.LiftFour.datum_conj_half_fourier D G Pl0 T0 A Ks R F hC hG i hV (R.xiR t) Q ⟨t, hQ⟩
    (fun PP hP => kerDat_xiR_ne D G Pl0 T0 A Ks R F hC i _ _ _ _ _ _ hK PP (hQ hP)) N hN hNQ eQ hq ϖ hϖ0 hϖ
  refine ⟨Gc, hU, _root_.GlobalTheory.DilFlat.isSBHalf_dilFlat D G Pl0 T0 A Ks R F hC hG i hV (R.xiR t) Q ⟨t, hQ⟩ eQ hq ϖ hϖ0 hϖ Gc, fun Tm hTm φ hθ => ?_⟩
  have h1 := GlobalTheory.DatumFourier.thetaAt_eq_sum (fun q : Y => q.1) (fun q : Y => a q.1) hθ
    (fun q => by rw [GlobalTheory.LatVac.cA_cA]; exact hY q.1 q.2)
    (fun s => by
      refine (hΦ s).trans ?_
      congr 1; exact (Finset.sum_coe_sort Y fun y => a y * R.ψ (symplO (Vc D i) (Wc D i) s y)).symm)
  have h2 : (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) =
      ∑ y ∈ Y, a y • fun s => halfInd eQ (lattice₂ R i) (s + y) := by
    funext s
    rw [← hS s, Finset.sum_apply]
    rfl
  have hvac : Tm (halfInd eQ (lattice₂ R i)) = fg := by simpa using hTm.vac
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, h2, map_sum, ← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.trans _ (GlobalTheory.isSBHalf_halfInd eQ (lattice₂ R i)) _ (hY q.1 q.2), hvac]

theorem flat_eq_unit_smul_om_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa : Finset (Pl D.host.E)), Sa ⊆ R.Q t → ∀ (eg ea : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt ea (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ h g, ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i Sa (R.xiR t) ea) h → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) g → h = c • R.ωP i t (z⁻¹, 1) g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV Sa hSa eg ea fg heg hea hfg
  obtain ⟨ϖ, hϖ0, hϖ⟩ := GlobalTheory.FlatLift.exists_unif D.host.E Sa
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, -, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i Sa ea hea (ϖ : D.host.E) hϖE
  have hN : GlobalTheory.TwistField.tupPrime R t ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact GlobalTheory.TupDil.card_ne_zero PP
  have hNQ : ∀ PP ∈ Sa, ((GlobalTheory.TwistField.tupPrime R t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ GlobalTheory.TwistField.tupPrime R t :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) (hSa hPP))
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.TupDil.card_mem PP)
  obtain ⟨hsupp, κ, hκ, hact⟩ := dil_part hC hQG i t hV Sa hSa _ hN hNQ eg ea fg heg hea hfg ϖ hϖE hϖ z hzm
  obtain ⟨Gc, hG, hSB, hvP⟩ := lift_part hC hQG i t hV Sa hSa _ hN hNQ ea fg hea ϖ hϖ0 hϖ
  have hsp := splitSet_tuple hC i t
  have hsub : idem (R.Q t) * ea = ea := by rw [← idem_eq hea]; exact idem_mul_of_subset hsp hSa
  have hsi := GlobalTheory.SplitHecke.Stab.suppAt_inv hsupp
  refine ⟨z⁻¹, (κ * Gc)⁻¹, hsi, suppAt_mono hsub hea.2 hsp.isIdemSum.2 hsi, GlobalTheory.FlatLift.unitOff_inv_mul hκ hG,
    fun h g hh hg => ?_⟩
  obtain ⟨Tm, hTm⟩ := hh.1
  have hfT := hh.2 Tm hTm
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    ext a b
    simp only [dil, Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  rw [inv_inv, hvP Tm hTm g hg, hact Tm hTm _ hSB]
  simp only [hcomp]
  have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * flatDat R i Sa (R.xiR t) ea x) = Gc • flatDat R i Sa (R.xiR t) ea := rfl
  rw [hsm, map_smul, ← hfT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.PartFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSizesLogBoundStatement
section
open NumberField GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridSizes_log_bound : ∀ c : ℝ, GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  first | exact @GlobalTheory.SqTop.SizesBound.sizes | exact GlobalTheory.SqTop.SizesBound.sizes | (intros; apply GlobalTheory.SqTop.SizesBound.sizes <;> assumption)
end

