module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0640

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace

variable {D : D7}

theorem isIdemSum_of_isPlc {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) : IsIdemSum p.e {w} :=
  ⟨⟨fun _ => p.e, fun PP h => by rw [Finset.mem_singleton] at h; subst h; exact hp.1, by simp⟩, p.split.2.1⟩


open Classical in
theorem cpt_up {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y]
    [Fintype Y'] [DecidableEq Y'] (FS : Frame (Kw w) S.rank Y') (FT : Frame (Kw w) T.rank Y) (x : Matrix Y Y' (Kw w))
    (Q : Pl D.host.E) :
    (((p.up FS FT x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map (cpt Q) =
      (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Place.up]
  rw [hp.2.2]
  exact (atPl_spec w _).2 Q

theorem up_mem_latO_iff {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    {w : Pl D.host.E} (hw : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {p : Place D (Kw w)} (hp : IsPlc w p)
    {NS NT : ℕ} (hNS : NS = S.rank) (hNT : NT = T.rank) (x : Matrix (Fin NT) (Fin NS) (Kw w)) :
    p.up (frOf hNS βS w) (frOf hNT βT w) x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation (Kw w)) := by
  classical
  subst hNS hNT
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT fS fT {w} p.e (isIdemSum_of_isPlc hp)
    (by simpa using hw) _ (Witness.up_half p _ _ x)]
  set FS := frOf rfl βS w
  set FT := frOf rfl βT w
  have hmap : ∀ Q, (frMapO S T βS βT (p.up FS FT x)).map (cpt (D := D) Q) =
      (loc Q βT⁻¹).val * (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) * (loc Q βS).val := by
    intro Q
    rw [← cpt_up hp FS FT x Q]
    unfold frMapO
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  have hw' : (loc w βT⁻¹).val * (FT.β * x * FS.γ) * (loc w βS).val = x := by
    have e1 : (loc w βT⁻¹).val = FT.γ := by
      rw [map_inv]; exact (Matrix.submatrix_id_id _).symm
    have e2 : (loc w βS).val = FS.β := (Matrix.submatrix_id_id _).symm
    rw [e1, e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  have hval : ∀ Q i j, cpt (D := D) Q (frMapO S T βS βT (p.up FS FT x) i j) = if h : Q = w then h ▸ x i j else 0 := by
    intro Q i j
    have := congrFun (congrFun (hmap Q) i) j
    rw [Matrix.map_apply] at this
    rw [this]
    split_ifs with h
    · subst h
      simp only [Pi.single_eq_same, Matrix.map_id']
      rw [hw']
    · have h0 : (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) = 0 :=
        Matrix.ext fun _ _ => by simp [Pi.single_eq_of_ne h]
      rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
  unfold IsIntM
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · have := (mem_OA_iff _).1 (h a b) w
    rw [hval, dite_eq_left rfl] at this
    rw [Valuation.mem_integer_iff, (Good.isEquiv_Kw w).le_one_iff_le_one]
    exact this
  · refine (mem_OA_iff _).2 fun Q => ?_
    rw [hval]
    split_ifs with hQ
    · subst hQ
      have := h a b
      rw [Valuation.mem_integer_iff, (Good.isEquiv_Kw Q).le_one_iff_le_one] at this
      exact this
    · exact zero_mem _

theorem big_latP : Big fun ch => LatP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  intro t w hw p hp j hj
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hb := Good.badInt_notMem hL hde hc hw
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  refine ⟨fun x => up_mem_latO_iff ?_ ?_ (ch.S.B.isFrame_β hL le_rfl hj.le) (ch.S.B.isFrame_β hL le_rfl hj) hb hp _ _ x,
    fun x => up_mem_latO_iff ?_ ?_ (ch.S.βp_is j hj.le) (ch.S.βp_is (j + 1) hj) hb hp _ _ x⟩
  · exact (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩ fun _ e => by injection e with h; exact hm h).sd
  · exact (ch.G.isV (X := .grid D.R.m (j + 1)) ⟨le_rfl, hj⟩ fun _ e => by injection e with h; exact hm h).sd
  · exact (ch.G.isV (X := .top j) hj.le fun _ e => by cases e).sd
  · exact (ch.G.isV (X := .top (j + 1)) hj fun _ e => by cases e).sd

end GlobalTheory.FlatPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFnEqExtDat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.ChainColRead


set_option maxHeartbeats 1000000 in
theorem givenFn_eq_extDat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ → L.Pg ⊆ G.pl.W0 → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ∀ (Φ : G.Datum) (e e' : AE D), IsIdemSum e (locPl G t) → IsIdemSum e' (L.Pg ∪ L.Q t) → (∀ w ∈ locPl G t, w ∉ L.Pg ∪ L.Q t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ x : WO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)), GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) x = extDat e e' (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) (stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j) (L.chi (j + 1)) (L.xiR t) (L.Q t) e') x := by
  intro D T L sc G B μ₀ hL hPg t j hj1 Φ e e' he he' hAA x
  have hj : j < D.R.m := by omega
  have hsub : L.Pg ∪ L.Q t ⊆ locPl G t := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (hPg h)
    · exact Finset.mem_union_right _ h
  obtain ⟨he₁, -⟩ := _root_.GlobalTheory.IdemSubDiff.isIdemSum_sdiff he he' hsub
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  have h2 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'
  obtain ⟨-, d1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  unfold GlobalTheory.FlipStart.givenFn extDat
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  rw [if_pos hx]
  set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D)) = toEAf D a • N := by
    intro a
    rw [hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]
    congr 1
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
    intro a w hw
    rw [hfr]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]
  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb)
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheory.FunObj.Comparison₂.ixOf G t w ha).symm l),
      fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  rw [Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]
  have hout : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), stepFn L t w j ((N.map (cpt (D := D) w)).submatrix
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) =
      if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    intro w hw
    obtain ⟨-, hw2⟩ := Finset.mem_sdiff.1 hw
    have hP : w ∉ L.Pg := fun h => hw2 (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw2 (Finset.mem_union_right _ h)
    unfold stepFn
    rw [if_neg hP, if_neg hQ, Set.indicator_apply]
    exact if_congr (hsubm w) rfl rfl
  rw [Finset.prod_congr rfl hout, Finset.prod_boole]

  have hx1 : IsHalf (e - e') (x.map ((e - e') * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h2]
  have hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j)) := (colY_isV D T L μ₀ hL j hj.le).sd
  have hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j)) := (colY_isV D T L μ₀ hL (j + 1) hj).sd
  have hAA' : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw =>
    hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2
  have hlat := GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA'
    (x.map ((e - e') * ·)) hx1
  have k1 : x.map ((e - e') * ·) ∈ latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _)
      (G.latT (.mu t 0 j) : Set _) (fun _ => True) ↔
      ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    rw [hlat]
    exact forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]

  have hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      have := (mem_OA_iff _).1 (h i l) w
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul] at this
      exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      by_cases hw : w ∈ L.Pg ∪ L.Q t
      · rw [c1 w hw, one_mul]
        exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [c0 w hw, zero_mul]
        exact zero_mem _
  have hx0 : IsHalf e' (x.map (e' * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h1]
  have hfrO : frMapO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (x.map (e' * ·)) =
      toEAf D e' • N := hfr e'
  have k0 : stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j)
      (L.chi (j + 1)) (L.xiR t) (L.Q t) e' (x.map (e' * ·)) = ∏ w ∈ L.Pg ∪ L.Q t, stepFn L t w j
      ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    unfold stepDat
    rw [hfrO]
    by_cases H : ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
    · rw [if_pos ⟨hx0, hint.2 H⟩]
      have key := GlobalTheory.FunObj.Comparison₂.omega_eq_prod_stepFn G t hL hj ha hb (r_le_colY L j) (toEAf D e' • N) (hint.2 H)
      refine key.trans (Finset.prod_congr rfl fun w hw => ?_)
      have e1 : (toEAf D e' • N).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
        rw [← hfr e']; exact hcomp e' w (c1 w hw)
      rw [e1]
    · rw [if_neg fun h => H (hint.1 h.2)]
      push_neg at H
      obtain ⟨w, hw, hn⟩ := H
      refine (Finset.prod_eq_zero hw ?_).symm
      by_contra h0
      exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))
  rw [k0]
  by_cases hl : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
  · rw [if_pos hl, one_mul, if_pos ⟨hx, k1.2 hl⟩]
  · rw [if_neg hl, zero_mul, if_neg fun h => hl (k1.1 h.2)]

end GlobalTheory.ChainColRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointCarriesLatticeToMovedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.BaseMoveAt

theorem val_of_reGL_eq_inv_diagGL {k : Type} [Field k] {a b : ℕ} (h : a = b) (Y : GL (Fin a) k) (c : Fin b → kˣ)
    (hY : GlobalTheory.StepData.reGL (finCongr h) Y = (GlobalTheory.SplitFlip.diagGL c)⁻¹) :
    (Y : Matrix (Fin a) (Fin a) k) = diagonal fun i => (((c (Fin.cast h i))⁻¹ : kˣ) : k) := by
  subst h
  have e : GlobalTheory.StepData.reGL (finCongr (rfl : a = a)) Y = Y := by
    ext i j
    simp [GlobalTheory.StepData.reGL]
  rw [e] at hY
  rw [hY]
  rfl

theorem submatrix_mulVec_comp {k : Type} [CommRing k] {m n ι : Type} [Fintype n] [Fintype ι] (M : Matrix m n k) (F : ι ≃ n)
    (y : n → k) : (M.submatrix id F) *ᵥ (fun i => y (F i)) = M *ᵥ y := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, id]
  exact Fintype.sum_equiv F _ _ fun _ => rfl

end GlobalTheory.BaseMoveAt

namespace GlobalTheory.BaseMoveAt


set_option maxHeartbeats 1000000 in
theorem lat_moves_at_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → ∀ (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (t : T), t ∈ U → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ b : Pts G, IsBase t S.B b → ∀ w ∈ locPl G t, ∀ p : GlobalTheory.FinPl.SplitPt D (Kw w), Formalism.L2.NTheta.IsIdemAt p.e w → (∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a))) → ∀ x : Fin (G.V (.grid D.R.m 0)).rank → Kw w, ((fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = p.v) ↔ (fun i => p.sec (((Formalism.L2.Theta.mt _ (b 0)).map p.pr *ᵥ x) i)) ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = p.v)) := by
  intro D T L sc μ₀ hL hde G W U S t ht hc b hb w hw p hpw hpr x
  have h0 : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hpr' : ∀ a : D.host.E, p.pr (incA D a) = algebraMap D.host.E (Kw w) a := fun a =>
    (hpr _).trans (GlobalTheory.FunObj.Good.cpt_incA w a)
  have hN : (Formalism.L2.Theta.mt _ (b 0)).map p.pr =
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) := by
    ext i j
    rw [Matrix.map_apply, hpr]
    rfl
  obtain ⟨e, -, -, hloc⟩ := hb.1
  have hl := hloc ⟨w, hw⟩
  simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply] at hl
  have hY := val_of_reGL_eq_inv_diagGL _ _ _ hl
  simp only [Fin.coe_cast, topRank_eq G t w (Nat.zero_le _), map_mul, map_inv] at hY
  have hrow := S.row t ht w hw 0 h0
  unfold GlobalTheory.FunObj.IsSumFrame at hrow
  simp only [if_true] at hrow
  have hΛ : G.Λ (.grid D.R.m 0) = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) :=
    G.sp.colLat D.R.m h0 le_rfl
  have hR : GlobalTheory.RowShape.rowN G 0 = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (GlobalTheory.RowShape.rowId D 0) := by
    simp [GlobalTheory.RowShape.rowN, h0]

  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (G.V (.grid D.R.m 0)).rank → Kw w, δ = fun i =>
      ((((unifAt w) ^ (cosExp G w * (i.1 + 1 - (G.V (.top 0)).rank)))⁻¹ : (Kw w)ˣ) : Kw w) := ⟨_, rfl⟩
  have hcomm : ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) =
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) * diagonal δ := by
    rw [hδ, ← hY, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

  obtain ⟨s, hs⟩ : ∃ s : Fin (D.R.m - 1 - 0) → Kw w, s = fun r =>
      frameSign (Kw w) (D.R.m - 1 - 0) r * ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      M' = (fromCols (frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι) (G.rowDec 0 h0).a).map
        (fun a => p.pr (incA D a)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      Q = fromBlocks ((GlobalTheory.StdFrames.loc w (S.βp 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) 0 0 (diagonal s) := ⟨_, rfl⟩
  have hLb : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)).submatrix id
      (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank) = M' * Q := by
    have hM'' : M' = fromCols ((frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι).map
        (algebraMap D.host.E (Kw w))) ((G.rowDec 0 h0).a.map (algebraMap D.host.E (Kw w))) := by
      rw [hM']
      ext i j
      rcases j with j | j <;> simp [hpr']
    rw [hrow, hM'', hQ, fromCols_mul_fromBlocks, hs]
    simp only [Matrix.mul_zero, add_zero, zero_add]

  have hδl : ∀ i, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inl i)) = 1 := by
    intro i
    have hi : i.1 + 1 - (G.V (.top 0)).rank = 0 := by have := i.2; omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hδr : ∀ r, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inr r)) =
      ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1)))⁻¹ := by
    intro r
    have hi : (G.V (.top 0)).rank + r.1 + 1 - (G.V (.top 0)).rank = r.1 + 1 := by omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hQc : Q * diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) =
      diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) * Q := by
    ext i j
    rw [mul_diagonal, diagonal_mul, hQ]
    rcases i with i | i <;> rcases j with j | j
    · simp [hδl]
    · simp
    · simp
    · by_cases h : i = j
      · subst h; exact mul_comm _ _
      · simp [diagonal_apply, h]
  obtain ⟨z, hx, hNx⟩ : ∃ z, M' *ᵥ z = x ∧
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x =
        M' *ᵥ (diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ z) := by
    obtain ⟨y, hy⟩ : ∃ y : Fin (G.V (.grid D.R.m 0)).rank → Kw w, y = (((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0))⁻¹ : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x := ⟨_, rfl⟩
    have hxy : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ y = x := by
      rw [hy, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨Q *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i), ?_, ?_⟩
    · rw [mulVec_mulVec, ← hLb, submatrix_mulVec_comp, hxy]
    · rw [← hxy, mulVec_mulVec, hcomm, ← mulVec_mulVec, ← submatrix_mulVec_comp _ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank), hLb]
      have hv : (fun i => (diagonal δ *ᵥ y) (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i)) =
          diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i) := by
        funext i
        simp [mulVec_diagonal]
      rw [hv]
      simp only [mulVec_mulVec]
      rw [Matrix.mul_assoc, hQc]

  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have h3 := GlobalTheory.FunObj.ne_zero_of_conj h2.1 h2.2
  have h1' := GlobalTheory.FunObj.ne_zero_of_conj h1.1 h1.2
  have hA := GlobalTheory.FunObj.count_AA_AAbar w (GlobalTheory.FunObj.Good.badInt_notMem hL hde hc hw)
  have hmo : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [GlobalTheory.ChiGrid.Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  have hI1 : ∀ r, stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r ≠ 0 := fun r =>
    mul_ne_zero (pow_ne_zero _ h2.1) (inv_ne_zero (pow_ne_zero _ h3))
  have hn1 : ∀ r : Fin (D.R.m - 1 - 0), FractionalIdeal.count D.host.E w
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r) = ((cosExp G w * (r.1 + 1) : ℕ) : ℤ) := by
    intro r
    rw [GlobalTheory.FunObj.count_stairId h2.1 h3, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar,
      FractionalIdeal.count_mul _ _ h1.1 (inv_ne_zero hmb), FractionalIdeal.count_mul _ _ h1' (inv_ne_zero hmo),
      FractionalIdeal.count_inv, FractionalIdeal.count_inv, GlobalTheory.FunObj.count_modulBar G hw, GlobalTheory.FunObj.count_modul, hA.1, hA.2]
    push_cast
    ring
  have hrId : ∀ r, GlobalTheory.RowShape.rowId D 0 r = stairId D.host.AA D.host.AAbar (D.R.m - 1 - 0) r := by
    intro r
    simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc]
  have hI2 : ∀ r, GlobalTheory.RowShape.rowId D 0 r ≠ 0 := fun r => by
    rw [hrId]
    exact mul_ne_zero (pow_ne_zero _ h1.1) (inv_ne_zero (pow_ne_zero _ h1'))
  have hn2 : ∀ r, FractionalIdeal.count D.host.E w (GlobalTheory.RowShape.rowId D 0 r) = ((0 : ℕ) : ℤ) := by
    intro r
    rw [hrId, GlobalTheory.FunObj.count_stairId h1.1 h1', hA.1, hA.2]
    simp
  have hϖ := GlobalTheory.SplitFlip.IsUnif.irreducible (isUnif_unifAt w)
  rw [hN, hNx]
  subst hx
  subst hM'
  rw [hΛ, hR, GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero),
    GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero)]
  simp only [mulVec_diagonal, hδl, one_mul, hδr]
  refine and_congr Iff.rfl (forall_congr' fun r => ?_)
  rw [GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI1 r) (hn1 r), GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI2 r) (hn2 r)]
  have hq : ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [ho, pow_zero, one_mul, ← mul_assoc]
    exact (inv_mul_cancel₀ hq).symm ▸ (one_mul _)
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [pow_zero, one_mul] at ho
    rw [← ho, ← mul_assoc]
    exact ((mul_inv_cancel₀ hq).symm ▸ (one_mul _)).symm

end GlobalTheory.BaseMoveAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorsAreCombinationsOfVacuaOfLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem comb_smul_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  have h : ∀ u, heisO ψ S T u (a • f) = a • heisO ψ S T u f := fun u => by
    funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  unfold comb
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [h, smul_comm]

theorem movedAt_big : Big fun ch => MovedAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs _ => ?_⟩⟩
  obtain ⟨v, hv, κ, z, hz, hcol⟩ := _root_.GlobalTheory.ColVac.colVac large₂ F hS ch hIs
  choose κ' hκ' using fun i : Fin D.R.m => _root_.GlobalTheory.RowVac.moved_vac_eq large₂ F hS ch hIs i i.2
  refine ⟨v, hv, κ, fun i => if h : i < D.R.m then κ' ⟨i, h⟩ else 1, z, hz,
    fun t a β τ c hSum hExp hC d hd => ⟨fun j => ?_, fun i => ?_⟩⟩
  · have hvec := ((hSum.vec β τ hExp d hd).1 j)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).1 j).2.2
    rw [_root_.GlobalTheory.MovedComb.movedVec_eq_comb large₂ F hS ch hIs t (.top t j) (show DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) from j.2) (d.1 j) ((c d).1 j) hz1 hvec ((hC d hd).1 j),
      hcol t j j.2, comb_smul_heis]
  · have hvec := ((hSum.vec β τ hExp d hd).2 i)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).2 i).2.2
    rw [_root_.GlobalTheory.MovedComb.movedVec_eq_comb large₂ F hS ch hIs t (.chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) (d.2 i) ((c d).2 i) hz1 hvec ((hC d hd).2 i),
      hκ' i, comb_smul_heis]
    simp only [dif_pos i.2, combR]

end GlobalTheory.RowVal

end
end

