module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonneg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsoundQdPlacesUniformConst
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremBTB

theorem localTB : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h) ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := _root_.GlobalTheory.TBLocalW.tb_of_localW

theorem l_ge_three (D : D7) (i : D.nd.Loc) (hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) : 3 ≤ D.nd.l i := by
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
  rcases hl with h | h <;> rw [h]
  · have := D.host.qd_big.1; nlinarith
  · have := D.host.qd_big.2; nlinarith

theorem jointCond_at_qd (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool)
    (h0 : EmbeddingTypeJumps.Conclusion0 D) (hJump : EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂) (hPar : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc) (hQ : EmbeddingTypeJumps.AtQD i)
    (π : D.nd.X i) :
    JointConditionTameBound D HW F i (r i) π ⌊2 * large₂.sc.b⌋₊ ⌊2 * large₂.sc.b⌋₊
      (GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV)) := by
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  have hl3 := l_ge_three D i hl
  refine ⟨by omega, fun w hw => ?_⟩
  obtain ⟨-, hK1, -, hdegK⟩ := h0 i hl w hw
  refine ⟨GlobalTheory.BridgeInertia.inertEq D i w hw, hK1, fun C hs Y hc hY => ?_⟩
  have hs1 : (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).W.s = 1 :=
    (HW (D.nd.l i)).W_s _ 1 _ hs
  have hell : LocalSituation.ell (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = D.nd.l i :=
    (D.loc (D.nd.l i)).PD_p _
  haveI : CharZero (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp :=
    inferInstanceAs (CharZero ℚ_[D.nd.l i])
  haveI : FiniteDimensional (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp
      (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).K := (D.nbr i w hw).Kw.2
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)
  have hdeg := GlobalTheory.bridge_finrank_le D i w hw
  obtain ⟨hv1, -⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks (D.nd.l i) (D.nbr i w hw).Kw
  have hK0 : Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≠ 0 := Module.finrank_pos.ne'
  have hgK : LocalSituation.gK (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = 0 := by
    unfold LocalSituation.gK
    rw [hs1, hell]
    show padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1)) -
      padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1) = 0
    have hpos : (D.nd.l i - 1) / 2 ≠ 0 := by omega
    have hv : padicValNat (D.nd.l i) ((D.nd.l i - 1) / 2) = 0 := by
      rw [Nat.padicValNat_def]
      apply multiplicity_eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    rw [hdegK, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hpos hK0, hv, zero_add, Nat.sub_self]
  have hvd : ∀ m : ℕ, 0 < m → LocalSituation.vdegMs (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) m = m - 1 := by
    intro m hm
    unfold LocalSituation.vdegMs
    rw [hs1, hell]
    exact hv1 m hm
  have hb := hPar
  unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hb
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hfl : ∀ z : ℤ, (z : ℝ) ≤ 2 * large₂.sc.b → z ≤ (⌊2 * large₂.sc.b⌋₊ : ℤ) := by
    intro z hz
    rcases le_or_gt z 0 with h | h
    · exact h.trans (Int.natCast_nonneg _)
    · have h2 : ((z.toNat : ℕ) : ℝ) ≤ 2 * large₂.sc.b := by
        rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg h.le]; exact hz
      have := Nat.le_floor h2
      omega
  have ht : D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ := by
    have := hfl (D.R.t : ℤ) (by push_cast; linarith)
    omega
  have key := GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings
    (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y ⌊2 * large₂.sc.b⌋₊ D.R.nV (4 * D.R.n) D.R.t
    hs1 hcard hdeg hgK (hvd _ (by unfold LocalSituation.mN; omega)) ht (fun τ => by
      obtain ⟨s, Jc, Jl, hs1', hs2', hJc, hJl, hlow, hcl, -, -, hiff⟩ := hJump i hQ w hw C τ
      classical
      refine ⟨Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t, ?_, ?_, fun a ha => ?_⟩
      · calc (Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t).card ≤ (Jc ∪ Jl).card + (Finset.Ico (0 : ℤ) D.R.t).card :=
              Finset.card_union_le _ _
          _ ≤ Jc.card + Jl.card + (Finset.Ico (0 : ℤ) D.R.t).card := by
              have := Finset.card_union_le Jc Jl; omega
          _ = D.R.nV := by
              rw [hJc, hJl, Int.card_Ico]
              unfold Ranks.nV Ranks.r
              have := D.R.m_add_three_le_k
              simp only [sub_zero, Int.toNat_natCast]
              omega
      · intro u hu
        simp only [Finset.mem_union, Finset.mem_Ico] at hu
        rcases hu with (hu | hu) | hu
        · rcases hcl with hc' | hc'
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
            · exact hfl (u + 1) (by push_cast; linarith)
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
        · obtain ⟨hb', -, -, -⟩ := hlow u hu
          rcases hb' with ⟨a1, a2⟩ | ⟨a1, a2⟩
          · constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · omega
          · constructor
            · omega
            · exact hfl (u + 1) (by push_cast; linarith)
        · constructor
          · omega
          · omega
      · have := (hiff π a).1 (hY τ a ha)
        simp only [Finset.mem_union, Finset.mem_Ico]
        tauto)
  refine ⟨key.1, fun e he => (key.2 e he).trans (le_of_eq ?_)⟩
  rw [hell]

theorem cBnum_le (l t n r : ℕ) (b : ℝ) (hl : 3 ≤ l) (ht : 1 ≤ t) (hn : 1 ≤ n) (hr : 1 ≤ r) (hb : 1 < b)
    (hL : 1 < Real.log b) :
    (GlobalTheory.HubLoc.cBnum l ⌊2 * b⌋₊ t (4 * n * (r + t)) : ℝ) ≤
      60 * (t : ℝ) * ((2 * n : ℕ) : ℝ) * ((r : ℝ) + (t : ℝ)) * Real.log b := by
  set L := Real.log b with hLdef
  set lam := Nat.log l (2 * ⌊2 * b⌋₊) with hlam
  have hfl2 : 2 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hpow : l ^ lam ≤ 2 * ⌊2 * b⌋₊ := Nat.pow_log_le_self l (by omega)
  have h3pow : 3 ^ lam ≤ l ^ lam := Nat.pow_le_pow_left hl lam
  have hfb : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have h3R : (3 : ℝ) ^ lam ≤ 4 * b := by
    have : ((3 ^ lam : ℕ) : ℝ) ≤ ((2 * ⌊2 * b⌋₊ : ℕ) : ℝ) := by exact_mod_cast h3pow.trans hpow
    push_cast at this
    linarith
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hlamL : (lam : ℝ) ≤ 4 * L := by
    have h1 : Real.log ((3 : ℝ) ^ lam) ≤ Real.log (4 * b) := Real.log_le_log (by positivity) h3R
    rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : (lam : ℝ) ≤ (lam : ℝ) * Real.log 3 := by
      have : (0 : ℝ) ≤ lam := by positivity
      nlinarith
    linarith
  unfold GlobalTheory.HubLoc.cBnum
  rw [← hlam]
  push_cast
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlam0 : (0 : ℝ) ≤ lam := by positivity
  set P : ℝ := (t : ℝ) * (2 * n) * (r + t) with hP
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
    nlinarith
  have hA : 3 + (lam : ℝ) + 3 ≤ 10 * P * L := by nlinarith
  have hB : 4 * (t : ℝ) + 3 * t ≤ 7 * P * L := by
    have : (t : ℝ) ≤ P := by
      have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
      nlinarith
    nlinarith
  have hC : (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) ≤ 24 * P * L := by
    have h4 : (4 : ℝ) + 2 * lam ≤ 12 * L := by linarith
    have hq : (0 : ℝ) ≤ (t : ℝ) * (4 * n * (r + t)) := by positivity
    calc (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) = ((t : ℝ) * (4 * n * (r + t))) * (4 + 2 * lam) := by ring
      _ ≤ ((t : ℝ) * (4 * n * (r + t))) * (12 * L) := mul_le_mul_of_nonneg_left h4 hq
      _ = 24 * P * L := by rw [hP]; ring
  have hPL : 0 ≤ P * L := by positivity
  nlinarith

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := by
  intro D HW F r ρ large₂ ep h0 _h1 hW hTB hJump _hFon _hG2 _hSet hLit hPar i hQ π _hπ
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  refine ⟨GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV), ?_, ?_⟩
  · exact localTB D HW F i (r i) π _ _ _ hTB (fun w hw C h => hW i hQ w hw C h) (hLit i hQ).2.2.2.1
      (jointCond_at_qd D HW F r large₂ ep h0 hJump hPar i hQ π)
  · have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
    have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have hn1 : 1 ≤ D.R.n := by unfold Ranks.n; have := D.R.two_le_m; have := D.R.m_le_f; omega
    have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
    have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
    have hLb : 1 < Real.log large₂.sc.b := by
      unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
      exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
    have key := cBnum_le (D.nd.l i) D.R.t D.R.n D.R.r large₂.sc.b (l_ge_three D i hl) ht1 hn1 hr1 hb1 hLb
    have hnV : D.R.nV = D.R.r + D.R.t := rfl
    have hf : D.R.f = 2 * D.R.n := rfl
    rw [hnV, hf]
    exact key

end GlobalTheory.TheoremBTB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundary
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.ReadC

section Gen
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    Formalism.WeaklyAdmissibleFiltrations.actT (latOne hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  simp only [Formalism.WeaklyAdmissibleFiltrations.actT, LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • x = ((ψ g : Oˣ) : O) • x
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ) (g : G) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g = (((χ g)⁻¹ * ψ g : Oˣ) : O) • LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul, Units.val_mul]

theorem actD_one (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (g : G) :
    actD (stdLatG hinj M) g = M g 0 0 • LinearMap.id := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply, actD,
    ← Submodule.Quotient.mk_smul]
  erw [Submodule.mapQ_apply]
  congr 1
  funext j
  fin_cases j
  simp [stdLatG, matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem equivG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O)) (g : G)
    (u : ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) :
    iotaC LL lam a (tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u) =
      actD (stdLatG hinj M) g (iotaC LL lam a u) := by
  have h1 : tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u = (((χ g)⁻¹ * ψ g : Oˣ) : O) • u := by
    rw [actTw_latOne]; rfl
  rw [h1, actD_one, hM]
  exact (iotaC LL lam a).map_smul _ u

end Gen
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC
section Gen2
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem readG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O))
    (z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.IsCob (latOne hinj ψ) ↥(Xq LL lam a) χ z') :
    (fun g => iotaC LL lam a (z' g)) ∈ BD (stdLatG hinj M) := by
  obtain ⟨m, hm⟩ := hz
  refine ⟨iotaC LL lam a m, ?_⟩
  funext g
  have key := equivG hinj lam a ψ χ M hM g m
  rw [hm g]
  refine Eq.trans ?_ ((iotaC LL lam a).map_sub _ m).symm
  exact (congrArg (fun y => y - iotaC LL lam a m) key).symm

end Gen2
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem entry (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, mapM, chiRatO, twistM, Br.iota]

theorem ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    (chiT C θ 1 g)⁻¹ * chiT C θ c g = chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g := by
  have h1 : chiOC C 1 g = 1 := by simp [chiOC]
  simp only [chiT, MonoidHom.mul_apply, mul_inv_cancel, h1, one_mul]
  rw [mul_comm (chiOC C _ g) (θ g)]
  exact inv_mul_cancel_left _ _

theorem entry_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  rw [entry, ratio]

end GlobalTheory.UseLoc.Cases.ReadC

theorem GlobalTheory.UseLoc.Cases.readC_cob : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) :=
  fun D i w hw C lam θ c a z' hz =>
    ReadC.readG (LL := ↥C.LL.1) Subtype.val_injective lam a (chiT C θ c) (chiT C θ 1) (locOC C (chiRatO D.nd i c))
      (ReadC.entry_ratio C θ c) z' hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelLiftBaseOfRealisationLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwistLiftW

theorem isLevelLift_base_of_realisation_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : X.Γ) (κ : GA D (Wc D j)),
    Lev.IsLevelLift (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) κ →
    Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b (X.cG (X.R.eG g))) κ := by
  intro D X E Y i j b g κ h
  have P := Y.Z.pin
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hβ := P.frT i j b
  have hP := P.Pg i j b
  have tri : ∀ (PP : Pl D.host.E) (r t : ℕ), r = (Wc D j).rank → ∀ x : GL (Fin (Wc D j).rank) (kP PP),
      x ∈ blockTri (blkOf r t) := fun PP r t hr x => mem_blockTri.2 fun a c hac => by
    have ha : a.val < r := lt_of_lt_of_eq a.2 hr.symm
    have e : blkOf r t a = 0 := if_pos ha
    exact absurd (lt_of_lt_of_eq hac e) (Nat.not_lt_zero _)
  refine ⟨h.1, mem_parLev.2 ⟨parLev_UA h.2.1, ?_, fun PP _ => tri PP _ _ rfl _,
    fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
  · rw [hβ]; exact parLev_St h.2.1
  · funext PP
    obtain ⟨PP, hPP⟩ := PP
    have hPP' : PP ∈ X.R.Pg := hP ▸ hPP
    refine Units.ext (Matrix.ext fun a c => ?_)
    have e1 := P.grp i j b (X.cG (X.R.eG g)) PP hPP hPP' a c
    rw [MulEquiv.symm_apply_apply] at e1
    refine Eq.trans ?_ e1.symm
    rw [← h.2.2, hβ]
    have e2 := upper_block_val_submatrix (le_refl _) (blockTri_blkOf_le _ 1 (tri PP _ 1 rfl (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    have e3 := upper_block_val_submatrix rW.ge (blockTri_blkOf_le _ 1 (tri PP _ 1 rW.symm (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    exact (congrFun (congrFun e2 a) c).trans (congrFun (congrFun e3 (Fin.cast rW a)) (Fin.cast rW c)).symm

end GlobalTheory.TwistLiftW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgro
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {G : Type} [Group G] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    actT (latOne (LL := LL) hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  ext t
  change Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ) g (t : LL) = (((ψ g : Oˣ) : O) • t : LL)
  simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (X : Type)
    [AddCommGroup X] [Module O X] (g : G) :
    tableLineDegreeTwo.actTw (latOne (LL := LL) hinj ψ) X ψ g = LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul]
  simp

theorem eq_zero_of_isUnr_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ)
    (X : Type) [AddCommGroup X] [Module O X] (I : Subgroup G) (z : G → ↥(latOne (LL := LL) hinj ψ).T ⊗[O] X)
    (h : tableLineDegreeTwo.IsUnr (latOne (LL := LL) hinj ψ) X ψ I z) : ∀ g ∈ I, z g = 0 := by
  obtain ⟨m, hm⟩ := h
  intro g hg
  rw [hm g hg, actTw_latOne, LinearMap.id_apply, sub_self]

theorem mem_Z1urD_of_eq_zero {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (I : Subgroup G) (c : G → V ⧸ L.T)
    (h : ∀ g ∈ I, c g = 0) : c ∈ Z1urD L I :=
  ⟨0, fun g hg => by rw [h g hg, map_zero, sub_zero]⟩

end Gen

end GlobalTheory.UseLoc.Cases

theorem GlobalTheory.UseLoc.Cases.readU_unr : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  intro D i w hw C lam θ a I z' h
  exact GlobalTheory.UseLoc.Cases.mem_Z1urD_of_eq_zero _ I _ (fun g hg =>
    (congrArg (iotaC ↥C.LL.1 lam a) (GlobalTheory.UseLoc.Cases.eq_zero_of_isUnr_latOne _ _ _ I z' h g hg)).trans (map_zero _))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonnegStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.rankinSelberg_cell_integral_finite_part_nonneg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ k : GL (Fin (m + r + 1 + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (n := (m + r + 1 + 1))) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + r + 1 + 1) k) = GlobalTheory.JSW.whit φ g) →
    (∀ k : GL (Fin (m + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (n := (m + 1))) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) k) = GlobalTheory.JSW.whit φ' g) →
    (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
    Continuous κ → (∀ h, 0 ≤ κ h) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 ∧ 0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h₀)).re) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) → (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
        (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' 0 g = (f g : ℂ)) ∧
        (∀ (x : ℝ) (g : GA E (m + 1)), ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ) = Complex.exp (x * t g)) ∧
        (∀ x : ℝ, ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ (x - ((r : ℝ) + 1)))) ∂μ ≠ ⊤) ∧
        (∀ π' : CuspSub E (m + 1), π'.IsUnitary → φ' ∈ GlobalTheory.JSW.mspanR π' →
          F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)) → ∀ x : ℝ, 1 < x →
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (‖GlobalTheory.JSW.whit φ' (g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ x)) ∂μ ≠ ⊤) := by
  first | (exact @GlobalTheory.RSnmFT.exists_cellPart_unfoldedIntegral_positive_alt) | (exact GlobalTheory.RSnmFT.exists_cellPart_unfoldedIntegral_positive_alt) | (intros; apply GlobalTheory.RSnmFT.exists_cellPart_unfoldedIntegral_positive_alt  <;> assumption)
end

