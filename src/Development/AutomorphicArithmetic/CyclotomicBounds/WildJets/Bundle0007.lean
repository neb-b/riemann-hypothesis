module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0005
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.TabBd
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0003
public import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Imports
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.depth :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p), d.P = locPl G t →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w → ∀ k : ℕ, 0 < k → IsCosetDatum k d →
      ∃ k' : ℕ, 0 < k' ∧ IsCosetDatum k' d ∧ padicValNat l k' ≤ padicValNat l k ∧ (l ∣ k' → GlobalTheory.NormSum.SplitIn D l) := by
  classical
  intro D T L sc G large₂ hS t p d hP w l hl hlw hA k hk hc
  by_cases h : ∃ PP ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨PP, hPP, hlPP⟩ := h
    have key : ((l : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast]
      exact hlPP
    have hsplit : GlobalTheory.NormSum.SplitIn D l := by
      rw [hP] at hPP
      unfold locPl at hPP
      rcases Finset.mem_union.mp hPP with h0 | hQ
      · unfold GlobalTheory.ChiGrid.Places.W0 at h0
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h0
        rw [G.pl.w_over v hv] at key
        exact UpperTheory.WildA.small_set_primes_split large₂ hS v hv l hl key
      · rcases hA PP hQ with hS0 | hno
        · exact UpperTheory.WildA.small_set_primes_split large₂ hS _ hS0 l hl key
        · exact absurd hlw (hno l hl hlPP)
    exact ⟨k, hk, hc, le_rfl, fun _ => hsplit⟩
  · obtain ⟨k', hk', hnd, hc'⟩ := UpperTheory.WildA.depthDrop d l hl (fun w hw hlw' => h ⟨w, hw, hlw'⟩) k hk hc
    refine ⟨k', hk', hc', ?_, fun hd => absurd hd hnd⟩
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnd]
    exact Nat.zero_le _
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem bigN_le_sc_b {D : D7} {large₂ : SizeData₂ D} {Pm : ParameterChoice' D large₂} (P : ParamsT D large₂ Pm)
    (hf : 1 ≤ D.R.f) (hm : 1 ≤ D.R.m) : (bigN D : ℝ) ≤ large₂.sc.b := by
  have hx : 1 ≤ large₂.sc.x ^ P.Cb := Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) P.Cb_nonneg
  have hb := P.precision_cube_order_sq_le
  have hPPn := P.PP_nW
  have hNle := P.nW_le
  have h40 := P.TO_40
  have hsplit := P.split
  have hnP := P.nP_eq
  obtain ⟨hlo1, hlo2, hlo3⟩ := P.nW_lo
  have hN4 : 4 ≤ P.nWn := by omega
  have hk : D.R.k ≤ P.nWn + 1 := by
    have : D.R.k - 1 ≤ (D.R.k - 1) * D.R.f := Nat.le_mul_of_pos_right _ hf
    omega
  have hr : D.R.r ≤ P.nWn := by omega
  have ht : D.R.t ≤ P.nWn + P.TO * P.nWn := by omega
  have hmN : D.R.m ≤ (2 * D.R.f * D.R.m) ^ 4 * P.nWn := by
    calc D.R.m ≤ 2 * D.R.f * D.R.m := by nlinarith
      _ ≤ (2 * D.R.f * D.R.m) ^ 4 := Nat.le_self_pow (by norm_num) _
      _ ≤ (2 * D.R.f * D.R.m) ^ 4 * P.nWn := Nat.le_mul_of_pos_right _ (by omega)
  have hbig : bigN D ≤ (P.nWn + 1) + D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7) := by
    unfold bigN sLen
    have : D.R.m * (D.R.t + (D.R.r + 6) + 1) ≤ D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    omega
  have hmR : (D.R.m : ℝ) ≤ P.PP := by
    have : ((D.R.m : ℕ) : ℝ) ≤ (((2 * D.R.f * D.R.m) ^ 4 * P.nWn : ℕ) : ℝ) := by exact_mod_cast hmN
    push_cast at this
    linarith
  have hNR : (P.nWn : ℝ) ≤ P.PP := hNle
  have hN4R : (4 : ℝ) ≤ P.nWn := by exact_mod_cast hN4
  have hTR : (40 : ℝ) ≤ P.TO := by
    have : 40 * (P.Dp + 2) ≤ P.TO := h40
    have : 40 ≤ P.TO := by omega
    exact_mod_cast this
  have hbigR : (bigN D : ℝ) ≤ (P.nWn + 1) + D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7) := by
    exact_mod_cast hbig
  have hPP1 : 1 ≤ P.PP := by linarith
  have hm0 : (0 : ℝ) ≤ D.R.m := by positivity
  have hT0 : (0 : ℝ) ≤ P.TO := by positivity
  have hN0 : (0 : ℝ) ≤ P.nWn := by positivity
  have step1 : ((P.nWn : ℝ) + 1) + D.R.m * (P.TO * P.nWn + 2 * P.nWn + 7)
      ≤ P.PP ^ 2 * P.TO ^ 2 := by
    have e1 : (D.R.m : ℝ) * (P.TO * P.nWn + 2 * P.nWn + 7) ≤ P.PP * (P.TO * P.PP + 2 * P.PP + 7) := by
      apply mul_le_mul hmR _ (by positivity) (by linarith)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hPP1 (by linarith : (0:ℝ) ≤ P.PP)]
  have step2 : P.PP ^ 2 * P.TO ^ 2 ≤ P.PP ^ 3 * P.TO ^ 2 * large₂.sc.x ^ P.Cb := by
    have h3 : P.PP ^ 2 ≤ P.PP ^ 3 := by nlinarith [sq_nonneg P.PP]
    have hT2 : (0 : ℝ) ≤ P.TO ^ 2 := by positivity
    calc P.PP ^ 2 * P.TO ^ 2 ≤ P.PP ^ 3 * P.TO ^ 2 := mul_le_mul_of_nonneg_right h3 hT2
      _ = P.PP ^ 3 * P.TO ^ 2 * 1 := by ring
      _ ≤ P.PP ^ 3 * P.TO ^ 2 * large₂.sc.x ^ P.Cb := mul_le_mul_of_nonneg_left hx (by positivity)
  linarith

theorem UpperTheory.WildA.kerLe :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p →
      ((∑ τ, ∑ a, (wt G p.big τ).natW a : ℕ) : ℝ) + (D.R.f : ℝ) * (G.V p.small).rank * (G.V p.big).rank ≤ 13 * D.R.f * bigN D * large₂.sc.b := by
  intro D T L sc G large₂ hS hH hc p hp
  have hw : ∀ τ a, (((wt G p.big τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b :=
    fun τ a => wtBd large₂ hS hH hc p hp τ a
  obtain ⟨⟨Pm, P, -⟩, -, hmf, hm44, -⟩ := hS
  have hm : 1 ≤ D.R.m := by omega
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have hNb := bigN_le_sc_b P hf hm
  have hnodes : DefNode D.R.m p.big ∧ DefNode D.R.m p.small := by
    cases p with
    | chi i j =>
      obtain ⟨h1, h2⟩ := hp
      exact ⟨⟨h1, h2⟩, ⟨by omega, h2⟩⟩
    | mu t i j => exact hp.elim
    | core i => exact hp.elim
    | top t j =>
      exact ⟨show j + 1 ≤ D.R.m from hp, show j ≤ D.R.m by have : j + 1 ≤ D.R.m := hp; omega⟩
  have rb : ((G.V p.big).rank : ℝ) ≤ bigN D := by exact_mod_cast GlobalTheory.DefRank.rank_le_bigN G p.big hnodes.1
  have rs : ((G.V p.small).rank : ℝ) ≤ bigN D := by exact_mod_cast GlobalTheory.DefRank.rank_le_bigN G p.small hnodes.2
  have hsum : ((∑ τ, ∑ a, (wt G p.big τ).natW a : ℕ) : ℝ) ≤ D.R.f * (G.V p.big).rank * (12 * large₂.sc.b) := by
    push_cast
    calc (∑ τ, ∑ a, (((wt G p.big τ).natW a : ℕ) : ℝ))
        ≤ ∑ τ : D.what₂.Tau, ∑ a : Fin (G.V p.big).rank, 12 * large₂.sc.b :=
          Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun a _ => hw τ a
      _ = D.R.f * (G.V p.big).rank * (12 * large₂.sc.b) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, D.what₂.card_Tau]
          ring
  have hb0 : (0 : ℝ) ≤ large₂.sc.b := le_trans (by positivity) hNb
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hrb0 : (0 : ℝ) ≤ (G.V p.big).rank := by positivity
  have hrs0 : (0 : ℝ) ≤ (G.V p.small).rank := by positivity
  have e1 : (D.R.f : ℝ) * (G.V p.big).rank * (12 * large₂.sc.b) ≤ 12 * D.R.f * bigN D * large₂.sc.b := by
    have := mul_le_mul_of_nonneg_left rb (by positivity : (0:ℝ) ≤ 12 * D.R.f * large₂.sc.b)
    nlinarith
  have e2 : (D.R.f : ℝ) * (G.V p.small).rank * (G.V p.big).rank ≤ D.R.f * bigN D * large₂.sc.b := by
    have hsb : ((G.V p.small).rank : ℝ) ≤ large₂.sc.b := le_trans rs hNb
    have h1 : ((G.V p.small).rank : ℝ) * (G.V p.big).rank ≤ large₂.sc.b * bigN D :=
      mul_le_mul hsb rb hrb0 hb0
    have := mul_le_mul_of_nonneg_left h1 hf0
    nlinarith
  linarith
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerStd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.kerStd :
    ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R), GlobalTheory.NormSum.Inp D → DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (l ∣ k → GlobalTheory.NormSum.SplitIn D l) →
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt ch.S.toGridChoice p.small x) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) →
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt ch.S.toGridChoice p.big y) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) → ∀ (b : ℝ) i j,
        LossLe w ((bVV ℂ (wt ch.G p.big)).repr (ch.S.Z.kkMap 1 d x y (bVV ℂ (wt ch.G p.small) j)) i)
          ((vw w ((l : ℕ) : D.what₂.LL) : ℝ) * GlobalTheory.SumSize.TopInt.kerLoss ch.G δ 1 b p.small p.big l (padicValNat l k)) := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hI hD S δ hL t p hp k d hk hc hz hP x y hR w l hl hw hsp hx hy b i j
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, hr, -, hq, htab⟩ := hD t p hp k d hk hc hz hP x y
  obtain ⟨hEs, hEt, hκ1⟩ := hq l hx hy
  have hcc : D.host.ccK = ⊤ := hS.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hkk := UpperTheory.WildA.kkTab ch.S.Z hp d x y _ htab
  obtain ⟨c, hcJ⟩ := UpperTheory.WildA.jetInt _ _ _ (wtOK_of_defPair ch.G p hp).2 j i
  have hB := UpperTheory.WildA.tabBd D hI S δ hL D.host.ccK hcc ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.4 _ _ (ch.S.Z.e0 p)
    (ch.S.Z.e0_is p hp) Ls Lt hLs hLt l hEs hEt k hk hsp κ n _ r s hκ hκ1 hs hr
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.one_le
  have hopp : ∀ (z : ℂ) (C : ℝ), (∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam C z) →
      ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam C (opp p z) := by
    intro z C h lam
    have hcj : GlobalTheory.NormSum.Term.Bd lam C ((starRingEnd ℂ) z) :=
      ⟨(GlobalTheory.NormSum.conjQbar ⟨z, (h lam).1⟩).2, GlobalTheory.NormSum.conj_bound (h lam).1 (fun lam => (h lam).2) lam⟩
    cases p
    all_goals first | exact h lam | exact hcj
  have hrk : ((ch.G.pS p).rank : ℝ) * (ch.G.pT p).rank = ((ch.G.V p.small).rank : ℝ) * (ch.G.V p.big).rank := by
    cases p
    all_goals first | rfl | exact mul_comm _ _
  refine UpperTheory.WildA.bdLoss D w l hw _ _ ?_ fun lam => ?_
  · have := hR i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this
  · rw [hkk, hcJ, Finsupp.sum]
    refine GlobalTheory.NormSum.Term.Bd.sum (by positivity) _ _ fun m _ => ?_
    rw [← one_mul ((l : ℝ) ^ _)]
    refine (GlobalTheory.NormSum.Term.Bd.intCast _).mul ?_
    split_ifs with hm
    · refine (hopp _ _ (fun lam => hB lam _) lam).mono (Real.rpow_le_rpow_of_exponent_le hl1 ?_)
      rw [Finsupp.degree_mapDomain, hm]
      unfold GlobalTheory.SumSize.TopInt.kerLoss
      have h0 := hL.2.1 l
      have h2 : 0 ≤ (if (l : ℝ) ≤ 1 * b then Real.logb l (1 * b) else 0) := by
        split_ifs with h
        · exact Real.logb_nonneg (by exact_mod_cast hl.one_lt) (hl1.trans h)
        · exact le_rfl
      have h3 : (0 : ℝ) ≤ (if l = D.host.d then 1 else 0) := by split_ifs <;> norm_num
      have h4 : (if l = D.host.d then (1 : ℝ) / 4 else 0) ≤ (if l = D.host.d then 1 else 0) := by split_ifs <;> norm_num
      have h5 : ((D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank : ℕ) : ℝ) =
          (D.R.f : ℝ) * (ch.G.V p.small).rank * (ch.G.V p.big).rank := by
        push_cast
        rw [mul_assoc, mul_assoc, hrk]
      rw [h5, add_mul]
      refine le_add_of_le_of_nonneg (add_le_add ?_ ?_) (by positivity)
      · exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · exact GlobalTheory.NormSum.Term.Bd.zero (by positivity)
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MatLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lossLe_mul_wild_jets {D : D7} (w : PlL D) {x y : ℂ} {a b : ℝ}
    (hx : LossLe w x a) (hy : LossLe w y b) : LossLe w (x * y) (a + b) := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s * t, by rw [map_mul, hs, ht], ?_⟩
  rcases hs' with h0 | h1
  · left; simp [h0]
  rcases ht' with h0 | h2
  · left; simp [h0]
  by_cases hs0 : s = 0
  · left; simp [hs0]
  by_cases ht0 : t = 0
  · left; simp [ht0]
  right
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w s t hs0 ht0]
  push_cast
  linarith
private theorem lossLe_add {D : D7} (w : PlL D) {x y : ℂ} {a : ℝ}
    (hx : LossLe w x a) (hy : LossLe w y a) : LossLe w (x + y) a := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s + t, by rw [map_add (f := _), hs, ht], ?_⟩
  by_cases hs0 : s = 0
  · subst hs0; simpa using ht'
  by_cases ht0 : t = 0
  · subst ht0; simpa using hs'
  by_cases hst : s + t = 0
  · left; exact hst
  right
  have h1 : -a ≤ (vw w s : ℝ) := hs'.resolve_left hs0
  have h2 : -a ≤ (vw w t : ℝ) := ht'.resolve_left ht0
  have h3 := Formalism.PairingDivisionLocalBalance.vw_add w s t hs0 ht0 hst
  have h4 : ((min (vw w s) (vw w t) : ℤ) : ℝ) ≤ (vw w (s + t) : ℝ) := by exact_mod_cast h3
  rw [Int.cast_min] at h4
  exact le_trans (le_min h1 h2) h4
private theorem lossLe_finset_sum {D : D7} (w : PlL D) {ι : Type*} (S : Finset ι) (g : ι → ℂ) {a : ℝ}
    (hg : ∀ i ∈ S, LossLe w (g i) a) : LossLe w (∑ i ∈ S, g i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, Or.inl rfl⟩
  | insert j S hj ih =>
    rw [Finset.sum_insert hj]
    exact lossLe_add w (hg j (Finset.mem_insert_self j S))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem UpperTheory.WildA.matLat :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (w : PlL D) (l : ℕ), l.Prime →
      (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)),
      Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ (Formalism.MainNotions.StandardLatticesGL3.stdL D n) → Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ' (Formalism.MainNotions.StandardLatticesGL3.stdL D n') →
      ∀ (f : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ), (∀ i j, LossLe w ((bVV ℂ lam').repr (f (bVV ℂ lam j)) i) c) →
      ∀ (a : ℝ) (v : VV ℂ lam), InLat lam w a Λ v → InLat lam' w (a + c) Λ' (f v) := by
  intro D n n' lam lam' w l hl hlw Λ Λ' hΛ hΛ' f c hf a v hv
  apply UpperTheory.WildA.latCoordB D lam' w l hl hlw Λ' hΛ' (a + c) (f v)
  intro i
  have hv' := UpperTheory.WildA.latCoordA D lam w l hl hlw Λ hΛ a v hv
  have hsum := (bVV ℂ lam).sum_repr v
  have hrepr : (bVV ℂ lam').repr (f v) i =
      ∑ j, (bVV ℂ lam).repr v j * (bVV ℂ lam').repr (f (bVV ℂ lam j)) i := by
    calc (bVV ℂ lam').repr (f v) i
        = (bVV ℂ lam').repr (f (∑ j, (bVV ℂ lam).repr v j • bVV ℂ lam j)) i := by rw [hsum]
      _ = _ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_apply']
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hrepr]
  exact lossLe_finset_sum w _ _ fun j _ => lossLe_mul_wild_jets w (hv' j) (hf i j)
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MoveTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.moveTop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t t' : T) (j : ℕ), j + 1 ≤ D.R.m →
      ∀ (d : FinDatum G t (GlobalTheory.ChiGrid.Pair.top t' j)) (x r : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (y r' : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big)
        (U : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t t' j hj d x r y r' U U' hU hU'
  have hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T) := hj
  have hω := W.om_is (GlobalTheory.ChiGrid.Pair.top t' j) hj
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := UpperTheory.WildA.expEx (G := G) hL _ hp
  obtain ⟨γ, hγ, k, hk, hrk, hρ⟩ := UpperTheory.WildA.ratReal W N.fr _ r U hU
  obtain ⟨γ', hγ', k', hk', hrk', hρ'⟩ := UpperTheory.WildA.ratReal W N.fr _ r' U' hU'
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FockRealVec.vec_theta_fock W Z hp d (Z.hasVec_of_defPair hL hp d)
  have hB : ∀ X, DefNode D.R.m X → ∀ τ, (N.frC X τ)ᴴ * gramAt D (G.V X) τ * N.frC X τ = 1 := fun X hX τ =>
    GlobalTheory.FockJetOrigin.frame_map τ (N.fr_on X hX)
  have hF : ∀ Q, IsThetaFunO W.ψ _ _ (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) := fun Q =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ h1 Q
  have haut : ∀ Q g h, W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) (γ * g) (γ' * h) =
      W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) g h := by
    intro Q g h
    show thetaKO (W.om (.top t' j)) (γ * g) (γ' * h) _ = thetaKO (W.om (.top t' j)) g h _
    have e : ((γ * g, γ' * h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ (hF Q))
  let ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.top t' j)).rank (G.pS (GlobalTheory.ChiGrid.Pair.top t' j)).rank →ₗ[ℂ] ℂ :=
    { toFun := fun Q => kerFin W (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q)
        (x * N.u _) (y * N.u _)
      map_add' := fun P Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_add (f := _), Pi.add_apply]
      map_smul' := fun c Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, RingHom.id_apply] }
  have key := UpperTheory.WildA.realTop (W := W) N hL t' j hj a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'
  have tab : jetTab W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) (r * x * N.u _) (r' * y * N.u _) =
      fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.top t' j) e₁ e₂ k k' *
        ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) k k'
          (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t' j))) 1)) := by
    funext m
    rw [jetTab, kerFin, mul_assoc r, mul_assoc r', hrk, hrk', haut]
    exact GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp hB a b ha hb e₁ e₂ he₁ he₂ _ h1 h2 k hk k' hk' _ _ _
  have hid : GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k ∘ₗ
      GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hρ, ← hρ', Normal.kkMap, Normal.kkMap, fockComp, fockComp, tab, key, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_assoc, LinearMap.comp_assoc, hid, LinearMap.comp_id]
  rfl
end

