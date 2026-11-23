module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0051
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoFree

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanClassCountBound
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.ClassCount
set_option maxHeartbeats 2000000 in
theorem archimedean_class_count_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → InfClassK := by
  intro _
  obtain ⟨c1, hT1⟩ := _root_.GlobalTheory.LevTopCong.congLev_le_levTop
  obtain ⟨c2, hR1⟩ := _root_.GlobalTheory.ClassCount.levRow_congLev_le
  refine ⟨max c1 c2, fun CF hCF => ⟨144, fun ε C hC => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := hT1 CF ((le_max_left _ _).trans hCF) ε
  obtain ⟨x2, hx2⟩ := hR1 CF ((le_max_right _ _).trans hCF) ε
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hFO => ?_⟩
  have hTop := hx1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  have hRow := hx2 D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  obtain ⟨hNb, hfb, hN1, hf1, hm2, hrd1, hlrd, hb12⟩ := _root_.GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
  set b := large₂.sc.b with hb
  set N := bigN D with hNdef
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hb0 : 0 < b := by linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hf0 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  set base := 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 with hbase
  have hbase1 : 1 ≤ base := by
    have : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 := one_le_pow₀ hf0
    have : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN0
    have : (1 : ℝ) ≤ D.host.rdE ^ 2 := one_le_pow₀ hrd1
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 := by nlinarith
    nlinarith
  have hlbase : Real.log base ≤ 8 * Real.log b := by
    have h12 : Real.log 12 ≤ Real.log b := Real.log_le_log (by norm_num) hb12
    have hlf : Real.log (D.R.f:ℝ) ≤ Real.log b := Real.log_le_log (by linarith) hfb
    have hlN : Real.log N ≤ Real.log b := Real.log_le_log (by linarith) hNb
    have e : Real.log base = Real.log 12 + 2 * Real.log (D.R.f:ℝ) + 4 * Real.log N + 2 * Real.log D.host.rdE := by
      rw [hbase, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast; ring
    rw [e]; nlinarith
  set M := hBd D N * Real.exp (2 * sig ch.G) ^ (N ^ 2) with hM
  have hM0 : 0 ≤ M := by rw [hM, hBd]; positivity
  have factor : ∀ (n : ℕ), n ≤ N → ∀ a : ℝ, 0 ≤ a → a ≤ Real.exp (2 * sig ch.G) → hBd D n * a ^ (n ^ 2) ≤ M := by
    intro n hn a ha0 ha
    have h1 : hBd D n ≤ hBd D N := hBd_mono hn hbase1 hrd0.le
    have h2 : a ^ (n ^ 2) ≤ Real.exp (2 * sig ch.G) ^ (N ^ 2) :=
      (pow_le_pow_left₀ ha0 ha _).trans (pow_le_pow_right₀ (Real.one_le_exp (by linarith)) (by gcongr))
    exact mul_le_mul h1 h2 (by positivity) (by rw [hBd]; positivity)
  have hmod := _root_.GlobalTheory.ModulNorm.absNorm_modul_le ch.G hS.hF
  have fin : ∀ (X : Node), DefNode D.R.m X → ∀ K : Subgroup (GL (Fin (ch.G.V X).rank) (Lev.EAf D)),
      congLev D.sp.cm (ch.G.V X).gram (ch.G.Λ X) ch.G.modul ≤ K → (Nat.card (FinCl (ch.G.V X) K) : ℝ) ≤ M := fun X hX K hK =>
    (_root_.GlobalTheory.FrameTransport.finCl_card_le ch.G ch.S.N X hX _ (ch.G.pl.modul_ne_bot _) K hK).trans
      (factor _ (_root_.GlobalTheory.DefRank.rank_le_bigN ch.G X hX) _ (Nat.cast_nonneg _) hmod)
  set K0 := 48 * (D.R.f:ℝ) * (N : ℝ) ^ 2 * Real.log b + 2 * (N : ℝ) ^ 2 * sig ch.G with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hMK : M ≤ Real.exp K0 := by
    have e1 : hBd D N ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) := by
      rw [Real.exp_nat_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [← Real.log_le_iff_le_exp (by positivity)]
      exact hlbase
    have e2 : Real.exp (2 * sig ch.G) ^ (N ^ 2) = Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) := (Real.exp_nat_mul _ _).symm
    rw [hM, e2, hK0]
    calc _ ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) * Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf
  have hm0 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have key : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ D.R.m * aOne ch.G C b := by
    have hm00 : (0 : ℝ) ≤ D.R.m := by linarith
    have h3 : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ 3 * D.R.m * K0 :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hK00
    refine h3.trans ?_
    have hX : 0 ≤ (D.R.f : ℝ) * N * Real.log b := by positivity
    have t1 : 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b ≤ C * D.R.f * N * b * Real.log b :=
      calc 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b = 144 * ((D.R.f * N * Real.log b) * N) := by ring
        _ ≤ 144 * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ ≤ C * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ = C * D.R.f * N * b * Real.log b := by ring
    have hCm : (6 : ℝ) ≤ C * D.R.m := by
      have := mul_le_mul hC hm0 (by norm_num) (by linarith)
      linarith
    have t2 : 6 * ((N : ℝ) ^ 2 * sig ch.G) ≤ (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G) :=
      mul_le_mul_of_nonneg_right hCm (by positivity)
    calc 3 * (D.R.m : ℝ) * K0 = D.R.m * (144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b + 6 * ((N : ℝ) ^ 2 * sig ch.G)) := by
          rw [hK0]; ring
      _ ≤ D.R.m * (C * D.R.f * N * b * Real.log b + (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_left (add_le_add t1 t2) hm00
      _ = D.R.m * aOne ch.G C b := by rw [aOne]; ring
  have hexp : Real.exp K0 ^ (2 * D.R.m + 1) ≤ Real.exp (D.R.m * aOne ch.G C b) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 key
  refine ⟨?_, fun Φ β hβ => ?_⟩
  ·
    have h := (_root_.GlobalTheory.ClassCount.card_clPlus_le ch.G ch.S.N).trans
      (factor _ (_root_.GlobalTheory.DefRank.rank_le_bigN ch.G (.top 0) (by simp [DefNode])) _ (Nat.cast_nonneg _) hmod)
    refine h.trans (hMK.trans ((le_self_pow₀ (Real.one_le_exp hK00) (by omega)).trans hexp))
  ·
    rw [GridChoice.Classes, Nat.card_prod, Nat.card_pi, Nat.card_pi]
    push_cast
    have hT : ∏ j : Fin D.R.m, (Nat.card (FinCl (ch.G.V (.top j)) (ch.S.levTop A.μ0 Φ β j j.2)) : ℝ) ≤ M ^ D.R.m := by
      calc _ ≤ ∏ _j : Fin D.R.m, M := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun j _ =>
            fin (.top j) (by simp [DefNode]) _
            (hTop Φ β hβ j)
        _ = _ := by simp
    have hR : ∏ i : Fin (D.R.m + 1), (Nat.card (FinCl (ch.G.V (.grid i D.R.m))
        (ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2))) : ℝ) ≤ M ^ (D.R.m + 1) := by
      calc _ ≤ ∏ _i : Fin (D.R.m + 1), M := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun i _ =>
            fin (.grid i D.R.m) (by simp [DefNode]; omega) _
            (hRow i)
        _ = _ := by simp
    calc _ ≤ M ^ D.R.m * M ^ (D.R.m + 1) := mul_le_mul hT hR (by positivity) (by positivity)
      _ = M ^ (2 * D.R.m + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ Real.exp K0 ^ (2 * D.R.m + 1) := pow_le_pow_left₀ hM0 hMK _
      _ ≤ _ := hexp
end GlobalTheory.ClassCount
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_count_bound_archimedean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → InfClassK := by
  first | exact @_root_.GlobalTheory.ClassCount.archimedean_class_count_bound | exact _root_.GlobalTheory.ClassCount.archimedean_class_count_bound | (intros; apply _root_.GlobalTheory.ClassCount.archimedean_class_count_bound <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFieldMinorJetDescription
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BottomFieldDict
theorem vacuum_translate_minor_jet_alt : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∃ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (e0 : TaylorLogMetric.VC D A'.rank WW.rank → ℂ),
      StandardLatticesGL3.Crv D cc δ ∧ GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0 ∧ StandardLatticesGL3.oddE0 D cc δ t0 A'.rank WW.rank e0 ∧
      ∃ Qf : GlobalTheory.NormSum.Tup D A'.rank WW.rank n → MvPolynomial (GL3Theta.Idx D A'.rank WW.rank) ℂ,
        (∀ U α, IsAlgebraic ℚ ((Qf U).coeff α)) ∧
        ∀ w : WO A' WW, w.map (infPart D) = 0 → (∃ m : ℕ, 0 < m ∧ m • w ∈ latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) →
          ∃ (ζ : ℂ) (s : TaylorLogMetric.VC D A'.rank WW.rank), IsAlgebraic ℚ ζ ∧
            StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank) s ∧
            ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n,
              pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (heisO W.ψ A' WW w X.vac') (GlobalTheory.NormSum.minorPol D U) 0 =
                Ω * (ζ * GL3Theta.applyAt0 D (Qf U) (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) s e0)) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX n
  obtain ⟨δ, hc, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D D.host.ccK δ hc).1
  have hd : Even WW.rank := by
    rw [← hX.is.rank, hX.rank, hX.rank']
    obtain ⟨h1, h2, h3⟩ := SqNum.ranks_exact D i j
    exact ⟨SqNum.halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, he0, he0ne⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hc t0 ht0 A'.rank WW.rank (hd.mul_left _)
  have hon : ∀ {V : HSp D}, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 *
      V.gram * (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    rw [hV]
    simp [Formalism.UG.cT]
  have hfr : ∀ {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V}, r.IsStd → r.B = GlobalTheory.FockPos.frAt (1 : GL (Fin V.rank) D.host.E) := by
    intro V r hr
    funext τ
    rw [(hr.2.2 τ).2]
    simp [GlobalTheory.FockPos.frAt]
  have hS := hon hX.std'.1
  have hT := hon hX.stdW.1
  have hcS := fun τ => (hX.is.rigA'.2.2 τ).1
  have hcT := fun τ => (hX.is.rigW.2.2 τ).1
  have hv := hX.is.isVac'
  have hv1 := hv
  rw [lat_eq_colLat hX.std', lat_eq_colLat hX.stdW] at hv1
  obtain ⟨Θ, hΘ, hΘ0, hj⟩ := GlobalTheory.FockPos.fock_jets_eq_theta W.ψ W.θ A' WW _ _ 1 1 hS hT hcS hcT δ hc hδ _ hv1
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨c, hce⟩ := (GlobalTheory.ThetaLine.theta_line D hG1 _ δ hc _ _ _
    (Or.inr ⟨_, _, GlobalTheory.FinWeil.Vacuum.sd_std D _, GlobalTheory.FinWeil.Vacuum.sd_std D _, rfl⟩)).1 Θ hΘ e0 he0.1 he0ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΘ0 (by rw [hce, zero_smul])
  set p : ℂ := δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) with hp
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = p := fun τ => by
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hp0 : p ≠ 0 := by
    refine mul_ne_zero hδ (inv_ne_zero ?_)
    have hx : 0 < Formalism.L2.Pj.xiR D := GlobalTheory.SupDict.xiR_pos D
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hprod : ∀ k : GL3Theta.Idx D A'.rank WW.rank →₀ ℕ,
      (k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) = p ^ (k.sum fun _ e => e) := fun k => by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  refine ⟨c * p ^ (A'.rank * ∑ τ, n τ), mul_ne_zero hc0 (pow_ne_zero _ hp0), D.host.ccK, δ, t0, e0, hc, ht0, he0,
    fun U => GlobalTheory.NormSum.minorPol D U, fun U α => minorPol_coeff_isAlgebraic U α, ?_⟩
  rintro w - ⟨m, hm, hw⟩
  rw [lat_eq_inV hX.std', lat_eq_inV hX.stdW] at hv hw
  obtain ⟨ζ, s, hζ, hs, hk⟩ := GlobalTheory.HeisTrans.core W.ψ W.θ A' WW _ _ 1 1 hS hT hcS hcT _ _
    (GlobalTheory.FinWeil.Vacuum.sd_std D _) (GlobalTheory.FinWeil.Vacuum.sd_std D _) δ hδ e0 he0.1.1 c X.vac' hv (fun k => by
      have h := hj k
      rw [hce, GlobalTheory.FunObj.TopJet.applyAt0_monomial, GlobalTheory.FunObj.TopJet.taylor_const_smul D e0 he0.1.1] at h
      rw [GlobalTheory.FunObj.TopJet.applyAt0_monomial]
      refine h.trans ?_
      ring) m hm w hw
  obtain ⟨ζ', hζ', -⟩ := GlobalTheory.HeisTrans.qbar_of_root hζ
  refine ⟨ζ, s, hζ' ▸ mem_algebraicClosure_iff.1 ζ'.2, ⟨m, hm, hs⟩, fun U => ?_⟩
  have hUd : Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK δ) s e0) := by
    have h : Differentiable ℂ (fun z : TaylorLogMetric.VC D A'.rank WW.rank => TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D D.host.ccK δ) z s) := by
      unfold TaylorLogMetric.Hf
      fun_prop
    have h0 : Differentiable ℂ e0 := he0.1.1
    unfold TaylorLogMetric.U
    fun_prop
  rw [hfr hX.std', hfr hX.stdW]
  refine apply_minorPol U ((LinearMap.proj (0 : WO A' WW)).comp (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s
    (GlobalTheory.FockPos.frAt 1) (GlobalTheory.FockPos.frAt 1) (heisO W.ψ A' WW w X.vac'))) c p ζ _ fun k => ?_
  have h := hk k
  rw [hprod k, GlobalTheory.FunObj.TopJet.applyAt0_monomial] at h
  have e : (fun z => ζ * TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK δ) s e0 z) = ζ • TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK δ) s e0 := rfl
  rw [e, GlobalTheory.FunObj.TopJet.taylor_const_smul D _ hUd] at h
  rw [GlobalTheory.FunObj.TopJet.applyAt0_monomial]
  refine h.trans ?_
  ring
theorem kernel_minor_polynomial_eq_jet : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW,
      ∃ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (e0 : TaylorLogMetric.VC D A'.rank WW.rank → ℂ) (k : ℕ) (c : Fin k → ℂ)
        (s : Fin k → TaylorLogMetric.VC D A'.rank WW.rank),
        StandardLatticesGL3.Crv D cc δ ∧ GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0 ∧ StandardLatticesGL3.oddE0 D cc δ t0 A'.rank WW.rank e0 ∧
        (∀ l, IsAlgebraic ℚ (c l)) ∧ (∀ l, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank) (s l)) ∧
        ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n, ∃ Q : MvPolynomial (GL3Theta.Idx D A'.rank WW.rank) ℂ,
          (∀ α, IsAlgebraic ℚ (Q.coeff α)) ∧
          X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D U) h x = Ω * GL3Theta.applyAt0 D Q (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D cc δ) c s e0) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX n
  obtain ⟨Ω, hΩ, cc, δ, t0, e0, hc, ht0, he0, Qf, hQf, H⟩ :=
    _root_.GlobalTheory.BottomFieldDict.vacuum_translate_minor_jet_alt hP hI hL hX n
  refine ⟨Ω, hΩ, fun t x hx h hh => ?_⟩
  obtain ⟨k, c, w, hca, hwf, hwl, hexp⟩ := _root_.GlobalTheory.BotExpand.kernel_eq_sum_of_jets hP hI hL hX t x hx h hh
  choose ζ s hζ hs hζeq using fun l => H (w l) (hwf l) (hwl l)
  have hd : Differentiable ℂ e0 := he0.1.1
  have hU : ∀ l, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s l) e0) := fun l => by
    have h1 : Differentiable ℂ (fun z : TaylorLogMetric.VC D A'.rank WW.rank => TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z (s l)) := by
      unfold TaylorLogMetric.Hf
      fun_prop
    unfold TaylorLogMetric.U
    fun_prop
  refine ⟨cc, δ, t0, e0, k, fun l => c l * ζ l, s, hc, ht0, he0, fun l => (hca l).mul (hζ l), hs,
    fun U => ⟨Qf U, hQf U, ?_⟩⟩
  rw [hexp]
  unfold StandardLatticesGL3.comb
  rw [GlobalTheory.LiftTypePrime.Jets.applyAt0_comb Finset.univ _ _ hU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hζeq l U]
  ring
end GlobalTheory.BottomFieldDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_field_minor_jet_description : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW,
      ∃ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (e0 : TaylorLogMetric.VC D A'.rank WW.rank → ℂ) (k : ℕ) (c : Fin k → ℂ)
        (s : Fin k → TaylorLogMetric.VC D A'.rank WW.rank),
        StandardLatticesGL3.Crv D cc δ ∧ GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0 ∧ StandardLatticesGL3.oddE0 D cc δ t0 A'.rank WW.rank e0 ∧
        (∀ l, IsAlgebraic ℚ (c l)) ∧ (∀ l, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank) (s l)) ∧
        ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n, ∃ Q : MvPolynomial (GL3Theta.Idx D A'.rank WW.rank) ℂ,
          (∀ α, IsAlgebraic ℚ (Q.coeff α)) ∧
          X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D U) h x = Ω * GL3Theta.applyAt0 D Q (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D cc δ) c s e0) := by
  first | exact @_root_.GlobalTheory.BottomFieldDict.kernel_minor_polynomial_eq_jet | exact _root_.GlobalTheory.BottomFieldDict.kernel_minor_polynomial_eq_jet | (intros; apply _root_.GlobalTheory.BottomFieldDict.kernel_minor_polynomial_eq_jet <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaIntegralClassSumFormula
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotFormula.ClassSumMonotone
open GlobalTheory.SqTop
end GlobalTheory.BotFormula.ClassSumMonotone
theorem GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ v : ℂ, v ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : GA D WW) (pt : GA D P.a → GA D A),
          (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ T : Tup D P.a P.d P.n,
            X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
              v * ∑ᶠ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
                ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (pt x.out) := by
  intro hPr hTA hLM hInp hBS
  refine GlobalTheory.BotFormula.ClassSumMonotone.gbig_mono' (GlobalTheory.BotFormula.ClassSumMonotone.gbig_and' (_root_.GlobalTheory.T.bottom_large_level_kernel hPr hTA hLM hInp hBS) (_root_.GlobalTheory.T.bottom_kernel_real_invariant hPr hTA hLM hInp hBS)) ?_
  intro D T Lc sc G μ₀ C x b H
  obtain ⟨H3, H4⟩ := H
  intro W hW i j A A' WW X δ t0 hX
  obtain ⟨v, hv, hsum⟩ := _root_.GlobalTheory.BotClassMeas.integral_eq_vol_mul_classSum A hX.std.1 X.m X.fd hX.is.meas.1 hX.is.meas.2
  refine ⟨v, hv, fun s Q P P' hB ea ed g pt hpt T => ?_⟩
  exact hsum P.a ea pt hpt _ (_root_.GlobalTheory.ClassSumLeft.ker_left_rat hX s _ g)
    (fun k hk y => H4 W hW i j A A' WW X hX s Q δ t0 P P' hB ea ed g T k hk y)
    (fun x k hx hk y => H3 W hW i j A A' WW X hX s _ g P.a x k hx hk y)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_thetaIntegral_classSum_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ v : ℂ, v ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : GA D WW) (pt : GA D P.a → GA D A),
          (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ T : Tup D P.a P.d P.n,
            X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
              v * ∑ᶠ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
                ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (pt x.out) := by
  first | exact @_root_.GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum | exact _root_.GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum | (intros; apply _root_.GlobalTheory.BotFormula.bottom_thetaIntegral_eq_classSum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DivisibilityAlongQuadraticTower
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.divisibility_along_quadratic_tower : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E a) (V' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E a')
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E (a + a')) (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (R R₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (oa ob : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (oa' ob' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (Ra Rb Sa Sb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (ca cb da db : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B Γ Xa oa oa' R Ra → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B Γ Xb ob ob' R Rb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B (GlobalTheory.ThK.reG Γ V V' Z) Xa oa oa' R₂ Sa → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B (GlobalTheory.ThK.reG Γ V V' Z) Xb ob ob' R₂ Sb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B Γ Xa oa oa' R Ra ca → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B Γ Xb ob ob' R Rb cb →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B (GlobalTheory.ThK.reG Γ V V' Z) Xa oa oa' R₂ Sa da → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst B (GlobalTheory.ThK.reG Γ V V' Z) Xb ob ob' R₂ Sb db →
      ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, da * cb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * ca) := by
  intro hP hK _ F E _ _ _ _ _ σ B a a' Γ V V' Z Xa Xb R R₂ oa ob oa' ob' Ra Rb Sa Sb ca cb da db m1 m2 n1 n2 k1 k2 l1 l2
  exact _root_.GlobalTheory.ReBase.rebase_ratio_real_part hP hK m1 m2 n1 n2 k1 k2 l1 l2
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DominantTermNeZero
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.BigNZ
open Formalism.IndefR GlobalTheory.RowTest GlobalTheory.RowClaim
theorem large_term_nonzero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t, ∃ M : Vol ch.G, M.Is t ∧ ∃ a τ τ' n Φ,
    (∀ w ∈ locPl ch.G t, depthAt ch.G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip ch.S.B t ch.rm i j n Φ τ τ' ∧
    ∃ g g₁, ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  intro hP hK hLM _ _ _
  obtain ⟨CF0, hH⟩ := standing
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc i j t => ?_⟩
  exact exists_integral_ne_zero hP.strongApproxSU hK hLM hS.core.lev ch.W ch.S.B ch.rm t i j
    (hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc t)
end GlobalTheory.BigNZ
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_term_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t, ∃ M : Vol ch.G, M.Is t ∧ ∃ a τ τ' n Φ,
    (∀ w ∈ locPl ch.G t, depthAt ch.G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip ch.S.B t ch.rm i j n Φ τ τ' ∧
    ∃ g g₁, ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  first | exact @_root_.GlobalTheory.BigNZ.large_term_nonzero | exact _root_.GlobalTheory.BigNZ.large_term_nonzero | (intros; apply _root_.GlobalTheory.BigNZ.large_term_nonzero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SiegelWeilFockAnisotropicUnconditional
section
section
namespace UpperTheory.Lit.Sw47
theorem siegelWeil_fock_anisotropic_unconditional (D : Formalism.BasicNotions.D7) :
    GlobalTheory.BottomRallis.SiegelWeilFockAniso D := fa D
end UpperTheory.Lit.Sw47
end
end

