module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMinAtHalfMax
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped nonZeroDivisors

namespace GlobalTheory.RawThetaSup


set_option maxHeartbeats 800000 in
theorem exists_small_inv (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ξ : K) (x : ℝ) (hx : 0 < x)
    (hξ : ∀ τ : K →+* ℂ, ‖τ ξ‖ = x) (A B : FractionalIdeal (𝓞 K)⁰ K)
    (h : FractionalIdeal.spanSingleton (𝓞 K)⁰ ξ * A * B * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) = 1)
    (hAB : FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm A) :
    ∃ b : K, b ≠ 0 ∧ (∀ a ∈ A, IsIntegral ℤ (b * a)) ∧ ∀ τ : K →+* ℂ, ‖τ b‖ ^ 2 ≤ x * rdE K ^ 2 := by
  have hA : A ≠ 0 := by rintro rfl; simp at h
  obtain ⟨c, hc⟩ : ∃ c, c = InfinitePlace.nrComplexPlaces K := ⟨_, rfl⟩
  have hn : Module.finrank ℚ K = 2 * c := hc ▸ IsTotallyComplex.finrank K
  have hc0 : c ≠ 0 := by have := Module.finrank_pos (R := ℚ) (M := K); omega
  have hcard : Fintype.card (InfinitePlace K) = c := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hc]
  have hd : 0 < |(discr K : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hNξ : ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) = x ^ (2 * c) := by
    rw [← InfinitePlace.prod_eq_abs_norm, ← hn, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← hξ w.embedding, InfinitePlace.norm_embedding_eq]
  have hN := congrArg FractionalIdeal.absNorm h
  rw [map_mul, map_mul, map_mul, map_one, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal K (𝓞 K)] at hN
  have hN' : x ^ (2 * c) * (FractionalIdeal.absNorm A : ℝ) * (FractionalIdeal.absNorm B : ℝ) * |(discr K : ℝ)| = 1 := by
    rw [← hNξ]
    have := congrArg (Rat.cast : ℚ → ℝ) hN
    simpa [Nat.cast_natAbs] using this
  have hB0 : (0 : ℝ) ≤ (FractionalIdeal.absNorm B : ℝ) := by exact_mod_cast FractionalIdeal.absNorm_nonneg B
  have hAB' : (FractionalIdeal.absNorm B : ℝ) ≤ (FractionalIdeal.absNorm A : ℝ) := by exact_mod_cast hAB
  have hA0 : (0 : ℝ) < (FractionalIdeal.absNorm A : ℝ) := by
    rcases (hB0.trans hAB').eq_or_lt with e | e
    · rw [← e] at hN'; simp at hN'
    · exact e
  have hrd : rdE K ^ (2 * c) = |(discr K : ℝ)| := by
    unfold rdE dE
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le, hn, one_div_mul_cancel (by exact_mod_cast (by omega : 2 * c ≠ 0)),
      Real.rpow_one]
  have hrd0 : 0 < rdE K := Real.rpow_pos_of_pos hd _
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt |(discr K : ℝ)| := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hd
  have hss : s * s = |(discr K : ℝ)| := hs ▸ Real.mul_self_sqrt hd.le
  have hpos : 0 < x * rdE K ^ 2 := mul_pos hx (pow_pos hrd0 2)
  have hu : (FractionalIdeal.absNorm A : ℝ)⁻¹ ≤ x ^ c * s := by
    rw [inv_le_iff_one_le_mul₀ hA0]
    refine (one_le_sq_iff₀ (by positivity)).1 ?_
    calc (1 : ℝ) = x ^ (2 * c) * (FractionalIdeal.absNorm A : ℝ) * (FractionalIdeal.absNorm B : ℝ) * |(discr K : ℝ)| :=
          hN'.symm
      _ ≤ x ^ (2 * c) * (FractionalIdeal.absNorm A : ℝ) * (FractionalIdeal.absNorm A : ℝ) * |(discr K : ℝ)| := by gcongr
      _ = _ := by rw [← hss]; ring
  obtain ⟨b, hb, hb0, hbw⟩ := Formalism.ExtensionFiltration.mk_lt K (Units.mk0 A⁻¹ (inv_ne_zero hA)) (fun _ => Real.sqrt (x * rdE K ^ 2))
    (fun _ => Real.sqrt_pos.2 hpos) (by
      rw [Real.sq_sqrt hpos.le, Finset.prod_const, Finset.card_univ, hcard, mul_pow, ← pow_mul, hrd, ← hc, ← hs,
        Units.val_mk0, map_inv₀, Rat.cast_inv]
      calc (FractionalIdeal.absNorm A : ℝ)⁻¹ * 2 ^ c * s ≤ x ^ c * s * 2 ^ c * s := by gcongr
        _ = 2 ^ c * (x ^ c * |(discr K : ℝ)|) := by rw [← hss]; ring
        _ < _ := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) hc0)
            (by positivity))
  refine ⟨b, hb0, fun a ha => ?_, fun τ => ?_⟩
  · have hm : b * a ∈ A⁻¹ * A := FractionalIdeal.mul_mem_mul hb ha
    rw [inv_mul_cancel₀ hA, FractionalIdeal.mem_one_iff] at hm
    obtain ⟨z, hz⟩ := hm
    rw [← hz]
    exact z.isIntegral_coe
  · have h1 := (hbw (InfinitePlace.mk τ)).le
    rw [InfinitePlace.apply] at h1
    exact (Real.le_sqrt (norm_nonneg _) hpos.le).1 h1

theorem exists_small_inv_AA (D : D7) : ∃ b : D.host.E, b ≠ 0 ∧ (∀ a ∈ D.host.AA, IsIntegral ℤ (b * a)) ∧
    ∀ τ : D.host.E →+* ℂ, ‖τ b‖ ^ 2 ≤ xiR D * rdE D.host.E ^ 2 := by
  have h1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar *
      (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 1 :=
    Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hx := GlobalTheory.SupDict.xiR_pos D
  have hξ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D
  rcases le_total (FractionalIdeal.absNorm D.host.AAbar) (FractionalIdeal.absNorm D.host.AA) with h | h
  · exact exists_small_inv _ _ _ hx hξ _ _ h1 h
  · obtain ⟨b, hb0, hb, hτ⟩ := exists_small_inv _ _ _ hx hξ D.host.AAbar D.host.AA
      (by rw [← h1]; ring) h
    refine ⟨D.host.conj b, (map_ne_zero _).2 hb0, fun a ha => ?_, fun τ => ?_⟩
    · have := (hb _ (conj_mem_AAbar D ha)).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom
      simpa [conj_conj] using this
    · exact hτ (τ.comp (D.host.conj : D.host.E →+* D.host.E))

section Level

variable {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
  {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r}

theorem firstMin_at_halfMax (hLw : Laws D j Xo c U dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp)
    (la : Wt ((U σ).X k).Ψ D.R.r) {w : ℝ} (hw0 : 0 < w) (hw : (∑ τ, ((U σ).X k).spread la τ) ≤ w)
    (hχ : ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1) {P : Frame ((U σ).X k).Ψ D.R.r → ℂ}
    (hP : P ∈ ((U σ).X k).SS la) {z0 : Frame ((U σ).X k).Ψ D.R.r} (hz0 : z0 ∈ ((U σ).X k).dom)
    (hhalf : ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm la P x ≤ 2 * ((U σ).X k).pnorm la P z0)
    (hpos : 0 < ((U σ).X k).pnorm la P z0) :
    2 * epsLev D.host.E D.host.d l.M w / rdE D.host.E ^ 2 ≤ ((U σ).X k).firstMinimumSq z0 := by
  have habs := hLw.xiAbs σ hσ k
  obtain ⟨Xx, hX, -, hΛ, -, M', hM', hk, hT⟩ := exists_dataX_transv D j H Dw l Xo c U dict hLw σ hσ k
  generalize (U σ).X k = X at *
  subst hX
  have hmax := maxBound_holds D.R.r Xx la P M' w hP hM' hw hw0
    (fun v hv hiso b hb hbi => by
      obtain ⟨γ, hγ, he⟩ := hT v hv hiso b hb hbi
      exact ⟨γ, hγ, hχ γ hγ, he⟩) z0 hz0 hhalf hpos
  rw [GlobalTheory.SupModel.epStar_eq_epsLev D.host.d l.M w M' Xx.k0 hk] at hmax
  generalize epsLev D.host.E D.host.d l.M w = ep at hmax ⊢
  obtain ⟨b, hb0, hb, hbτ⟩ := exists_small_inv_AA D
  have hx := GlobalTheory.SupDict.xiR_pos D
  have hrd : 0 < rdE D.host.E := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (GlobalTheory.SupDict.one_le_dE _)) _
  have hc : ∀ τ : Xx.Ψ, Xx.toData.c τ = 2 * xiR D := fun τ => by unfold Data.c; rw [habs]
  have hsub : ∀ v ∈ Xx.Λ, b • v ∈ Xx.L' := by
    intro v hv
    rw [hΛ] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hx
      rw [smul_smul]
      exact Xx.L'.smul_mem (⟨b * a, hb a ha⟩ : 𝓞 D.host.E) hu
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Xx.L'.smul_mem c hx
  have hlow : ∀ v ∈ Xx.Λ, v ≠ 0 →
      2 * ep / rdE D.host.E ^ 2 ≤ ∑ τ, Xx.toData.c τ * Xx.toData.maj z0 τ (Data.emb τ.1 v) := by
    intro v hv hv0
    obtain ⟨τ0, hτ0⟩ := hmax _ (hsub v hv) (smul_ne_zero hb0 hv0)
    have hemb : Data.emb τ0.1 (b • v) = τ0.1 b • Data.emb τ0.1 v := by
      funext a; simp [Data.emb]
    rw [hemb, FinrankRieszBounds.maj_csmul hz0] at hτ0
    have hm0 := fun τ => MajorantConjugateTransfer.maj_nonneg Xx.toData hz0 τ (Data.emb τ.1 v)
    have hterm : ∀ τ, 0 ≤ Xx.toData.c τ * Xx.toData.maj z0 τ (Data.emb τ.1 v) := fun τ =>
      mul_nonneg (by rw [hc]; positivity) (hm0 τ)
    refine le_trans ?_ (Finset.single_le_sum (fun τ _ => hterm τ) (Finset.mem_univ τ0))
    rw [hc, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right (hbτ τ0.1) (hm0 τ0)
    nlinarith
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hne : ∃ v ∈ Xx.Λ, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : Submodule.span D.host.E (Xx.Λ : Set (Fin D.R.r → D.host.E)) = ⊥ := Submodule.span_eq_bot.2 hcon
    rw [Xx.Λ_span] at h1
    haveI : Nonempty (Fin D.R.r) := ⟨⟨0, hr⟩⟩
    exact top_ne_bot h1
  obtain ⟨v0, hv0, hv00⟩ := hne
  exact le_csInf ⟨_, v0, hv0, hv00, rfl⟩ (fun t ⟨v, hv, hv0', ht⟩ => ht ▸ hlow v hv hv0')

theorem half_sup_at_ortho (hLw : Laws D j Xo c U dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) {w : ℝ} (hw0 : 0 < w) (hw : ∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w)
    (hχ : ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) {P : FDSec (U σ).X} (hP : P ∈ holSub (U σ).X la)
    (hpos : 0 < supN (U σ).X la P) :
    ∃ (k : (U σ).Comp) (xf : ((U σ).X k).dom), ((U σ).X k).IsOrtho xf.1 ∧ supN (U σ).X la P ≤ 2 * ‖P k xf.1‖ ∧
      2 * epsLev D.host.E D.host.d l.M w / rdE D.host.E ^ 2 ≤ ((U σ).X k).firstMinimumSq xf.1 := by
  have hSS := abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ).X la hP
  have hE : supE (U σ).X la P ≠ ⊤ := supE_ne_top _ la hP
  have hE0 : supE (U σ).X la P ≠ 0 := by
    intro h0; rw [supN, h0] at hpos; simp at hpos
  have hhalf' := ENNReal.half_lt_self hE0 hE
  unfold supE at hhalf'
  obtain ⟨p, hp⟩ := lt_iSup_iff.1 hhalf'
  have hp' : supN (U σ).X la P / 2 < ((U σ).X p.1).pnorm (la p.1) (P p.1) p.2 := by
    have := ENNReal.toReal_lt_of_lt_ofReal hp
    rw [ENNReal.toReal_div] at this
    simpa [supN, supE] using this
  have hle : ∀ q : Formalism.L2.Pj.FPt (U σ).X, ((U σ).X q.1).pnorm (la q.1) (P q.1) q.2 ≤ supN (U σ).X la P := by
    intro q
    have h1 : ENNReal.ofReal (((U σ).X q.1).pnorm (la q.1) (P q.1) q.2) ≤ supE (U σ).X la P :=
      le_iSup (fun q : Formalism.L2.Pj.FPt (U σ).X => ENNReal.ofReal (((U σ).X q.1).pnorm (la q.1) (P q.1) q.2)) q
    exact (ENNReal.ofReal_le_iff_le_toReal hE).1 h1
  obtain ⟨k, x, hx⟩ := p
  have hPS := (hSS k).1.1.2.1
  have hb := FrameDegreeData.bOf_mem ((U σ).X k) hx
  have hx' := OrthogonalFrameDomain.rmul_mem_dom ((U σ).X k) hx hb
  have hort := FrameDegreeData.ortho_bOf ((U σ).X k) hx
  have hunit := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((U σ).X k) hort
  have hpn := FrameDegreeData.pnorm_rmul ((U σ).X k) (la k) (P k) hPS x hx _ hb
  have hla := ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel ((U σ).X k) hx hb
  have h2 : supN (U σ).X la P ≤ 2 * ((U σ).X k).pnorm (la k) (P k) x := by linarith [hp']
  have hposx : 0 < ((U σ).X k).pnorm (la k) (P k) x := by linarith
  have hl := firstMin_at_halfMax hLw hσ k (la k) hw0 (hw k) (hχ k) (hSS k) hx
    (fun y hy => le_trans (hle ⟨k, y, hy⟩) h2) hposx
  refine ⟨k, ⟨_, hx'⟩, hort, ?_, by rw [hla]; exact hl⟩
  rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((U σ).X k) (la k) (P k) hunit, hpn]
  exact h2

end Level

end GlobalTheory.RawThetaSup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

theorem cT_map' {A B : Type} [CommRing A] [CommRing B] {m p : Type} (s : A →+* A) (t : B →+* B) (ι : A →+* B)
    (h : ∀ a, t (ι a) = ι (s a)) (M : Matrix m p A) :
    Formalism.UG.cT t (M.map ι) = (Formalism.UG.cT s M).map ι := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem conj_unitary {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) (t : C →+* C) (u : B →+* B) (ι : A →+* B) (φ : C →+* B)
    (hι : ∀ a, u (ι a) = ι (s a)) (hφ : ∀ c, u (φ c) = φ (t c))
    (P Q J : Matrix n n A) (H : Matrix n n C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hfr : Formalism.UG.cT s P * J * P = 1) (hH : Formalism.UG.cT t H * H = 1) :
    Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * J.map ι * (P.map ι * H.map φ * Q.map ι) = J.map ι := by
  have hJ : J = Formalism.UG.cT s Q * Q := by
    calc J = Formalism.UG.cT s (P * Q) * J * (P * Q) := by
            rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by
            rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]
  have hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1 := by
    rw [cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP' : Q.map ι * P.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1 := by
    rw [← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]
  have hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
    rw [hJ, Matrix.map_mul, cT_map' s u ι hι]
  rw [hJ']
  calc Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * (Formalism.UG.cT u (Q.map ι) * Q.map ι) * (P.map ι * H.map φ * Q.map ι)
      = Formalism.UG.cT u (Q.map ι) * (Formalism.UG.cT u (H.map φ) * (Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι))
          * (Q.map ι * P.map ι) * H.map φ) * Q.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
        rw [hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  unfold adSwap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  generalize (GlobalTheory.BotFormula.toAfE D) y = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]

theorem sigR_inclEAf (D : D7) (a : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D a) = inclEAf D (D.sp.cm.sig a) := by
  simp only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem frConj_mem_UA {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram
      * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (h : StandardLatticesGL3.GA D V.rank) : GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  have h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
      * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := h.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h2
  have key := conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm)
    (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    V.gram (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hfr h2
  exact key

end GlobalTheory.FrameTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMulVecCompletedIdealMemCompletedIdealLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameColSmul

theorem colMul_mem_of_span {A : Type} [CommRing A] (S : Subring A) {ι : Type} (M : Submodule S (ι → A))
    (c : ι → A) (G : Set A) (hG : ∀ y ∈ G, (fun i => c i * y) ∈ M) (x : A)
    (hx : x ∈ Submodule.span S G) : (fun i => c i * x) ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero =>
    have : (fun i => c i * (0 : A)) = 0 := by funext i; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b) := by
      funext i; simp [mul_add]
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => c i * (r • a)) = r • (fun i => c i * a) := by
      funext i
      show c i * ((r : A) * a) = (r : A) * (c i * a)
      exact mul_left_comm _ _ _
    rw [this]; exact M.smul_mem r ha

theorem mulVec_eq_sum_col {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (w : Fin n → A) :
    P *ᵥ w = ∑ j, (fun i => P i j * w j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

theorem map_col_mul {E A : Type} [Field E] [NumberField E] [CommRing A] (φ : E →+* A) {n : ℕ}
    (c : Fin n → E) (b : 𝓞 E) :
    (fun i => φ (c i) * φ (b : E)) = fun i => φ ((b • c) i) := by
  funext i
  show _ = φ ((b : E) * c i)
  rw [map_mul, mul_comm]

theorem gen_mem {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (j : Fin n)
    (b : 𝓞 D.host.E) (hb : b ∈ 𝔪) :
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j) *
        GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  have hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr :=
    Submodule.subset_span ⟨j, rfl⟩
  have hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr :=
    Submodule.smul_mem_smul hb hcol
  rw [map_col_mul]
  exact Submodule.subset_span ⟨_, hm, rfl⟩

theorem mulVec_mem : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  intro D n fr 𝔪 w hw
  rw [mulVec_eq_sum_col]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _
    (by
      rintro _ ⟨b, hb, rfl⟩
      exact gen_mem fr 𝔪 j b hb) (w j) (hw j)

end GlobalTheory.FrameColSmul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumStepCharacterTwistPlaceDvd
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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.TwistGaussInt

theorem gauss_dvd : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : AddChar (AF D.host.F) ℂ), PsiUnr ψ v →
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 →
      ∃ g : 𝓞 D.what₂.LL, D.what₂.embLL (g : D.what₂.LL) = gauss ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) ∧
        g ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.what₂.LL) := by
  intro D T Lc sc G W S μ₀ hL hN i j t v τ ψ hψ hloc hc
  set ν := chrW (GlobalTheory.SqStep.chs G i j t).ν τ with hν
  have hval : ∀ x : (Fv D.host.F v)ˣ, (ν x : ℂ) = ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) : ℂ) := fun x => by
    rw [hν, GlobalTheory.SqStepArith.chrW_chs G hL]
  have hcont : Continuous (fun x : (Fv D.host.F v)ˣ => (ν x : ℂ)) := by
    have h1 : Continuous ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)) :=
      (nuH G t i j).2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele _)
    have h2 := Continuous.units_map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom
      (GlobalTheory.LFun.SplitChart.continuous_complMap (GlobalTheory.AdelicU.splitPrime_under τ))
    have := Units.continuous_val.comp (h1.comp h2)
    refine this.congr fun x => ?_
    rw [hval]; rfl
  have hnorm : ∀ x, ‖(ν x : ℂ)‖ = 1 := fun x => by
    show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
    exact Circle.norm_coe _
  have hrange : ∀ x : (Fv D.host.F v)ˣ, (ν x : ℂ) ∈ Set.range D.what₂.embLL := by
    intro x
    rw [hval]
    generalize Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x = y
    have hm : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
    have e : ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) =
        ((Lc.C.mu0 j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) * ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) / ((G.ch.chiH (D.R.m - i)).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) := by
      simp [nuH, Formalism.L2.Host.HChar.loc, div_eq_mul_inv]
    rw [e]
    have r1 := hN.chars.mu0 j (GlobalTheory.AdelicU.splitPrime τ) y
    have r2 := hN.chars.xi t (GlobalTheory.AdelicU.splitPrime τ) y
    have r3 := hN.chars.chi (D.R.m - i) hm (Nat.sub_le _ _) (GlobalTheory.AdelicU.splitPrime τ) y
    rw [← RingHom.coe_fieldRange] at r1 r2 r3 ⊢
    exact div_mem (mul_mem r1 r2) r3
  have hroots : ∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range D.what₂.embLL := by
    intro ζ hζ
    rw [hc, pow_one] at hζ
    apply hN.roots t _ hloc
    rw [GlobalTheory.LFun.SplitChart.absNorm_splitPrime]
    have hd : 1 ≤ depthAt G (GlobalTheory.AdelicU.splitPrime τ) := le_max_right _ _
    obtain ⟨k, hk⟩ : ∃ k, depthAt G (GlobalTheory.AdelicU.splitPrime τ) = k + 1 := ⟨_, (Nat.sub_add_cancel hd).symm⟩
    rw [hk, pow_succ, pow_mul', hζ, one_pow]
  obtain ⟨g, g', hg, hgg⟩ := _root_.GlobalTheory.GaussDiv.gauss_dvd_pow D.what₂.embLL ψ v ν hψ hcont hnorm (by rw [hc]) (fun x _ _ => hrange x) hroots
  refine ⟨g, hg, ⟨g', ?_⟩⟩
  rw [hgg, hc, pow_one]

end GlobalTheory.TwistGaussInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsEqSpanReadings
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Onto


set_option maxHeartbeats 1000000 in
theorem holSub0_eq_span_readings : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) σ).X (laU (T.U ((i : ℕ) + 1) σ) (wtA (κ i)) (κ i).n) = Submodule.span ℂ (Set.range fun f : Cu T κ i => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) := by
  intro D T κ h hκ hl hn i σ hσ
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega)
  have hni : (κ i).n = D.R.nV := (hκ i τ).2.2
  apply le_antisymm
  · refine (_root_.GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h _ (inR i) (κ i) (hl i) (hni ▸ hn) σ hσ).trans (Submodule.span_mono ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.mem_inf.2 ⟨((Formalism.L2.Pj.mem_cusp _ _ _ _ _ _).1 f.2).2 σ hσ, Formalism.L2.Pj.rdU_mem_offZero _ _⟩

end GlobalTheory.Onto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRepStatement
section
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset)
open CompanionTheory.D.LK (IsKMod)

theorem GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D),
      CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E →
      ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ :=
  @GlobalTheory.KFinIrr.kMod_irred
end

