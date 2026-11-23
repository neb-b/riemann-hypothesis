module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortPhi

theorem exists_shortBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  intro E _ _ _ H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  let := H.starRing
  let := io.toAlgebra
  obtain ⟨Q', β, hQ', h0, hβ, hβ2, -⟩ :=
    GlobalTheory.ValForm.main E H T.V C.I.G P ϖ hϖ (IsCMField.complexConj E : E → E) fun _ => rfl
  obtain rfl : Q = Q' := funext fun χ => QForm.QVal_unique hϖ P.D (hQ χ) (hQ' χ)
  have hφ' : HasPhi y (Formalism.MainNotions.ModuliIntegralCharts.phiC _ β) := ⟨C.I.G, C.I.t', C.I.m1, C.I.m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ2, rfl⟩
  have hnn := hφ.nonneg
  obtain rfl : φ = Formalism.MainNotions.ModuliIntegralCharts.phiC _ β := (hasPhi_exists_ext_and_unique E H Dw l Xo c).2 T io y _ _ hφ hφ'
  obtain ⟨ρ, hρ, -, hq⟩ := GlobalTheory.ToricRank.rank_le_signature E H Dw l Xo T.V C.I.G P C.I.t' C.I.m2 y.1.x C.I.m1
    inferInstance
  have hrt : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
    rw [← H.bar_eq, HostModel.bar_rt]; simp
  have hw : (H.w0 : E) + IsCMField.complexConj E (H.w0 : E) = 1 := by
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      simpa only [map_mul, map_add (f := _), map_one, map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    have h3 := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hrt] at h3
    linear_combination (h2 + h3) / 2
  have hne : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra! h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hpos := QForm.gram_posDef hϖ P.D hQ (Module.finBasis ℤ P.D.toPre.X)
  obtain ⟨b, h1, h2⟩ := gram_form_phi_holds E (IsCMField.complexConj E : E → E)
    (fun ψ z => IsCMField.complexEmbedding_complexConj E ψ z) hne H.w0 hw P.D.toPre.X β
    ⟨_, inferInstance, Module.finBasis ℤ P.D.toPre.X, by simpa only [hβ] using hpos⟩
  refine ⟨Module.finrank ℤ P.D.toPre.X, ?_, by positivity, b, fun j => ?_, fun j z => ?_⟩
  · rw [hρ]
    exact Nat.mul_le_mul (Nat.mul_div_le _ _) hq
  · have := h1 j
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero] at this
  · have := h2 j z
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero, hβ] at this

end GlobalTheory.ShortPhi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LargeCover

open IsDedekindDomain Formalism.MainNotions GlobalTheory.IntCuspLat


set_option maxHeartbeats 1000000 in
theorem exists_smul_nonneg_of_dvd (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o) (w : ℕ)
    (hw : ∀ (u : D.host.E) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n)
    (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n) (hla : ∀ σ k τ i, (w : ℤ) ∣ laU (Y.U σ) a n k τ i)
    (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n) :
    ∃ s : 𝓞 Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  let σ : Y.d.c₂.F →+* ℂ := Y.d.c₂.F.val.toRingHom
  have hσ : GoodEmb Y.d.c₂ σ := rfl
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hU : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) := (Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)
  have hpq : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := hU.1
  have hA : Y.d.l₂.A = 1 := hG.lev.2
  have hC := GlobalTheory.ChartFree.chartIndep
  have hP : ∀ k, PrincUpTo ((Y.U σ).X k) Y.d.l₂.M (laU (Y.U σ) a n k) := fun k =>
    princUpTo_of_root _ _ w hw _ (hla σ k)
      (GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _ _ hU hA hr k)
  obtain ⟨_, hW⟩ := hG.modelW σ hσ
  have hGm : ∀ k k', ((Y.U σ).X k).Gm = ((Y.U σ).X k').Gm ∧ ((Y.U σ).X k).ξ0 = ((Y.U σ).X k').ξ0 :=
    fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  have hχ := fun k => hG.chiTriv σ hσ a n hdom k
  have hf' := (mem_cusp _ _ _ a n f).1 hf
  have h1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := hpq ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n := by
    have h0 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have : D.R.r ≤ Module.finrank ℚ D.host.E * D.R.r := Nat.le_mul_of_pos_left _ h0
    omega
  have hd : ∃ d : DeltaDat Y.d.Xo₂ Y.d.c₂ n, d.IsLev ∧ (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧
      d.cδ = 1 ∧ d.pd = 1 ∧ d.l₂.A = Y.d.l₂.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ Y.d.Xo₂ Y.d.c₂ h1 n 1 ⊤ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hone : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y = 1 :=
    fun k _ _ y => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
  have hunit : GlobalTheory.Dict.UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : Y.d.c₂.Fˣ) : Y.d.c₂.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [hone K y, hone K y']
    simp
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ σ
    D.R.r _ hU a n).1
  refine exists_smul_nonneg_of_span (fun la => isVal_valSet la)
    (fun b => shortGen Y.d.Xo₂ Y.d.c₂ nab b 0 a n d) (fun b hb => ?_) fun b hb g hg => ?_
  · have htot : ShortValTot Y.d.Xo₂ Y.d.c₂ nab b 0 a n d :=
      GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d (GlobalTheory.levelMaps_closed hL _ _ _ h1)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ Y.d.Xo₂ Y.d.c₂).2.2.1
        (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ Y.d.Xo₂ Y.d.c₂)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
        nab b 0 a
    have hsp := holSub0_le_span_shortGen_upto hC _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d σ D.R.r _ hσ hU hr hA hGm
      hlev hnab hunit h3 (fun _ => ⟨ph, 1, x₀, hpin⟩) nab b 0 a hb hdom hn hP hχ htot
    refine GlobalTheory.mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)))
      (sec Y.d.Xo₂ Y.d.c₂ a n) hind (shortGen Y.d.Xo₂ Y.d.c₂ nab b 0 a n d) (fun g hg => hg.1) hf'.1 (hsp ?_)
    exact ⟨hf'.2 _ hσ, fun k x hx => dif_neg hx⟩
  · obtain ⟨hsec, Λ, N, x0, P, hUn, hTb, hTM, hN, -, hPl, hR⟩ := hg
    obtain ⟨inst, hnab⟩ := hnab
    obtain ⟨t, ht, hb'⟩ := exists_smul_nonneg_of_shortRule_any_level D _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev hnab
      (fun k _ _ y => by rw [hone k y, one_pow])
      (GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev ph 1 x₀ hpin)
      Λ N hUn hTM hN a P hPl x0 g hsec hR
    exact ⟨t, N, ht, hN.1.pos, fun la ℓ hℓ hm hor =>
      hb' la ℓ hℓ hm (hor.elim (trivAt_of_dvd hTb) (trivAt_of_not_dvd hUn hN hℓ))⟩

theorem exists_smul_nonneg_all (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n) (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n)
    (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n) :
    ∃ s : 𝓞 Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  have hmul : CuspMul Y.d.Xo₂ Y.d.c₂ Y.U := cusp_mul_of_M5 ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _
  have hD : ∀ k : ℕ, Dom (k • a) (k * n) := fun k =>
    ⟨fun τ i i' hi => Nat.mul_le_mul_left k (hdom.1 τ hi), hdom.2.mul_left k⟩
  have hpow : ∀ k : ℕ, f ^ (k + 1) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U ((k + 1) • a) ((k + 1) * n) := fun k => by
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [pow_succ, succ_nsmul a (k + 1), Nat.succ_mul (k + 1)]
      exact hmul _ _ _ _ _ _ (hD _) hdom ih hf
  obtain ⟨w, hw0, hw⟩ := exists_pow_root_eq_one D.host.E
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have h2 : ((k + 1 : ℕ) : ℤ) ∣ (((k + 1) * n / 2 : ℕ) : ℤ) := by
    obtain ⟨m, hm⟩ := hdom.2
    rw [hm, ← two_mul, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
    exact Int.natCast_dvd_natCast.2 (dvd_mul_right _ _)
  have h1 : ∀ x, ((k + 1 : ℕ) : ℤ) ∣ ((((k + 1) • a) x : ℕ) : ℤ) := fun x =>
    Int.natCast_dvd_natCast.2 (dvd_mul_right (k + 1) (a x))
  obtain ⟨s, hs, h⟩ := exists_smul_nonneg_of_dvd D T j Y e o hG (k + 1) hw _ _ (hD (k + 1))
    (hn.trans (Nat.le_mul_of_pos_left _ hw0)) (fun σ c τ i => by
      unfold laU
      split_ifs
      · exact (h1 _).add h2
      · exact (h1 _).neg_right.sub h2) _ (hpow k)
  exact ⟨s, hs, fun la v hv => nonneg_of_pow (fun la => isVal_valSet la) hv s f _ (h la v hv)⟩

end GlobalTheory.LargeCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRing
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback_ring {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR S ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR S) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsVanishingOfSimplePoleMulExtends
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

theorem fun_eq_of_dense [IsReduced Y] {O : Y.Opens} (hd : Dense (O : Set Y)) {W : Y.Opens} {a b : Γ(Y, W)}
    (h : ∀ z (hz : z ∈ W), z ∈ O → ger z hz a = ger z hz b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot (a - b) ?_
  by_contra hne
  obtain ⟨z, hz', hz⟩ := hd.inter_open_nonempty _ (Y.basicOpen (a - b)).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have hm := Y.basicOpen_le _ hz'
  have hu : IsUnit (ger z hm (a - b)) := (Y.mem_basicOpen _ z hm).1 hz'
  rw [map_sub, h z hm hz, sub_self] at hu
  exact not_isUnit_zero hu

theorem glue_of_dense [IsReduced Y] {O : Y.Opens} (hd : Dense (O : Set Y)) {B : LB Y} (hB : B.IsLB)
    {ι : Type} (V : ι → Y.Opens) (c : ι → B.ι) (hc : ∀ s, V s ≤ B.U (c s)) (cover : ∀ y, ∃ s, y ∈ V s)
    (u : ∀ s, Γ(Y, V s)) (f : H0 p B O)
    (hu : ∀ s z (h : z ∈ V s) (hz : z ∈ O), ger z h (u s) = H0.germ (c s) z hz (hc s h) f) :
    ∃ g : H0 p B ⊤, (∀ s z (h : z ∈ V s), H0.germ (c s) z (memTop z) (hc s h) g = ger z h (u s)) ∧
      H0.restr le_top g = f := by
  obtain ⟨g, hg⟩ := H0.exists_of_germs (p := p) (O := ⊤) hB V c (fun _ => le_top) hc (fun y _ => cover y) u
    fun z s s' h h' => by
      have hW : V s ⊓ V s' ≤ B.U (c s) ⊓ B.U (c s') := fun x hx => ⟨hc s hx.1, hc s' hx.2⟩
      have e : resG Y (inf_le_left : V s ⊓ V s' ≤ V s) (u s) =
          resG Y hW (B.g (c s) (c s')).val * resG Y (inf_le_right : V s ⊓ V s' ≤ V s') (u s') :=
        fun_eq_of_dense hd fun x hx hxO => by
          rw [map_mul, ger_resG, ger_resG, ger_resG, hu s x _ hxO, hu s' x _ hxO, ← val_tr B x (hW hx)]
          exact H0.germ_change _ _ x hxO _ _ f
      have e' := congrArg (ger z (show z ∈ V s ⊓ V s' from ⟨h, h'⟩)) e
      rwa [map_mul, ger_resG, ger_resG, ger_resG, ← val_tr B z (hW ⟨h, h'⟩)] at e'
  refine ⟨g, fun s z h => hg s z h, H0.ext_germ fun y hy => ?_⟩
  obtain ⟨s, hs⟩ := cover y
  exact ⟨c s, hc s hs, by rw [H0.germ_restr, hg s y hs, hu s y hs hy]⟩

theorem extends_vanishing_of_mul [IsReduced Y] {O : Y.Opens} (hd : Dense (O : Set Y)) {P B N : LB Y}
    (C : ProdChart P B N) (ω : H0 p P O) (hω : SimplePoleAlong O C ω) (G : H0 p N ⊤) (f : H0 p B O)
    (hG : H0.restr le_top G = C.mul ω f) :
    ∃ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi,
      H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ∧ H0.restr le_top g = f := by
  choose V hyV τ ha hb hc t u ht hu _ htu using hω
  have hU (y : Y) (hy : y ∉ O) : IsUnit (u y hy) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => hu y hy z hz
  let w (y : Y) (hy : y ∉ O) : Γ(Y, V y hy) :=
    t y hy * (hU y hy).unit⁻¹.val *
      resG Y (le_inf le_top (hc y hy) : V y hy ≤ ⊤ ⊓ N.U (C.c (τ y hy))) (G.loc (C.c (τ y hy)))
  have hw (y : Y) (hy : y ∉ O) (z : Y) (hz : z ∈ V y hy) : ger z hz (w y hy) =
      ger z hz (t y hy) * ger z hz (hU y hy).unit⁻¹.val * H0.germ (C.c (τ y hy)) z (memTop z) (hc y hy hz) G := by
    simp only [w, map_mul, ger_resG]
    rfl
  let VV : C.τ ⊕ {y : Y // y ∉ O} → Y.Opens := fun s => match s with
    | .inl i => O ⊓ B.U (C.b i)
    | .inr y => V y.1 y.2
  let cc : C.τ ⊕ {y : Y // y ∉ O} → B.ι := fun s => match s with
    | .inl i => C.b i
    | .inr y => C.b (τ y.1 y.2)
  have hcc : ∀ s, VV s ≤ B.U (cc s) := fun s => match s with
    | .inl _ => inf_le_right
    | .inr y => hb y.1 y.2
  let uu : ∀ s, Γ(Y, VV s) := fun s => match s with
    | .inl i => f.loc (C.b i)
    | .inr y => w y.1 y.2
  have cover : ∀ y, ∃ s, y ∈ VV s := fun y => by
    by_cases hy : y ∈ O
    · obtain ⟨i, -, hi, -⟩ := C.cover y
      exact ⟨.inl i, hy, hi⟩
    · exact ⟨.inr ⟨y, hy⟩, hyV y hy⟩
  have huu : ∀ s z (h : z ∈ VV s) (hz : z ∈ O), ger z h (uu s) = H0.germ (cc s) z hz (hcc s h) f := by
    rintro (i | ⟨y, hy⟩) z h hz
    · rfl
    · change ger z h (w y hy) = H0.germ (C.b (τ y hy)) z hz (hb y hy h) f
      have e2 : ger z h (u y hy) * ger z h (hU y hy).unit⁻¹.val = 1 := by
        rw [← map_mul, IsUnit.mul_val_inv, map_one]
      have e1 := htu y hy z h hz
      rw [hw, ← H0.germ_restr le_top _ z hz, hG, C.germ_mul ω f (τ y hy) z hz (ha y hy h) (hb y hy h)]
      linear_combination (ger z h (hU y hy).unit⁻¹.val * H0.germ (C.b (τ y hy)) z hz (hb y hy h) f) * e1 +
        H0.germ (C.b (τ y hy)) z hz (hb y hy h) f * e2
  obtain ⟨g, hg, hgf⟩ := glue_of_dense hd C.isLB₂ VV cc hcc cover uu f huu
  refine ⟨g, fun y hy i hi => ?_, hgf⟩
  have e : H0.germ (C.b (τ y hy)) y (memTop y) (hb y hy (hyV y hy)) g = ger y (hyV y hy) (w y hy) :=
    hg (.inr ⟨y, hy⟩) y (hyV y hy)
  rw [H0.germ_change i (C.b (τ y hy)) y (memTop y) hi (hb y hy (hyV y hy)), e, hw, mul_assoc]
  refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ ?_)
  exact (IsLocalRing.mem_maximalIdeal _).2 fun hu' => hy ((ht y hy y (hyV y hy)).1 hu')

end GlobalTheory.LogCanonicalReflexive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowGramAlgebraicSection
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR

theorem hatL_cong_of_hat {D : D7} (V : HSp D) (κ : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin V.rank → D.host.E))) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V κ).1 *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  intro z hz
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (h _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ z hz))
  have e : (Lev.finE V κ).1 = (finHom V κ).1.map (Algebra.TensorProduct.comm D.host.F _ D.host.E) := rfl
  convert h1 using 1
  funext j
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.sub_apply, map_sub, Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply,
    Matrix.map_apply]

end GlobalTheory.BaseLevelInj

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cLoc_finPt (γ : UE E n) (w : Pl E) (i j : Fin n) :
    (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val i j = algebraMap E (w.adicCompletion E) ((γ : GL (Fin n) E).val i j) :=
  congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) (GlobalTheory.BCT.FinPart.pU_finPt γ)

theorem cLoc_conj_mem_KGL {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') (x g : finU (E := E) (n := n))
    (hg : g ∈ (globLev S K').map (MulAut.conj x).toMonoidHom) :
    ∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro w hw
  obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 hg
  have e' : x⁻¹ * g * x = k := by
    rw [← e]
    simp [MulAut.conj_apply, mul_assoc]
  rw [e']
  have hk' : ∀ u ∈ S, ∃ a ∈ K' u, (a : GLw n u) = cLoc u k.1 := by
    simpa [globLev, Subgroup.mem_iInf] using hk
  obtain ⟨a, ha, hae⟩ := hk' w hw
  rw [← hae]
  exact Subgroup.mem_subgroupOf.1 ((hK.1 w).2.1 ha)

end GlobalTheory.BCT.StabFin


open GlobalTheory.BCT.StabFin in
theorem GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  intro E _ _ _ _ n _ S hS K' hK x
  obtain ⟨d, hd, hC⟩ := GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate E n S hS x
  haveI : Finite {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈
      w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} := (_root_.GlobalTheory.NumFin.finite_bdd_denom_conj_le_one E d hd).to_subtype
  have hrat := (GlobalTheory.BCT.FinPart.finPt_props E n).2.2
  let γ : ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) → UE E n :=
    fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose
  have hγ : ∀ g, finPt (γ g) = g.1 := fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose_spec
  refine Finite.of_injective (β := Fin n → Fin n → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) *
      algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1})
    (fun g i j => ⟨((γ g : UE E n) : GL (Fin n) E).val i j, fun w => by
        have := hC g.1 (cLoc_conj_mem_KGL hK x g.1 (Subgroup.mem_inf.1 g.2).2) w i j
        rwa [← hγ g, cLoc_finPt] at this,
      fun τ => _root_.GlobalTheory.BCT.FinPart.norm_emb_entry_le_one E n (γ g) τ i j⟩) fun g g' e => ?_
  have e1 : γ g = γ g' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg Subtype.val (congrFun (congrFun e i) j)
  apply Subtype.ext
  rw [← hγ g, ← hγ g', e1]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVarsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  first | exact @GlobalTheory.LagIntTransl.main | exact GlobalTheory.LagIntTransl.main | (intros; apply GlobalTheory.LagIntTransl.main <;> assumption)
end

