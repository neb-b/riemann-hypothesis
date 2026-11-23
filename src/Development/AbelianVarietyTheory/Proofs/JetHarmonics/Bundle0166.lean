module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0033
public import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniformisedModelIntegralChartAtPointStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedModel_integralChart_at_point : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), letI := T.Q.H.starRing; ∃ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ) (_ : OverLa la T'.V io e) (z : IntFr (T.Q.Xo j) T.Q.c T' io) (_ : z.IsAlg) (_ : T.G.lies j la T' io z (imgV y)) (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z) (P : PELUnif (maximalIdeal T'.V) C.I.G), FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ ∀ w : WeightFamilies.Wt D j, ∀ f ∈ T.th j w, vAtV y f = nval T'.V e (evI z f) := by
  first | exact @GlobalTheory.UnifPoint.exists_uniformised_chart | exact GlobalTheory.UnifPoint.exists_uniformised_chart | (intros; apply GlobalTheory.UnifPoint.exists_uniformised_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProof
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertPackage

theorem not_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (τ : E →+* ℂ) (h1 : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h2
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1] at h2
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have e3 := H.sqrt_neg_disc_sq
  rw [hr] at e3
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem zero_eq_bg_iff {d : ℕ} [NeZero d] (s : ZMod d) : (0 : Fin 2) = RF.bg s ↔ Even s.val := by
  unfold RF.bg
  split_ifs with h <;> simp [h]

theorem pkgInert : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgInertSt Xo c := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hqq hdd hM _ T io e hover y hy C3 nW ν hν
    hin hphi TT θ0 C1 hdeg hrows
  obtain ⟨C, _, _, V, ι, hl, hι, hac, hcpl, hla, hunit, hval⟩ := GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  have hν' := hval y C3 lv.M a nW ν hν
  have hMu := hunit lv.M hM
  rw [← hl] at h2 hqq hdd hin hphi hdeg hrows ⊢
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl (ne_two_of_not_small h2)
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M hMu
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E := hpl.unr V.l V.l_prime h2 hqq hdd
  obtain ⟨Z, hZ, hZne, heven, hbij, hfr⟩ := GlobalTheory.InertLabelling.main E H lv c N pl hpl la T io C V ι hι hl hla hin hphi j
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hpl.psi _).2 ⟨z, rfl⟩
  have hmk := N.R.m_add_three_le_k
  let lab : Lab E Z (N.ordP V.l) :=
    { tau := fun o => tauIn N pl V.l o.1
      n := N.R.k - 1
      j := j
      j' := N.R.m - j
      big := fun _ g s => g = RF.bg s }
  have harith : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => (hfr o.1 0).2 s
      frob := fun o g => (hfr o.1 g).1
      sep := fun x x' hx => (GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.exists_idempotent_of_unramified_place E H lv c T io C V ι hι hunr _ _ (hfr o.1 g).1 }
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s hg => ?_, fun g s hg => ?_⟩
    · show 1 - g = RF.bg s ↔ ¬ g = RF.bg s
      generalize RF.bg s = b
      revert g b
      decide
    · have hg' : g = RF.bg s := hg
      show Dw.mult (tauIn N pl V.l o.1 g s) = N.R.k - 1 + j
      unfold tauIn Datum.mult
      rw [if_pos hg']
      refine (if_pos (hpsi _)).trans ?_
      rw [hp]
      show N.R.k + j - 1 = _
      omega
    · have hg' : ¬ g = RF.bg s := hg
      show Dw.mult (tauIn N pl V.l o.1 g s) = N.R.m - j
      unfold tauIn Datum.mult
      rw [if_neg hg']
      exact (if_neg (not_inPsi_conjugate H _ (hpsi _))).trans hq
  have hsup := _root_.GlobalTheory.RowAt.supply_pairs hUp E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy hunr Z (N.ordP V.l) lab harith
    hbij.2 hrank (show N.R.m - j < N.R.k - 1 by omega) (fun _ => Or.inl ⟨heven, fun s => zero_eq_bg_iff s⟩) a hdom nW ν hν'
  obtain ⟨I, J, fI, fJ, X, F, hn, hbig, hvb⟩ := GlobalTheory.RowAt.supply_extend C V (N.ordP V.l) (RPl N.R) Z (N.R.k - 1) (j + (N.R.m - j))
    (fun _ g s => g = RF.bg s) (fun z g s => Dw.mult (tauIn N pl V.l z g s))
    (fun z g s => gap (Dw.mult (tauIn N pl V.l z g s)) fun i => a (tauIn N pl V.l z g s, i)) nW ν hZne hsup
  have hwt := GlobalTheory.RowAt.wtHyp_gap E H Dw N j pl a hj1 hjm hpsi hp hq hdom (N.ordP V.l) (N.pos V.l) Z RF.bg (tauIn N pl V.l) hZ hbij
    (fun z s => if_pos rfl)
  refine ⟨{ R := { C := C, V := V, hVl := rfl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F
                   hn := fun z => ⟨(hn z).1, (hn z).2.trans (by show j + (N.R.m - j) = N.R.m; omega)⟩ }
            Z := Z
            hZ := hZ
            alt := fun z hz => ⟨heven, fun s => ((hbig z hz 0 s).1).trans (zero_eq_bg_iff s)⟩
            ga := fun z g s => gap (Dw.mult (tauIn N pl V.l z g s)) fun i => a (tauIn N pl V.l z g s, i)
            W := gapW N pl a
            nW := nW
            T := TT
            θ0 := θ0
            rest := restOf N Dw pl a
            ν := ν
            wt := ⟨fun z hz g s k' hk => ?_, hwt.main, hwt.rest_eq⟩
            what₂ := hrows
            deg := hdeg
            val := hvb }, rfl, rfl⟩
  have h := hwt.supp z hz g s k' hk
  exact ⟨h.1, h.2.trans_eq (hbig z hz g s).2.symm⟩

end GlobalTheory.InertPackage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDepthLeResidueCharTwo
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem sum_log_div_log_le_of_rpow_le_prod {ι : Type} (S : Finset ι) (x : ι → ℝ) (r B : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (hx : ∀ i ∈ S, x i ≠ 0) (h : r ^ B ≤ ∏ i ∈ S, x i) :
    ∑ i ∈ S, Real.log (x i) / Real.log r ≤ B := by
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hr0 B) h
  rw [Real.log_rpow hr0, Real.log_prod hx] at h1
  rw [← Finset.sum_div, div_le_iff_of_neg hl]
  exact h1

theorem nuLocC_le_over_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ¬ IsUnit ((p : ℕ) : T.V) → UpperTheory.Depth.SplitAt H.d p → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuLocC Ch e k a n ≤ (((vV T.V ((p : ℕ) : T.Fr) : ℝ) / (e : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  intro p _ hAv hHT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch hy h2 hsp f vd hvd htp e k n a he hdom hn Ap hAp haA
  classical
  obtain ⟨X⟩ := _root_.GlobalTheory.CharDepth.nonempty_valExt T p h2
  obtain ⟨τT, -, hty, -⟩ := _root_.GlobalTheory.CharDepth.exists_types_valuationRing E H l c T io p X
  obtain ⟨hw0, happ⟩ := UpperTheory.cmDatum_splitPlaces_conj_stable p Fact.out E H hsp X.C X.v X.O X.ints X.nonunit.out
  obtain ⟨xs, hxs, hprod⟩ := GlobalTheory.T.integralChart_colength_bound_prime_two p hAv E H Dw l Xo c T io y Ch X hy f vd htp
  obtain ⟨N, u, hu, hspan⟩ := GlobalTheory.T.hodgeTate_inclusion_integralChart p hHT E H Dw l Xo c T io y Ch X hy
  have h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C) := map_natCast _ _
  have h2C0 : ((p : ℕ) : X.C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h2O0 : ((p : ℕ) : X.O) ≠ 0 := fun h => h2C0 (by rw [← h2C, h, map_zero])
  have hr0 : (0 : ℝ) < (X.v ((p : ℕ) : X.C) : ℝ) := by
    have : X.v ((p : ℕ) : X.C) ≠ 0 := (Valuation.ne_zero_iff _).2 h2C0
    exact_mod_cast pos_iff_ne_zero.2 this
  have hr1 : (X.v ((p : ℕ) : X.C) : ℝ) < 1 := by
    have hle : X.v ((p : ℕ) : X.C) ≤ 1 := by rw [← h2C]; exact X.ints.map_le_one _
    have hne : X.v ((p : ℕ) : X.C) ≠ 1 := fun h =>
      X.nonunit.out (X.ints.isUnit_iff_valuation_eq_one.2 (by rw [h2C]; exact h))
    exact_mod_cast lt_of_le_of_ne hle hne
  set r : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hr
  have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
  have hxs0 : ∀ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (lt_of_lt_of_le (Real.rpow_pos_of_pos hr0 _) hprod).ne'
  have hxs0' : ∀ τ, InPsi H τ → xs τ ≠ 0 := fun τ hτ h =>
    hxs0 τ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) (by rw [h]; rfl)
  let len : (E →+* ℂ) → ℝ := fun τ => if InPsi H τ then Real.log (xs τ) / Real.log r else (Dw.q : ℝ)
  have hlen0 : ∀ τ, 0 ≤ len τ := by
    intro τ
    by_cases hτ : InPsi H τ
    · simp only [len, if_pos hτ]
      have h1 := (GlobalTheory.T.exists_flag_characters_leading_minors_colength X.C X.v X.O X.ints _ _ _ _ _ (hxs τ hτ) (hxs0' τ hτ)).1
      exact div_nonneg_of_nonpos (Real.log_nonpos (xs τ).2 (by exact_mod_cast h1)) hlog.le
    · simp only [len, if_neg hτ]
      exact Nat.cast_nonneg _
  have key := GlobalTheory.T.chartDepth_le_of_characterFlags E H Dw l Xo c T io y Ch p X _ hty (fun τ => ⟨H.w0, hw0 _⟩)
    (fun x hx => by
      obtain ⟨M, hM, hM'⟩ := happ x hx
      exact ⟨M, hM, fun τ => hM' _⟩) e k n a he hdom hn len hlen0 (by
      intro τ
      by_cases hτ : InPsi H τ
      · obtain ⟨-, χ, hχ, hχ'⟩ := GlobalTheory.T.exists_flag_characters_leading_minors_colength X.C X.v X.O X.ints _ _ _ _ _ (hxs τ hτ) (hxs0' τ hτ)
        refine ⟨χ, hχ, fun i => ?_⟩
        have hpos : (0 : ℝ) < xs τ := by exact_mod_cast pos_iff_ne_zero.2 (hxs0' τ hτ)
        have : r ^ len τ = xs τ := by
          simp only [len, if_pos hτ]
          rw [Real.rpow_def_of_pos hr0, mul_div_cancel₀ _ hlog.ne, Real.exp_log hpos]
        rw [← hr, this]
        exact_mod_cast hχ' i
      · obtain ⟨χ, hχ, hχ'⟩ := _root_.GlobalTheory.CharDepth.exists_chars_leading_minors_ge X.C X.v X.O X.ints _ _ N _ _
          (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X _ hty τ).2 u hu ((p : ℕ) : X.O) h2O0
          (hspan _ (by
            rw [h2C]
            have hle : X.v ((p : ℕ) : X.C) ≤ 1 := by exact_mod_cast hr1.le
            exact pow_le_of_le_one zero_le hle (by have := (Fact.out : p.Prime).two_le; omega)))
        refine ⟨χ, hχ, fun i => ?_⟩
        have hm : Dw.mult τ = Dw.q := if_neg hτ
        have : r ^ len τ = ((X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ^ Dw.mult τ : NNReal) : ℝ) := by
          simp only [len, if_neg hτ]
          rw [Real.rpow_natCast, h2C, hm, NNReal.coe_pow]
        rw [← hr, this]
        exact_mod_cast hχ' i)
  refine key.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left ?_ ?_))
  · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => InPsi H τ)]
    refine add_le_add ?_ (le_of_eq ?_)
    · have hsum := sum_log_div_log_le_of_rpow_le_prod _ (fun τ => (xs τ : ℝ)) r _ hr0 hr1 hxs0 hprod
      refine le_trans ?_ (mul_le_mul_of_nonneg_right hsum hAp)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun τ hτ => ?_
      have hτ' : InPsi H τ := (Finset.mem_filter.1 hτ).2
      have h0 := hlen0 τ
      simp only [len, if_pos hτ'] at h0 ⊢
      exact mul_le_mul_of_nonneg_left (haA τ hτ') h0
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have hτ' : ¬ InPsi H τ := (Finset.mem_filter.1 hτ).2
      simp only [len, if_neg hτ']
  · have h0 := GlobalTheory.vV_algebraMap_nonneg_dvr T ((p : ℕ) : T.V)
    rw [map_natCast] at h0
    exact div_nonneg (by exact_mod_cast h0) (Nat.cast_nonneg _)

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProof
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LargePkg

theorem not_inPsi_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  unfold InPsi at h h'
  rw [ComplexEmbedding.conjugate_coe_eq, h] at h'
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h'
  have e := H.sqrt_neg_disc_sq
  rw [hr] at e
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem pkg_of_supply (P : RF.Par) (l : ℕ) {C : Type} [Field C] (V : VF C) (hV : V.l = l) (Z : Finset P.Pl)
    (hZ : RF.IsReps P Z) (hw : ∀ z, 0 ≤ P.w z) (big : P.Pl → Fin 2 → ZMod P.d → Prop)
    (rk : P.Pl → Fin 2 → ZMod P.d → ℕ) (b : P.Pl → Fin 2 → ZMod P.d → ℕ → ℕ) (K s nW : ℕ) (ν : ℝ)
    (hK : ∀ z g a, rk z g a ≤ K) (hb : ∀ z g a i j, i ≤ j → j < rk z g a → b z g a j ≤ b z g a i)
    (h0 : ∀ z g a, 0 < rk z g a → b z g a 0 ≤ s * (l - 1)) (hrows : 2 * K * s * Z.card ≤ nW)
    (hS : Supply V P.d P.Pl Z (P.k - 1) P.m big rk (fun z g a => gap (rk z g a) (b z g a)) nW ν) :
    ∃ Pk : RF.PkgZero P l, Pk.ν = ν := by
  obtain ⟨I, J, fI, fJ, X, F, hn, hrk, hval⟩ := hS
  refine ⟨{ R := { C := C, V := V, hVl := hV, I := I, J := J, X := X, F := F, hn := hn }
            Z := Z, hZ := hZ, ga := fun z g a => gap (rk z g a) (b z g a), K := K, s := s, nW := nW, T := 1, ν := ν
            T_one := le_rfl, w_nonneg := hw, supp := ?_, first := ?_, what₂ := hrows, val := hval }, rfl⟩
  · intro z hz g a k hk
    obtain ⟨h1, h2⟩ := (GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)).1 k hk
    exact ⟨h1, h2.trans_eq (hrk z hz g a).2.symm, h2.trans (hK z g a)⟩
  · intro z _ g a
    obtain ⟨h1, h2⟩ := GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)
    rcases Nat.eq_zero_or_pos (rk z g a) with h | h
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ?_) (Nat.zero_le _)
      by_contra hk
      have := h1 k hk
      omega
    · exact le_of_eq_of_le ((h2 K (hK z g a)).1 0 h) (h0 z g a h)

theorem pkg_of_labels (hU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {lv : Level H}
    {Xo : Moduli Dw lv} {c : Coeff lv} [StarRing (𝓞 E)] (hstar : ∀ x : 𝓞 E, star x = H.bar x)
    (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ N.R.m)
    (hpsi : ∀ z, InPsi H (pl z)) (hp : Dw.p = (N.R.sigW j).1) (hq : Dw.q = (N.R.sigW j).2) (ha : DomW Dw a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (hy : y.IsAlg) (C3 : IntChart T io y)
    {C : Type} [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C) (hι : EmbOK T V ι) {k : ℕ}
    (Y : FBChart C V (𝓞 E) (chD C3.ch)) (hY : IsBC C3 ι k Y) (hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E)
    (nW : ℕ) (ν : ℝ) (hν : (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW)
    (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (sel : ZMod d → Fin 2)
    (hsel : (Even d ∧ ∀ s : ZMod d, (0 = sel s ↔ Even s.val)) ∨ ∀ s, 0 = sel s)
    (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ))
    (htau : ∀ z g s, tau z g s = if g = sel s then pl (pos z s.val) else ComplexEmbedding.conjugate (pl (pos z s.val)))
    (Z : Finset (RPl N.R)) (hZ : RF.IsReps (parAt N j d pos) Z) (hne : Z.Nonempty)
    (hbij : Function.Bijective fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2)
    (hfrob : ∀ z g, FrobOrd V io ι (tau z g)) (hw : ∀ z, 0 ≤ N.w j z) (s : ℕ)
    (hs : ∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (V.l - 1)) (hrows : 2 * N.R.r * s * N.R.f ≤ nW) :
    ∃ Pk : RF.PkgZero (parAt N j d pos) V.l, Pk.ν = ν := by
  have hk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  let lab : Lab E Z d := ⟨fun o => tau o.1, N.R.k - 1, j, N.R.m - j, fun _ g s => g = sel s⟩
  have hconj : ∀ z s, tau z 1 s = ComplexEmbedding.conjugate (tau z 0 s) := by
    intro z s
    rw [htau, htau]
    generalize sel s = g
    fin_cases g
    · simp
    · have : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
        ext x; simp
      simp [this]
  have hA : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => hconj o.1 s
      frob := fun o g s x => hfrob o.1 g s x
      sep := fun x x' hx => (GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (hbij.1 h)
      unr := fun o g => _root_.GlobalTheory.exists_idempotent_of_unramified_place E H lv c T io C V ι hι hunr d (tau o.1 g) (hfrob o.1 g) }
  have hR : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s h => ?_, fun g s h => ?_⟩
    · change 1 - g = sel s ↔ ¬ g = sel s
      generalize sel s = g'
      revert g g'
      decide
    · change Dw.mult (tau o.1 g s) = N.R.k - 1 + j
      rw [htau, if_pos (show g = sel s from h), Datum.mult]
      exact (if_pos (hpsi _)).trans (by omega)
    · change Dw.mult (tau o.1 g s) = N.R.m - j
      rw [htau, if_neg (show ¬ g = sel s from h), Datum.mult]
      exact (if_neg (not_inPsi_conj H (hpsi _))).trans hq'
  have h1 := _root_.GlobalTheory.RowAt.supply_pairs hU E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hunr Z d lab hA hbij.2 hR
    (show N.R.m - j < N.R.k - 1 by omega) (fun _ => hsel) a ha nW ν hν
  have hm : lab.j + lab.j' = N.R.m := show j + (N.R.m - j) = N.R.m by omega
  rw [hm] at h1
  have h2 := GlobalTheory.RowAt.supply_extend C V d (RPl N.R) Z (N.R.k - 1) N.R.m (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) nW ν hne h1
  have hcard : Z.card ≤ N.R.f := by
    refine (Finset.card_le_univ Z).trans_eq ?_
    simp [Ranks.f_eq_ord, Formalism.HC.Frame.card_A]
  refine pkg_of_supply (parAt N j d pos) V.l V rfl Z hZ hw (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s i => a (tau z g s, i)) N.R.r s nW ν ?_ ?_ ?_ ?_ h2
  · intro z g s
    unfold Datum.mult Ranks.r
    split_ifs <;> omega
  · intro z g s i i' h h'
    exact ha (tau z g s) ⟨i, h.trans_lt h'⟩ ⟨i', h'⟩ h
  · intro z g s h
    exact hs _ h
  · exact (Nat.mul_le_mul_left _ hcard).trans hrows

theorem pkgZero : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgZeroSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hT hp hq ha la h2 hlq hld hM _ T io e hO y hy C3 nW ν hν
    hphi hw s hs hrows
  obtain ⟨C, _, _, V, ι, hV, hι, hac, hcpl, hla, hunit, hnu⟩ := _root_.GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hO
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl (hV ▸ ne_two_of_not_small h2)
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  have hν' := hnu y C3 lv.M a nW ν hν
  rw [← hV] at h2 hlq hld hphi hs ⊢
  have hunr := hT.unr V.l V.l_prime h2 hlq hld
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  by_cases hin : Inert N V.l
  · obtain ⟨Z, hZ, hne, hev, hbij, hfr⟩ := _root_.GlobalTheory.InertLabelling.main E H lv c N pl hT la T io C V ι hι hV hla hin hphi j
    refine ⟨N.ordP V.l, inferInstance, N.pos V.l, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' (N.ordP V.l) (N.pos V.l) RF.bg (Or.inl ⟨hev, fun s => ?_⟩) (tauIn N pl V.l) (fun _ _ _ => rfl)
      Z hZ hne hbij (fun z g => (hfr z g).1) hw s hs hrows⟩
    unfold RF.bg
    split_ifs with h <;> simp [h]
  · have hsp : N.cls V.l = PrimeClass.splitK := by
      unfold Inert NumDatum.cls primeClass at *
      rw [if_neg h2, if_neg hlq, if_neg hld] at hin ⊢
      split_ifs at hin ⊢ <;> simp_all
    obtain ⟨d, _, pos, Z, hZ, hne, hbij, hfr⟩ := GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime E H lv c N pl hT la T io C V ι hι hV hla hsp j
    exact ⟨d, inferInstance, pos, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' d pos (fun _ => 0) (Or.inr fun _ => rfl) (tauSp N pl pos) (fun _ _ _ => rfl)
      Z hZ hne hbij hfr hw s hs hrows⟩

end GlobalTheory.LargePkg
end

