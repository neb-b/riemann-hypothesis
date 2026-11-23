module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeTransform
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitTrivialOnBothAxes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeUnit
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransform
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.WitnessIsFormalParam
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientBilinear
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

theorem frame_gauge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ P : Matrix (Fin d') (Fin d) k, Q.IsDiff g gB P → ∃ Z : Matrix (Fin d) (Fin d) k, ∀ a, bil (g.B.ad a) 1 1 + (rho g.B a).transpose * Z - Z * rho g.B (star a) = P.transpose * bil (gB.B.ad a) 1 1 * P := by
  intro E _ _ _ H _ hstar X t k _ _ p _ _ x Q d d' g gB P hP
  obtain ⟨w, hw⟩ := Q.bun
  obtain ⟨Qs, hc, hQ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main E H hstar X t k p x Q d d' g gB
  have hl := GlobalTheory.T.abelian_quotient_differential_matrix E H hstar X t k p x Q d d' g gB P hP Qs hc hQ
  obtain ⟨lam, hax, hlam⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.Lamex.exists_lam E H hstar X t k p x Q d d' g gB w hw Qs hc hQ
  refine ⟨bil lam 1 1, fun a => ?_⟩
  obtain ⟨wL, hwL, hrL⟩ := g.frame.ad a
  obtain ⟨wB, hwB, hrB⟩ := gB.frame.ad a
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio E H hstar X t k p x Q d d' g gB w hw a wL wB hwL hwB
  obtain ⟨h0, h1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes E H hstar X t k p x Q d d' g gB w hw Qs hc hQ a wL wB hwL hwB hrL hrB u hu
  obtain rfl := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes E H hstar X t k p x Q d g u h0 h1
  have hrel := GlobalTheory.T.abelian_quotient_gauge_relation E H hstar X t k p x Q d d' g gB w hw Qs hc hQ lam hlam a wL wB hwL hwB hrL hrB hu
  rw [← hstar a] at hrel
  obtain ⟨hA, hbA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ k d d' Qs (gB.B.ad a) hc ⟨gB.B.adjoint_zero_fst a, gB.B.adjoint_zero_snd a⟩
  have hadx : AxOne (g.B.ad a) := ⟨g.B.adjoint_zero_fst a, g.B.adjoint_zero_snd a⟩
  have hcs : ∀ (b : 𝓞 E) (i : Fin d), MvPowerSeries.constantCoeff (g.B.A.act b i) = 0 := fun b i => g.B.A.const b i
  have hp0 : ∀ i : Fin d, MvPowerSeries.constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => by simp [pt]
  have hp2 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (pt k (n := 2) d j i) = 0 := fun j i => by simp [pt]
  obtain ⟨-, -, -, hT, hbT, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (pt k d 0) (g.B.A.act (star a)) hax hax hp0 (hcs _)
  obtain ⟨-, -, -, hS, hbS, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (g.B.A.act a) (pt k d 0) hax hax (hcs _) hp0
  rw [germ_comp1_zero_point_left _ (hp2 0)] at hT hbT
  rw [germ_comp1_zero_point_left _ (hp2 1)] at hS hbS
  obtain ⟨-, -, e1, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d (subQ Qs (gB.B.ad a)) _ (pt k d 0) (pt k d 0) hA hT hp0 hp0
  obtain ⟨-, -, e2, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d _ (g.B.ad a) (pt k d 0) (pt k d 0) hS hadx hp0 hp0
  have h := congrArg (fun f => bil f 1 1) hrel
  beta_reduce at h
  rw [e1, e2, hbT, hbS, hbA, hl, lin_pt_eq_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  change _ + (rho g.B a).transpose * _ - _ * rho g.B (star a) = _
  change _ + bil lam 1 1 * rho g.B (star a) = (rho g.B a).transpose * bil lam 1 1 + _ at h
  rw [eq_sub_of_add_eq h]
  abel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartOfBasis
section
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Conj.GermInh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem chart_of_basis (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {n : ℕ}
    (tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (h : GlobalTheory.ChartCompare.IsTanBasisG t x0 tg) :
    ∃ (G : Germ.FGLaw S (Fintype.card (Fin n))) (A : Germ.OAct (𝓞 E) G)
      (tg' : Fin (Fintype.card (Fin n)) → (Sp (DualNumber S) ⟶ t.G.left)) (x : ∀ m, jOG x0 _ m 1 ⟶ t.G),
      IsChartG t x0 _ G.F A.act tg' (fun l j => if l = j then 1 else 0) x ∧ (∀ l, IsTanAtG t x0 (tg' l)) ∧
      ∀ w, IsTanAtG t x0 w → ∃! a : Fin (Fintype.card (Fin n)) → S, IsCombAtG t x0 tg' a w := by
  obtain ⟨d, G, A, uvec, x, rfl, hu, hc⟩ := GlobalTheory.ChartData.exists_isChartG_of_basis E H X0 t S x0 _ tg h.1 h.2
  let e := Fintype.equivFin (Fin n)
  refine ⟨G, A, fun i => tg (e.symm i), x, ⟨hc.zero, hc.trunc, hc.law, hc.act, fun l => ?_, fun v => ?_⟩,
    fun l => h.1 _, fun w hw => ?_⟩
  · have := hc.tan (e.symm l)
    convert this using 2 with j
    rw [hu]; simp [e, Fin.ext_iff, eq_comm]
  · refine ⟨v, fun j => by simp, fun a ha => funext fun j => by simpa using ha j⟩
  · obtain ⟨a, ha, hu⟩ := h.2 w hw
    refine ⟨fun i => a (e.symm i), ha, fun b hb => ?_⟩
    have := hu (fun l => b (e l)) (by simpa only [e, Equiv.apply_symm_apply] using hb)
    funext i; rw [← this]; simp

theorem germ_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0), ∃ d, Nonempty (GermAt t x d) := by
  intro E _ _ _ H _ hs X0 t hp S _ _ x0
  obtain ⟨n, tg, h⟩ := GlobalTheory.ChartDataChecks.premises_met t x0
  obtain ⟨G, A, tg', x, hc, ht, hb⟩ := chart_of_basis t x0 tg h
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, -, htr, hfa, had, -⟩ := GermB.frameSt_holds E H X0 t S x0 _ G A _ tg' _ x hc
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg' _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨_, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg', hc, ht, hb, hfr, htr, hfa⟩⟩⟩

section One
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

end One

end GlobalTheory.CompanionTheory.Ar.Conj.GermInh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombination
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.VanDescent

theorem exists_closed_mem_notMem : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F), LocallyOfFiniteType p → ∀ (U O : Y.Opens), ¬ U ≤ O → ∃ z : Y, IsClosed ({z} : Set Y) ∧ z ∈ U ∧ z ∉ O := by
  intro F _ Y p hp U O hUO
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, hzU, hzO⟩ := Set.not_subset.1 hUO
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (O : Set Y)ᶜ)
    ⟨z, hzU, hzO⟩ (U.isOpen.isLocallyClosed.inter O.isOpen.isClosed_compl.isLocallyClosed)
  exact ⟨y, hc, hy, hy'⟩

theorem secVal_eq_zero_of_le {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ}
    {B : LB Y} {O : Y.Opens} (s : B.Sec) (hs : nonzeroLocus s ≤ O) (i : B.ι) (y : CxPts p σ)
    (hy : y ∉ ptsIn p σ O) : secVal p σ s i y = 0 := by
  by_contra h
  by_cases hi : y ∈ ptsIn p σ (B.U i)
  · exact hy (ptsIn_mono hs ((secVal_ne_zero_iff s hi).1 h))
  · exact h (by rw [secVal_apply]; exact ev_of_notMem hi _)

theorem vanish_descent : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  intro F _ Y p σ hp B hB O x hx
  let J := {z : Y // IsClosed ({z} : Set Y) ∧ z ∉ O}
  have hpt := fun j : J => GlobalTheory.CompanionTheory.Ar.ClosedPt.exists_residue_eval F Y p σ hp B hB j.1 j.2.1
  choose K instF instA instFD e he_smul he_ne he_pt using hpt
  let G : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    Submodule.span ℂ {f | ∃ s : B.Sec, nonzeroLocus s ≤ O ∧ secVal p σ s = f}
  let Z : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    { carrier := {v | ∀ i y, y ∉ ptsIn p σ O → v i y = 0}
      add_mem' := fun {u v} hu hv i y hy => by simp [hu i y hy, hv i y hy]
      zero_mem' := fun i y _ => rfl
      smul_mem' := fun c v hv i y hy => by simp [hv i y hy] }
  have hGZ : G ≤ Z := Submodule.span_le.2 (by
    rintro _ ⟨s, hs, rfl⟩ i y hy
    exact secVal_eq_zero_of_le s hs i y hy)
  have key : ∀ (n : ℕ) (b : Fin n → B.Sec) (d : Fin n → ℂ) (g : B.ι → CxPts p σ → ℂ), g ∈ G →
      (∑ l, d l • secVal p σ (b l) + g) ∈ Z → (∑ l, d l • secVal p σ (b l) + g) ∈ G := by
    intro n
    induction n with
    | zero => intro b d g hg _; simpa using hg
    | succ m ih =>
      intro b d g hg hv
      by_cases H : ∀ a : Fin (m + 1) → F,
          (∀ j, ∑ l, algebraMap F (K j) (a l) * e j (b l) = 0) → a = 0
      · have hz : ∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ →
            ∑ l, d l * τ (e j (b l)) = 0 := by
          intro j τ hτ
          obtain ⟨y, i, hyz, hy⟩ := he_pt j τ hτ
          have hyO : y ∉ ptsIn p σ O := fun h => j.2.2 (hyz ▸ mem_ptsIn.1 h)
          have h1 := hv i y hyO
          have h2 := hGZ hg i y hyO
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h2, add_zero,
            hy] at h1
          exact h1
        have hd : d = 0 := GlobalTheory.CompanionTheory.Arith.DedekindDescent.linIndep_descent F σ J K (Fin (m + 1)) (fun l j => e j (b l)) H d hz
        subst hd
        simpa using hg
      · push Not at H
        obtain ⟨a, ha0, ha⟩ := H
        have hes : ∀ j, e j (∑ l, algX p ⊤ (a l) • b l) = 0 := fun j => by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, he_smul]
          exact ha0 j
        have hsO : nonzeroLocus (∑ l, algX p ⊤ (a l) • b l) ≤ O := by
          by_contra h
          obtain ⟨z, hzc, hzs, hzO⟩ := exists_closed_mem_notMem F Y p hp _ O h
          exact he_ne ⟨z, hzc, hzO⟩ _ hzs (hes _)
        have hsG : secVal p σ (∑ l, algX p ⊤ (a l) • b l) ∈ G :=
          Submodule.subset_span ⟨_, hsO, rfl⟩
        have hsv : secVal p σ (∑ l, algX p ⊤ (a l) • b l) = ∑ l, σ (a l) • secVal p σ (b l) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, secVal_smul]
        rw [hsv] at hsG
        obtain ⟨l₀, hl₀⟩ := Function.ne_iff.1 ha
        have hσ : σ (a l₀) ≠ 0 := (map_ne_zero σ).2 hl₀
        obtain ⟨c, hc⟩ : ∃ c, c = d l₀ * (σ (a l₀))⁻¹ := ⟨_, rfl⟩
        have hdc : d l₀ = c * σ (a l₀) := by rw [hc, inv_mul_cancel_right₀ hσ]
        have heq : ∑ l, d l • secVal p σ (b l) + g =
            ∑ i, (d (l₀.succAbove i) - c * σ (a (l₀.succAbove i))) •
              secVal p σ (b (l₀.succAbove i)) + (g + c • ∑ l, σ (a l) • secVal p σ (b l)) := by
          rw [Fin.sum_univ_succAbove _ l₀, Fin.sum_univ_succAbove (fun l => σ (a l) • _) l₀]
          simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdc]
          module
        rw [heq] at hv ⊢
        exact ih _ _ _ (G.add_mem hg (G.smul_mem c hsG)) hv
  have hxspan : x ∈ Submodule.span ℂ (Set.range (SecC.of p σ : B.Sec → SecC p σ B)) :=
    by rw [SecC.span_range_of (p := p) (σ := σ) (B := B)]; exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hxspan
  choose b hb using fun i => (g i).2
  have hval : SecC.val x = ∑ l, f l • secVal p σ (b l) + 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hfg, add_zero, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← hb l, SecC.val_of]
  have hxZ : SecC.val x ∈ Z := hx
  rw [hval] at hxZ
  have hmem := key n b f 0 G.zero_mem hxZ
  rw [← hval] at hmem
  obtain ⟨m, as, ss, hss⟩ := Submodule.mem_span_set'.1 hmem
  choose t ht1 ht2 using fun j => (ss j).2
  exact ⟨m, as, t, ht1, by rw [← hss]; exact Finset.sum_congr rfl fun j _ => by rw [ht2]⟩

end GlobalTheory.CompanionTheory.VanDescent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpenStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_of_stable_under_generalization_specialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k)), StableUnderGeneralization U → StableUnderSpecialization U → IsOpen U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | exact GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem curve0_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 :=
  @PositivityTheory.Xgf.curve_z_ne_zero

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteGroupSchemeSumExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem gm_comp_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp R') (z : Z) :
    gm (r ≫ spMap f) z ⊤ (unitOn u) = gm r z ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  refine (gm_pull r (spMap f) z ⊤ trivial (unitOn u)).symm.trans (congrArg (gm r z ⊤) ?_)
  apply Units.ext
  exact (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

def FG.scaled {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) : FG M Y :=
  ⟨a.K, a.φ, a.ε, scaleGen a.t c, scaleGen_isGen hM a.t a.ht c⟩

theorem FG.v_scaled {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) : (a.scaled hM c).v r z J = gm r z ⊤ c * a.v r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem a.φ r) _) rfl)

theorem exists_root_in_ext (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 1 ≤ n) (c : Kˣ) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (u : K'ˣ),
      u ^ n = Units.map (algebraMap K K').toMonoidHom c := by
  let P : Polynomial K := Polynomial.X ^ n - Polynomial.C (c : K)
  have hdeg : P.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by omega)]
    exact_mod_cast (by omega : n ≠ 0)
  have : FiniteDimensional ℚ P.SplittingField := Module.Finite.trans K _
  obtain ⟨ρ, hρ⟩ := (Polynomial.IsSplittingField.splits P.SplittingField P).exists_eval_eq_zero
    (by rwa [Polynomial.degree_map])
  have hρn : ρ ^ n = algebraMap K P.SplittingField (c : K) := by
    simpa [P, sub_eq_zero, Polynomial.eval_map] using hρ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hρn
    exact (map_ne_zero _).2 c.ne_zero hρn.symm
  refine ⟨P.SplittingField, inferInstance, NumberField.mk, inferInstance, Units.mk0 ρ hρ0, Units.ext ?_⟩
  simpa using hρn

theorem exists_gen_normalised {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Field K] [NumberField K] (n : ℕ)
    (hn : 1 ≤ n) (xl : Sp K ⟶ X) (A : FG M (Sp K))
    (hA : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')),
      (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J →
        e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  obtain ⟨z₀⟩ : Nonempty (Sp K) := inferInstance
  choose d hd using fun χ : Sp K ⟶ X => exists_chart hM (χ z₀)
  have hJ₀ : Good M z₀ d := hd
  obtain ⟨t₀, ht₀, -⟩ := GlobalTheory.ThetaInValues.exists_gen_of_value hM (fun _ : PUnit => xl) (fun _ => (1 : ℤ)) hJ₀ (1 : Kˣ)
  let e₀ : FG M (Sp K) := ⟨PUnit, _, _, t₀, ht₀⟩
  have hs₀ : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), e₀.sum U h = h xl := by
    intro U _ h
    show ∏ _k : PUnit, h xl ^ (1 : ℤ) = _
    simp
  have hg : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), ((e₀.pow n).mul A).sum U h = 1 := by
    intro U _ h
    rw [FG.sum_mul, FG.sum_pow, hs₀, hA]
    exact _root_.mul_inv_cancel _
  obtain ⟨c, hc⟩ := FG.exists_unit hM _ hg
  let c₀ : Kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c
  have hcc : unitOn c₀ = c := by
    apply Units.ext
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val
  obtain ⟨K', iF, iN, iA, u, hu⟩ := exists_root_in_ext K n hn c₀⁻¹
  refine ⟨K', iF, iN, iA, (e₀.pull (spMap (algebraMap K K'))).scaled hM (unitOn u), ?_, ?_⟩
  · intro U _ h
    exact hs₀ U fun q => h (spMap (algebraMap K K') ≫ q)
  · intro Z r z J hJ
    have key : unitOn u ^ n * unitOn (Units.map (algebraMap K K').toMonoidHom c₀) = 1 := by
      have e1 : unitOn u ^ n = unitOn (u ^ n) := (map_pow _ _ _).symm
      have e2 : ∀ a b : K'ˣ, unitOn a * unitOn b = unitOn (a * b) := fun a b => (map_mul _ _ _).symm
      rw [e1, e2, hu, ← map_mul, inv_mul_cancel, map_one]
      exact map_one _
    rw [FG.v_scaled hM _ _ r hJ, FG.v_pull hJ, _root_.mul_pow, _root_.mul_assoc, ← FG.v_pow hJ, ← FG.v_mul hJ,
      hc Z _ z J hJ, ← hcc, gm_comp_spMap_unitOn, ← map_pow, ← map_mul, key, map_one]

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelGenericCover
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem unitAt_of_pow_eq_one {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hN : Flat.NormalCpt ξ)
    {N : ℕ} (hN0 : N ≠ 0) {a : Ω} (ha : a ^ N = 1) (q : Cpt ξ) : unitAt ξ q a :=
  Flat.ZUnit.of_pow_of_normal hN hN0 (by rw [ha]; exact Flat.ZUnit.one)

theorem exists_full_level_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] (i : K →+* Ω) (y : Sp K ⟶ Xo.XF c) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk (spMap i ≫ y ≫ Y.j) ⟶ Y.t.G)), 1 ≤ N → IsFullLevelAt D Y.t (spMap i ≫ y ≫ Y.j) N z ev → ∀ (X : Scheme.{0}) (ξ : Sp Ω ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ f : X ⟶ Y.X, ξ ≫ f = spMap i ≫ y ≫ Y.j → ∃ (t : SAB H X) (_ : SABMap t Y.t f) (ev' : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev' ∧ FullTorsion t.G ξ N ∧ ∀ q : Cpt ξ, unitAt ξ q (z : Ω) := by
  intro E _ _ _ H D l Xo c Y K Ω _ _ _ i y N z ev hN hlev X ξ _ hnorm f hf
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull f Y.t
  have hid : ξ ≫ f = spMap (RingHom.id Ω) ≫ spMap i ≫ y ≫ Y.j := by
    rw [hf]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨ev', hev', -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move E H D Y.X X Y.t t f m Ω Ω (RingHom.id Ω) (spMap i ≫ y ≫ Y.j) ξ hid N z ev hlev
  have hz : Units.map (RingHom.id Ω).toMonoidHom z = z := by ext; rfl
  rw [hz] at hev'
  obtain ⟨hprim, -, -, -, -, hfull, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props E H D X t Ω ξ N hN z ev' hev'
  refine ⟨t, m, ev', hev', hfull, fun q => ?_⟩
  have hpow : (z : Ω) ^ N = 1 := by
    have := congrArg Units.val hprim.pow_eq_one
    simpa using this
  exact unitAt_of_pow_eq_one hnorm (by omega) hpow q

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_component_alg_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c) → Z'.IsGeom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | exact GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundlePullbackGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem exists_sec_cleared : ∀ {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (Mn : Submonoid R) [IsLocalization Mn Rm] {X X' Y : Scheme.{0}} {π : X' ⟶ Spec (CommRingCat.of R)} {π' : Y ⟶ Spec (CommRingCat.of Rm)} {κ : Y ⟶ X'}, IsPullback κ π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))) → ∀ [CompactSpace X'] [QuasiSeparatedSpace X'] {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}, PGen w → L.IsLB → L'.IsLB → ∀ (th : Out.H0 L 1) (ψ : Y ⟶ X) (n : ℕ) (u : FG L Y), (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), u.sum U h = h ψ * (h (κ ≫ F) ^ n)⁻¹) → ∃ (s : Out.H0 L' n), ∃ t ∈ Mn, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → (gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n).val * sval s (r ≫ κ) z J' = GlobalTheory.TwistLoc.gc (r ≫ κ ≫ π) z t * (sval th (r ≫ ψ) z J * ((u.v r z J)⁻¹).val) := by
  intro R Rm _ _ _ Mn _ X X' Y π π' κ H _ _ L L' F w hw hL hL' th ψ n u hu
  have fe : FormEq (Sum.elim (fun k : Fin 1 => ψ ≫ (fun _ : Fin 1 => 𝟙 X) k) u.inv.φ)
      (Sum.elim (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) u.inv.ε)
      (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) (fun _ : Fin 1 => (n : ℤ)) := fun U _ h => by
    have e := FG.sum_inv U u h
    rw [hu U h] at e
    have e' : ∏ k, h (u.inv.φ k) ^ u.inv.ε k = (h ψ * (h (κ ≫ F) ^ n)⁻¹)⁻¹ := e
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, e', Fintype.prod_unique, Category.comp_id, Category.id_comp, Nat.cast_one,
      zpow_one, zpow_natCast, mul_inv, inv_inv, mul_inv_cancel_left]
  obtain ⟨s', hs'⟩ := exists_sec hL fe (pullMulSec th ψ u.inv.t u.inv.ht)
  obtain ⟨t, ht, σ, hσ⟩ := GlobalTheory.TwistLoc.exists_clear_denominator Mn H hL (fun _ : Fin 1 => 𝟙 X' ≫ F)
    (fun _ => (n : ℤ)) s'
  obtain ⟨a, ha⟩ := GlobalTheory.SecPull.exists_down_sec hw hL hL' (fun _ : Fin 1 => 𝟙 X') (fun _ : Fin 1 => 𝟙 X' ≫ F)
    (fun _ => (n : ℤ)) (𝟙 X') (fun _ => by simp) σ
  refine ⟨a, t, ht, fun Z r z J J' hJ hJ' => ?_⟩
  let p : Fin 1 → L.ι := fun _ => J ((r ≫ κ) ≫ F)
  let q : Fin 1 → L'.ι := fun _ => J' (r ≫ κ)
  have m₁ : (r ≫ κ) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X' ≫ F) p :=
    Set.mem_iInter.2 fun _ => hJ ((r ≫ κ) ≫ F)
  have m₂ : (r ≫ κ) z ∈ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') q := Set.mem_iInter.2 fun _ => hJ' (r ≫ κ)
  have m₃ : r z ∈ LB.wchart L (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) p :=
    Set.mem_iInter.2 fun _ => hJ ((r ≫ κ) ≫ F)
  have e₁ := ha Z (r ≫ κ) z p q m₁ m₂
  rw [Category.comp_id] at e₁
  have e₂ := hσ Z r z p m₃
  have e₃ : pw w (fun _ : Fin 1 => 𝟙 X') (fun _ => (n : ℤ)) (r ≫ κ) z p q = gw w (r ≫ κ) z (J ((r ≫ κ) ≫ F)) (J' (r ≫ κ)) ^ n := by
    simp only [pw, Fintype.prod_unique, Category.comp_id, zpow_natCast, p, q]
  have e₄ : sval s' r z J = gs r z (LB.wchart L (fun _ : Fin 1 => κ ≫ 𝟙 X' ≫ F) p) (s'.f p) := sval_of s' r z J p fun _ => by
    simp only [p, Category.assoc, Category.id_comp]
  rw [sval_of a (r ≫ κ) z J' q (fun _ => by simp only [q, Category.comp_id]), ← e₃, e₁, ← _root_.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.one_mul, e₂, ← e₄, hs' Z r z J hJ,
    sval_pullMulSec _ _ _ _ r z hJ, show val u.inv.t r z J = (u.v r z J)⁻¹ from FG.v_inv u r]

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodsSpanPureDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_pure_vectors_periods_span_of_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  exact @PositivityTheory.Xgf.periods_span_pure_decomposition

end GlobalTheory.CompanionTheory.Ar.Fl
end

