module

public import Mathlib
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyUniformisedFormalChartAlgebraicPointStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrime
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColengthBoundPrimeTwo
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem family_cast_iff {V : Type} (P : ∀ s : ℕ, (Fin s → V) → Prop) {n s : ℕ} (h : n = s) (g : Fin s → V) :
    P n (fun i => g (Fin.cast h i)) ↔ P s g := by
  subst h; rfl

theorem colength_bound_at_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∀ (f : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H f vd → ∃ xs : (E →+* ℂ) → NNReal, (∀ τ, InPsi H τ → HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) (xs τ)) ∧ (open Classical in (X.v ((p : ℕ) : X.C) : ℝ) ^ ((f : ℝ) * Dw.q * (1 + vd / 2)) ≤ ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) := by
  intro p _ hAV E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch X hy f vd hTP
  classical
  obtain ⟨U⟩ := GlobalTheory.T.nonempty_uniformised_formal_chart_algebraic_point E H Dw l Xo c T io y Ch hy p X
  obtain ⟨τT, -, hty, hinj, hrt, -⟩ := _root_.GlobalTheory.CharDepth.exists_types_valuationRing E H l c T io p X
  set τO : (E →+* ℂ) → (𝓞 E →+* X.O) := fun τ => X.ι.comp (τT τ) with hτO
  have heig := fun τ => (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X τO hty τ).1
  obtain ⟨n, w, vdi, hwn, hsum, he, hu, hb, hvd⟩ := hTP X.C X.v X.O X.ints τO hinj hrt
  choose t hvd using hvd
  choose s hs hst using fun (i : Fin n) (j : Fin (w i).n) => he i (t i j : 𝓞 E →+* X.O) (t i j).2
  have hp : ∀ τ, InPsi H τ → Dw.p = Dw.mult τ := fun τ h => by
    unfold Datum.mult; exact (if_pos h).symm
  have hq : ∀ τ, ¬ InPsi H τ → Dw.q = Dw.mult τ := fun τ h => by
    unfold Datum.mult; exact (if_neg h).symm
  have hact : actMap U.ι' U.act = fun a i => MvPowerSeries.map X.ι (Ch.actT a i) := funext U.act_eq
  have hnu : ¬ IsUnit ((p : U.T'.V)) := fun h => X.nonunit.out (by have h' := h.map U.ι'; rwa [map_natCast] at h')
  have key := fun i0 : Fin n => hAV U.T'.V hnu U.t.G U.P.D U.P.A U.P.U.toUnifPre _ U.F U.x U.chart (𝓞 E)
    U.t.act.toRingAct U.P.oD U.P.oA U.P.lin U.act U.acts X.C X.v X.O X.ints U.ι' U.ι'_local (w i0) (t i0) (vdi i0) (hvd i0) Dw.p Dw.q
    (fun j i k => X.ι (Ch.uvecT ⟨s i0 j, Fin.cast (hp _ (hs i0 j)) i⟩ k))
    (fun j => by
      rw [hact, hst i0 j]
      exact (family_cast_iff (fun _ g => IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO (s i0 j)) g)
        (hp _ (hs i0 j)) (fun i k => X.ι (Ch.uvecT ⟨s i0 j, i⟩ k))).2 (heig (s i0 j)))
    (fun σ hσ => by
      obtain ⟨τ, hτ, rfl⟩ := hb i0 σ hσ
      rw [hact]
      exact ⟨_, (family_cast_iff (fun _ g => IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) g)
        (hq _ hτ) (fun i k => X.ι (Ch.uvecT ⟨τ, i⟩ k))).2 (heig τ)⟩)
  choose xs hxs hle using key
  let σs : (Σ i : Fin n, Fin (w i).n) → (E →+* ℂ) := fun z => s z.1 z.2
  have hmem : ∀ i j, τO (s i j) ∈ Emb (O := X.O) (w i).e := fun i j => by rw [← hst i j]; exact (t i j).2
  have hsinj : Function.Injective σs := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : s i j = s i' j' := h
    obtain rfl : i = i' := (hu _ (hs i j)).unique (hmem i j) (by rw [h']; exact hmem i' j')
    have : j = j' := by
      apply (t i).injective
      apply Subtype.ext
      rw [hst i j, hst i j', h']
    rw [this]
  have hssurj : ∀ τ, InPsi H τ → ∃ z, σs z = τ := fun τ h => by
    obtain ⟨i, hi, -⟩ := hu τ h
    refine ⟨⟨i, (t i).symm ⟨τO τ, hi⟩⟩, hinj ?_⟩
    have := hst i ((t i).symm ⟨τO τ, hi⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  let xz : (Σ i : Fin n, Fin (w i).n) → NNReal := fun z => xs z.1 z.2
  refine ⟨Function.extend σs xz (fun _ => 1), ?_, ?_⟩
  · intro τ hτ
    obtain ⟨⟨i, j⟩, rfl⟩ := hssurj τ hτ
    rw [hsinj.extend_apply, ← U.law_eq]
    exact (family_cast_iff (fun _ g => HasAF X.v (U.F.mapF U.ι') g (xs i j))
        (hp _ (hs i j)) (fun i' k => X.ι (Ch.uvecT ⟨s i j, i'⟩ k))).1 (hxs i j)
  · have hprod : ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), ((Function.extend σs xz (fun _ => 1) τ : NNReal) : ℝ) =
        ∏ z, (xz z : ℝ) := by
      symm
      refine Finset.prod_bij (fun z _ => σs z) (fun z _ => by simpa using hs z.1 z.2) (fun j _ j' _ h => hsinj h)
        (fun τ hτ => ?_) (fun j _ => by rw [hsinj.extend_apply])
      obtain ⟨j, hj⟩ := hssurj τ (by simpa using hτ)
      exact ⟨j, Finset.mem_univ _, hj⟩
    have h2 : algebraMap X.O X.C (p : X.O) = (p : X.C) := map_natCast _ _
    have hpp : p.Prime := Fact.out
    have hr0 : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
      have : X.v (p : X.C) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
      exact_mod_cast pos_iff_ne_zero.2 this
    have hr1 : (X.v (p : X.C) : ℝ) ≤ 1 := by
      have hle : X.v (p : X.C) ≤ 1 := by rw [← h2]; exact X.ints.map_le_one _
      exact_mod_cast hle
    have h1 : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      rw [div_le_one (by linarith)]; linarith
    have hi : ∀ i, (X.v (p : X.C) : ℝ) ^ (((w i).n : ℝ) * Dw.q * (1 + vdi i / 2)) ≤ ∏ j, (xs i j : ℝ) := fun i => by
      have h3 := NNReal.coe_le_coe.2 (hle i)
      rw [h2, NNReal.coe_rpow, NNReal.coe_prod] at h3
      refine le_trans (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ?_) h3
      have : (0 : ℝ) ≤ ((w i).n : ℝ) * Dw.q := by positivity
      nlinarith
    have hexp : (f : ℝ) * Dw.q * (1 + vd / 2) = ∑ i, ((w i).n : ℝ) * Dw.q * (1 + vdi i / 2) := by
      have a1 : (f : ℝ) = ∑ i, ((w i).n : ℝ) := by rw [← hwn]; push_cast; rfl
      have a2 : ∑ i, ((w i).n : ℝ) * Dw.q * (1 + vdi i / 2) =
          Dw.q * (∑ i, ((w i).n : ℝ)) + Dw.q / 2 * ∑ i, ((w i).n : ℝ) * vdi i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [a2, hsum, ← a1]; ring
    have hfin : (X.v (p : X.C) : ℝ) ^ ((f : ℝ) * Dw.q * (1 + vd / 2)) ≤ ∏ z, (xz z : ℝ) := by
      rw [hexp, Real.rpow_sum_of_pos hr0, Fintype.prod_sigma]
      exact Finset.prod_le_prod₀ (fun i _ => (Real.rpow_pos_of_pos hr0 _).le) fun i _ => hi i
    convert hfin using 1

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_generators_least_value_over_level_prime : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) → ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → l.M = g' * g → ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) → l.Mb = Ideal.span {π * π'} → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ¬ IsUnit ((g : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → 2 * (Dw.p + Dw.q) ≤ n → 1 ≤ n → 0 < e → DF Dw a < g - 1 → 4 * DF Dw a + 4 ≤ g' → (DF Dw a : ℝ) * M0 < g' → (⨅ f ∈ thGen Xo c nab a n, nval T.V e (evI y f)) + nval T.V e (∏ τ : E →+* ℂ, (io (embK c τ (star π * star π'))) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) ≤ ((((vV T.V ((g : ℕ) : T.Fr) : ℤ) : ℝ) * DF Dw a / (g - 1) + (Dw.p + Dw.q : ℕ) * r * Φ / (4 * g') + 2 * (DF Dw a : ℝ) ^ 2 * Φ / g') / e : ℝ) := by
  first | exact @GlobalTheory.LevelPrimePoint.least_value_le | exact GlobalTheory.LevelPrimePoint.least_value_le | (intros; apply GlobalTheory.LevelPrimePoint.least_value_le <;> assumption)
end

