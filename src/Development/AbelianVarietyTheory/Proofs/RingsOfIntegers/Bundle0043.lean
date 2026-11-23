module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSymmetricTranslationUnitsEqKappaRatio
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConnectionValueLevelKappaMulPullback
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem kappa_mul_pullM_mul_expS {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
    (K : Type) [CommRing K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O)
    (hh : MvPowerSeries.constantCoeff h = 0) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d)
    (hκ : IsKappa B K h w0 mu N κ) (g : PS V n d) :
    FB.toK K (κ * pullM B mu g) * FB.expS K ((N : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
        (FB.toK K g * FB.expS K (((1 : ℕ) : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0))) := by
  have hpt : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V :=
    fun b i => by rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b i]; exact Ideal.zero_mem _
  have h0 : ∀ (b : Fin n) (i : Fin d),
      MvPowerSeries.constantCoeff (matV B mu (fun j => pt V (n := n) d j) b i) = 0 :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n mu mu (fun j => pt V (n := n) d j) (fun j => pt V (n := n) d j) hpt hpt).2.2.2.2.2.1
  have hy : ∀ b : Fin n,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) := by
    intro b i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap V K) (matV B mu (fun j => pt V (n := n) d j) b i)) = 0
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  have hact : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (B.actK K w0) := by
    intro i
    unfold FB.actK
    rw [MvPowerSeries.constantCoeff_map, B.A.const w0 i, map_zero]
  have hL0 : MvPowerSeries.constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.pair_points_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_comp1 _ _ hact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0))) _ hh
  have hsm : ∀ (c : K) (f : PS K n d), MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (c • f) = 0 := by
    intro c f hf
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hS : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b)) _ hL0
  have hA : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n)
      ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (hy b)) _ hL0
  have hsub : MvPowerSeries.HasSubst
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h0 p.1 p.2
  have hpull : FB.toK K (pullM B mu g) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) (FB.toK K g) := by
    have hC := (_root_.GlobalTheory.PlaceInt.evC_spec V (Fin n × Fin d) (Fin n × Fin d) (Fin n × Fin d)
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2)
      (fun p => by rw [h0]; exact Ideal.zero_mem _)).2.2.1 (fun p => h0 p.1 p.2)
    unfold pullM evV
    rw [hC]
    unfold FB.toK ev
    exact MvPowerSeries.map_subst hsub _
  have hevy : ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
      (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0) := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_sum hy]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_ev' _ _ hy (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b))]
    congr 1
    funext j
    fin_cases j
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.evP_pt _ hy b
  have hm : FB.toK K (κ * pullM B mu g) = FB.toK K κ * FB.toK K (pullM B mu g) :=
    map_mul (MvPowerSeries.map (algebraMap V K)) κ (pullM B mu g)
  have hk := hκ
  unfold IsKappa at hk
  have hAS := hsm (N : K) _ hS
  rw [Nat.cast_one, one_smul, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_mul _ hy, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_expS _ hy _ hS,
    hevy, ← hpull, hm, hk, _root_.mul_comm (FB.expS K _) (FB.toK K (pullM B mu g)), _root_.mul_assoc,
    ← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_expS_add _ _ (by rw [map_sub, hA, hAS, sub_zero]) hAS, sub_add_cancel]

theorem nabValN_kappa_mul_pullM : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O), MvPowerSeries.constantCoeff h = 0 → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d), IsKappa B K h w0 mu N κ → ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS V n d), nabValN B K h w0 N (FB.toK K (κ * pullM B mu g)) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B K h w0 1 (FB.toK K g) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ h w0 hh n mu N κ hκ Ty _ r σ u hu P g
  unfold nabValN
  rw [kappa_mul_pullM_mul_expS B K h w0 hh mu N κ hκ g]
  exact GlobalTheory.T.constantCoeff_invariant_operator_along_matrix V d O B K n mu Ty r σ u hu P _

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem map_mem_span_of_constantCoeff_eq_zero {σ R S : Type} [Finite σ] [CommRing R] [CommRing S]
    (ψ : MvPowerSeries σ R →+* S) (g : MvPowerSeries σ R) (hg : MvPowerSeries.constantCoeff g = 0) :
    ψ g ∈ Ideal.span (Set.range fun j => ψ (MvPowerSeries.X j)) := by
  have h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
    rw [← germIdeal_eq_span]
    exact hg
  have h4 := Ideal.mem_map_of_mem ψ h3
  rwa [Ideal.map_span, ← Set.range_comp] at h4

theorem exists_pow_span_X_le_span_matV : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → PS (ResidueField V) n d)) ^ M ≤ Ideal.span (Set.range fun s : Fin n × Fin d => MvPowerSeries.map (residue V) (matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  intro V _ _ _ _ _ d O _ _ B hB n p p' N hN hp
  obtain ⟨M, hM⟩ := hB N hN
  have hpt0 : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) = 0 := by
    intro b i; simp [pt]
  have hpt : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V := by
    intro b i; rw [hpt0]; exact zero_mem _
  obtain ⟨-, hmul, -, hsm, -, -, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p' p (fun j => pt V d j) (fun j => pt V d j) hpt hpt
  obtain ⟨hy, -, -, -, -, -, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p p (fun j => pt V d j) (fun j => pt V d j) hpt hpt
  set y : Fin n → Pt V n d := matV B p (fun j => pt V d j) with hydef
  obtain ⟨-, -, -, -, hev, h0, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p' p y y hy hy
  obtain ⟨⟨ψ, hψX, hψ⟩, -⟩ := evC_spec V (Fin n × Fin d) (Fin n × Fin d) Unit
    (fun s => y s.1 s.2) (fun s => hy s.1 s.2)

  have hA : ∀ (b : Fin n) (i : Fin d), compV (B.A.act (N : O)) (pt V (n := n) d b) i ∈
      Ideal.span (Set.range fun s : Fin n × Fin d => y s.1 s.2) := by
    intro b i
    have e1 : compV (B.A.act (N : O)) (pt V (n := n) d b) i = matV B p' y b i := by
      rw [← hmul, hp, hsm]
    rw [e1, ← hev, evV, hψ]
    have := map_mem_span_of_constantCoeff_eq_zero ψ.toRingHom _ (h0 b i)
    simpa [hψX] using this
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.span_le]
  rintro _ ⟨⟨b, i⟩, rfl⟩
  let a : Fin 1 × Fin d → PS V n d := fun q => (![pt V (n := n) d b] : Fin 1 → Pt V n d) q.1 q.2
  have ha : ∀ q, a q = MvPowerSeries.X (b, q.2) := by
    rintro ⟨q1, q2⟩
    obtain rfl : q1 = 0 := Subsingleton.elim _ _
    rfl
  have ha0 : ∀ q, MvPowerSeries.constantCoeff (a q) = 0 := by
    intro q; rw [ha]; simp
  obtain ⟨-, -, hs, -⟩ := evC_spec V (Fin 1 × Fin d) (Fin n × Fin d) Unit a
    (fun q => by rw [ha0]; exact zero_mem _)
  have hS : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hS' : MvPowerSeries.HasSubst (fun q => MvPowerSeries.map (residue V) (a q)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by rw [ha]; simp)
  let θ : PS (ResidueField V) 1 d →ₐ[ResidueField V] PS (ResidueField V) n d := MvPowerSeries.substAlgHom hS'
  have hθ : ∀ f : PS V 1 d, θ (MvPowerSeries.map (residue V) f) = MvPowerSeries.map (residue V) (evC a f) := by
    intro f
    rw [hs ha0, MvPowerSeries.map_subst hS]
    simp only [θ, MvPowerSeries.coe_substAlgHom]
  have hX : θ (MvPowerSeries.X (0, i)) = MvPowerSeries.X (b, i) := by
    simp only [θ, MvPowerSeries.coe_substAlgHom]
    rw [MvPowerSeries.subst_X hS', ha]
    simp
  have h1 := Ideal.mem_map_of_mem θ (hM (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (0, i))) M))
  rw [map_pow, hX] at h1
  refine ⟨M, ?_⟩
  refine SetLike.le_def.1 ?_ h1
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  have h2 := Ideal.mem_map_of_mem (MvPowerSeries.map (σ := Fin n × Fin d) (residue V)) (hA b j)
  rw [Ideal.map_span, ← Set.range_comp] at h2
  rw [SetLike.mem_coe, hθ]
  exact h2

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain

namespace GlobalTheory.PlaceInt.HostChart

theorem vV_nat_nonneg (T : CDVR) (p : ℕ) : 0 ≤ vV T.V (p : T.Fr) := by
  rw [← map_natCast (algebraMap T.V T.Fr)]
  unfold vV
  by_cases ha : valV T.V (algebraMap T.V T.Fr p) = 0
  · rw [ha]; simp
  have h1 : valV T.V (algebraMap T.V T.Fr p) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have := (WithZero.log_le_log ha one_ne_zero).2 h1
  simp only [WithZero.log_one] at this
  omega

theorem chBound_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
    {y : IntFr Xo c T io} {C : IntegralChartA3 Xo c T io y} {e : ℕ} {ρ ρ' : ℝ} {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (h : ChBound C e ρ w n) (hle : ρ ≤ ρ') : ChBound C e ρ' w n :=
  fun k => le_trans (EReal.coe_le_coe_iff.2 (neg_le_neg hle)) (h k)

theorem chBound_host : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n DFw : ℕ), Formalism.L2.Pj.DF Dw w ≤ DFw → ChBound C e (∑ p ∈ D.host.condN.primeFactors, (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2) w n := by
  intro D H Dw l Xo c _ hstar T io y C e he w n DFw hDF
  obtain ⟨hG, -, hD, hP⟩ := _root_.GlobalTheory.PlaceInt.host_galois_discr_moves D H
  have hd0 : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  have hnn : ∀ p ∈ D.host.condN.primeFactors, (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2 := by
    intro p _
    have h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_nat_nonneg T p
    have h2 := D.host.vdH_nonneg p
    positivity
  by_cases hu : ∀ p ∈ D.host.condN.primeFactors, IsUnit (p : T.V)
  · refine chBound_mono (_root_.GlobalTheory.PlaceInt.chBound_zero_of_isUnit_discr D.host.E H Dw l Xo c hstar T io y C ?_ e w n) (Finset.sum_nonneg hnn)
    have h1 : IsUnit (((NumberField.discr D.host.E).natAbs : ℕ) : T.V) := by
      rw [← Nat.prod_factorization_pow_eq_self hd0, Finsupp.prod, Nat.cast_prod]
      refine IsUnit.prod_iff.2 fun p hp => ?_
      have hp' := Nat.mem_primeFactors.1 (Nat.support_factorization _ ▸ hp)
      rw [Nat.cast_pow]
      exact (hu p (Nat.mem_primeFactors.2 ⟨hp'.1, hD p hp'.1 (Int.natCast_dvd.2 hp'.2.1), D.host.condN_ne_zero⟩)).pow _
    rcases Int.natAbs_eq (NumberField.discr D.host.E) with h | h
    · rw [h, Int.cast_natCast]; exact h1
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact h1.neg
  · push Not at hu
    obtain ⟨p, hp, hpu⟩ := hu
    have hpp := (hP p hp).1
    haveI : Fact p.Prime := ⟨hpp⟩
    have hm : ¬ p ∣ ordCompl[p] (NumberField.discr D.host.E).natAbs := Nat.not_dvd_ordCompl hpp hd0
    have hDa := (Nat.ordProj_mul_ordCompl_eq_self (NumberField.discr D.host.E).natAbs p).symm
    refine chBound_mono (_root_.GlobalTheory.PlaceInt.ChartRam.chBound_ramified D.host.E H Dw l Xo c hstar T io y C hG p _ _ hpp hpu hm hDa
      (hP p hp).2 e he w n) (le_trans ?_ (Finset.single_le_sum hnn hp))
    rw [Nat.factorization_def _ hpp]
    have h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_nat_nonneg T p
    have h2 := D.host.vdH_nonneg p
    have h3 : (Formalism.L2.Pj.DF Dw w : ℝ) ≤ DFw := by exact_mod_cast hDF
    simp only [Formalism.HC.HostRaw.vdH, Nat.padicValNat_def] at h2 ⊢
    gcongr

end GlobalTheory.PlaceInt.HostChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegral
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem integral_of_frOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; letI := io₂.toAlgebra; (∀ a : c.F, io₂ (d.eF a) = io a) → ∀ y₂ : FrPt d.Xo₂ d.c₂ T.Fr, FrOver d y₂ y.1 → Integral T io₂ y₂ := by
  intro E _ _ _ H Dw l Xo c n d T io io₂ y hio y₂ hy
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨y, hInt⟩ := y
  have hy' : FrOver d y₂ y := hy
  obtain ⟨G, t', m1, m2, ⟨ub, b1, b2, b3, b4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, p2, hg⟩ := hInt.2
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (FrameLift.frOver_iff d y₂ y).1 hy'
  have key : ∀ (x : Sp T.Fr ⟶ Xo.X) (m : SABMap t' Xo.univ.t x), x = y₂.x ≫ d.r →
      ∃ m' : SABMap t' d.Xo₂.univ.t y₂.x, m.φ = m'.φ ≫ d.m.φ := by
    intro x m hx
    subst hx
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ d.m m
  obtain ⟨m', e₁⟩ := key _ m1 e.symm
  have eig : ∀ τ v, Formalism.L2.Pj.IsEigV d.c₂ io₂ G τ v ↔ Formalism.L2.Pj.IsEigV c io G τ v := fun τ v =>
    forall_congr' fun a => forall_congr' fun z => by rw [← FrameLift.embK_eF d τ a, hio]
  have he : m1.cm.e = m'.cm.e ≫ d.m.cm.e := by rw [m1.base, m'.base, d.m.base]; exact e.symm
  obtain ⟨w', r', tri⟩ := ArcQ.FrBC.exists_rigIso_cancel d.m.cm m'.cm m1.cm e₁ he t'.PP d.Xo₂.univ.t.PP Xo.univ.t.PP
    w w1 hw r1
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w').1 r'.1) d.Xo₂.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', m', m2, ⟨ub, b1, fun τ i => (eig τ _).2 (b2 τ i), fun τ v h1 h2 => b3 τ v h1 ((eig τ v).1 h2),
    fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, r', r2,
    (ArcQ.FrUniq.isoMaps_iff w' σ s').2 fun Z r z j k hj hk => hs' Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    i2, p2, ?_⟩
  · obtain ⟨q, h2, h3⟩ := b4 τ i
    have ubo : (ub τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ i)
    have h4 : q ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Mono (spMap (algebraMap T.V T.Fr)) :=
        haveI := IsPreimmersion.of_isLocalization (R := CommRingCat.of T.V) (S := CommRingCat.of T.Fr)
          (nonZeroDivisors T.V)
        inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
      rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, h3,
        Category.assoc]
      exact (congrArg _ ubo).trans (ArcQ.FrBC.dual_alg _)
    refine ⟨q, d.m.cart.1.hom_ext ?_ ?_, h3⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) e₁.symm).trans (h2.trans (hu τ i).symm))
    · rw [Category.assoc, m'.cart.1.w, ← Category.assoc, h4]
      exact (y₂.tan τ i).1.symm
  · intro g g₁ g₂ (J : PUnit → d.Xo₂.univ.t.PP.L.ι) hJ
    refine fn_ext fun z hz => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB z
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (d.m.φ (m'.φ z))
    have hi : m'.φ z ∈ d.Xo₂.univ.t.PP.L.U (J PUnit.unit) := mem_pull.1 hz
    have hj' : m1.φ z ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq e₁ z)).mpr hj
    have a₁ : (g ≫ p) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ := by
      rw [Category.assoc, p₁, ← Category.assoc, g₁, e₁]
    have a₂ : (g ≫ p) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom := by
      rw [Category.assoc, p₂, g₂]
    have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => j) ≤ (g ≫ p) ⁻¹ᵁ (PPx y.x).U (fun _ => j) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (· ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq a₁ q)).mpr (mem_pull.1 hq)
    have u₁ := (ArcQ.FrUniq.isoMaps_iff w1 σ s1).1 i1 _ (𝟙 _) z j k hj' hk
    rw [hg (g ≫ p) a₁ a₂ (fun _ => j) le, gs_appLE (g ≫ p) _ _ le (𝟙 _) z (mem_pull.2 hj'),
      tri _ (𝟙 _) z j (J PUnit.unit) k hj hi hk, Category.id_comp, Category.id_comp] at u₁
    have u₂ := R _ g z j (J PUnit.unit)
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq g₁ z)).mpr hj)
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq g₁ z)).mpr hi)
    rw [g₁] at u₂
    have u₃ := u₁.symm.trans u₂
    rw [Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at u₃
    rw [hs' _ (𝟙 _) z J k hz hk, gs_appLE _ _ _ hJ (𝟙 _) z hz, Category.id_comp]
    exact u₃

end GlobalTheory.PlaceInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSymmetricTranslationUnitsEqKappaRatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_symmetricTranslationUnits_eq_kappa_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (Θ : PS V 3 d) (jo : PS V 1 d), IsTheta B K h w0 Θ → IsIota B K h w0 jo → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ), Odd N → (∀ j k, ∑ i, star (mu i j) * mu i k = if j = k then (N : O) else 0) → ∀ κ : PS V n d, IsKappa B K h w0 mu N κ → ∀ α ∈ kerM B mu, ∀ u : Fin n → PS V 1 d, (∀ b, TrUnit B Θ jo N (α b) (u b)) → (∏ b, evV (n := n) ![pt V d b] (u b)) * shift B.G.F α κ = κ := by
  first | exact @GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa | exact GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa | (intros; apply GlobalTheory.PlaceInt.prod_trUnit_mul_shift_kappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SpecPowerSeriesHomExtOfJetsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_powerSeries_hom_ext_of_jets : ∀ (V : Type) [CommRing V] [IsLocalRing V] (κ : Type) [Fintype κ] [DecidableEq κ] (Y : Scheme.{0}) (f g : Sp (MvPowerSeries κ V) ⟶ Y), (∀ m, spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ f = spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ g) → f = g := by
  first | exact @GlobalTheory.TransUnit.hom_ext_of_jets | exact GlobalTheory.TransUnit.hom_ext_of_jets | (intros; apply GlobalTheory.TransUnit.hom_ext_of_jets <;> assumption)
end

