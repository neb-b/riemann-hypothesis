module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0102
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0012
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PotentialChartsRegularBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0146
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TiedSettingSymmetricCharts
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameBallCoordinateStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_ball_coordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) (W : Matrix (Fin j') (Fin j) ℂ), (∀ u : Matrix (Sg j j') (Sg j j') ℂ, IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef) → (∀ x y : Fin j' → ℂ, R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y)) → C.IsAdapted R A → (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j' → W = moebW (C.cinv (A₀ τ) τ * A τ) 0 → (∀ v : Fin j → ℂ, C.pPart R τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) ∧ R.gram (fun b : Fin j' => C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))) * (1 - W * Wᴴ) = ((2 * C.c : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) ∧ (1 - W * Wᴴ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbedding
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx

theorem zero_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by ext a b; simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem trace_zero_of_int {E : Type} [Field E] [NumberField E] (w : E)
    (hw : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * w) = 0) : w = 0 := by
  have nd := traceForm_nondegenerate ℚ E
  apply nd.1
  intro a
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ E ((n • a) * w) = 0 := hw ⟨n • a, hint⟩
  have hnq : ((n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have h2 : (n • a) * w = ((n : ℚ)) • (w * a) := by
    rw [← Int.cast_smul_eq_zsmul ℚ n a, smul_mul_assoc, mul_comm a w]
  rw [h2, map_smul, smul_eq_mul] at h1
  rw [Algebra.traceForm_apply]
  exact (mul_eq_zero.1 h1).resolve_left hnq

theorem exists_latEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (_H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (LatEmb F) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F
  have h0 : (0 : Fin n → ℂ) ∈ ballDom F.q := zero_mem_ballDom F.q
  obtain ⟨R, hR⟩ : ∃ R, R = F.R 0 := ⟨_, rfl⟩
  have := R.free
  have := R.fin
  have hform : R.form = F.form := by rw [hR]; exact F.form_eq 0
  have hrk := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card E Ψ F.σ F.cm
  have hg := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim.dim_eq_card_mul E Ψ g j j' R.B F.σ F.cm (by rw [hR]; exact F.sig 0 h0)
  obtain ⟨N, hN, e, einj, esmul, hspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding E Λ
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hNj : N = j + j' := by
    rw [R.rank, hrk, hg] at hN
    have hc : 0 < Fintype.card Ψ := by omega
    have : Fintype.card Ψ * N = Fintype.card Ψ * (j + j') := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left hc this
  subst hNj
  have hunim : Function.Bijective F.form := hform ▸ R.unimod
  have halt : ∀ x, F.form x x = 0 := fun x => by rw [← hform]; exact R.alt x
  have hadj : ∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, F.form (a • x) y = F.form x (a' • y) := by
    rw [← hform]; exact R.adj
  obtain ⟨B, hBe, hBadj, hBskew, hBnd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil.exists_rat_bilin E Λ (j + j') e einj esmul hspan F.form halt hunim hadj
  obtain ⟨h, m, hm, hmaster, hint⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace.exists_hermitian_of_trace E H Λ (j + j') e B hBadj hBskew hBnd
  have hdual := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.latEmb_relIndex_dual_ne_zero E H Λ (j + j') e einj F.form hunim B hBe hBskew hBnd hspan h m hm hmaster
  have hrt : (H.rt : E) ≠ 0 := by
    intro h0
    have h1 : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E) := by rw [H.rt_sq]
    have hd : H.d ≠ 0 := H.d_prime.ne_zero
    simp [h0] at h1
    exact hd h1
  have hxi : ((m : E) * (H.rt : E))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by exact_mod_cast hm) hrt)
  choose eps heps hxieq using fun τ => GlobalTheory.T.embedding_inverse_root_imaginary E H (F.σ τ) m hm
  have hmat : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x)) := by
    intro x y
    have := hmaster 1 (e x) (e y)
    rw [one_mul, one_smul] at this
    rw [this, hBe]
  let lam : Module.Basis (Fin (2 * g)) ℤ Λ := (Module.finBasisOfFinrankEq ℤ Λ R.rank)
  obtain ⟨bas, hbas⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Dict.exists_realBasis_of_latBasis E Ψ g (j + j') F.σ F.cm hg Λ e hspan lam
  have hlat : IsLattice E e.range := by
    refine ⟨?_, ?_, ?_⟩
    · rintro a _ ⟨x, rfl⟩
      exact ⟨a • x, esmul a x⟩
    · have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (inferInstance : AddGroup.FG e.range)
    · rw [eq_top_iff]
      intro v _
      obtain ⟨k, x, hk, hx⟩ := hspan v
      have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
      have : v = (k : E)⁻¹ • e x := by
        rw [hx, Nat.cast_smul_eq_nsmul E k v |>.symm, smul_smul, inv_mul_cancel₀ hk', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hintegral : IsIntegralOn h e.range := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hint x y
  have hDI : IsDIntegral h (e.range.relIndex (dualLattice h e.range)) e.range := ⟨hlat, hintegral, hdual, le_rfl⟩
  have horth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0 := by
    intro x y
    have hsw : h.toSesq (e x) (e y) = 0 ↔ h.toSesq (e y) (e x) = 0 := by
      constructor
      · intro h1
        have h2 := h.isSymm.eq (e x) (e y)
        rw [h1] at h2
        simpa using h2.symm
      · intro h1
        have h2 := h.isSymm.eq (e y) (e x)
        rw [h1] at h2
        simpa using h2.symm
    have hfa : ∀ a : 𝓞 E, ((F.form (a • x) y : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x))) := by
      intro a
      rw [hmaster (a : E) (e x) (e y), ← hBe, esmul]
    rw [hsw]
    constructor
    · intro h1 a
      have := hfa a
      rw [h1, mul_zero, mul_zero, map_zero] at this
      exact_mod_cast this
    · intro h1
      have : ((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x) = 0 := by
        apply trace_zero_of_int
        intro a
        rw [← hfa a, h1 a]
        simp
      exact (mul_eq_zero.1 this).resolve_left hxi
  have hcpos : 0 < 1 / ((m : ℝ) * Real.sqrt H.d) := by
    have h1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have h2 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    positivity
  exact ⟨{ h := h, e := e, e_inj := einj, e_smul := esmul, Dn := _, integral := hDI, orth := horth,
           xi := ((m : E) * (H.rt : E))⁻¹, c := 1 / ((m : ℝ) * Real.sqrt H.d), c_pos := hcpos, eps := eps, eps_sq := heps,
           xi_eq := hxieq, form_eq := hmat, lam := lam, bas := bas, bas_eq := hbas }⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRegularizationSetting
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem GlobalTheory.CompanionTheory.Ar.Cusp.breg_margin_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ => max t (C / Real.log t⁻¹ + C * t)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => C / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have h2 := h0.max (h1.add (h0.const_mul C))
  simpa using h2


set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_regularization_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ), LogHom D Hd.aMu w → ChartPsh D w → ChartCont D w → ChartBdd D w → ConjOff D w → ∃ S' : BoundedRegularisationSetting M D.Xo Hd.aMu w, S'.IsTied ∧ ConjU S' := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w hL hP hC hB hO
  obtain ⟨ref, hra, hrs, hrc⟩ := GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric K J Hd.aMu
  obtain ⟨P, S, κ, hth, had, -, hsym, -⟩ :=
    _root_.LevelTowerAlt.exists_potential_charts K J II Ψ Ω W D M ref (fun _ _ => 1) hrs hrc fun _ _ => one_pos
  obtain ⟨B, rfl, hph, hcj⟩ := _root_.LevelTowerAlt.potential_charts_regular_bound K J II Ψ Ω W D M ref w P S hrs hth had (hra ▸ hL) hP hC hB
  obtain ⟨ρ, hρ⟩ := GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier D.n
  obtain ⟨cut, Cη, hcut, hcc⟩ := GlobalTheory.CompanionTheory.Relay.exists_cutoff_family_symmetric K J II Ψ Ω W D M _ κ hsym
  obtain ⟨C, t₀, ht₀, hcmp⟩ := GroundTheory.Heights₂.Heights.Regular.BoundedChartComparison.proof
    GroundTheory.Heights₂.Heights.Regular.MollifiedLowerBound.closed
    GroundTheory.Heights₂.Heights.Regular.PolyMaxOscillation.proof_closed M.Xc D.n M.atlas B ρ
  let S' : BoundedRegularisationSetting M D.Xo Hd.aMu w :=
    { ref := ref, ref_deg := hra, ref_smooth := hrs, B := B, th_ref := hth, ph_eq := hph, ρ := ρ, «η» := cut,
      Cη := Cη, cutoff := hcut, e1 := fun t => max t (C / Real.log t⁻¹ + C * t),
      e1_ge := fun _ _ => le_max_left _ _ }
  have hT : S'.IsTied := by
    refine ⟨GlobalTheory.CompanionTheory.Ar.Cusp.breg_margin_tendsto C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht j k x hx
    exact (hcmp t ht.1 ht.2 j k x hx).trans (le_max_right _ _)
  exact ⟨S', hT, _root_.LevelTowerAlt.tied_setting_symmetric_charts K J II Ψ Ω W D Hd M w S' κ hT hsym hρ hcc hrc (hcj hrc hO)⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrameStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_coefficients_in_frame : ∀ (n m g : ℕ) (U : Set (Fin n → ℂ)) (d : Fin m → (Fin n → ℂ) → Fin g → ℂ) (x : (Fin n → ℂ) → Fin g → ℂ) (w : (Fin n → ℂ) → Fin m → ℂ), IsOpen U → (∀ b, DifferentiableOn ℂ (d b) U) → DifferentiableOn ℂ x U → (∀ t ∈ U, LinearIndependent ℂ (fun b => d b t)) → (∀ t ∈ U, x t = ∑ b, w t b • d b t) → DifferentiableOn ℂ w U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.Proportional
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace TopProp

open FlLines

theorem degFl_yLines (hIn : Inputs) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1)) :
    degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w =>
      ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  refine formPoly_eq_toWt _ _ _ fun lam => ?_
  set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef
  have hS : S.Finite := divSupp_finite _ _
  set m : Ideal (MRing (FlIdx Ψ N)) → ℝ :=
    fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm
  have hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) →
      ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ) :=
    fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two
  have hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a) :=
    FlagHeightMultilinear.isSmoothHerm_fsHerm
  have h1 := degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)
  have h2 := degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)
  have hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) =
      fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k := by
    funext _ k
    exact deg_abel lam k
  rw [hv, ← h2] at h1
  have ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
        ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ) :=
    fun w => hD _ fun _ => hsm _
  have ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) =
        ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ) :=
    fun w => hD _ fun _ => hsm _
  simp only [ex, ey]
  exact h1

theorem degFl_eq (hIn : Inputs) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ) (hN : 2 ≤ N) :
    ∃ (d : ℕ) (S₀ : AnSys (d + 1) (Ψ × Fin N)), d + 1 = antisymDegree Ψ N ∧
      IsUniformised S₀.A S₀.open' N S₀.potH ∧ degFlPoly Ψ N = toWt S₀.degPoly := by
  obtain ⟨d, S₀, Re, hd, hdeg, href, -, ⟨F⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.flagVarieties_flagSys hIn Ψ N hN
  have hP := (_root_.GlobalTheory.CompanionTheory.Ar.PB.flag_isArithVar_and_image Ψ N hN).1
  have hR := _root_.GlobalTheory.CompanionTheory.Ar.PB.re_pot hIn.2.1.1 _ _ _ _ S₀ _ Re
  have hw : ∀ w : Fin (d + 1) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) = S₀.degNum w := by
    intro w
    have := hR.2.1 w
    simp only [href, hdeg] at this
    simpa using this
  refine ⟨d, S₀, hd, F.unif, ?_⟩
  rw [degFl_yLines hIn Ψ N hP, AnSys.degPoly]
  congr 1
  rw [← hd]
  congr 1
  funext w
  exact hw w

end TopProp

open TopProp

theorem proportional : Proportional := by
  intro hIn Ψ _ _ _ N j hN hj
  obtain ⟨d, S₀, hd, hU₀, hfl⟩ := degFl_eq hIn Ψ N hN
  obtain ⟨c, hc, hc'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.anSys_proportional hIn Ψ N N (d + 1) S₀ le_rfl hd hU₀
  have hΔ : 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta Ψ N (∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, X (τ, m)) 1
      (fun c => by simp [map_prod, map_sum])).2
  have hfl' : degFlPoly Ψ N = C c * antisymDelta Ψ N := hfl.trans hc'
  refine ⟨⟨c, hc, hfl'⟩, fun D S hD hU => ?_⟩
  obtain ⟨v, hv, hv'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.anSys_proportional hIn Ψ N j D S hj hD hU
  have hvol : volOf S = v / c := by
    unfold volOf
    rw [hv', hfl', eval_mul, eval_mul, eval_C, eval_C]
    field_simp
  refine ⟨hvol ▸ div_pos hv hc, ?_⟩
  rw [hvol, hv', hfl', ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hc.ne']

end GlobalTheory.CompanionTheory.Ar.PB
end
end

