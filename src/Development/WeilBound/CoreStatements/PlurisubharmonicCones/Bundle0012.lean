module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0053
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContinuousAtOfHolo
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsJoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace LevelTowerAlt

theorem exists_join {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)
    (hT' : CoordTie ℤ ξ' fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (g : X' ⟶ X) (i : Ω →+* Ω')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ g i) :
    ∃ (K₃ : Type) (_ : Fintype K₃) (J₃ : K₃ → Type) (_ : ∀ k, Fintype (J₃ k)) (y₃ : (Σ k, J₃ k) → Ω') (bk : K → K₃)
      (bx : ∀ k, J k ≃ J₃ (bk k)), Nonempty K₃ ∧ Function.Injective bk ∧ (∀ k x, y₃ ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧
      CoordTie ℤ ξ' fun c' : (k : K₃) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩ := by
  let J₁ : K ⊕ Unit → Type := Sum.elim J fun _ => Unit
  letI : ∀ k, Fintype (J₁ k) := fun k => match k with
    | .inl k => (inferInstance : Fintype (J k))
    | .inr _ => (inferInstance : Fintype Unit)
  let s : (Σ k, J₁ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => i (y ⟨k, a⟩)
    | ⟨.inr _, _⟩ => 1
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi X' Ω' ξ' K' J' y' (K ⊕ Unit) J₁ s hT' (by
    rintro (k | k) p
    · obtain ⟨hsp, hreg, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' g i hd p
      obtain ⟨c, hc⟩ := hT.cover ⟨g p.1, hsp⟩
      refine ⟨c k, (map_ne_zero i).2 (TiePrimes.ne_of_seg hc.1 k), fun a => ?_⟩
      have := hreg _ (TiePrimes.ratio_mem hc ⟨k, a⟩)
      rw [map_div₀] at this
      exact this
    · refine ⟨(), one_ne_zero, fun a => ?_⟩
      show (1 : Ω') / 1 ∈ _
      rw [div_one]; exact one_mem _)
  let J₃ : K' ⊕ (K ⊕ Unit) → Type := Sum.elim J' J₁
  let y₃ : (Σ k, J₃ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => y' ⟨k, a⟩
    | ⟨.inr k, a⟩ => s ⟨k, a⟩
  refine ⟨K' ⊕ (K ⊕ Unit), inferInstance, J₃, fun k => match k with
    | .inl k => (inferInstance : Fintype (J' k))
    | .inr k => (inferInstance : Fintype (J₁ k)), y₃, fun k => .inr (.inl k), fun k => Equiv.refl _,
    ⟨.inr (.inr ())⟩, fun a b h => by simpa using h, fun _ _ => rfl, ?_⟩
  have e : (fun c' : (k : K' ⊕ (K ⊕ Unit)) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩) =
      fun c' : (k : K' ⊕ (K ⊕ Unit)) → Sum.elim J' J₁ k =>
        (∏ k, y' ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ :=
    funext fun c' => Fintype.prod_sum_type _
  rw [e]; exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω}

@[reducible] def reTie (B : HodgeCpt Y S y) (h : CoordTie ℤ B.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) :
    HodgeCpt Y S y' := { B with tie := h }

theorem flag_zero [∀ k, Fintype (J k)] (B : HodgeCpt Y S y) (d : ℕ) (hc : B.IsCover d) (h0 : D.p + D.q = 0) :
    Nonempty B.Flag := by
  have hrk : ∀ s, labelRk D s = 0 := by
    rintro (τ | τ)
    · show D.p = 0; omega
    · show D.q = 0; omega
  haveI : ∀ s, IsEmpty (Fin (labelRk D s)) := fun s => by rw [hrk s]; infer_instance
  have hV : ∀ s, B.Vgen s = ⊥ := fun s => by
    obtain ⟨U, -, b, hb, -⟩ := B.vb s ⟨_, specializes_rfl⟩ trivial
    refine hb.symm.trans ?_
    rw [Set.range_eq_empty, Submodule.span_empty]
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Y.X Y.t.G B.Ω₀ B.ξ₀
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieJ.exists_map Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M B.fn_over B.m.cart
  obtain ⟨hext, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePull.main Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M j B.gen₀
    B.tie.gen B.fn_over B.m.cart Y.t.semi.smooth hj
  refine ⟨{ b := fun _ => isEmptyElim, sub := fun s p _ => ?_, Li₀ := Li₀, M₀ := M₀, j := j, j_pt := hj,
            V₀ := fun _ => ⊥, V₀_mem := fun s e => ?_, deg := d, generic := ?_ }⟩
  · obtain ⟨U, hU, b, -, hb⟩ := B.vb s p trivial
    exact ⟨U, hU, b, fun _ => by rw [Subsingleton.elim b isEmptyElim], hb⟩
  · rw [hV, Submodule.mem_bot, Submodule.mem_bot]
    refine ⟨fun h => by rw [h, map_zero], fun h => by_contra fun hne => ?_⟩
    have := hext.2 1 (fun _ => e) (linearIndependent_unique_iff.2 hne)
    exact this.ne_zero 0 h
  · letI := B.fn.toAlgebra
    refine ⟨fun _ => isEmptyElim, fun _ => 0, fun s => ⟨linearIndependent_empty_type, ?_⟩, hext.1,
      fun _ => linearIndependent_empty_type, fun _ => linearIndependent_empty_type, fun _ => isEmptyElim,
      fun _ => isEmptyElim, fun s i => congrArg (fun b => flagStep Ω b i) (Subsingleton.elim _ _), ?_, hc.1, ?_⟩
    · rw [Set.range_eq_empty, Submodule.span_empty]
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H,
          {lk : Fin (labelRk D σ) × Fin (labelRk D σ) // lk.2 < lk.1}) := ⟨fun q => isEmptyElim q.2.1.1⟩
      exact algebraicIndependent_empty_type
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H, Fin (labelRk D σ) × Fin (labelRk D σ)) :=
        ⟨fun q => isEmptyElim q.2.1⟩
      rw [Set.range_eq_empty, IntermediateField.adjoin_empty, IntermediateField.finrank_bot']
      exact hc.2

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPotentialCharts
section
namespace LevelTowerAlt.Charts

open Filter Topology Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart LocPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} {M : XModel D}

structure IsChartOf (M : XModel D) (γ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)) : Prop where
  good : Good (mCoordIdeal D.y) γ
  target : e.target = ball 0 1
  symm : ∀ t, e.symm t = M.proj (γ t)
  compat : IsCompatChart M.atlas e

section One

variable {γ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ} {e e' : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)}

theorem IsChartOf.mem_ball (h : IsChartOf M γ e) {x : M.Xc} (hx : x ∈ e.source) : e x ∈ ball (0 : Fin D.n → ℂ) 1 :=
  h.target ▸ e.map_source hx

theorem IsChartOf.sec (h : IsChartOf M γ e) (x : M.Xc) (hx : x ∈ e.source) :
    γ (e x) ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (γ (e x)) = x :=
  ⟨h.good.mem _ (h.mem_ball hx), by rw [← h.symm, e.left_inv hx]⟩

theorem IsChartOf.holo (h : IsChartOf M γ e) (p : Σ k, J k) : M.atlas.HoloOn e.source fun x => γ (e x) p :=
  fun j y hy => analyticAt_pi_iff.1 ((h.good.an _ (h.mem_ball hy.2)).comp_of_eq ((h.compat j).1 y hy) rfl) p

theorem IsChartOf.q_smooth (h : IsChartOf M γ e) {ref : HermLine J} (hr : IsSmoothHerm ref) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Real.log (ref.h (γ t))) e.target := by
  rw [h.target]
  exact (ContDiffOn.comp hr (h.good.an.contDiffOn_of_completeSpace.restrict_scalars ℝ)
    fun t ht => (h.good.mem t ht).1).log fun t ht => (ref.pos _ (h.good.mem t ht).1).ne'

theorem IsChartOf.closure_sub (h : IsChartOf M γ e) {r r' : ℝ} (hr : r < r') (hr' : r' ≤ 1) :
    closure (e.source ∩ e ⁻¹' ball 0 r) ⊆ e.source ∩ e ⁻¹' ball 0 r' := by
  have hs : closedBall (0 : Fin D.n → ℂ) r ⊆ e.target :=
    h.target ▸ closedBall_subset_ball (hr.trans_le hr')
  have hc : IsClosed (e.symm '' closedBall 0 r) :=
    ((isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hs)).isClosed
  have hsub : e.source ∩ e ⁻¹' ball 0 r ⊆ e.symm '' closedBall 0 r :=
    fun x hx => ⟨e x, ball_subset_closedBall hx.2, e.left_inv hx.1⟩
  refine (closure_minimal hsub hc).trans ?_
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨e.map_target (hs ht), ?_⟩
  rw [mem_preimage, e.right_inv (hs ht)]
  exact closedBall_subset_ball hr ht

theorem IsChartOf.torus (h : IsChartOf M γ e) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hs : M.proj z ∈ e.source) : ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ γ (e (M.proj z)) = torusSmul c z :=
  (M.fibre _ hz _ (h.sec _ hs).1).1 (h.sec _ hs).2.symm

theorem IsChartOf.conj (h : IsChartOf M γ e) (h' : IsChartOf M (cj γ) e') {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) (hs : M.proj z ∈ e.source) :
    M.proj (conjVec z) ∈ e'.source ∧ e' (M.proj (conjVec z)) = star (e (M.proj z)) := by
  obtain ⟨c, hc, he⟩ := h.torus hz hs
  have ht : star (e (M.proj z)) ∈ e'.target := h'.target ▸ star_mem_ball.2 (h.mem_ball hs)
  have key : M.proj (conjVec z) = e'.symm (star (e (M.proj z))) := by
    rw [h'.symm]
    refine (M.fibre _ (SncPiece.conj_mem hz) _ (h'.good.mem _ (h'.target ▸ ht))).2
      ⟨fun k => starRingEnd ℂ (c k), fun k => (map_ne_zero _).2 (hc k), ?_⟩
    simp only [cj, star_star, he, conj_torus]
  rw [key]
  exact ⟨e'.map_target ht, e'.right_inv ht⟩

theorem IsChartOf.conj_iff (h : IsChartOf M γ e) (h' : IsChartOf M (cj γ) e') {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) : M.proj (conjVec z) ∈ e'.source ↔ M.proj z ∈ e.source := by
  refine ⟨fun hs => ?_, fun hs => (h.conj h' hz hs).1⟩
  have := (h'.conj (e' := e) (by rwa [cj_cj]) (SncPiece.conj_mem hz) hs).1
  rwa [SncPiece.conj_conj] at this

theorem IsChartOf.conj_ball (h : IsChartOf M γ e) (h' : IsChartOf M (cj γ) e') {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) (r : ℝ) :
    M.proj (conjVec z) ∈ e'.source ∩ e' ⁻¹' ball 0 r ↔ M.proj z ∈ e.source ∩ e ⁻¹' ball 0 r := by
  rw [mem_inter_iff, mem_inter_iff, h.conj_iff h' hz]
  refine and_congr_right fun hs => ?_
  rw [mem_preimage, mem_preimage, (h.conj h' hz hs).2, star_mem_ball]

theorem IsChartOf.mem_bd (h : IsChartOf M γ e) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hs : M.proj z ∈ e.source) : z ∈ D.Bd ↔ γ (e (M.proj z)) ∈ D.Bd := by
  obtain ⟨c, hc, he⟩ := h.torus hz hs
  rw [he]
  refine ⟨fun hb => D.bd_torus z hb c hc, fun hb => ?_⟩
  have := D.bd_torus _ hb (fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
  convert this using 1
  funext p
  simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]

end One

noncomputable def famCharts {N : ℕ} (γ : Fin N → (Fin D.n → ℂ) → (Σ k, J k) → ℂ)
    (e : Fin N → OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)) (h : ∀ j, IsChartOf M (γ j) (e j))
    (hcov : ∀ x, ∃ j, x ∈ (e j).source ∩ e j ⁻¹' ball 0 (1 / 4)) (ref : HermLine J) (hr : IsSmoothHerm ref) :
    PotentialCharts M.atlas where
  N := N
  chart := e
  compat j := (h j).compat
  target_subset j := (h j).target.subset
  mid j := (e j).source ∩ e j ⁻¹' ball 0 (1 / 2)
  inner j := (e j).source ∩ e j ⁻¹' ball 0 (1 / 4)
  isOpen_mid j := (e j).isOpen_inter_preimage isOpen_ball
  isOpen_inner j := (e j).isOpen_inter_preimage isOpen_ball
  closure_inner j := (h j).closure_sub (by norm_num) (by norm_num)
  closure_mid j := ((h j).closure_sub (r' := 1) (by norm_num) le_rfl).trans inter_subset_left
  cover := hcov
  th :=
    { U := fun x => (e (hcov x).choose).source
      isOpen_U := fun _ => OpenPartialHomeomorph.open_source _
      mem_U := fun x => (hcov x).choose_spec.1
      φ := fun x y => Real.log (ref.h (γ (hcov x).choose (e (hcov x).choose y))) }
  th_pot := ⟨fun x k => ((h _).q_smooth hr).comp
      (((h _).compat k).1.contDiffOn_of_completeSpace.restrict_scalars ℝ)
      fun _ hy => OpenPartialHomeomorph.map_source _ hy.2,
    fun x x' y hy => sec_diff M ref (OpenPartialHomeomorph.open_source _) (OpenPartialHomeomorph.open_source _)
      (h _).sec (h _).sec (h _).holo (h _).holo hy⟩
  q j t := Real.log (ref.h (γ j t))
  q_smooth j := (h j).q_smooth hr
  q_th j x y hy := by
    obtain ⟨V, hV, hyV, G, hG, he⟩ := sec_diff M ref (e j).open_source (e (hcov x).choose).open_source
      (h _).sec (h _).sec (h _).holo (h _).holo ⟨hy.2, hy.1⟩
    exact ⟨V, hV, hyV, G, hG, fun z hz => he z ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩⟩

theorem good_chart (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts) :
    Good (n := D.n) (mCoordIdeal D.y) (D.chart a).γ :=
  ⟨(D.chart a).analytic, (D.chart a).mem, (D.chart a).injective, _root_.GlobalTheory.CompanionTheory.Ar.Cusp.chart_torus_open K J II Ψ Ω W D a⟩

theorem exists_eps {n : ℕ} (t₀ : Fin n → ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε ≤ r ∧ ε ≤ 1 / 4 ∧ ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖ := by
  have h : ∀ b : ℝ, 0 < b → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε ≤ b := fun b hb => by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hb)] with ε hε
    linarith [hε.2]
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖ := eventually_all.2 fun i => by
    by_cases hi : t₀ i = 0
    · exact Eventually.of_forall fun _ h0 => absurd hi h0
    · exact (h _ (norm_pos_iff.2 hi)).mono fun _ h1 _ => h1
  obtain ⟨ε, ⟨⟨h1, h3⟩, h4⟩, h5⟩ := ((((h r hr).and (h (1 / 2) (by norm_num))).and h2).and self_mem_nhdsWithin).exists
  exact ⟨ε, h5, h1, by linarith, h4⟩

end LevelTowerAlt.Charts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

open LevelTowerAlt.Charts Metric Set in
theorem LevelTowerAlt.exists_potential_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (r : Fin D.nCharts → (Fin D.n → ℂ) → ℝ), IsSmoothHerm ref → IsConjInvariantH ref → (∀ a t, 0 < r a t) → ∃ (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)) (κ : Equiv.Perm (Fin P.N)), ThRef M ref P.th ∧ Adapted M P S ∧ FromSnc M P ∧ SymmCharts M P κ ∧ ∀ j, ∃ (a : Fin D.nCharts) (t₀ : Fin D.n → ℂ) (ε : ℝ), ‖t₀‖ ≤ 1 / 2 ∧ 0 < ε ∧ 2 * ε ≤ r a t₀ ∧ ε ≤ 1 / 4 ∧ ((∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj ((D.chart a).γ (t₀ + (ε : ℂ) • t)) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • t)))) ∨ ∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • star t)))) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M ref r hr hrc hr0
  classical
  let I := {p : Fin D.nCharts × (Fin D.n → ℂ) // ‖p.2‖ ≤ 1 / 2}
  choose ε hε0 hεr hε4 hεs using fun p : I => exists_eps p.1.2 (hr0 p.1.1 p.1.2)
  let g : I → (Fin D.n → ℂ) → (Σ k, J k) → ℂ := fun p t => (D.chart p.1.1).γ (p.1.2 + (ε p : ℂ) • t)
  let g' : I × Bool → (Fin D.n → ℂ) → (Σ k, J k) → ℂ := fun i => cond i.2 (cj (g i.1)) (g i.1)
  have hg : ∀ p, Good (mCoordIdeal D.y) (g p) := fun p => (good_chart D p.1.1).affine p.2 (hε0 p) (hε4 p)
  have hg' : ∀ i, Good (mCoordIdeal D.y) (g' i) := by
    rintro ⟨p, _ | _⟩
    exacts [hg p, (hg p).cj]
  have hg0 : ∀ p, g p 0 = (D.chart p.1.1).γ p.1.2 := fun p =>
    congrArg (D.chart p.1.1).γ (by rw [smul_zero, add_zero] : p.1.2 + (ε p : ℂ) • (0 : Fin D.n → ℂ) = p.1.2)
  choose E hEt hEs hEc using fun i => (hg' i).exists_chart M
  have hE : ∀ i, IsChartOf M (g' i) (E i) := fun i => ⟨hg' i, hEt i, hEs i, hEc i⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun p : I => (E (p, false)).source ∩ E (p, false) ⁻¹' ball 0 (1 / 4))
    (fun p => (E _).isOpen_inter_preimage isOpen_ball) (fun x _ => by
      obtain ⟨z, hz, rfl⟩ := M.surj x
      obtain ⟨a, t, ht, c, hc, e⟩ := D.chart_cover z hz
      have h0 : (0 : Fin D.n → ℂ) ∈ (E (⟨(a, t), ht⟩, false)).target := hEt _ ▸ by exact Set.mem_preimage.mpr (mem_ball_self one_pos)
      have e0 : g' (⟨(a, t), ht⟩, false) 0 = (D.chart a).γ t := hg0 ⟨(a, t), ht⟩
      have e1 : M.proj z = (E (⟨(a, t), ht⟩, false)).symm 0 := by
        rw [hEs]
        exact ((M.fibre _ ((hg' _).mem _ (by exact Set.mem_preimage.mpr (mem_ball_self one_pos))) _ hz).2 ⟨c, hc, by rw [e0]; exact e⟩).symm
      refine mem_iUnion.2 ⟨⟨(a, t), ht⟩, ?_⟩
      rw [e1]
      refine ⟨(E _).map_target h0, ?_⟩
      rw [mem_preimage, (E _).right_inv h0]
      exact mem_ball_self (by norm_num))
  let sg := (Fintype.equivFin (F × Bool)).symm
  let ix : Fin (Fintype.card (F × Bool)) → I × Bool := fun j => ((sg j).1.1, (sg j).2)
  let fl : Equiv.Perm (F × Bool) := Equiv.prodCongr (Equiv.refl _) Equiv.boolNot
  let κ : Equiv.Perm (Fin (Fintype.card (F × Bool))) := (sg.trans fl).trans sg.symm
  have hκ : ∀ j, ix (κ j) = ((ix j).1, !(ix j).2) := fun j => by
    simp [ix, κ, fl, Equiv.boolNot]
  have hcj : ∀ j, g' (ix (κ j)) = cj (g' (ix j)) := fun j => by
    rw [hκ]
    rcases ix j with ⟨p, _ | _⟩
    · rfl
    · exact (LevelTowerAlt.Charts.cj_cj _).symm
  have hκκ : ∀ j, κ (κ j) = j := fun j => by
    have : ∀ x, fl (fl x) = x := fun x => by simp [fl, Equiv.boolNot, Prod.map]
    simp only [κ, Equiv.trans_apply, Equiv.apply_symm_apply, this, Equiv.symm_apply_apply]
  have hqq : ∀ j t, Real.log (ref.h (g' (ix (κ j)) (star t))) = Real.log (ref.h (g' (ix j) t)) := fun j t => by
    rw [hcj]
    simp only [cj, star_star]
    exact congrArg Real.log (hrc _)
  have hcov : ∀ x, ∃ j, x ∈ (E (ix j)).source ∩ E (ix j) ⁻¹' ball 0 (1 / 4) := fun x => by
    obtain ⟨p, hp, hx⟩ := mem_iUnion₂.1 (hF (mem_univ x))
    refine ⟨sg.symm (⟨p, hp⟩, false), ?_⟩
    simpa only [ix, Equiv.apply_symm_apply] using hx
  have hdis : ∀ i : I × Bool, (∀ t, g' i t = (D.chart i.1.1.1).γ (i.1.1.2 + (ε i.1 : ℂ) • t)) ∨
      ∀ t, g' i t = conjVec ((D.chart i.1.1.1).γ (i.1.1.2 + (ε i.1 : ℂ) • star t)) := by
    rintro ⟨p, _ | _⟩
    exacts [Or.inl fun _ => rfl, Or.inr fun _ => rfl]
  refine ⟨famCharts (fun j => g' (ix j)) (fun j => E (ix j)) (fun j => hE _) hcov ref hr,
    fun j => Finset.univ.filter fun i => (i : ℕ) < (D.chart (ix j).1.1.1).a ∧ (ix j).1.1.2 i = 0, κ,
    fun x y hy => ⟨_, OpenPartialHomeomorph.open_source _, hy, subset_rfl, _, (hE _).sec, (hE _).holo, fun _ => 0,
      fun _ => analyticOnNhd_const, fun _ _ => sub_self _⟩,
    fun j z hz hs => ?_, fun j => ⟨hEt _, (ix j).1.1.1, (ix j).1.1.2, ε (ix j).1, (ix j).1.2, hε0 _, hε4 _,
      fun i _ hi => hεs _ i hi, ?_⟩, ⟨hκκ, hqq, fun j z hz => ?_⟩,
    fun j => ⟨(ix j).1.1.1, (ix j).1.1.2, ε (ix j).1, (ix j).1.2, hε0 _, hεr _, hε4 _, ?_⟩⟩
  · have hs' : M.proj z ∈ (E (ix j)).source := hs
    have ht : ‖E (ix j) (M.proj z)‖ < 2 := (mem_ball_zero_iff.1 ((hE _).mem_ball hs')).trans one_lt_two
    change _ ↔ E (ix j) (M.proj z) ∈ _
    rw [(hE _).mem_bd hz hs']
    rcases hdis (ix j) with h | h
    · rw [h, SncPiece.mem_bd_iff D (ix j).1.2 (hε0 _) (hε4 _) (fun i _ hi => hεs _ i hi) ht]
      simp [ReciprocityTheory.AnForm.A.coordDiv]
    · rw [h, SncPiece.conj_mem_bd_iff, SncPiece.mem_bd_iff D (ix j).1.2 (hε0 _) (hε4 _) (fun i _ hi => hεs _ i hi)
        (by rwa [norm_star])]
      simp [ReciprocityTheory.AnForm.A.coordDiv]
  · exact (hdis (ix j)).imp (fun h t _ => (hEs _ t).trans (congrArg M.proj (h t)))
      fun h t _ => (hEs _ t).trans (congrArg M.proj (h t))
  · have h' : IsChartOf M (cj (g' (ix j))) (E (ix (κ j))) := hcj j ▸ hE (ix (κ j))
    exact ⟨(hE _).conj_iff h' hz, (hE _).conj_ball h' hz _, (hE _).conj_ball h' hz _,
      fun hs => ((hE _).conj h' hz hs).2⟩
  · refine (hdis (ix j)).imp (fun h t _ => ⟨(hEs _ t).trans (congrArg M.proj (h t)), ?_⟩)
      fun h t _ => ⟨(hEs _ t).trans (congrArg M.proj (h t)), ?_⟩
    · change Real.log (ref.h (g' (ix j) t)) = _
      rw [h]
    · change Real.log (ref.h (g' (ix j) t)) = _
      rw [h]
      exact congrArg Real.log (hrc _)
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.VerticalFactorSmoothLine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_conjVec (z : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.eval (conjVec z) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, conjVec]

theorem contDiff_conjVec : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, J k) → ℂ => conjVec z) :=
  contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)

theorem conjVec_ne {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∀ k, ∃ i, conjVec z ⟨k, i⟩ ≠ 0 :=
  fun k => (hz k).imp fun _ hi => (map_ne_zero _).2 hi

noncomputable def symmLine (Z : HermLine J) : HermLine J where
  a := Z.a
  h z := Real.sqrt (Z.h z * Z.h (conjVec z))
  pos z hz := Real.sqrt_pos.2 (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz)))
  smul c z hc := by
    have h1 : conjVec (fun p : Σ k, J k => c p.1 * z p) =
        fun p : Σ k, J k => (fun k => starRingEnd ℂ (c k)) p.1 * conjVec z p := by
      funext p
      simp [conjVec]
    have h2 := Z.smul (fun k => starRingEnd ℂ (c k)) (conjVec z) fun k => (map_ne_zero _).2 (hc k)
    have hP := prod_norm_zpow_pos hc Z.a
    rw [h1, h2, Z.smul c z hc]
    simp only [Complex.norm_conj]
    rw [_root_.mul_mul_mul_comm, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hP.le]

theorem symmLine_smooth {Z : HermLine J} (hZ : IsSmoothHerm Z) : IsSmoothHerm (symmLine Z) :=
  ContDiffOn.sqrt (ContDiffOn.mul hZ (ContDiffOn.comp hZ contDiff_conjVec.contDiffOn fun _ hz => conjVec_ne hz))
    fun z hz => (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz))).ne'

theorem symmLine_conj (Z : HermLine J) : IsConjInvariantH (symmLine Z) := by
  intro z
  show Real.sqrt (Z.h (conjVec z) * Z.h (conjVec (conjVec z))) = Real.sqrt (Z.h z * Z.h (conjVec z))
  rw [SncPiece.conj_conj, mul_comm]

end

theorem vertical_factor_smooth_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D p hp
  have hpos := VertFactorPos.proof II Ψ K J Ω W D p hp
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K J Ω W D p hp
  constructor
  · obtain ⟨Z, hZa, hZs, hZ⟩ := HermExtend.proof K J (mCoordIdeal D.y) (D.vdeg p) (D.vertFactor p) D.arith.2.1.2.1
      hpos hsm.1 hsm.2
    refine ⟨symmLine Z, hZa, symmLine_smooth hZs, symmLine_conj Z, fun z hz => ?_⟩
    have hconj : D.vertFactor p (conjVec z) = D.vertFactor p z := by
      obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
      rw [VertFactorSmooth.vertFactor_eq D hp (SncPiece.conj_mem hz) hG hH hdeg hrel
          (by rw [eval_conjVec]; exact (map_ne_zero _).2 hHz),
        VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz, eval_conjVec, eval_conjVec, ← map_div₀,
        Complex.norm_conj]
    show Real.sqrt (Z.h z * Z.h (conjVec z)) = _
    rw [hZ z hz, hZ _ (SncPiece.conj_mem hz), hconj, Real.sqrt_mul_self (hpos z hz).le]
  · intro a t ht
    have hz := (D.chart a).mem t ht
    obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
    have hγ := (D.chart a).analytic t ht
    have hev : ∀ f : MRing J, AnalyticAt ℂ
        (fun t' => MvPolynomial.eval ((D.chart a).γ t') (MvPolynomial.map (Int.castRingHom ℂ) f)) t := fun f =>
      AnalyticAt.comp (g := fun z => MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f))
        (AnalyticOnNhd.eval_mvPolynomial _ _ (Set.mem_univ _)) hγ
    have h0 := hpos _ hz
    rw [VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz] at h0
    obtain ⟨L, hL, hLe⟩ := exists_log_re ((hev G).div (hev H) hHz) (norm_pos_iff.1 h0)
    refine ⟨L, hL, ?_⟩
    filter_upwards [hLe, (hev H).continuousAt.eventually_ne hHz, Metric.isOpen_ball.mem_nhds ht] with t' h1 h2 h3
    rw [VertFactorSmooth.vertFactor_eq D hp ((D.chart a).mem t' h3) hG hH hdeg hrel h2]
    exact h1

end LevelTowerAlt
end

