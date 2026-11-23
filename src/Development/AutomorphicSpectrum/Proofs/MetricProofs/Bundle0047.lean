module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RelabelTransport
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareIntersectionPullback
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2), (∀ (L : Fin (d + 2) → HermLine ι) (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 0) (Q.v 0) (L j) (L' j)) → IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) = (N.a (Q.κ 1 k₀) : ℝ) * II K ι P (d + 2) L) ∧ ∀ (L : Fin (d + 3) → HermLine ι) (L' : Fin (d + 3) → HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 1) (Q.v 1) (L j) (L' j)) → II Q.KW Q.ιW Q.PW (d + 3) L' = 0 := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q
  obtain ⟨hFam, -, -, hCM⟩ := hII
  letI := Q.finKW
  letI := Q.finιW
  refine ⟨?_, ?_⟩
  · classical
    intro L L' N hL hLL' hN
    haveI : Q.PW.IsPrime := Q.arithW.2.1.1
    let G := GroundTheory.Heights₂.Heights.Inter.genFibreOf (Q.v 0) Q.PW
    let b : FibreBlock (Q.κ 0) := ⟨Q.κ 1 k₀, Q.new⟩
    have hb : ∀ c : FibreBlock (Q.κ 0), c = b := by
      intro c
      apply Subtype.ext
      rcases Q.all c.1 with h | h
      · exact absurd h c.2
      · exact h
    let e : Unit ≃ FibreBlock (Q.κ 0) :=
      { toFun := fun _ => b, invFun := fun _ => (), left_inv := fun _ => rfl,
        right_inv := fun c => (hb c).symm }
    let hq : (u : Unit) → Q.ιW (Q.κ 1 k₀) ≃ fibreIdx Q.ιW (Q.κ 0) (e u) := fun _ => Equiv.refl _
    let I₀ : IFamily G.Φ (fun _ : Unit => Q.ιW (Q.κ 1 k₀)) := fun V _ Ls => NumbersDVR.intNum G.Φ V Ls
    have hI₀ : IsFieldIntersection I₀ := NumbersDVR.IntNumIsFieldIntersection.full G.Φ Unit _
    let J := Targets.Relabel.pullFamily e hq I₀
    have hJ : IsFieldIntersection J := Targets.Relabel.isFieldIntersection_pull e hq hI₀
    have hP := hIn.2.2.2.1.1 II hFam K ι Q.KW Q.ιW (Q.κ 0) (Q.v 0) Q.PW (d + 2) 1 G J L L' (fun _ => N)
      (Q.block 0) Q.arithW (by rw [Q.image 0]; exact Q.arithY) hJ hL hLL' (fun _ => hN)
    rw [Fin.append_right_eq_snoc, Q.image 0] at hP
    rw [hP]
    congr 1
    obtain ⟨V, hV⟩ := Targets.Relabel.exists_map_eq e hq (fibreIdeal (Q.κ 0) G)
    have hVd : IsProjVarF V 1 := by
      rw [← Targets.Relabel.isProjVarF_map_iff e hq, ← hV]
      exact hIn.2.2.2.1.2.2 K ι Q.KW Q.ιW (Q.κ 0) (Q.v 0) Q.PW (d + 2) 1 G (Q.block 0) Q.arithW
        (by rw [Q.image 0]; exact Q.arithY)
    have hVs : ∃ S : Set (MRingOver G.Φ fun _ : Unit => Q.ιW (Q.κ 1 k₀)),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ V = Ideal.span S := by
      obtain ⟨T, hT, hTs⟩ := Q.fibre_line G
      refine ⟨(Targets.Relabel.ringEquiv G.Φ e hq).symm '' T, ?_, ?_⟩
      · rintro f ⟨g, hg, rfl⟩
        exact Targets.Relabel.isMultiHomog_symm e hq (hT g hg)
      · rw [← Ideal.map_span, ← hTs, hV, Ideal.map_symm, Targets.Relabel.comap_map]
    have hL1 := hIn.2.2.2.1.2.1 G.Φ _ V I₀ hVd hVs hI₀ (N.a (Q.κ 1 k₀))
    have key : (fun j : Fin 1 => fibreDeg (Q.κ 0) N.a ∘ e) = ![fun _ : Unit => N.a (Q.κ 1 k₀)] := by
      funext j u
      fin_cases j
      rfl
    show ((I₀ (Ideal.comap (Targets.Relabel.ringEquiv G.Φ e hq) (fibreIdeal (Q.κ 0) G)) 1
      fun j => fibreDeg (Q.κ 0) N.a ∘ e : ℤ) : ℝ) = _
    rw [hV, Targets.Relabel.comap_map, key, hL1]
  · intro L L' hL hLL'
    have h := hCM K ι Q.KW Q.ιW (Q.κ 1) (Q.v 1) Q.PW (d + 2) (d + 3) 0 L L' Fin.elim0 (Q.block 1)
      Q.arithW (by rw [Q.image 1]; exact Q.arithY) (by omega) hL hLL' (fun j => j.elim0)
    simpa [Fin.append_elim0] using h
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtHolomorphicComposition
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holo_in_charts (e n : ℕ) (X : Type) [TopologicalSpace X]
    (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → X) (w₀ : Fin e → ℂ)
    (W : Set X) (f : X → ℂ) (hUn : IsOpen Un) (hw₀ : w₀ ∈ Un) (hc : ContinuousOn bp Un)
    (hb : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source))
    (_hW : IsOpen W) (hwW : bp w₀ ∈ W) (hf : A.HoloOn W f) : AnalyticAt ℂ (f ∘ bp) w₀ := by
  obtain ⟨k, hk⟩ := A.cover (bp w₀)
  have hca : ContinuousAt bp w₀ := hc.continuousAt (hUn.mem_nhds hw₀)
  have h1 : AnalyticAt ℂ (A.chart k ∘ bp) w₀ := hb k w₀ ⟨hw₀, hk⟩
  have h2 : AnalyticAt ℂ (f ∘ (A.chart k).symm) ((A.chart k ∘ bp) w₀) := by
    apply hf k
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (bp w₀)) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hwW
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hev : ∀ᶠ w in 𝓝 w₀, bp w ∈ (A.chart k).source :=
    hca ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart k).left_inv hw]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticLiftToLogResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib


open GlobalTheory.CompanionTheory.Ar.PB.Proj in
theorem holo_of_lift_orbit_top :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D) (V : Set (Fin e → ℂ)) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (h : (Fin e → ℂ) → R.X), J = ⊤ → IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, SameOrbit (R.lift (h u) (h u)) (zex u)) → ContinuousOn h V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ h) (V ∩ h ⁻¹' (R.A.chart k).source) := by
  open GlobalTheory.CompanionTheory.Ar.PB.Proj in
  intro K _ ι _ P J D e R V zex h hJ hV han hmc horb
  subst hJ
  have hloc : ∀ x, ∀ u ∈ V, h u ∈ R.U x → SameOrbit (R.lift x (h u)) (zex u) := fun x u hu hx =>
    orbit_trans (R.compat x (h u) (h u) ⟨hx, R.mem_U (h u)⟩) (horb u hu)
  have hcont : ∀ u0 ∈ V, ContinuousAt h u0 := by
    intro u0 hu0
    refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) ?_
    intro x _ hx
    obtain ⟨𝒰, h𝒰, hx𝒰⟩ := mapClusterPt_iff_ultrafilter.1 hx
    have hev : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), u ∈ V ∧ h u ∈ R.U x := by
      have e1 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), u ∈ V := h𝒰 (hV.mem_nhds hu0)
      have e2 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), h u ∈ R.U x :=
        hx𝒰 ((R.isOpen_U x).mem_nhds (R.mem_U x))
      exact e1.and e2
    have hlim : ∀ q, Filter.Tendsto (fun u => R.lift x (h u) q) 𝒰 (𝓝 (R.lift x x q)) := fun q =>
      (continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hx𝒰
    have hzlim : ∀ q, Filter.Tendsto (fun u => zex u q) 𝒰 (𝓝 (zex u0 q)) := fun q =>
      (han q u0 hu0).continuousAt.tendsto.comp (Filter.tendsto_id'.2 h𝒰)
    have horb0 : SameOrbit (R.lift x x) (zex u0) := by
      refine orbit_of_cross (R.mem x x (R.mem_U x)).1 (hmc u0 hu0).1 ?_
      intro k i i'
      have h1 := ((hlim ⟨k, i⟩).mul (hzlim ⟨k, i'⟩)).sub ((hlim ⟨k, i'⟩).mul (hzlim ⟨k, i⟩))
      have h2 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)),
          (0 : ℂ) = R.lift x (h u) ⟨k, i⟩ * zex u ⟨k, i'⟩ - R.lift x (h u) ⟨k, i'⟩ * zex u ⟨k, i⟩ :=
        hev.mono fun u hu => (sub_eq_zero.2 (orbit_cross (hloc x u hu.1 hu.2) k i i')).symm
      have h3 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2)
      exact sub_eq_zero.1 h3
    exact R.inj x (h u0) (not_mem_mcPts_top _) (orbit_trans horb0 (orbit_symm (horb u0 hu0)))
  refine ⟨fun u hu => (hcont u hu).continuousWithinAt, ?_⟩
  rintro k u0 ⟨hu0, hs0⟩
  have hs0' : h u0 ∈ (R.A.chart k).source := hs0
  choose p hp using (R.mem (h u0) (h u0) (R.mem_U (h u0))).1
  have hsym : (R.A.chart k).symm (R.A.chart k (h u0)) = h u0 := (R.A.chart k).left_inv hs0'
  have ha : AnalyticAt ℂ (fun w => affCoord p (R.lift (h u0) ((R.A.chart k).symm w))) (R.A.chart k (h u0)) :=
    analyticAt_affCoord R.A (R.holo (h u0)) k ((R.A.chart k).map_source hs0')
      (by rw [hsym]; exact R.mem_U (h u0)) p (by rw [hsym]; exact hp)
  have hker := R.immersion (h u0) (not_mem_mcPts_top _) p hp k hs0'
  obtain ⟨G, hG, hGa⟩ := exists_analytic_retraction ha hker
  have hzp : ∀ k', zex u0 ⟨k', p k'⟩ ≠ 0 := fun k' => orbit_ne (horb u0 hu0) (hp k')
  have hb : AnalyticAt ℂ (fun u => affCoord p (zex u)) u0 := by
    rw [analyticAt_pi_iff]
    intro q
    exact (han q u0 hu0).div (han ⟨q.1, p q.1⟩ u0 hu0) (hzp q.1)
  have hG' : AnalyticAt ℂ G (affCoord p (zex u0)) := by
    have hab : affCoord p (R.lift (h u0) ((R.A.chart k).symm (R.A.chart k (h u0)))) = affCoord p (zex u0) := by
      rw [hsym]; exact affCoord_eq (horb u0 hu0) p
    rw [← hab]; exact hG
  refine (AnalyticAt.comp (g := G) (f := fun u => affCoord p (zex u)) hG' hb).congr ?_
  filter_upwards [hV.mem_nhds hu0,
    (hcont u0 hu0).eventually (((R.isOpen_U (h u0)).inter (R.A.chart k).open_source).mem_nhds ⟨R.mem_U (h u0), hs0'⟩),
    (((R.A.chart k).continuousAt hs0').tendsto.comp (hcont u0 hu0)).eventually hGa] with u hu hhu hGu
  simp only [Function.comp_apply] at hGu ⊢
  rw [← hGu, (R.A.chart k).left_inv hhu.2, affCoord_eq (hloc (h u0) u hu hhu.1) p]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionCompositionStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_of_immersion_composition : ∀ {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V) (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ), AnalyticAt ℂ ψ (F y₀) → (fderiv ℂ ψ (F y₀)).ker = ⊥ → AnalyticAt ℂ H y₀ → ContinuousAt F y₀ → (∀ᶠ y in nhds y₀, ψ (F y) = H y) → AnalyticAt ℂ F y₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | exact GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | (intros; apply GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystemStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biholomorphic_lift_system : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}, J = ⊤ → ∀ {e : ℕ} (R : AnLogRes P J e) {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X), (∀ y, g (h y) = y) → (∀ x, h (g x) = x) → HoloMap A R.A g → HoloMap R.A A h → IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorProperties
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear

variable {N : ℕ}

theorem shear_above {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {x y : Fin N} (hxy : x < y) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y = 0 := by
  rw [SchurCalc.elem_apply, if_neg hxy.ne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact lt_asymm hab hxy

theorem shear_diag {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (x : Fin N) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x x = 1 := by
  rw [SchurCalc.elem_apply, if_pos rfl, if_neg, add_zero]
  rintro ⟨rfl, h⟩
  exact hab.ne h

theorem det_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun x y h => shear_above hab t h)]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t x

theorem minor_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (S : Finset (Fin N)) :
    minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  have ht : ((1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).submatrix (S.orderEmbOfFin rfl)
      (S.orderEmbOfFin rfl)).BlockTriangular OrderDual.toDual :=
    fun x y h => shear_above hab t ((S.orderEmbOfFin rfl).strictMono h)
  rw [MinorCalc.minorIJ_eq_det _ S S _ rfl rfl, Matrix.det_of_lowerTriangular _ ht]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t _

theorem support_shear {ca cb : Fin N} (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S) (k c : Fin N)
    (hc : c ∈ S) (hk : k ∉ S) : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) k c = 0 := by
  have hne : k ≠ c := fun e => hk (e ▸ hc)
  rw [SchurCalc.elem_apply, if_neg hne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact hk (hS hc)

theorem minor_mul_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (A : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ (A * (1 + Matrix.single cb ca t)) I S = minorIJ A I S := by
  rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ (support_shear t hS), minor_shear hab, mul_one]

theorem minor_gram_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (G h : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ ((h * (1 + Matrix.single cb ca t))ᴴ * G * (h * (1 + Matrix.single cb ca t))) S S =
      minorIJ (hᴴ * G * h) S S := by
  obtain ⟨H, hH⟩ : ∃ H, H = hᴴ * G * h := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℂ, U = 1 + Matrix.single cb ca t := ⟨_, rfl⟩
  have e : (h * U)ᴴ * G * (h * U) = (Uᴴ * H) * U := by
    rw [hH]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← hU, ← hH, e, hU, minor_mul_shear hab t hS, ← hU]
  apply star_injective
  rw [← SchurCalc.minor_conjTranspose, ← SchurCalc.minor_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hU, minor_mul_shear hab t hS]

theorem shear_main : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  intro N j a b ca cb t hj hb hcase hca hcb
  have hab : ca < cb := Fin.lt_def.2 (by omega)
  have ha2 := a.2
  have hb2 := b.2
  have hcb2 := cb.2
  unfold lastCol at hca
  have hblock : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      omega
    · rw [if_neg (by omega)] at hca
      omega
  have hw : ca ∈ wIdx N j → cb ∈ wIdx N j := by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have ho : ca ∈ omIdx N j → cb ∈ omIdx N j := by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hstep : ∀ i : Fin N, i ≠ a → ca ∈ stepCols N j i → cb ∈ stepCols N j i := by
    intro i hi
    have hia : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
    have hi2 := i.2
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      split_ifs <;> omega
    · rw [if_neg (by omega)] at hca
      split_ifs <;> omega
  refine ⟨?_, det_shear hab t, ?_, ?_⟩
  · intro p q hpq
    rw [SchurCalc.elem_apply, if_neg (fun e => hpq (by rw [e])), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hpq hblock.symm
  · intro h i
    unfold facOf
    rw [minor_mul_shear hab t hw, minor_mul_shear hab t ho]
  · intro G h i hi
    unfold blockPot
    rw [minor_gram_shear hab t (hstep i hi)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSection
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Inverse

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem notMem_mcPts_top_inv (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro h
  have h1 := h.2 1 trivial
  simp at h1

theorem minors_of_sameOrbit_inv {a z : (Σ k, ι k) → ℂ} (h : SameOrbit a z) (k : K) (i i' : ι k) :
    a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  show c k * z ⟨k, i⟩ * z ⟨k, i'⟩ = c k * z ⟨k, i'⟩ * z ⟨k, i⟩
  ring

theorem sameOrbit_of_minors_inv {a z : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (i i' : ι k), a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩) : SameOrbit a z := by
  choose q hq using hz
  refine ⟨fun k => a ⟨k, q k⟩ / z ⟨k, q k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := ha k
    refine div_ne_zero (fun h0 => hi ?_) (hq k)
    have h1 := h k i (q k)
    rw [h0, zero_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hq k)
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, q k⟩ / z ⟨k, q k⟩ * z ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hq k)]
    exact h k i (q k)

end Inverse

theorem exists_continuousOn_inv_pts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P ⊤ e), Nonempty R.X →
    ∃ r : ((Σ k, ι k) → ℂ) → R.X, (∀ z ∈ mcPts P, SameOrbit (R.lift (r z) (r z)) z) ∧
      ContinuousOn r (mcPts P) := by
  intro K _ ι _ P e R hX
  have hs : ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z :=
    fun z hz => R.surj z hz (notMem_mcPts_top_inv z)
  choose! r hr using hs
  refine ⟨r, hr, fun z₀ hz₀ => ?_⟩
  refine isCompact_univ.le_nhds_of_unique_clusterPt (by simp) fun x' _ hx' => ?_
  obtain ⟨G, hG, hGr⟩ := mapClusterPt_iff_ultrafilter.mp hx'
  have hUx : R.U x' ∈ 𝓝 x' := (R.isOpen_U x').mem_nhds (R.mem_U x')
  have hGS : ∀ᶠ z in (G : Filter _), z ∈ mcPts P := hG self_mem_nhdsWithin
  have hGU : ∀ᶠ z in (G : Filter _), r z ∈ R.U x' := hGr hUx
  have hGz : (G : Filter _) ≤ 𝓝 z₀ := hG.trans nhdsWithin_le_nhds
  have hmin : ∀ᶠ z in (G : Filter _), SameOrbit (R.lift x' (r z)) z := by
    filter_upwards [hGS, hGU] with z h1 h2
    exact orbit_trans (R.compat x' (r z) (r z) ⟨h2, R.mem_U _⟩) (hr z h1)
  have ha : ∀ p, Tendsto (fun z => R.lift x' (r z) p) (G : Filter _) (𝓝 (R.lift x' x' p)) :=
    fun p => (((continuousOn_lift R x' p).continuousAt hUx).tendsto).comp hGr
  have hzc : ∀ p, Tendsto (fun z : (Σ k, ι k) → ℂ => z p) (G : Filter _) (𝓝 (z₀ p)) :=
    fun p => ((continuous_apply p).tendsto z₀).comp hGz
  have hsame : SameOrbit (R.lift x' x') z₀ :=
    sameOrbit_of_minors_inv (R.mem x' x' (R.mem_U x')).1 hz₀.1 fun k i i' =>
      tendsto_nhds_unique_of_eventuallyEq ((ha _).mul (hzc _)) ((ha _).mul (hzc _))
        (hmin.mono fun z hz => minors_of_sameOrbit_inv hz k i i')
  exact R.inj x' (r z₀) (notMem_mcPts_top_inv _) (orbit_trans hsame (orbit_symm (hr z₀ hz₀)))

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsUpperOfMinors
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell

theorem det_sub_congr {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P Q : Fin N → Prop)
    [Fintype {a // P a}] [Fintype {a // Q a}] [DecidableEq {a // P a}] [DecidableEq {a // Q a}]
    (hPQ : ∀ a, P a ↔ Q a) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det =
      (h.submatrix (Subtype.val : {a // Q a} → Fin N) Subtype.val).det := by
  obtain rfl : P = Q := funext fun a => propext (hPQ a)
  congr!

theorem det_sub_eq_minorIJ {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, P a ↔ a ∈ S) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ h S S := by
  let e : Fin S.card ≃ {a // P a} :=
    (S.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight fun a => (hP a).symm)
  rw [minorIJ, dite_eq_left rfl, ← Matrix.det_submatrix_equiv_self e]
  congr 1

theorem exists_upper_of_minors : ∀ (N j : ℕ) (h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → h.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ h (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ B : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsLowerUni (h * B) := by
  intro N j h hj hbd hdet hmin
  have hsplit := Matrix.twoBlockTriangular_det h (fun a : Fin N => (a : ℕ) < N - j)
    (fun a ha b hb => hbd a b fun e => ha (e.2 hb))
  rw [hsplit] at hdet
  have hA := left_ne_zero_of_mul hdet
  have hC := right_ne_zero_of_mul hdet
  have hu : ∀ b : Fin N, IsUnit (h.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := by
    intro b
    rw [isUnit_iff_ne_zero]
    have hbN := b.isLt
    by_cases hb : (b : ℕ) < N - j
    · by_cases hl : (b : ℕ) + 1 = N - j
      · rw [det_sub_congr h _ (fun a : Fin N => (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_true]; omega]
        exact hA
      · let i : Fin N := ⟨(b : ℕ) + j, by omega⟩
        have hi : (i : ℕ) = (b : ℕ) + j := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : ¬ ((i : ℕ) + 1 ≤ j) := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg this, Fin.le_def, hb, iff_true]
          omega
    · by_cases hl : (b : ℕ) + 1 = N
      · rw [det_sub_congr h _ (fun a : Fin N => ¬ (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_false]
          have := a.isLt
          omega]
        exact hC
      · let i : Fin N := ⟨(b : ℕ) - (N - j), by omega⟩
        have hi : (i : ℕ) = (b : ℕ) - (N - j) := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : (i : ℕ) + 1 ≤ j := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos this, Fin.le_def, hb, iff_false]
          omega
  obtain ⟨B, h1, h2, h3⟩ := hbd.exists_upper hu
  refine ⟨B, h1, h2, fun hB => ?_, h3⟩
  have := h3.det
  rw [Matrix.det_mul, hB, mul_zero] at this
  exact zero_ne_one this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticSpaceNonempty
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty

theorem flagAn_S_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Nonempty FA.S.X := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  exact FA.Re.nonempty_base

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty
end
end

