module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HolomorphicFamilySmoothHermitian
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetCuspFramePlurisubharmonic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactor
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem log_vertFactor_eq_re_holo : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p M U s hp hU hs hhol y₀ hy₀
  obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp (hs y₀ hy₀)
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp (s y₀) (hs y₀ hy₀)
  rw [VertFactorSmooth.vertFactor_eq D hp (hs y₀ hy₀) hG hH hdeg hrel hHz] at hpos
  have hGz : eval (s y₀) (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, zero_div, norm_zero] at hpos
    exact lt_irrefl _ hpos
  set A := M.atlas with hA
  have HG := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol G
  have HH := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol H
  set Gf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) G) with hGf
  set Hf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) H) with hHf
  set W₁ : Set M.Xc := U ∩ {y | Hf y ≠ 0} with hW₁
  have hW₁o : IsOpen W₁ := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.isOpen_inter_ne A hU HH
  have hsub : W₁ ⊆ U := Set.inter_subset_left
  have mono : ∀ {f : M.Xc → ℂ} {S T : Set M.Xc}, T ⊆ S → A.HoloOn S f → A.HoloOn T f := by
    intro f S T hTS hf j
    exact (hf j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hTS))
  set g : M.Xc → ℂ := fun y => Gf y / Hf y with hg
  have Hg : A.HoloOn W₁ g :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_div_congr A hW₁o (mono hsub HG) (mono hsub HH)
      (fun y hy => hy.2) fun y _ => rfl
  set c : ℂ := g y₀ with hc
  have hc0 : c ≠ 0 := div_ne_zero hGz hHz
  set V : Set M.Xc := W₁ ∩ {y | g y / c ∈ Complex.slitPlane} with hV
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hy, hsl⟩
    have hcont : ContinuousAt (fun y => g y / c) y :=
      (GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.continuousAt_of_holoOn A Hg hy).div_const c
    filter_upwards [hW₁o.mem_nhds hy, hcont (Complex.isOpen_slitPlane.mem_nhds hsl)] with u h1 h2
    exact ⟨h1, h2⟩
  have hy₀V : y₀ ∈ V := by
    refine ⟨⟨hy₀, hHz⟩, ?_⟩
    show g y₀ / c ∈ Complex.slitPlane
    rw [← hc, div_self hc0]
    exact Complex.one_mem_slitPlane
  refine ⟨V, hVo, hy₀V, fun y hy => hsub hy.1, fun y => Complex.log (g y / c) + (Real.log ‖c‖ : ℂ), ?_, ?_⟩
  · intro j u hu
    have hgu : AnalyticAt ℂ (g ∘ (A.chart j).symm) u :=
      Hg j u ⟨hu.1, hu.2.1⟩
    have hsl : (g ∘ (A.chart j).symm) u / c ∈ Complex.slitPlane := hu.2.2
    have h1 : AnalyticAt ℂ (fun v => (g ∘ (A.chart j).symm) v / c) u := hgu.div analyticAt_const hc0
    have h2 := (h1.clog hsl).add (analyticAt_const (v := ((Real.log ‖c‖ : ℝ) : ℂ)))
    exact h2
  · rintro y ⟨hy, hsl⟩
    have hsl' : g y / c ∈ Complex.slitPlane := hsl
    have hgy : g y ≠ 0 := by
      intro h
      rw [h, zero_div] at hsl'
      exact Complex.slitPlane_ne_zero hsl' rfl
    rw [VertFactorSmooth.vertFactor_eq D hp (hs y (hsub hy)) hG hH hdeg hrel hy.2]
    show Real.log ‖g y‖ = (Complex.log (g y / c) + ((Real.log ‖c‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div (g y) c,
      Real.log_div (norm_ne_zero_iff.2 hgy) (norm_ne_zero_iff.2 hc0)]
    ring

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEigenFramePlurisubharmonic
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open ReciprocityTheory.AnForm.A (IsPsh)

theorem psh_add {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ) (hψ : IsPsh U ψ) :
    IsPsh U (fun z => φ z + ψ z) := by
  refine ⟨hφ.1.add hψ.1, fun z w hd => ?_⟩
  obtain ⟨h1, h2⟩ := hφ.2 z w hd
  obtain ⟨h3, h4⟩ := hψ.2 z w hd
  refine ⟨h1.add h3, ?_⟩
  rw [Real.circleAverage_fun_add h1 h3]
  exact add_le_add h2 h4

theorem psh_const {d : ℕ} (U : Set (Fin d → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) := by
  refine ⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩
  rw [Real.circleAverage_const]

theorem psh_sum {d : ℕ} {U : Set (Fin d → ℂ)} {ι : Type} (S : Finset ι) {f : ι → (Fin d → ℂ) → ℝ}
    (h : ∀ i ∈ S, IsPsh U (f i)) : IsPsh U (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psh_const U 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact psh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem psh_congr {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : ∀ z ∈ U, φ z = ψ z)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h z hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h x hxU]
  · obtain ⟨h1, h2⟩ := hφ.2 z w hd
    have e : ∀ θ : ℝ, φ (z + circleMap 0 1 θ • w) = ψ (z + circleMap 0 1 θ • w) := fun θ =>
      h _ (hd _ (by simp))
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    refine ⟨?_, ?_⟩
    · unfold CircleIntegrable at h1 ⊢
      simpa only [e] using h1
    · rw [← h z hz]
      simpa only [Real.circleAverage_def, e] using h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

noncomputable def term (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ)) :
    Option F → ℝ
  | none => 0
  | some I => -Real.log (R.nz σ I.1)

theorem cuspW_eq (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ))
    (h1 : ∀ I ∈ F, R.IsCusp I) (h2 : ∀ I, R.IsCusp I → R.nz σ I ≤ 1 → I ∈ F) :
    R.cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
  have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) :=
    Finset.le_sup' (term R σ F) (Finset.mem_univ none)
  have hb : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)},
      x ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
    rintro x ⟨I, hI, rfl⟩
    by_cases h : R.nz σ I ≤ 1
    · exact Finset.le_sup' (term R σ F) (Finset.mem_univ (some ⟨I, h2 I hI h⟩))
    · have := Real.log_nonneg (not_le.1 h).le
      linarith
  unfold RiemLat.cuspW
  refine le_antisymm (max_le h0 (Real.sSup_le hb h0)) (Finset.sup'_le _ _ fun o _ => ?_)
  cases o with
  | none => exact le_max_left _ _
  | some I => exact le_max_of_le_right (le_csSup ⟨_, hb⟩ ⟨I.1, h1 I.1 I.2, rfl⟩)

theorem add_sup {ι : Type} [Fintype ι] [Nonempty ι] (a : ℝ) (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j => a + f j) = a + Finset.univ.sup' Finset.univ_nonempty f := by
  refine le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) ?_
  · have := Finset.le_sup' f hj
    linarith
  · obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f
    rw [e]
    exact Finset.le_sup' (fun j => a + f j) hj

end GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open GlobalTheory.CompanionTheory.Ar.Cusp.Corr in
theorem _root_.GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m b hU hH hσ hb
  have hrank : ∀ t ∈ U, (R t).HasRank σ m := by
    intro t ht τ
    have h := hb.2 t ht τ
    have e : Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => b τ i t)) = m := by
      rw [finrank_span_eq_card h.1, Fintype.card_fin]
    rw [h.2] at e
    exact e
  have hL : ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) :=
    psh_sum Finset.univ fun τ _ =>
      (_root_.LevelTowerAlt.holomorphic_family_smooth_hermitian E g Λ Ψ n U R hU hH).2.2 m (b τ) (hb.1 τ) (fun t ht => (hb.2 t ht τ).1)
  have hloc : ∀ t₀ ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧
      ReciprocityTheory.AnForm.A.IsPsh (U ∩ W) (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧
      ContinuousOn (fun t => (R t).cuspW σ) (U ∩ W) := by
    intro t₀ ht₀
    obtain ⟨ε, F, hε, hF⟩ := _root_.LevelTowerAlt.cusps_locally_finite_family E g Λ Ψ n U R σ m hU hH hσ hrank t₀ ht₀
    have hVo : IsOpen (U ∩ Metric.ball t₀ ε) := hU.inter Metric.isOpen_ball
    have hVU : U ∩ Metric.ball t₀ ε ⊆ U := Set.inter_subset_left
    have hphi := fun I : F => _root_.GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous E g Λ Ψ n (U ∩ Metric.ball t₀ ε) R σ m b I.1 hVo
      ⟨fun t ht t' ht' => hH.1 t ht.1 t' ht'.1, fun x => (hH.2 x).mono hVU⟩ hσ
      ⟨fun τ i => (hb.1 τ i).mono hVU, fun t ht => hb.2 t ht.1⟩ (fun t ht => (hF t ht).1 I.1 I.2)
    have heq : ∀ t ∈ U ∩ Metric.ball t₀ ε,
        (R t).cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term (R t) σ F) :=
      fun t ht => cuspW_eq (R t) σ F (hF t ht).1 (hF t ht).2
    refine ⟨Metric.ball t₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_⟩
    · have hs := ReciprocityTheory.AnForm.A.isPsh_sup_thm n (Option F) (U ∩ Metric.ball t₀ ε)
        (fun o t => (R t).logDet (fun τ i => b τ i t) + term (R t) σ F o) hVo (fun o => by
          cases o with
          | none =>
            exact psh_congr (fun z _ => (add_zero _).symm) (GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono hVU hL)
          | some I => exact psh_congr (fun z _ => sub_eq_add_neg _ _) (hphi I).1)
      refine psh_congr (fun t ht => ?_) hs
      rw [heq t ht]
      exact add_sup _ _
    · have hc : ∀ o : Option F, ContinuousOn (fun t => term (R t) σ F o) (U ∩ Metric.ball t₀ ε) := by
        intro o
        cases o with
        | none => exact continuousOn_const
        | some I =>
          refine ContinuousOn.neg ((hphi I).2.log fun t ht => ?_)
          have hI := (hF t ht).1 I.1 I.2
          obtain ⟨⟨r, v, hv⟩, h2⟩ := _root_.LevelTowerAlt.isotropic_submodule_nonzero_family E g Λ Ψ (R t) σ I.1 hσ hI.2.2 hI.1
          exact (h2 r v hv).2.1.ne'
      have hs : ContinuousOn (fun t => Finset.univ.sup' Finset.univ_nonempty (fun o => term (R t) σ F o))
          (U ∩ Metric.ball t₀ ε) :=
        ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun o _ => hc o
      exact hs.congr heq
  refine ⟨hL, GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun z hz => ?_,
    continuousOn_of_locally_continuousOn fun z hz => ?_⟩
  · obtain ⟨W, h1, h2, h3, -⟩ := hloc z hz
    exact ⟨U ∩ W, hU.inter h1, ⟨hz, h2⟩, h3⟩
  · obtain ⟨W, h1, h2, -, h4⟩ := hloc z hz
    exact ⟨W, h1, h2, h4⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (A : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · exact (map_zero f).symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem regAt_neg {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    RegAt x (mCoordIdeal z) (-s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨d, -g, h, fun m hm k => hg m (by rwa [support_neg] at hm) k, hh, hn, ?_⟩
  rw [map_neg, heq, neg_mul]

def regRing (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {s | RegAt x (mCoordIdeal z) s}
  mul_mem' := ValRing.regAt_mul
  one_mem' := ValRing.regAt_one x z
  add_mem' := ValRing.regAt_add
  zero_mem' := ValRing.regAt_zero x z
  neg_mem' := regAt_neg

def regVal (x : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) : regRing x z →+* ℂ where
  toFun s := valAt x s z
  map_one' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1
  map_zero' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1
  map_mul' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.1
  map_add' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.2

def valMat {N : ℕ} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (A : Matrix (Fin N) (Fin N) Ω) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a b => valAt x (A a b) z

variable {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_sum (hz : z ∈ mcPts (mCoordIdeal x)) {σ : Type} (s : Finset σ) (f : σ → Ω)
    (hf : ∀ i ∈ s, RegAt x (mCoordIdeal z) (f i)) :
    RegAt x (mCoordIdeal z) (∑ i ∈ s, f i) ∧ valAt x (∑ i ∈ s, f i) z = ∑ i ∈ s, valAt x (f i) z := by
  revert hf
  refine Finset.induction_on s ?_ (fun a s ha ih hf => ?_)
  · intro _
    simp only [Finset.sum_empty]
    exact ⟨(ValRing.regAt_valAt_ring K ι Ω x z hz).1, (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1⟩
  · rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨-, hadd, -, hval⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 _ _ hfa h1
    exact ⟨hadd, by rw [hval, h2]⟩

theorem reg_mul (hz : z ∈ mcPts (mCoordIdeal x)) {s t : Ω} (hs : RegAt x (mCoordIdeal z) s)
    (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z := by
  obtain ⟨hm, -, hv, -⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t hs ht
  exact ⟨hm, hv⟩

theorem regMat_mul {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A B : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (hB : ∀ a b, RegAt x (mCoordIdeal z) (B a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b)) ∧ valMat x z (A * B) = valMat x z A * valMat x z B := by
  have key : ∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b) ∧
      valAt x ((A * B) a b) z = ∑ c, valAt x (A a c) z * valAt x (B c b) z := by
    intro a b
    rw [Matrix.mul_apply]
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun c => A a c * B c b)
      (fun c _ => (reg_mul hz (hA a c) (hB c b)).1)
    refine ⟨h1, ?_⟩
    rw [h2]
    exact Finset.sum_congr rfl fun c _ => (reg_mul hz (hA a c) (hB c b)).2
  refine ⟨fun a b => (key a b).1, ?_⟩
  ext a b
  simp only [valMat, Matrix.of_apply, Matrix.mul_apply]
  exact (key a b).2

theorem reg_minor {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (I J : Finset (Fin N)) :
    RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (valMat x z A) I J := by
  let A' : Matrix (Fin N) (Fin N) (regRing x z) := fun a b => ⟨A a b, hA a b⟩
  have hmap : A'.map (regRing x z).subtype = A := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : regRing x z) : Ω) := by
    have h := minorIJ_map (regRing x z).subtype A' I J
    rw [hmap] at h
    exact h
  have h2 : valMat x z A = A'.map (regVal x hz) := by
    ext a b
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h2, minorIJ_map, h1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonempty
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem exists_ratAlgHom_complex (A : Type) [CommRing A] [Nontrivial A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    Nonempty (A →ₐ[ℚ] ℂ) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
  let κ : (A ⧸ M) →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨κ.comp (Ideal.Quotient.mkₐ ℚ M)⟩

theorem aeval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {x : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal x) : aeval x f = 0 := by
  have h0 : mConeMap x f = 0 := hf
  have e : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap x).toRingHom) =
      (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro p
      simp [mConeMap]
  have := congrArg (fun g => g f) e
  simp only [RingHom.comp_apply] at this
  have h1 : (aeval x : MRing ι →ₐ[ℤ] Ω) f = (MvPolynomial.eval fun _ : K => (1 : Ω)) ((mConeMap x) f) := this.symm
  rw [h1, h0, map_zero]

theorem mcPts_mCoordIdeal_nonempty (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (x : (Σ k, ι k) → Ω) (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) : (mcPts (mCoordIdeal x)).Nonempty := by
  choose c hc using hx
  set u : Ω := ∏ k, x ⟨k, c k⟩ with hu
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  let S : Set Ω := Set.range x ∪ {u⁻¹}
  have hS : S.Finite := (Set.finite_range x).union (Set.finite_singleton _)
  let A : Subalgebra ℚ Ω := Algebra.adjoin ℚ S
  have : Algebra.FiniteType ℚ A := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨ρ⟩ := exists_ratAlgHom_complex A
  let xA : (Σ k, ι k) → A := fun p => ⟨x p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩
  let v : A := ⟨u⁻¹, Algebra.subset_adjoin (Or.inr rfl)⟩
  have huv : (∏ k, xA ⟨k, c k⟩) * v = 1 := by
    apply Subtype.ext
    have : ((∏ k, xA ⟨k, c k⟩ : A) : Ω) = u := by
      rw [hu]
      exact map_prod A.val _ _
    show ((∏ k, xA ⟨k, c k⟩ : A) : Ω) * u⁻¹ = 1
    rw [this, mul_inv_cancel₀ hu0]
  have hz : (∏ k, ρ (xA ⟨k, c k⟩)) * ρ v = 1 := by
    rw [← map_prod, ← map_mul, huv, map_one]
  refine ⟨fun p => ρ (xA p), fun k => ⟨c k, fun h0 => ?_⟩, fun f hf => ?_⟩
  · have : ∏ k, ρ (xA ⟨k, c k⟩) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [this, zero_mul] at hz
    exact zero_ne_one hz
  · have h1 : aeval xA f = 0 := by
      apply Subtype.ext
      have e : (A.val.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom) =
          (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro p
          simp [xA]
      have := congrArg (fun g => g f) e
      simp only [RingHom.comp_apply] at this
      exact this.trans (aeval_eq_zero_of_mem_mCoordIdeal hf)
    have e : ((MvPolynomial.eval fun p => ρ (xA p)).comp (MvPolynomial.map (Int.castRingHom ℂ))) =
        ρ.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro p
        simp
    have := congrArg (fun g => g f) e
    simp only [RingHom.comp_apply] at this
    refine this.trans ?_
    show ρ ((aeval xA : MRing ι →ₐ[ℤ] A) f) = 0
    rw [h1, map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightUniformOnCompact
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ ι _ P n M Xo B S hS K' hK' hc
  have hYo : IsOpen S.R.Yo := (_root_.GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part n M.Xc M.atlas S.R).1
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc]
  intro u hu x hx
  obtain ⟨j, hj⟩ := M.atlas.cover x
  have hO : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm hYo
  have hy : M.atlas.chart j x ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    ⟨(M.atlas.chart j).map_source hj, by
      simpa [Set.mem_preimage, (M.atlas.chart j).left_inv hj] using hK' hx⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hy
  have hsub : Metric.closedBall (M.atlas.chart j x) (ε / 2) ⊆
      (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hU := (_root_.GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied K ι P n M Xo B S hS j _ hsub (isCompact_closedBall _ _)).1
  refine ⟨(M.atlas.chart j).source ∩ (M.atlas.chart j) ⁻¹' Metric.ball (M.atlas.chart j x) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (((M.atlas.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨hj, by simp [hε]⟩), ?_⟩
  filter_upwards [hU u hu] with t ht y hy'
  have h := ht (M.atlas.chart j y) (Metric.ball_subset_closedBall hy'.2)
  simpa [Function.comp, (M.atlas.chart j).left_inv hy'.1] using h

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

