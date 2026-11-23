module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationDeterminesChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstants
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartStandardSmooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0143
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0064

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHolomorphicExponentialChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.ExpChart GlobalTheory.HolHom in
theorem exp_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (N : ℕ) (f : Fin N → Γ(G.left, V)) (ε : ℝ) (Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left) ∧ (∀ b ∈ ball b₀ ε, Ψ b 0 = 1 ∧ (∀ a : Fin g, IsDerivAt0 (fun z => (Ψ b z).left) (Pi.single a 1) (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)) ∧ ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V ∧ ∀ a, valAt' (Ψ b z).left V (t a) = z a) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) → (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (fun a => valAt' x.left V (t a)) := open GlobalTheory.CompanionTheory.Ar.Flat.ExpChart GlobalTheory.HolHom in by
  intro R _ G _ _ g n M B ψ hsm hB b₀ hb₀
  obtain ⟨V, t, ρ, hV, hρ, hss, hθ, hrat⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords R G g M (ψ b₀) hsm
  letI : Algebra R Γ(G.left, V) := (ExpChart.cst G.hom V).toAlgebra
  haveI : Algebra.IsStandardSmooth R Γ(G.left, V) := hss
  have halg : ∀ r, algebraMap R Γ(G.left, V) r = ExpChart.cst G.hom V r := fun _ => rfl
  have h₀ := (hθ (ψ b₀) hρ).1
  let χ₀ : Γ(G.left, V) →+* ℂ := evalHom (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V h₀
  have hχv : ∀ a, valAt' (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V a = χ₀ a := fun a => valR_eq _ _ h₀ a
  have hχc : χ₀.comp (algebraMap R Γ(G.left, V)) = ψ b₀ := RingHom.ext fun r => by
    show χ₀ (ExpChart.cst G.hom V r) = ψ b₀ r
    rw [← hχv]; exact val_cst V _ h₀ r
  have ht₀ : ∀ c, χ₀ (t c) = 0 := fun c => by rw [← hχv]; exact (hθ (ψ b₀) hρ).2.1 c
  have hder : ∀ (θ : R →+* ℂ) (a : Fin g), θ ρ ≠ 0 → ∃ D : Γ(G.left, V) →+ ℂ,
      (∀ f, D f = TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V f)) ∧
      (∀ r, D (ExpChart.cst G.hom V r) = 0) ∧
      (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * D f' +
        valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f' * D f) := by
    intro θ a hr
    have hin := (hθ θ hr).1
    obtain ⟨D, hD, hL⟩ := tan_der (tan_base M θ (Pi.single a 1)) hin
    refine ⟨D, hD, fun r => ?_, hL⟩
    have hv := (le_preimage_dual_iff (tan_base M θ (Pi.single a 1)) V).2 hin
    rw [hD, valR_eq _ _ hv, valR_cst G.hom V _ _ (tan_over M θ (Pi.single a 1)) hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl']
  have hD₀ : ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) →
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0 := by
    intro D hc hl hz
    obtain ⟨c, hcD, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis R G g M (ψ b₀) hsm V hV h₀ D hc (fun f f' => by
      rw [hχv, hχv]; exact hl f f')
    have hc0 : ∀ a, c a = 0 := fun a => by
      have := hcD (t a)
      rw [hz a] at this
      simp only [(hθ (ψ b₀) hρ).2.2] at this
      simpa using this.symm
    ext f
    rw [hcD f]
    simp [hc0]
  have hS₀ : ∀ c, ∃ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) ∧
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0 := by
    intro c
    obtain ⟨D, hD, hc, hl⟩ := hder (ψ b₀) c hρ
    refine ⟨D, hc, fun x y => ?_, fun c' => ?_⟩
    · rw [hl, hχv, hχv]
    · rw [hD]; exact (hθ (ψ b₀) hρ).2.2 c c'
  obtain ⟨N, f, ε, δ, Ψa, hε, hδ, hεB, hΨ₀, hprop, hdiff, hft, huniq⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.StdSmoothChart.exists_sections R Γ(G.left, V) n g B ψ hB.1 hB.2 b₀ hb₀ χ₀ t hχc ht₀ hD₀ hS₀

  have hev : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 ∧
      ∀ j, ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
    have hc : ∀ u, ContinuousAt (fun b => ψ b u) b₀ := fun u =>
      (hB.2 u).continuousOn.continuousAt (hB.1.mem_nhds hb₀)
    have h1 : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 := (hc ρ).eventually_ne hρ
    have h2 : ∀ j, ∀ᶠ b in 𝓝 b₀,
        ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
      intro j
      obtain ⟨u, k, hu⟩ := hrat (f j)
      have hq : ContinuousAt (fun b => ψ b u / ψ b ρ ^ k) b₀ := (hc u).div ((hc ρ).pow k) (pow_ne_zero k hρ)
      have hq0 : ψ b₀ u / ψ b₀ ρ ^ k = χ₀ (f j) := by
        rw [div_eq_iff (pow_ne_zero k hρ), ← hu _ hρ, hχv]
      have hb := hq.eventually (Metric.ball_mem_nhds _ hδ)
      filter_upwards [hb, h1] with b hb1 hb2
      have : valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) = ψ b u / ψ b ρ ^ k := by
        rw [eq_div_iff (pow_ne_zero k hb2)]; exact hu _ hb2
      rw [this, ← hq0]
      simpa [dist_eq_norm] using hb1
    filter_upwards [h1, eventually_all.2 h2] with b a1 a2 using ⟨a1, a2⟩
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', h1', h2', h3'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε₁ ∧ ε' ≤ ε ∧ ε' ≤ δ :=
    ⟨min ε₁ (min ε δ), lt_min hε₁ (lt_min hε hδ), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hex : ∀ b z, ∃ x : Over.mk (spMap (ψ b)) ⟶ G, b ∈ ball b₀ ε → z ∈ ball (0 : Fin g → ℂ) ε →
      ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = Ψa b z a := by
    intro b z
    by_cases h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε
    · obtain ⟨x, hx, hv⟩ := exists_pt hV (ψ b) (Ψa b z) (fun r => congrArg (fun q => q r) (hprop b h.1 z h.2).1)
      exact ⟨x, fun _ _ => ⟨hx, hv⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Ψ hΨ using hex
  have hbε : ∀ b ∈ ball b₀ ε', b ∈ ball b₀ ε := fun b hb => ball_subset_ball h2' hb
  have hzε : ∀ z ∈ ball (0 : Fin g → ℂ) ε', z ∈ ball (0 : Fin g → ℂ) ε := fun b hb => ball_subset_ball h2' hb
  have hzero : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε' := mem_ball_self hε'
  have hone : ∀ b ∈ ball b₀ ε', Ψ b 0 = 1 := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := hball b (ball_subset_ball h1' hb)
    have hin := (hθ (ψ b) hb1).1
    have hc : (evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w _) hin r
    have hv : ∀ a, evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin a = valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V a :=
      fun a => (valR_eq _ _ hin a).symm
    have := (huniq b (ball_subset_ball h3' hb) _ hc (fun j => by rw [hv]; exact hb2 j)).2
    have hz : (fun c => evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin (t c)) = 0 := by
      funext c
      rw [hv]; exact (hθ (ψ b) hb1).2.1 c
    rw [hz] at this
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    refine pt_ext hV hx hin fun a => ?_
    rw [hvx, ← this, hv]
  have hHol : ∀ p ∈ ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε', HolAt (fun q : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ q.1 q.2).left) p := by
    intro p hp
    have hop : IsOpen (ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε') := isOpen_ball.prod isOpen_ball
    have hnb := hop.mem_nhds hp
    have hop' : IsOpen (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) := isOpen_ball.prod isOpen_ball
    refine holAt_of_affine hV (hΨ _ _ (hbε _ hp.1) (hzε _ hp.2)).1 ?_ fun a => ?_
    · filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).1
    · have hd : DifferentiableAt ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψa bz.1 bz.2 a) p :=
        (hdiff a).differentiableAt (hop'.mem_nhds ⟨hbε _ hp.1, hzε _ hp.2⟩)
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).2 a
  have hfib : ∀ b ∈ ball b₀ ε', HolAt (fun z => (Ψ b z).left) 0 := by
    intro b hb
    have := (hHol (b, 0) ⟨hb, hzero⟩).precomp (k := fun z : Fin g → ℂ => (b, z)) (z := 0)
      ((differentiableAt_const b).prodMk differentiableAt_id)
    exact this
  refine ⟨V, t, N, f, ε', Ψ, hε', (ball_subset_ball h2').trans hεB, ?_, fun b hb => ⟨hone b hb, fun a => ?_, fun z hz => ?_⟩, ε', hε', fun b hb x hxV hnear => ?_⟩
  · exact isHolTo_of_holAt (isOpen_ball.prod isOpen_ball) hHol
  ·
    obtain ⟨hb1, -⟩ := hball b (ball_subset_ball h1' hb)
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    obtain ⟨v', hv'⟩ := (hfib b hb).exists_isDerivAt (Pi.single a 1)
    have hb' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left) = (Ψ b 0).left := by
      rw [tan_base M (ψ b) (Pi.single a 1), hone b hb]
    obtain ⟨D₁, hD₁, hL₁⟩ := tan_der hv'.1 hx
    obtain ⟨D₂, hD₂, hL₂⟩ := tan_der hb' hx
    have hnb : ball (0 : Fin g → ℂ) ε' ∈ 𝓝 (0 : Fin g → ℂ) := ball_mem_nhds _ hε'
    have hval : ∀ c, D₁ (t c) = if a = c then 1 else 0 := by
      intro c
      have e : (fun z => valAt' (Ψ b z).left V (t c)) =ᶠ[𝓝 0] fun z => z c := by
        filter_upwards [hnb] with z hz
        rw [(hΨ b z (hbε b hb) (hzε z hz)).2]
        exact (hprop b (hbε b hb) z (hzε z hz)).2.1 c
      rw [hD₁, hv'.2 V hx, e.fderiv_eq, (hasFDerivAt_apply c (0 : Fin g → ℂ)).fderiv]
      simp [Pi.single_apply, eq_comm]
    have hcon1 : ∀ r, D₁ (ExpChart.cst G.hom V r) = 0 := by
      intro r
      have e : (fun z => valAt' (Ψ b z).left V (ExpChart.cst G.hom V r)) =ᶠ[𝓝 0] fun _ => ψ b r := by
        filter_upwards [hnb] with z hz
        exact val_cst V _ (hΨ b z (hbε b hb) (hzε z hz)).1 r
      rw [hD₁, hv'.2 V hx, e.fderiv_eq]
      simp
    obtain ⟨D₃, hD₃, hcon2, -⟩ := hder (ψ b) a hb1
    have hD23 : ∀ f, D₂ f = D₃ f := fun f => by rw [hD₂, hD₃]
    have hz : D₁ - D₂ = 0 := by
      refine (hprop b (hbε b hb) 0 (hzε 0 hzero)).2.2 _ (fun r => ?_) (fun x y => ?_) (fun c => ?_)
      · show D₁ (ExpChart.cst G.hom V r) - D₂ (ExpChart.cst G.hom V r) = 0
        rw [hcon1, hD23, hcon2, sub_zero]
      · simp only [AddMonoidHom.sub_apply]
        rw [hL₁, hL₂, hvx, hvx]
        ring
      · simp only [AddMonoidHom.sub_apply]
        rw [hval, hD₂, (hθ (ψ b) hb1).2.2 a c, sub_self]
    have heq : v' = spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left := by
      refine point_ext hV ((le_preimage_dual_iff hv'.1 V).2 hx) ((le_preimage_dual_iff hb' V).2 hx) fun f => ?_
      refine TrivSqZeroExt.ext ((fst_valR hv'.1 hx f).trans (fst_valR hb' hx f).symm) ?_
      have := DFunLike.congr_fun hz f
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this
      rw [← hD₁, ← hD₂, this]
    rw [← heq]
    exact (isDerivAt0_iff _ _ _).2 hv'
  · obtain ⟨hx, hvx⟩ := hΨ b z (hbε b hb) (hzε z hz)
    refine ⟨hx, fun a => ?_⟩
    rw [hvx]
    exact (hprop b (hbε b hb) z (hzε z hz)).2.1 a
  · have hbδ := ball_subset_ball h3' hb
    have hc : (evalHom x.left V hxV).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w x) hxV r
    have hv : ∀ a, evalHom x.left V hxV a = valAt' x.left V a := fun a => (valR_eq _ _ hxV a).symm
    have hΨb₀ : ∀ a, valAt' (Ψ b₀ 0).left V a = χ₀ a := fun a => by
      rw [(hΨ b₀ 0 (mem_ball_self hε) (hzε 0 hzero)).2, hΨ₀]
    have hn : ∀ j, ‖evalHom x.left V hxV (f j) - χ₀ (f j)‖ < δ := fun j => by
      rw [hv, ← hΨb₀]
      exact (hnear j).trans_le h3'
    obtain ⟨-, hχ⟩ := huniq b hbδ _ hc hn
    have hmem : (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε' := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε']
      intro c
      obtain ⟨j, hj⟩ := hft c
      have := hnear j
      rw [hΨb₀, hj, ht₀, sub_zero] at this
      exact this
    refine ⟨hmem, ?_⟩
    obtain ⟨hx, hvx⟩ := hΨ b _ (hbε b hb) (hzε _ hmem)
    refine pt_ext hV hxV hx fun a => ?_
    rw [hvx, ← hv, hχ]
    simp only [hv]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PullbackFramesComplexPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PointCompare

section Val
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {F : Type} [Field F] {z : Sp F ⟶ X}

theorem val_mul {a a' : Ω} {r r' : F} (h : ValAt ξ z a r) (h' : ValAt ξ z a' r') : ValAt ξ z (a * a') (r * r') := by
  obtain ⟨hs, s, e1, e2⟩ := h
  obtain ⟨_, s', e1', e2'⟩ := h'
  have f2 : RootHt.Pick.valMap z s = r := e2
  have f2' : RootHt.Pick.valMap z s' = r' := e2'
  refine ⟨hs, s * s', by rw [map_mul, e1, e1'], ?_⟩
  show RootHt.Pick.valMap z (s * s') = r * r'
  rw [map_mul, f2, f2']

theorem val_det (h : genPt ξ ⤳ centre z) {n : ℕ} {P : Matrix (Fin n) (Fin n) Ω} {A : Matrix (Fin n) (Fin n) F}
    (hP : ∀ i j, ValAt ξ z (P i j) (A i j)) : ValAt ξ z P.det A.det := by
  have : ∀ i j, ∃ s : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ s = P i j ∧
      (Scheme.stalkClosedPointTo z).hom s = A i j := fun i j => by
    obtain ⟨_, s, e1, e2⟩ := hP i j
    exact ⟨s, e1, e2⟩
  choose s e1 e2 using this
  refine ⟨h, (Matrix.of s).det, ?_, ?_⟩
  · rw [RingHom.map_det]
    congr 1
    ext i j
    exact e1 i j
  · show RootHt.Pick.valMap z _ = A.det
    rw [RingHom.map_det]
    congr 1
    ext i j
    exact e2 i j

end Val

section Gen
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {F : Type} [Field F] {x : Sp F ⟶ S}

theorem exists_comb {n : ℕ} (cf : Fin n → F) (v : Fin n → (epsAt x ⟶ G)) : ∃ w, IsComb cf v w :=
  ⟨_, fun i => LieTangent.epsScale x (cf i) ≫ v i, fun _ => rfl, rfl⟩

theorem frame_det {P : Type} [CommRing P] {act : OAct P G} {σ : P →+* F} {n : ℕ} {v v' : Fin n → (epsAt x ⟶ G)}
    {A : Matrix (Fin n) (Fin n) F} (hv : IsEigFrame act x σ v) (hv' : IsEigFrame act x σ v')
    (hA : ∀ i, IsComb (A i) v (v' i)) : A.det ≠ 0 := by
  have : ∀ i, ∃ cf, IsComb cf v' (v i) := fun i => (hv'.2 _ (hv.1 i)).exists
  choose C hC using this
  have ht : ∀ i, IsTanAt G x (v i) := fun i => (hv.1 i).1
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul S G F x n n n v v' v (Matrix.of C) A ht hA hC
  have h2 := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row S G F x n v ht
  have h3 : Matrix.of C * A = 1 := by
    ext i j
    have := (hv.2 _ (hv.1 i)).unique (h1 i) (h2 i)
    exact congrFun this j
  intro h0
  have := congrArg Matrix.det h3
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem expand (Z : CptOver Y U) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (σ' : 𝓞 E →+* F) {n : ℕ} {c₀ b₁ : Fin n → Z.V}
    {v₀ v : Vecs y n} {t : Z.Ω} (hc : (Z.eig σ).IsFrameAt c₀ ⟨_, h⟩) (h₀ : Rep.IsValFam Z y c₀ v₀)
    (h₁ : Rep.IsValFam Z y b₁ v) (he : ∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c σ)))
    (hf₀ : IsEigFrame Xo.univ.t.act (under y) σ' v₀) (hf : IsEigFrame Xo.univ.t.act (under y) σ' v)
    (hw : exteriorPower.ιMulti Z.Ω n b₁ = t • exteriorPower.ιMulti Z.Ω n c₀) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, IsComb (A i) v₀ (v i)) ∧ A.det ≠ 0 ∧
      ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) t A.det := by
  have hb : ∀ i, b₁ i ∈ Z.eig σ ⟨_, h⟩ := fun i => by
    obtain ⟨v', hv', -⟩ := h₁ i
    exact ⟨RootHt.Pick.mem_lat_of_val Z.M hv' h, he i⟩
  have hco : ∀ i, ∃ P : Fin n → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h⟩, ∑ j, P j • c₀ j = b₁ i := fun i => by
    have := hb i
    rw [hc.2] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose P hP using hco
  have hval : ∀ i j, ∃ r : F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (P i j : Z.Ω) r := fun i j =>
    RootHt.Pick.exists_valAt (P i j).2
  choose A hA using hval
  let Pm : Matrix (Fin n) (Fin n) Z.Ω := fun i j => (P i j : Z.Ω)
  have hb' : b₁ = fun i => ∑ j, Pm i j • c₀ j := by
    funext i
    rw [← hP i]
    rfl
  have hdet : t = Pm.det := by
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Z.Ω Z.V n c₀ Pm
    rw [← hb', hw] at h1
    have h2 : (t - Pm.det) • exteriorPower.ιMulti Z.Ω n c₀ = 0 := by
      rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right (GlobalTheory.T.iota_multi_ne_zero_of_lin_indep Z.Ω Z.V n c₀ hc.1))
  have hcomb : ∀ i, IsComb (Matrix.of A i) v₀ (v i) := fun i => by
    obtain ⟨w, hw'⟩ := exists_comb (Matrix.of A i) v₀
    obtain ⟨w', hw₁, hw₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb E H D l Xo c O β Y U Z F y n c₀ v₀ (Pm i) (Matrix.of A i) w h h₀ (hA i) hw'
    obtain ⟨v', hv₁, hv₂⟩ := h₁ i
    have e : ∑ j, Pm i j • c₀ j = b₁ i := by rw [hb']
    rw [e] at hw₁
    have e' := LieModel.ValAt.unique Z.gen hw₁ hv₁
    subst e'
    rw [← SameVec.unique_left hw₂ hv₂]
    exact hw'
  refine ⟨Matrix.of A, hcomb, frame_det hf₀ hf hcomb, ?_⟩
  rw [hdet]
  exact val_det h hA

end Main

theorem valAt_pull {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} {π : X' ⟶ X}
    (hd : ξ' ≫ π = ξ) {y' : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre y') {a : Ω} {r : ℂ}
    (h : ValAt ξ (y' ≫ π) a r) : ValAt ξ' y' a r := by
  obtain ⟨hp, s, hs, hr⟩ := h
  have hdom : Dominates ξ' ξ π (RingHom.id Ω) := by
    change ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, hd]
  refine ⟨hq, (π.stalkMap (centre y')).hom s, ?_, ?_⟩
  · exact (RegAtDom.genMap_stalkMap hdom (centre y') hq hp s).trans hs
  · rw [← hr, Scheme.stalkClosedPointTo_comp]
    rfl

theorem genPt_specializes {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} {π : X' ⟶ X}
    (hd : ξ' ≫ π = ξ) {y' : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre y') : genPt ξ ⤳ centre (y' ≫ π) := by
  have hdom : Dominates ξ' ξ π (RingHom.id Ω) := by
    change ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, hd]
  have := hq.map π.continuous
  rw [RegAtDom.map_genPt hdom] at this
  exact this

theorem point_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ v₁ : Fin D.p → Z.V) (b₂ v₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (ξ' : Sp Z.Ω ⟶ X') (y' : Sp ℂ ⟶ X') (yy : Sp ℂ ⟶ Xo.XF c) (v vz : Vecs yy D.p) (w wz : Vecs yy D.q) (α κ : Z.Ω) (r : ℂ), ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → yy ≫ Y.j = y' ≫ π → IsUnitAn τ σ Φ → IsFramed Set.univ τ σ yy v w → IsFramed Set.univ τ σ yy vz wz → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (b₁ i) v' ∧ SameVec Y yy (v i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (b₂ j) w' ∧ SameVec Y yy (w j) w') → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (v₁ i) v' ∧ SameVec Y yy (vz i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (v₂ j) w' ∧ SameVec Y yy (wz j) w') → (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) → (∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ))) → (∀ j, b₂ j ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) → α ≠ 0 → κ ≠ 0 → exteriorPower.ιMulti Z.Ω D.p v₁ = α • exteriorPower.ιMulti Z.Ω D.p b₁ → exteriorPower.ιMulti Z.Ω D.q v₂ = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → ValAt ξ' y' (α / κ) r → Φ yy v w = Φ yy vz wz * r := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ v₁ b₂ v₂ X' π ξ' y' yy v vz w wz α κ r hξ hgen hyy hΦ hf hfz hb₁ hb₂
    hz₁ hz₂ hfr he₁ he₂ hα hκ hw₁ hw₂ hr
  obtain ⟨hq, -⟩ := id hr
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (yy ≫ Y.j) := by
    rw [hyy]
    exact genPt_specializes hξ hq
  obtain ⟨hfr₁, hfr₂⟩ := hfr ⟨_, h⟩ rfl
  have hw₁' : exteriorPower.ιMulti Z.Ω D.p b₁ = α⁻¹ • exteriorPower.ιMulti Z.Ω D.p v₁ := by
    rw [hw₁, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hw₂' : exteriorPower.ιMulti Z.Ω D.q b₂ = κ⁻¹ • exteriorPower.ιMulti Z.Ω D.q v₂ := by
    rw [hw₂, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨A, hA, hA0, hAv⟩ := expand Z h τ (σ.comp (tauIn c τ)) hfr₁ hz₁ hb₁ he₁ hfz.2.2.1 hf.2.2.1 hw₁'
  obtain ⟨B, hB, -, hBv⟩ := expand Z h (ComplexEmbedding.conjugate τ)
    (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) hfr₂ hz₂ hb₂ he₂ hfz.2.2.2 hf.2.2.2 hw₂'
  rw [hyy] at hAv hBv
  have hA' := valAt_pull hξ hq hAv
  have hB' := valAt_pull hξ hq hBv
  have hm := val_mul hr hA'
  have e : α / κ * α⁻¹ = κ⁻¹ := by field_simp
  rw [e] at hm
  have hdet : r * A.det = B.det := LieTangent.valAt_unique hgen hm hB'
  have hc := hΦ.chg yy vz wz v w A B hfz hf hA hB
  rw [← hdet] at hc
  rw [← _root_.mul_assoc] at hc
  exact mul_right_cancel₀ hA0 hc

end GlobalTheory.CompanionTheory.Ar.Flat.PointCompare
end
end

