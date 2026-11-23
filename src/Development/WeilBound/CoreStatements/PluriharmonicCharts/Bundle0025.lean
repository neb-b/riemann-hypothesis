module

public import Mathlib
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.FamilyPeriod
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsImmersion
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

open PositivityTheory.Xgp.c_bm_exists_period FramePeriods in
theorem PositivityTheory.Xgp.t_c_bm_exists_immersion : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (d : ℕ), 𝔐.IsCover d → ∀ (Rb : AnLogRes (mCoordIdeal M.x) ⊤ (Fintype.card (CMType H) * D.p * D.q)) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ l, IsOpen (O l)) → (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ l, ∃ x ∈ O l \ bdry s, ∃ (V : Set Rb.X) (Pi : CMType H → Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), x ∈ V ∧ IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F l) τ Rb x')) ∧ ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p → ((Pi τ x)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0 := by
  intro hG E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie hp1 _ d hd Rb s hInt hcl q O F hO hcov hF hgood
  have hpq : 1 ≤ D.p + D.q := by omega
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  haveI : Countable M.Ω := countable_of_tie 𝔐.tie
  haveI : Countable c.F := 𝔐.cst.injective.countable
  obtain ⟨φ, hφ⟩ := exists_embedding c.F M.Ω 𝔐.cst c.F.val.toRingHom
  have tp := _root_.GlobalTheory.CompanionTheory.Ar.tie_points 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  obtain ⟨w, hw⟩ := tp.2.1 (spMap φ ≫ 𝔐.ξ) (𝔐.all _)
  have htop : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun z h => by simpa using h.2 1 trivial
  obtain ⟨x, a, ha, hxa⟩ := Rb.surj w ((_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).2 ⟨_, 𝔐.all _, hw⟩) (htop w)
  have hz : CoordsAt 𝔐.ξ M.x (spMap φ ≫ 𝔐.ξ) (Rb.lift x x) :=
    ((tp.2.2 _ _ (𝔐.all _) hw).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), hxa⟩
  have hcz : centre (spMap φ ≫ 𝔐.ξ) = centre 𝔐.ξ := SheetDecomposition.CovSch.centre_spMap φ 𝔐.ξ
  have hx : x ∉ bdry s := (hInt x _ hz).2 (by
    change centre _ ∈ _
    rw [hcz]
    exact (_root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l (Xo l) c _ _ Y S M.Ω _ _ M.x 𝔐 (FaithfulSMul.algebraMap_injective _ _)).1)
  obtain ⟨l₀, hl₀⟩ := hcov x
  obtain ⟨j, r, p, hr, hj, hwd, hp⟩ := exists_family (𝔐 := 𝔐) Rb hcl hx
  have hhol : IsHolTo (Metric.ball 0 1) p := _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all _ _ _ p
    Metric.isOpen_ball hwd fun u hu => (hp u hu).2.1
  obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) _ p hhol
  have hint : ∀ u ∈ Metric.ball 0 1, 𝔐.Interior (p u) := fun u hu => (hInt _ _ (hp u hu).2.2).1 (hp u hu).1
  have hb0 : 0 ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) 1 := Metric.mem_ball_self one_pos
  have hc0 : CoordsAt 𝔐.ξ M.x (p 0) (Rb.lift x x) := by
    have := (hp 0 hb0).2.1
    rwa [smul_zero, add_zero, (Rb.A.chart j).left_inv hj] at this
  have hp0 : p 0 = spMap φ ≫ 𝔐.ξ :=
    (tp.1 _ hz.1 (tp.2.2 _ _ (𝔐.all _) hz).1).unique ⟨𝔐.all _, hc0⟩ ⟨𝔐.all _, hz⟩
  have hτ₀ : τ₀ = c.F.val.toRingHom := by
    have h1 := hτ 0 hb0
    rw [hp0, Category.assoc, 𝔐.cst_over, spMap, spMap, spMap, ← Spec.map_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    rw [← hφ]
    exact IsFractionRing.ringHom_ext (A := 𝓞 c.F) fun t => (DFunLike.congr_fun h2 t).symm
  obtain ⟨ρ, B, Pi, Γ, hρ, hρ', hB, h0, hsub, hPi, hgr, hder⟩ := family_period hG.1.2.2.1 tie hpq (hF l₀) p τ₀
    (by rw [hτ₀]; rfl) hhol hτ hint (by rw [ptIdeal_centre hc0]; exact hgood l₀ x hl₀)
  obtain ⟨h1, h2, h3⟩ := to_manifold Rb.A j hj (r := (r : ℂ) * ρ) hB h0
  have hne : (r : ℂ) * ρ ≠ 0 := by exact_mod_cast (mul_pos hr hρ).ne'
  have hback : ∀ x' ∈ (Rb.A.chart j).source, (Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • (ρ : ℂ) •
      (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x))) = x' := fun x' hx' => by
    rw [smul_smul (r : ℂ), smul_inv_smul₀ hne, add_sub_cancel, (Rb.A.chart j).left_inv hx']
  refine ⟨l₀, x, ⟨hl₀, hx⟩, _, fun τ x' => Pi τ (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x)), h2,
    ⟨h1, fun τ a b => h3 _ (hPi τ a b), fun τ x' hx' => ?_⟩, fun k hk v hv => ?_⟩
  · have hm := smul_mem_ball' hρ hρ' (hsub hx'.2)
    have hc := (hp _ hm).2.2
    rw [hback x' hx'.1] at hc
    simp only
    rw [baseGram, gramFn_eq hc (hint _ hm) (hgr τ _ hx'.2).1]
    exact (hgr τ _ hx'.2).2
  let ψ : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) :=
    fun t => ((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j ((Rb.A.chart k).symm t) - Rb.A.chart j x)
  have hkx : (Rb.A.chart k).symm (Rb.A.chart k x) = x := (Rb.A.chart k).left_inv hk
  have hψ0 : ψ (Rb.A.chart k x) = 0 := by simp only [ψ, hkx, sub_self, smul_zero]
  have hψ : DifferentiableAt ℂ ψ (Rb.A.chart k x) :=
    by
    have := ((Rb.A.holo k j _ ⟨(Rb.A.chart k).map_source hk, by rw [Set.mem_preimage, hkx]; exact hj⟩).differentiableAt.sub_const
      (Rb.A.chart j x)).const_smul (((r : ℂ) * ρ)⁻¹)
    exact this
  have chain : ∀ f : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → ℂ, DifferentiableAt ℂ f 0 →
      HasFDerivAt (fun t => f (ψ t)) ((fderiv ℂ f 0).comp (fderiv ℂ ψ (Rb.A.chart k x))) (Rb.A.chart k x) :=
    fun f hf => HasFDerivAt.comp _ (by rw [hψ0]; exact hf.hasFDerivAt) hψ.hasFDerivAt
  obtain ⟨V, hV1, hV2⟩ := hder (fderiv ℂ ψ (Rb.A.chart k x) v) fun τ a b h₁ h₂ => by
    have := hv τ a b h₁ h₂
    simp only [sub_self, smul_zero] at this
    convert this using 3
    ext a' b'
    exact (congrArg (· v) (chain _ ((hPi τ a' b').differentiableAt (hB.mem_nhds h0))).fderiv).symm
  have hV3 : V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0 := by
    have e1 := hV1.1
    simp only [smul_zero] at e1
    rw [hp0] at e1 hV2 ⊢
    exact const_of_finite 𝔐.tie.gen 𝔐.gen₀ 𝔐.fn_over (hd.2 ▸ hd.1) e1 hV2
  choose pc hpc using hz.1
  have hball : ∀ᶠ u in nhds (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ), u ∈ Metric.ball 0 1 :=
    Metric.isOpen_ball.mem_nhds hb0
  let wv : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ := fun u =>
    Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • (ρ : ℂ) • u))
  have hwv0 : wv 0 = Rb.lift x x := by simp only [wv, smul_zero, add_zero, (Rb.A.chart j).left_inv hj]
  have hwv : ∀ q', DifferentiableAt ℂ (fun u => wv u q') 0 := fun q' => by
    have a1 := (differentiableOn_pi.1 hwd q').differentiableAt hball
    have a2 : DifferentiableAt ℂ (fun u : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ => (ρ : ℂ) • u) 0 := by
      fun_prop
    exact DifferentiableAt.comp (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) (by rw [smul_zero]; exact a1) a2
  have hne0 : ∀ k', wv 0 ⟨k', pc k'⟩ ≠ 0 := fun k' => by rw [hwv0]; exact (hpc k').ne_zero
  have hhol' : IsHolTo (Metric.ball 0 1) fun u => p ((ρ : ℂ) • u) :=
    _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all _ _ wv _ Metric.isOpen_ball
      (hwd.comp (by fun_prop) fun u hu => smul_mem_ball' hρ hρ' hu) fun u hu => (hp _ (smul_mem_ball' hρ hρ' hu)).2.1
  have hA : ∀ q', DifferentiableAt ℂ (fun u => affCoord pc (wv u) q') 0 ∧
      fderiv ℂ (fun u => affCoord pc (wv u) q') 0 (fderiv ℂ ψ (Rb.A.chart k x) v) = 0 := fun q' => by
    refine ⟨by
      simp only [affCoord, div_eq_mul_inv]
      exact (hwv q').mul ((hwv ⟨q'.1, pc q'.1⟩).inv (hne0 q'.1)), fderiv_value_zero 𝔐.tie.gen 𝔐.all hhol' hb0
      (by simp only [smul_zero]; rw [hp0, hcz]) (by simp only [smul_zero]; rw [← hV3]; exact hV1)
      (a := M.x q' / M.x ⟨q'.1, pc q'.1⟩) ?_⟩
    filter_upwards [hball, (hwv _).continuousAt.eventually_ne (hne0 q'.1)] with u hu hu'
    obtain ⟨t, ht, e⟩ := ((hp _ (smul_mem_ball' hρ hρ' hu)).2.1.2 q'.1 (pc q'.1) (IsUnit.mk0 _ hu')).2 q'.2
    have e' : wv u q' = t * wv u ⟨q'.1, pc q'.1⟩ := e
    rw [affCoord, e', mul_div_cancel_right₀ _ hu']
    exact ht
  have hker := Rb.immersion x (htop _) pc (fun k' => (hpc k').ne_zero) k hk
  have hev : (fun t => affCoord pc (Rb.lift x ((Rb.A.chart k).symm t))) =ᶠ[nhds (Rb.A.chart k x)]
      fun t q' => affCoord pc (wv (ψ t)) q' := by
    have hs : (Rb.A.chart j).source ∈ nhds ((Rb.A.chart k).symm (Rb.A.chart k x)) := by
      rw [hkx]; exact (Rb.A.chart j).open_source.mem_nhds hj
    filter_upwards [((Rb.A.chart k).continuousAt_symm ((Rb.A.chart k).map_source hk)).eventually hs] with t ht
    simp only [wv, ψ, hback _ ht]
  rw [hev.fderiv_eq, (hasFDerivAt_pi.2 fun q' => chain _ (hA q').1).fderiv] at hker
  rw [← Submodule.mem_bot ℂ, ← hker]
  exact funext fun q' => (hA q').2
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsPeriod
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

open PositivityTheory.Xgp.c_bm_exists_period FramePeriods in
theorem PositivityTheory.Xgp.t_c_bm_exists_period : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (x : Rb.X), x ∉ bdry s → M.GoodAt F (mCoordIdeal (Rb.lift x x)) → ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧ (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧ ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
  intro hG E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie hp1 _ n Rb s hInt hcl F hF τ x hx hg
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨j, r, p, hr, hj, hw, hp⟩ := exists_family (𝔐 := 𝔐) Rb hcl hx
  have hhol : IsHolTo (Metric.ball 0 1) p := _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all n _ _ p
    Metric.isOpen_ball hw fun u hu => (hp u hu).2.1
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p u) := fun u hu =>
    (hInt _ _ (hp u hu).2.2).1 (hp u hu).1
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hg0 : M.GoodAt F (ptIdeal 𝔐.ξ M.x ⟨centre (p 0), 𝔐.all _⟩) := by
    rw [ptIdeal_centre (hp 0 hb0).2.1, smul_zero, add_zero, (Rb.A.chart j).left_inv hj]
    exact hg
  have fin : ∀ (ρ : ℝ) (B : Set (Fin n → ℂ)) (Pi Γ : (Fin n → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
      0 < ρ → ρ ≤ 1 → IsOpen B → 0 ∈ B → B ⊆ Metric.ball 0 1 → HolM B Pi →
      (∀ u ∈ B, 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (gb tie F τ) (Γ u) ∧ IsPeriodGram D.p (Pi u) (blockG (Γ u))) →
      ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧
        (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧
        ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
    intro ρ B Pi Γ hρ hρ' hB h0 hsub hPi hgr
    obtain ⟨h1, h2, h3⟩ := to_manifold Rb.A j hj (r := (r : ℂ) * ρ) hB h0
    refine ⟨_, fun x' => Pi (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x)), h1, h2,
      fun a b => h3 _ (hPi a b), fun x' hx' => ?_⟩
    have hm := smul_mem_ball' hρ hρ' (hsub hx'.2)
    have hc := (hp _ hm).2.2
    have hne : (r : ℂ) * ρ ≠ 0 := by exact_mod_cast (mul_pos hr hρ).ne'
    rw [smul_smul (r : ℂ), smul_inv_smul₀ hne, add_sub_cancel, (Rb.A.chart j).left_inv hx'.1] at hc
    rw [baseGram, gramFn_eq hc (hint _ hm) (hgr _ hx'.2).1]
    exact (hgr _ hx'.2).2
  set σ : KA l →+* ℂ := τ₀.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨ρ, B, Pi, Γ, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
      family_period hG.1.2.2.1 tie hpq hF p τ₀ hs hhol hτ hint hg0
    exact fin ρ B (Pi τ) (Γ τ) h1 h2 h3 h4 h5 (h6 τ) (h7 τ)
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (_root_.GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj 𝔐.X M.Ω 𝔐.ξ _ _ M.x _ 0).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all n _ _ p'
      Metric.isOpen_ball (diffOn_star' hw)
      fun u hu => (_root_.GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj 𝔐.X M.Ω 𝔐.ξ _ _ M.x _ _).2 (hp _ (star_mem_ball' hu)).2.1
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ₀).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ₀.comp (algebraMap (𝓞 c.F) c.F)))
        (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_ball' hu)
    have hs' : (((starRingEnd ℂ).comp τ₀).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hg0' : M.GoodAt F (ptIdeal 𝔐.ξ M.x ⟨centre (p' 0), 𝔐.all _⟩) := by
      have e : (⟨centre (p' 0), 𝔐.all _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), 𝔐.all _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hg0
    obtain ⟨ρ, B, Pi, Γ, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
      family_period hG.1.2.2.1 tie hpq hF p' _ hs' hhol' hτ' hint' hg0'
    refine fin ρ (star ⁻¹' B) (fun u => (Pi τ (star u)).map (starRingEnd ℂ))
      (fun u => (Γ τ (star u)).map (starRingEnd ℂ)) h1 h2 (h3.preimage continuous_star) (by simpa using h4)
      (fun u hu => by simpa using star_mem_ball' (h5 hu)) (fun a b u hu => ?_) fun u hu => ⟨?_, ?_⟩
    · have := ((h6 τ a b).differentiableAt (h3.mem_nhds hu)).star_star
      rw [star_star] at this
      exact this.differentiableWithinAt
    · have := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ _ _ _ (h7 τ _ hu).1
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ : ℂ) • star u) = p ((ρ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this
    · rw [blockG_conj]
      exact periodGram_conj (h7 τ _ hu).2
end

