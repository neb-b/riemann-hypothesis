module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0110
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameGenericRankStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatible
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0102

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsFramePeriodsNoGlobal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.FramePeriods
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem exists_isFramePeriods_noGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∀ (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → (∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord y) cc p → unitAt 𝔐.ξ p f → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb p) → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
  intro E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 a b N bb n Bd χ t₀ cc f hBd ht₀ hfr hdom
  classical
  obtain ⟨a₀, π, ρ₀, ha, hρ₀, hρ₀', hπ, hgeo⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart K J Ω y _ n Bd χ t₀ cc f ht₀ hdom
  have hw : DifferentiableOn ℂ (fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u)) (Metric.ball 0 1) := by
    refine χ.analytic.differentiableOn.comp ?_ fun u hu => (hgeo ρ₀ hρ₀ le_rfl u hu).1
    unfold HodgeMetric.recentre
    exact (differentiable_const _ |>.add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))).differentiableOn
  set w : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u) with hwdef
  have htie := 𝔐.tie
  have hall := 𝔐.all
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧ CoordsAt 𝔐.ξ y z (w u) := fun u hu =>
    (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt 𝔐.X Ω 𝔐.ξ K J y htie (w u)).1 (χ.mem _ (hgeo ρ₀ hρ₀ le_rfl u hu).1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w' : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w' → CoordsAt 𝔐.ξ y z' w' → z = z' := fun z z' w' h h' => by
    obtain ⟨e1, -, e3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.tie_points 𝔐.X Ω 𝔐.ξ K J y htie ℂ
    exact (e1 w' h.1 (e3 z w' (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩

  have fin : ∀ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (ρ₁ : ℝ)
      (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), 0 < ρ₁ → ρ₁ ≤ 1 →
      (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) →
      (∀ u ∈ Flat.punct n a₀ 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w ((ρ₁ : ℂ) • u)) →
        𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (HodgeMetric.periodGram L U u)) →
      ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
    intro g Λ _ L ρ₁ U h1 h2 h3 h4 h5
    have hle : ρ₀ * ρ₁ ≤ ρ₀ := by nlinarith
    have hpos : 0 < ρ₀ * ρ₁ := mul_pos hρ₀ h1
    refine ⟨a₀, g, Λ, inferInstance, L, π, ρ₀ * ρ₁, U, hpos, by nlinarith, h3, h4, hπ, fun u hu => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hgeo _ hpos hle u hu
    refine ⟨g1, g2, g3, fun hup z hz => ?_⟩
    rw [recentre_mul] at hz
    exact h5 u hup z hz
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by simp
  have hfr0 : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p 0), hall _⟩ := by
    have hd := (hgeo ρ₀ hρ₀ le_rfl 0 hb0).2.1
    obtain ⟨c1, c2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain 𝔐.X Ω 𝔐.ξ K J y htie (p 0) (w 0) cc f (hall _) (hp 0 hb0) hd
    exact hfr _ c1 c2
  by_cases hpq : D.p + D.q = 0
  · have hV : ∀ s, 𝔐.Vgen s = ⊥ := fun s => by
      obtain ⟨-, -, b', hb', -⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
      have hr : labelRk D s = 0 := by
        rcases s with s | s <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
      have : IsEmpty (Fin (labelRk D s)) := by rw [hr]; infer_instance
      have e : Set.range b' = ∅ := Set.range_eq_empty b'
      rw [e, Submodule.span_empty] at hb'
      exact hb'.symm
    have hli := hfr0.1
    haveI : Subsingleton ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := by
      rw [hV a, hV b, sup_bot_eq]
      infer_instance
    haveI : IsEmpty (Fin N) := ⟨fun k => hli.ne_zero k (Subsingleton.elim _ _)⟩
    obtain ⟨Λ, _, ⟨L⟩⟩ := zeroPeriods n a₀ ha
    exact fin 0 Λ _ L 1 (fun _ _ => 0) one_pos le_rfl (fun k => isEmptyElim k) linearIndependent_empty_type
      fun u _ z _ => ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  have hpq' : 1 ≤ D.p + D.q := Nat.one_le_iff_ne_zero.2 hpq
  have hhol : IsHolTo (Metric.ball 0 1) p := _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family 𝔐.X Ω 𝔐.ξ K J y htie hall n _ w p Metric.isOpen_ball hw hp
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p u) := fun u hu => by
    have h1 := (hgeo ρ₀ hρ₀ le_rfl u hu.1).2.2
    have h2 := hBd (p u) (w u) (hp u hu.1)
    by_contra h
    exact (h1.2 hu) (h2.2 h)
  set σ : KA l →+* ℂ := τ.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨g, Λ, _, L, ρ₁, U, h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p τ hpq' hs ha hhol hτ hint (hall _) hfr0
    refine fin g Λ _ L ρ₁ U h1 h2 h3 h4 fun u hu z hz => ?_
    rw [huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
    exact h5 u hu
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcoord : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (p' u) (fun q => star (w (star u) q)) := fun u hu =>
      (_root_.GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj 𝔐.X Ω 𝔐.ξ K J y _ _).2 (hp _ (star_mem_ball' hu))
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (_root_.GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj 𝔐.X Ω 𝔐.ξ K J y _ (w 0)).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family 𝔐.X Ω 𝔐.ξ K J y htie hall n _ _ p' Metric.isOpen_ball
      (diffOn_star' hw) hcoord
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_punct' hu)
    have hs' : (((starRingEnd ℂ).comp τ).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hfr0' : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p' 0), hall _⟩ := by
      have e : (⟨centre (p' 0), hall _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), hall _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hfr0
    obtain ⟨g, Λ, _, L', ρ₁, U', h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p' _ hpq' hs' ha hhol' hτ' hint' (hall _) hfr0'
    obtain ⟨L, hL⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram n a₀ g N Λ L' U' (_root_.GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij.T_bijective n a₀ g Λ L')
    refine fin g Λ _ L ρ₁ (fun k u' => star (U' k (star u'))) h1 h2 (fun k => diffOn_star' (h3 k)) ?_ fun u hu z hz => ?_
    · refine Fintype.linearIndependent_iff.2 fun c' hc' k => ?_
      have e := congrArg star hc'
      simp only [star_sum, star_smul, star_star, star_zero] at e
      have := Fintype.linearIndependent_iff.1 h4 (fun k => star (c' k)) (by simpa [star_smul] using e) k
      simpa using this
    · rw [hL u hu, huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
      have := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point E H D l (Xo l) c Y S Ω K J y 𝔐 _ N _ _ (h5 (star u) (star_mem_punct' hu))
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ₁ : ℂ) • star u) = p ((ρ₁ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGiven
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists : GlobalTheory.CompanionTheory.Ar.Top.Given → PB.FlagModelExists := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 nd d bW bO hv hd
  classical
  have hVB := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐
  have hcc := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω (EE 𝔐)), IsTwistGen 𝔐.ξ (seg x₀) (LL 𝔐 s) m φ := fun s =>
    _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) 𝔐.tie 𝔐.all (hVB s)
  choose m n φ hφ using hg
  have hB : ∀ s, ∃ B : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (n s)) Ω, B * aOf 𝔐 bW bO φ s = 1 := fun s =>
    GlobalTheory.T.frame_via_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) (m s) (n s) (φ s) (cc 𝔐 bW bO s) 𝔐.tie (hVB s)
      (hφ s) (hcc s).1 (hcc s).2
  have hF : FormsOK 𝔐 bW bO m φ := ⟨hVB, hcc, hφ, hB⟩
  have hx₀ : ∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0 := by
    obtain ⟨c₀, hc₀⟩ := exists_inBlockChart 𝔐.tie ⟨genPt 𝔐.ξ, specializes_refl _⟩
    exact fun k => ⟨c₀ k, (hc₀ k).1⟩
  have ht := GlobalTheory.T.hodgeCpt_frame_change_determinant E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hP := GlobalTheory.T.blkF_properStep_injective_blockDiag (CMType H) D.p D.q Ω K₀
  have hmod : ModelOK (aOf 𝔐 bW bO φ) x₀ m :=
    ⟨hP.1, hP.2.1, _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne _ _ _ Ω _ _ K₀ J₀ x₀ hx₀ hB,
      GlobalTheory.T.basePart_yv_eq_algebraMap_xb _ _ _ Ω _ _ K₀ J₀ x₀, hP.2.2, GlobalTheory.T.isGenericFlag_gMat _ _ _ Ω, GlobalTheory.T.yv_eq_sum_minors_gMat _ _ _ Ω _ _ K₀ J₀ x₀,
      GlobalTheory.T.hodgeCpt_frame_change_regular E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht⟩
  have hT := GlobalTheory.T.hodgeCpt_frame_minor_valuation E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod
  obtain ⟨Z, ξ', f, htie, hall, hdom, hsm⟩ := GlobalTheory.T.hodgeCpt_frame_leading_term E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hnorm := GlobalTheory.T.hodgeCpt_frame_degree_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF Z ξ' f htie hall hdom hsm
  obtain ⟨𝔐', e, j, -, hov, hR, hsp, hV⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth E H D l Xo c Y S Ω _ (algebraMap Ω _) K₀ _ J₀ _ x₀ _ 𝔐 Z ξ' f hall htie hnorm hdom hsm
  obtain ⟨Fl, hdeg, hfl⟩ := GlobalTheory.T.hodgeCpt_frame_divisor_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ d hF hd 𝔐' _ j hov hsp hV
  obtain ⟨xdeg, hroot, hdy⟩ := GlobalTheory.T.hodgeCpt_frame_height_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod 𝔐' _ j Fl hov hsp hV hfl
  let M := model (aOf 𝔐 bW bO φ) x₀ m hmod
  let 𝔐₁ : HodgeCpt Y S M.x := reTie 𝔐 (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) ht
  let tie : FlagTie M 𝔐₁ :=
    { eW := bW, eO := bO, frameW := fun q F h h' τ => (hT q F h h' τ).1, frameO := fun q F h h' τ => (hT q F h h' τ).2 }
  have hκ : ∀ k : K₀, ∀ r, M.blk r ≠ some (.inl k) := fun k r h => by
    change blkF (CMType H) D.p D.q K₀ r = _ at h
    unfold blkF at h
    split_ifs at h
    simpa using h
  let κ : K₀ → NonPluckerBlocks M.blk := fun k => ⟨.inl k, hκ k⟩
  let v : (Σ k, J₀ k) → Σ k, baseIdx (idx (p := D.p) (q := D.q) J₀ n) M.blk k := fun r => ⟨κ r.1, r.2⟩
  refine ⟨K₀ ⊕ StepIx (CMType H) D.p D.q, inferInstance, idx J₀ n, inferInstance, GenField Ω (rk (CMType H) D.p D.q),
    inferInstance, yv (aOf 𝔐 bW bO φ) x₀, M, 𝔐₁, tie, κ, v, RingHom.id Ω, 𝟙 𝔐.X, AddMonoidHom.id 𝔐.Li, 𝔐', Fl, xdeg,
    fun _ => 1, ⟨?_, fun _ => rfl, Function.bijective_id, inferInstanceAs (IsIso (𝟙 𝔐.X)), ?_, rfl, ?_⟩,
    ⟨hd, GlobalTheory.T.hodgeCpt_frame_order_bound E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF ht hv, GlobalTheory.T.hodgeCpt_frame_generic_rank E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ ht⟩,
    GlobalTheory.T.hodgeCpt_frame_unit_criterion E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF hv, ?_, hdeg⟩
  · refine ⟨fun a b h => Sum.inl_injective (congrArg (fun k => k.1) h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      have h1 : k = k' := Sum.inl_injective (congrArg (fun r => r.1.1) h)
      subst h1
      have h2 : HEq i i' := (Sigma.mk.inj_iff.1 h).2
      rw [eq_of_heq h2]
    · rintro ⟨_, i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
  · exact HodgeOver.refl 𝔐
  · exact BasesOver.refl bW bO
  · refine ⟨⟨e.hom ≫ f, j, hov, hR, hV, hfl.1, hfl.2⟩, hroot, hdy, fun τ i => ?_⟩
    have h1 : detFac D.p i (M.g τ) = 1 := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat (CMType H) D.p D.q Ω τ i
    have h2 : M.lam (τ, i) = 1 := rfl
    rw [h1, h2]
    rcases M.blk (τ, i) with _ | b <;> simp
end
end

