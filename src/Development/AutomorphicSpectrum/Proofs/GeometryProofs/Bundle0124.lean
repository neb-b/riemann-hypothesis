module

public import Mathlib
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompare
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem torus_stratum_cocharacters_compare : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  exact @PositivityTheory.Xgn.torus_uniformization_compare

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI6OfReference
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.UpperTower

theorem proj_inl_mem {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω] (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L} (hz : z ∈ ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    (fun p => z (joinInl ι₁ ι₂ p)) ∈ ptsOver L (mCoordIdeal y₁) := by
  refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
  have key : ∀ g : MRing ι₁, mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) g) =
      rename (Sum.inl : K₁ → K₁ ⊕ K₂) (mConeMap y₁ g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X]
      rfl
  have hmem : rename (joinInl ι₁ ι₂) f ∈ mCoordIdeal (joinVec y₁ y₂) := by
    have hf' : mConeMap y₁ f = 0 := hf
    change mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) f) = 0
    rw [key, hf', map_zero]
  have h := hz.2 _ hmem
  rw [aeval_rename] at h
  exact h

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem weightAbsEntrySum_nonneg (mu : Wt Ψ N) : 0 ≤ l1 mu :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_le_card_mul_norm (mu : Wt Ψ N) (h : ‖mu‖ ≤ 2) : l1 mu ≤ (Fintype.card Ψ : ℝ) * (N * 2) := by
  have h1 : ∀ τ i, |mu τ i| ≤ 2 := fun τ i =>
    ((norm_le_pi_norm (mu τ) i).trans (norm_le_pi_norm mu τ)).trans h
  calc l1 mu ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => h1 τ i
    _ = _ := by simp

theorem rootHt_le (R : RootModel Ψ N) (t : ℝ) (mu : Wt Ψ N) (s D : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, R.ι k) → L) (hw : ∀ j, |lineHt (R.line t j) L w| ≤ D) :
    rootHt R t mu s L w ≤ (l1 mu + |s|) * D := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hw none)
  have h1 : ∀ j, R.coef mu s j * lineHt (R.line t j) L w ≤ |R.coef mu s j| * D := fun j =>
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _))
  refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hD
  rw [Fintype.sum_option, add_comm]
  refine add_le_add (le_of_eq ?_) ?_
  · simp [RootModel.coef, l1, Fintype.sum_prod_type]
  · have hk : (1 : ℝ) ≤ R.kA := by exact_mod_cast R.kA_pos
    simp only [RootModel.coef, abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg _) hk

theorem line_smooth (R : RootModel Ψ N) (t : ℝ) : ∀ j, IsSmoothHerm (R.line t j)
  | some r => R.x_smooth t r
  | none => R.A_smooth

theorem tower_upper : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
    (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → T.I6 II := by
  intro Ψ _ _ N T II R hII href c₀ hc₀
  obtain ⟨C, s₀, hs₀, href⟩ := href
  obtain ⟨θ₁, hθ₁, hθ₁1, hwt⟩ := _root_.GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant Ψ N T.j T.nu c₀ T.j_pos T.j_lt hc₀
  choose D hD using fun c : T.Comp =>
    _root_.GlobalTheory.CompanionTheory.Ar.Dense0.dense_bounded_lines (R c).K (R c).ι (R c).P _ (R c).arith _ ((R c).line 1) (line_smooth (R c) 1)
  set D' : ℝ := ∑ c, |D c| with hD'
  have hDle : ∀ c, D c ≤ D' := fun c =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun c => |D c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
  have hD'0 : 0 ≤ D' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set Λ : ℝ := (Fintype.card Ψ : ℝ) * (N * 2) + 1 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨min θ₁ s₀, lt_min hθ₁ hs₀, 2 * (Λ * D' + |C|) + Λ * |C|, ?_⟩
  intro B hB c lam θ s _ hlam hθ hθle hs hgap hcg
  have hθ1 : θ ≤ θ₁ := hθle.trans (min_le_left _ _)
  have hθs : θ ≤ s₀ := hθle.trans (min_le_right _ _)
  have hsθ : (s : ℝ) ≤ θ := by rw [hs]; nlinarith
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  obtain ⟨hdom, hnorm, -⟩ := hwt lam θ hlam hθ hθ1 hgap hcg
  rw [← hs] at hdom hnorm
  obtain ⟨i, u, hclose, harch⟩ := href B hB c
  have harch' := harch (T.lamS lam s) s hdom hnorm hs0 (hsθ.trans hθs)
  have hl : l1 (T.lamS lam s) + |(s : ℝ)| ≤ Λ := by
    rw [abs_of_pos hs0]
    exact add_le_add (l1_le_card_mul_norm _ hnorm) (by linarith)
  have hl0 : 0 ≤ l1 (T.lamS lam s) + |(s : ℝ)| := add_nonneg (weightAbsEntrySum_nonneg _) (abs_nonneg _)
  have hlog : 1 ≤ 2 * Real.log B := by
    have h2 : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
    have := Real.log_two_gt_d9
    linarith
  refine ⟨{W | (T.M B c).IsPt W ∧ T.mbarHt II B c lam s W ≤ (2 * (Λ * D' + |C|) + Λ * |C|) * Real.log B}, ?_,
    fun W hW => hW⟩
  intro f hf hfP
  obtain ⟨L, _, _, L', _, _, e, w, z, hz, hw, hQ, hze, hfz⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense Ψ N (T.M B c) (R c) i
      (fun L _ w => ∀ _ : NumberField L, ∀ j, |lineHt ((R c).line 1 j) L w| ≤ D c)
      (fun g hg hgP => by
        obtain ⟨L, _, _, w, hw, hgw, hb⟩ := hD c g hg hgP
        exact ⟨L, inferInstance, inferInstance, w, hw, hgw, fun _ => hb⟩) f hf hfP
  have hz₁ : (fun p => z (joinInl (T.M B c).ι (R c).ι p)) ∈ ptsOver L' (T.M B c).P := proj_inl_mem _ _ hz
  obtain ⟨hA, hle, hmem, hht⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height _ _ II hII _ _ (T.M B c).arith L' _ hz₁
  refine ⟨mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p), ⟨⟨hA, hle⟩, ?_⟩, fun h => hfz ((hmem f hf).1 h)⟩
  have e1 : T.mbarHt II B c lam s (mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p)) =
      rootHt (T.M B c) (scale s) (T.lamS lam s) s L' (fun p => z (joinInl (T.M B c).ι (R c).ι p)) := by
    simp only [RootTower.mbarHt, RootModel.ht, rootHt, Finset.sum_div, mul_div_assoc]
    exact Finset.sum_congr rfl fun j _ => by rw [hht _ (line_smooth _ _ j)]
  have hcl := (GlobalTheory.T.root_height_difference_bound Ψ N (T.M B c) (R c) i u _ _ _ _ _ _ hclose harch' L' z hz).2
  have hR : rootHt (R c) 1 (T.lamS lam s) s L' (fun p => z (joinInr (T.M B c).ι (R c).ι p)) ≤
      (l1 (T.lamS lam s) + |(s : ℝ)|) * D' := by
    refine rootHt_le _ _ _ _ _ _ _ fun j => ?_
    have h := _root_.GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale _ _ ((R c).line 1 j) L L' e w (fun _ => 1) hw.1 (fun _ => one_ne_zero)
    simp only [one_mul] at h
    rw [hze, h]
    exact (hQ inferInstance j).trans (hDle c)
  rw [e1]
  have hlog0 : 0 ≤ Real.log B := by linarith
  have b1 : (l1 (T.lamS lam s) + |(s : ℝ)|) * D' ≤ Λ * D' := mul_le_mul_of_nonneg_right hl hD'0
  have b2 : (l1 (T.lamS lam s) + |(s : ℝ)|) * (C * Real.log B) ≤ Λ * (|C| * Real.log B) :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0) hl0).trans
      (mul_le_mul_of_nonneg_right hl (mul_nonneg (abs_nonneg _) hlog0))
  have b3 : Λ * D' + |C| ≤ (Λ * D' + |C|) * (2 * Real.log B) :=
    le_mul_of_one_le_right (add_nonneg (mul_nonneg hΛ0 hD'0) (abs_nonneg _)) hlog
  have b4 := le_abs_self C
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.UpperTower
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem top_le_iff_centre (y : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ y ⁻¹ᵁ U ↔ centre y ∈ U :=
  ⟨fun h => h trivial, fun h => (Scheme.preimage_eq_top_of_closedPoint_mem y h).ge⟩

theorem val_germ (y : Sp ℂ ⟶ X) (N : X.Opens) (h : centre y ∈ N) (v : Γ(X, N)) :
    (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ N (centre y) h v) = valAt' y N v := by
  have e := congrArg (fun q => q.hom v) (germ_stalkClosedPointTo_eq y N h)
  rw [valAt'_of _ _ ((top_le_iff_centre y N).2 h)]
  simp only [valAt]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

def genV (ξ : Sp Ω ⟶ X) (N : X.Opens) (h : genPt ξ ∈ N) : Γ(X, N) →+* Ω :=
  ((X.presheaf.germ N (genPt ξ) h) ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (N : X.Opens) {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) (h : genPt ξ ∈ N) (v : Γ(X, N)) :
    genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q hN v) = genV ξ N h v := by
  have e := X.presheaf.germ_stalkSpecializes hN hq
  simp only [genMap, genV]
  rw [← e]
  rfl

theorem genPt_mem {N : X.Opens} {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) : genPt ξ ∈ N :=
  hq.mem_open N.isOpen hN

theorem ValAt.of_section {y : Sp ℂ ⟶ X} {N : X.Opens} (hy : centre y ∈ N) (h : genPt ξ ⤳ centre y) {v : Γ(X, N)}
    {a : Ω} (ha : genMap ξ ⟨centre y, h⟩ (X.presheaf.germ N (centre y) hy v) = a) :
    ValAt ξ y a (valAt' y N v) :=
  ⟨h, _, ha, val_germ y N hy v⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem ValAt.unique (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h₁⟩ (hs.trans hs'.symm)]

theorem ValAt.mul {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b r') : ValAt ξ z (a * b) (r * r') := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  exact ⟨h₁, s * s', by rw [map_mul, hs]; congr 1, map_mul _ _ _⟩

theorem ValAt.one {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) :=
  ⟨h, 1, map_one _, map_one _⟩

theorem ValAt.exists_of_mem {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem ValAt.exists_ne_zero (hξ : IsCptGen ξ) {z : Sp ℂ ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ r : ℂ, r ≠ 0 ∧ ValAt ξ z a r := by
  obtain ⟨r, hr⟩ := ValAt.exists_of_mem h ha.2.1
  obtain ⟨r', hr'⟩ := ValAt.exists_of_mem h ha.2.2
  have e := ValAt.unique hξ (ValAt.mul hr hr') (by rw [mul_inv_cancel₀ ha.1]; exact ValAt.one h)
  exact ⟨r, left_ne_zero_of_mul_eq_one e, hr⟩

theorem exists_section {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : a ∈ regAt ξ ⟨q, h⟩) (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨N, hq, v, hv⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  refine ⟨N ⊓ M, ⟨hq, hM⟩, X.presheaf.map (homOfLE inf_le_left).op v, inf_le_right, ?_⟩
  have e : X.presheaf.germ (N ⊓ M) q ⟨hq, hM⟩ (X.presheaf.map (homOfLE inf_le_left).op v) =
      X.presheaf.germ N q hq v := TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact congrArg (genMap ξ ⟨q, h⟩) (e.trans hv)

theorem exists_unit_section (hξ : IsCptGen ξ) {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : unitAt ξ ⟨q, h⟩ a)
    (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ IsUnit v ∧
      genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨N₁, h₁, v, l₁, e₁⟩ := exists_section h ha.2.1 M hM
  obtain ⟨N₂, h₂, w, l₂, e₂⟩ := exists_section h ha.2.2 M hM
  let i₁ : N₁ ⊓ N₂ ⟶ N₁ := homOfLE inf_le_left
  let i₂ : N₁ ⊓ N₂ ⟶ N₂ := homOfLE inf_le_right
  have hq : q ∈ N₁ ⊓ N₂ := ⟨h₁, h₂⟩
  have g₁ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v) = X.presheaf.germ N₁ q h₁ v :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have g₂ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₂.op w) = X.presheaf.germ N₂ q h₂ w :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have one : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v * X.presheaf.map i₂.op w) =
      X.presheaf.germ (N₁ ⊓ N₂) q hq 1 := by
    apply hξ.inj ⟨q, h⟩
    rw [map_mul, g₁, g₂, map_mul, e₁, e₂, mul_inv_cancel₀ ha.1, map_one, map_one]
  obtain ⟨N₃, h₃, j₁, j₂, e₃⟩ := TopCat.Presheaf.germ_eq X.presheaf q hq hq _ _ one
  have hj : j₁ = j₂ := Subsingleton.elim _ _
  subst hj
  refine ⟨N₃, h₃, X.presheaf.map (j₁ ≫ i₁).op v, (leOfHom (j₁ ≫ i₁)).trans l₁, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (X.presheaf.map (j₁ ≫ i₂).op w) ?_
    rw [map_mul, map_one] at e₃
    simpa [op_comp, Functor.map_comp] using e₃
  · rw [TopCat.Presheaf.germ_res_apply, e₁]

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a b : Ω} (ha : Λ.IsGenAt p a) (hb : Λ.IsGenAt p b) :
    unitAt ξ p (b / a) := by
  have h₁ : b ∈ Submodule.span (regAt ξ p) {a} := by
    rw [← ha.2, hb.2]; exact Submodule.mem_span_singleton_self b
  have h₂ : a ∈ Submodule.span (regAt ξ p) {b} := by
    rw [← hb.2, ha.2]; exact Submodule.mem_span_singleton_self a
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h₁
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.1 h₂
  have hc' : (c : Ω) * a = b := hc
  have he' : (e : Ω) * b = a := he
  refine ⟨div_ne_zero hb.1 ha.1, ?_, ?_⟩
  · rw [← hc', mul_div_cancel_right₀ _ ha.1]; exact c.2
  · rw [inv_div, ← he', mul_div_cancel_right₀ _ hb.1]; exact e.2

theorem isGenAt_mul_of_unitAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a u : Ω} (ha : Λ.IsGenAt p a) (hu : unitAt ξ p u) :
    Λ.IsGenAt p (u * a) := by
  refine ⟨mul_ne_zero hu.1 ha.1, ?_⟩
  rw [ha.2]
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, hu.2.2⟩, ?_⟩
    show u⁻¹ * (u * a) = a
    rw [← _root_.mul_assoc, inv_mul_cancel₀ hu.1, _root_.one_mul]
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, hu.2.1⟩, rfl⟩

structure IsChart (s : X ⟶ Sp ℂ) {d : ℕ} (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) : Prop where
  isOpen : IsOpen B
  hol : IsHolTo B Y
  isOver : ∀ b ∈ B, Y b ≫ s = 𝟙 _
  factor : ∀ (m : ℕ) (B' : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B' → IsHolTo B' y →
    (∀ b ∈ B', y b ≫ s = 𝟙 _) → ∀ b₀ ∈ B', ∀ b₁ ∈ B, y b₀ = Y b₁ →
    ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B' ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧
      κ b₀ = b₁ ∧ ∀ b ∈ ball b₀ ε, κ b ∈ B ∧ y b = Y (κ b)

theorem IsChart.mono {s : X ⟶ Sp ℂ} {d : ℕ} {B B₂ : Set (Fin d → ℂ)} {Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)}
    (h : IsChart s B Y) (o : IsOpen B₂) (l : B₂ ⊆ B) : IsChart s B₂ Y := by
  refine { isOpen := o, hol := ?_, isOver := fun b hb => h.isOver b (l hb), factor := ?_ }
  · intro U f
    have e : {b ∈ B₂ | ⊤ ≤ Y b ⁻¹ᵁ U} = B₂ ∩ {b ∈ B | ⊤ ≤ Y b ⁻¹ᵁ U} := by
      ext b; exact ⟨fun hb => ⟨hb.1, l hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
    rw [e]
    exact ⟨o.inter (h.hol U f).1, (h.hol U f).2.mono Set.inter_subset_right⟩
  · intro m B' y oB hy ov b₀ h₀ b₁ h₁ e
    obtain ⟨ε, κ, ε0, sub, dκ, k₀, hκ⟩ := h.factor m B' y oB hy ov b₀ h₀ b₁ (l h₁) e
    have c : ContinuousAt κ b₀ := (dκ.differentiableAt (ball_mem_nhds _ ε0)).continuousAt
    have m₂ : κ ⁻¹' B₂ ∈ 𝓝 b₀ := c.preimage_mem_nhds (o.mem_nhds (k₀ ▸ h₁))
    obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem m₂ (ball_mem_nhds b₀ ε0))
    have sb : ball b₀ δ ⊆ ball b₀ ε := fun b hb => (hδ hb).2
    exact ⟨δ, κ, δ0, sb.trans sub, dκ.mono sb, k₀, fun b hb => ⟨(hδ hb).1, (hκ b (sb hb)).2⟩⟩

structure HChart (s : X ⟶ Sp ℂ) (ξ : Sp Ω ⟶ X) (W U : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T : Ω) {d : ℕ}
    (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) : Prop where
  chart : IsChart s B Y
  inU : ∀ b ∈ B, centre (Y b) ∈ U
  cpt : ∀ b ∈ B, genPt ξ ⤳ centre (Y b)
  dense : ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W
  hol : DifferentiableOn ℂ H B
  ne : ∀ b ∈ B, H b ≠ 0
  rel : ∀ b ∈ B, centre (Y b) ∈ W → ∀ r : ℂ, ValAt ξ (Y b) T r → F (Y b) = H b * r

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueLocallyRegularFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SectionNear

theorem germ_closedPoint {Y : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem fromSpec_appLE_self {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V) :
    hV.fromSpec.appLE V ⊤ h ≫ (Scheme.ΓSpecIso Γ(T, V)).hom = 𝟙 _ := by
  have e : (Spec Γ(T, V)).presheaf.map (eqToHom hV.fromSpec_preimage_self).op ≫
      (Spec Γ(T, V)).presheaf.map (homOfLE h).op = 𝟙 _ := by
    have e₀ : (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [← Functor.map_comp, e₀, CategoryTheory.Functor.map_id]
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    reassoc_of% e]
  simp

theorem spMap_fromSpec_appLE {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (χ : Γ(T, V) →+* ℂ)
    (h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = CommRingCat.ofHom χ := by
  have h₁ : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have n := Scheme.ΓSpecIso_naturality (R := Γ(T, V)) (S := CommRingCat.of ℂ) (CommRingCat.ofHom χ)
  have a : (spMap χ).appLE ⊤ ⊤ le_top = Scheme.Hom.appTop (spMap χ) := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h₁ le_top, a, Category.assoc, n,
    reassoc_of% (fromSpec_appLE_self hV h₁)]

theorem section_near : ∀ (X T : Scheme.{0}) (j : T ⟶ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (y₀ : Sp ℂ ⟶ T) (t : Ω) (r₀ : ℂ), ValAt ξ (y₀ ≫ j) t r₀ → ∃ W₁ : T.Opens, ⊤ ≤ y₀ ⁻¹ᵁ W₁ ∧ ∀ (V : T.Opens) (hV : IsAffineOpen V), V ≤ W₁ → ∃ g : Γ(T, V), ∀ (χ : Γ(T, V) →+* ℂ) (r : ℂ), ValAt ξ ((spMap χ ≫ hV.fromSpec) ≫ j) t r → r = χ g := by
  intro X T j Ω _ ξ hξ y₀ t r₀ h₀
  obtain ⟨h, s, hs, -⟩ := h₀
  obtain ⟨N, hp, G, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s
  have hgen : genPt ξ ∈ N := h.mem_open N.2 hp
  have hgerm : ∀ (p : Cpt ξ) (hp : p.1 ∈ N), genMap ξ p (X.presheaf.germ N p.1 hp G) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ N (genPt ξ) hgen G) := by
    intro p hp
    have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
    have e' : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ N p.1 hp G) =
        X.presheaf.germ N (genPt ξ) hgen G := by
      rw [← e]; rfl
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom e'
  refine ⟨j ⁻¹ᵁ N, ?_, fun V hV hVN => ⟨j.appLE N V hVN G, fun χ r hr => ?_⟩⟩
  · intro x _
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst hx
    exact hp
  · obtain ⟨h', s', hs', rfl⟩ := hr
    have hcV : (spMap χ ≫ hV.fromSpec) (IsLocalRing.closedPoint ℂ) ∈ V := by
      have : hV.fromSpec ((spMap χ) (IsLocalRing.closedPoint ℂ)) ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
      rw [hV.range_fromSpec] at this
      exact this
    have hq : centre ((spMap χ ≫ hV.fromSpec) ≫ j) ∈ N := hVN hcV
    have e : s' = X.presheaf.germ N _ hq G :=
      hξ.inj ⟨_, h'⟩ (hs'.trans ((hs.symm.trans (hgerm ⟨_, h⟩ hp)).trans (hgerm ⟨_, h'⟩ hq).symm))
    subst e
    have e₂ : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hcV).ge
    have k := germ_closedPoint (R := CommRingCat.of ℂ) ((spMap χ ≫ hV.fromSpec) ≫ j) N hq
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge
    have d : ((spMap χ ≫ hV.fromSpec) ≫ j).appLE N ⊤
        (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = j.appLE N V hVN ≫ CommRingCat.ofHom χ := by
      rw [← Scheme.Hom.appLE_comp_appLE (spMap χ ≫ hV.fromSpec) j N V ⊤ hVN e₂, Category.assoc,
        spMap_fromSpec_appLE hV χ e₂]
    exact congrArg (fun φ => φ.hom G) (k.trans d)

end GlobalTheory.CompanionTheory.Ar.SectionNear
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isEigFrame_of_sameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (κ : 𝓞 E →+* F) {n : ℕ}
    (v : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)) (v₀ : Fin n → (epsAt (y ≫ Y.j) ⟶ Y.t.G))
    (hs : ∀ i, SameVec Y y (v i) (v₀ i)) (hf : IsEigFrame Y.t.act (y ≫ Y.j) κ v₀) :
    IsEigFrame Xo.univ.t.act (under y) κ v := by
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  choose u hu₀ hu₁ hu₂ using hs
  let a : Fin n → (epsAt y ⟶ Y.oF.t.G) := fun i => Over.homMk (u i) (hu₀ i)
  have e₀ : (fun i => tanMap hq y (a i)) = v₀ := funext fun i => Over.OverMorphism.ext (hu₂ i)
  have e₁ : (fun i => tanMap hp y (a i)) = v := funext fun i => Over.OverMorphism.ext (hu₁ i)
  have h₁ : IsEigFrame Y.oF.t.act y κ a :=
    (isEigFrame_iff hq Y.oF.t.act Y.t.act Y.m.act y κ a).1 (by rw [e₀]; exact hf)
  have h₂ := (isEigFrame_iff hp Y.oF.t.act Xo.univ.t.act Y.m0.act y κ a).2 h₁
  rw [e₁] at h₂
  exact h₂

theorem isFramed_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ σ y v w v₀ w₀ hy hv hw fv fw
  exact ⟨hy, Set.subset_univ _, isEigFrame_of_sameVec Y y _ v v₀ hv fv, isEigFrame_of_sameVec Y y _ w w₀ hw fw⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

