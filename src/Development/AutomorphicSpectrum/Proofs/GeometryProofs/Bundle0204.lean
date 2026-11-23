module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0041
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0171
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0029

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionsFlatAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

theorem exchange {F W : Type} [Field F] [AddCommGroup W] [Module F W] {n : ℕ} {t u : Fin n → W}
    (ht : LinearIndependent F t) (h : Submodule.span F (Set.range t) = Submodule.span F (Set.range u)) :
    LinearIndependent F u ∧ ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, t i = ∑ k, A i k • u k) ∧ IsUnit A.det := by
  have hu : LinearIndependent F u := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have := linearIndependent_iff_card_eq_finrank_span.1 ht
    rw [Set.finrank, ← h]
    exact this
  refine ⟨hu, ?_⟩
  have h1 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • u k = t i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • t k = u i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose A hA using h1
  choose B hB using h2
  have hAB : (Matrix.of A) * (Matrix.of B) = 1 := by
    ext i l
    have key : ∑ m, ((Matrix.of A * Matrix.of B) i m - (1 : Matrix (Fin n) (Fin n) F) i m) • t m = 0 := by
      have e1 : ∑ m, (Matrix.of A * Matrix.of B) i m • t m = t i := by
        conv_rhs => rw [← hA i]
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, ← hB, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      have e2 : ∑ m, (1 : Matrix (Fin n) (Fin n) F) i m • t m = t i := by
        simp [Matrix.one_apply]
      simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]
    have := Fintype.linearIndependent_iff.1 ht _ key l
    exact sub_eq_zero.1 this
  refine ⟨Matrix.of A, fun i => (hA i).symm, ?_⟩
  have := congrArg Matrix.det hAB
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_value_frame (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U)
    (hβ : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (τ : E →+* ℂ) (F : Type) [Field F]
    (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap βF)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (n : ℕ) (b : Fin n → Z.V)
    (hb : (Z.eig τ).IsFrameAt b ⟨centre (y ≫ Y.j), h⟩) (v : Vecs y n)
    (hv : IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v) :
    ∃ (v₀ : Vecs y n) (A : Matrix (Fin n) (Fin n) F),
      IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v₀ ∧
      (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b i) v' ∧ SameVec Y y (v₀ i) v') ∧
      (∀ i, IsComb (A i) v₀ (v i)) ∧ IsUnit A.det := by
  obtain ⟨W, _, _, Mu, Mz, ρ, hu, hz, hS⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieTransport.main E H D l Xo c O β Y F y
  obtain ⟨m, e, cf, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector E c.F (tauIn c τ)
  obtain ⟨u, hval, hspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ValueSpan.value_span Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M F (y ≫ Y.j) h W Mz (𝓞 E) Y.t.act Z.ρ ρ c.F Z.inc βF
    (tauIn c τ) m e cf n b Z.gen Y.t.semi.smooth Z.act hz (_root_.GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc E H D l Xo c O β Y U Z F βF y hβ hy h) h1
    (h2 Z.Ω Z.V Z.inc Z.ρ) hb
  choose t ht using fun i => Mu.onto _ (hv.1 i).1
  have hvt : v = fun i => Mu.pt (t i) := funext fun i => (ht i).symm
  subst hvt
  obtain ⟨hti, hts⟩ := (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ t).1 hv
  obtain ⟨hui, A, hA, hAu⟩ := exchange hti (hts.trans hspan.symm)
  refine ⟨fun i => Mu.pt (u i), A, (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ u).2 ⟨hui, hspan⟩,
    fun i => ⟨Mz.pt (u i), hval i, hS (u i)⟩, fun i => (Test.isComb_iff Mu (A i) u (t i)).2 (hA i), hAu⟩

theorem valAt_mul {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, hu, rfl⟩ := ha
  obtain ⟨_, w, hw, rfl⟩ := hb
  exact ⟨h, u * w, by rw [map_mul, hu, hw], map_mul _ _ _⟩

theorem valAt_eq {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

theorem exists_eq_smul_wedge {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ V} {x : Cpt ξ} {p : ℕ} {f : Fin p → V}
    (hf : L.IsFrameAt f x) {α : Ω} {a : ⋀[Ω]^p V} (hα : α ≠ 0)
    (hL : L.wedge p x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ g₀ : Ω, a = g₀ • exteriorPower.ιMulti Ω p f := by
  have hmem : exteriorPower.ιMulti Ω p f ∈ L.wedge p x :=
    Submodule.subset_span ⟨f, fun i => by
      rw [hf.2]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [hL] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
  have hr' : ((r : Ω) * α) • a = exteriorPower.ιMulti Ω p f := by
    rw [mul_smul]; exact hr
  have hne := WedgeFrame.wedge_ne_zero f hf.1
  have h0 : (r : Ω) * α ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hr'; exact hne hr'.symm
  exact ⟨((r : Ω) * α)⁻¹, by rw [← hr', smul_smul, inv_mul_cancel₀ h0, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

namespace GlobalTheory.CompanionTheory.Ar.Flat

open RepScalar

theorem exists_const_of_flatOnModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ φ φ' hβ hτ hg hl hfl hl' hfl'
  obtain ⟨-, a, b, hgen, hrep⟩ := hfl
  obtain ⟨-, a', b', hgen', hrep'⟩ := hfl'
  obtain ⟨x, s, t, hx, ht, hst, ha', hb'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ConstRatio.const_ratio E H D l Xo c O β Y U Z τ a a' b b' hβ hg hgen hgen'
  refine ⟨x, hx, fun F _ βF y v w hf => ?_⟩
  obtain ⟨hy, hU, hv, hw⟩ := id hf
  have hpt : y (IsLocalRing.closedPoint F) ∈ U := hU ⟨_, rfl⟩
  have hsp : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := ((Z.closure _).1 hpt).map Y.j.continuous
  have hmem : (⟨centre (y ≫ Y.j), hsp⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩
  obtain ⟨h1, h2, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨U₁, hU₁, b₁, -, hb₁⟩ := h1 _ hmem
  obtain ⟨U₂, hU₂, b₂, -, hb₂⟩ := h2 _ hmem
  have f₁ := hb₁ _ hmem hU₁
  have f₂ := hb₂ _ hmem hU₂
  obtain ⟨v₀, A, hv₀, hval₁, hA, hAu⟩ := exists_value_frame Y U Z hβ.2.2 τ F βF y hy hsp D.p b₁ f₁ v hv
  obtain ⟨w₀, B, hw₀, hval₂, hB, -⟩ := exists_value_frame Y U Z hβ.2.2 (ComplexEmbedding.conjugate τ) F βF y hy hsp D.q b₂ f₂ w hw
  have hf₀ : IsFramed U τ βF y v₀ w₀ := ⟨hy, hU, hv₀, hw₀⟩
  obtain ⟨-, hb0, hco⟩ := hgen
  obtain ⟨α, κ, hα, hκ, hWa, hWb, -⟩ := hco _ hmem
  obtain ⟨ga, hga⟩ := exists_eq_smul_wedge f₁ hα hWa
  obtain ⟨gb, hgb⟩ := exists_eq_smul_wedge f₂ hκ hWb
  have hgb0 : gb ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hgb, zero_smul])
  have r1 := hrep F βF y v₀ w₀ b₁ b₂ ga gb hf₀ hga hgb hval₁ hval₂
  have r2 := hrep' F βF y v₀ w₀ b₁ b₂ (s * ga) (t * gb) hf₀ (by rw [ha', hga, smul_smul])
    (by rw [hb', hgb, smul_smul]) hval₁ hval₂
  have r3 := valAt_mul (_root_.GlobalTheory.CompanionTheory.Ar.Flat.ConstVal.valAt_inc E H D l Xo c O β Y U Z F βF y hβ.2.2 hy hsp x) r1
  have e : s * ga / (t * gb) = Z.inc x * (ga / gb) := by
    rw [hst]; field_simp
  rw [e] at r2
  have e2 : φ' F y v₀ w₀ = βF x * φ F y v₀ w₀ := valAt_eq Z.gen r2 r3
  have c1 := hl.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  have c2 := hl'.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  refine hAu.mul_left_injective ?_
  show φ' F y v w * A.det = βF x * φ F y v w * A.det
  rw [c2, e2, _root_.mul_assoc (βF x), _root_.mul_assoc (βF x), c1]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeUniq

open GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A']

theorem isDiff_comp {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (f : A' ⟶ A) (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u'.ex z ≫ f) {a' : Fin g' → ℂ} {x' : epsR ℂ ⟶ A'} (ht : IsTangent x')
    (hd : u'.IsDiff a' x') : u.IsDiff (F a') (x' ≫ f) := by
  obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F a')
  have a1 := isDerivAt0_comp_linMap (isHolTo_ex u) F (isDerivAt0_of_isDiff u h₁ h₂)
  have a2 := GlobalTheory.FibreDeriv.isDerivAt0_comp (isDerivAt0_of_isDiff u' ht hd) f.left
  rw [show (fun z => (u.ex (F z)).left) = fun z => (u'.ex z).left ≫ f.left from
    funext fun z => by rw [hF, Over.comp_left]] at a1
  have e : t = x' ≫ f := Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique a1 a2)
  exact e ▸ h₂

theorem tangent_of_iso (e : A' ≅ A) [IsMonHom e.hom] {x : epsR ℂ ⟶ A} {x' : epsR ℂ ⟶ A'} (hx : IsTangent x)
    (h : x' ≫ e.hom = x) : IsTangent x' := by
  have h' : x' = x ≫ e.inv := by rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have h₁ : η[A'] ≫ e.hom = η[A] := IsMonHom.one_hom e.hom
  have h₂ : η[A] ≫ e.inv = η[A'] := by rw [← h₁, Category.assoc, e.hom_inv_id, Category.comp_id]
  unfold IsTangent at hx ⊢
  rw [h', Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, h₂]

theorem hermForm_eq_of_pullbacks : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G.left) (g g' : ℕ) (u : HolUnif A (L.pull φ) g) (u' : HolUnif A' (L.pull φ') g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), L.IsLB → IsAbelianScheme A → IsGrpPullback A G z φ → IsGrpPullback A' G z φ' → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (x y : epsR ℂ ⟶ A) (x' y' : epsR ℂ ⟶ A') (a b : Fin g → ℂ) (a' b' : Fin g' → ℂ), IsTangent x → IsTangent y → x'.left ≫ φ' = x.left ≫ φ → y'.left ≫ φ' = y.left ≫ φ → u.IsDiff a x → u.IsDiff b y → u'.IsDiff a' x' → u'.IsDiff b' y' → hermForm Hm' a' b' = hermForm Hm a b := by
  intro X G _ L z A A' _ _ φ φ' g g' u u' Hm Hm' χ χ' hL hAb hp hp' d₁ d₂ hAH hAH' x y x' y' a b a' b' hx hy hxx hyy
    da db da' db'
  obtain ⟨e, hmon, he⟩ := grpPullback_iso hp' hp
  haveI := hmon
  have hol : IsHolTo (Set.univ : Set (Fin g' → ℂ)) (fun w => (u'.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u') e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hAb (L.pull φ) g g' u d₁ d₂
    (fun w => u'.ex w ≫ e.hom) (fun p q => by rw [u'.ex_add, MonObj.mul_comp]) hol
  have hΛ : ∀ l ∈ u'.Λ, F l ∈ u.Λ := fun l hl => (u.ker _).1 (by
    rw [hF, (u'.ker l).2 hl, MonObj.one_comp])
  have iso : LBIso (lbPow (L.pull φ') 1) (lbPow ((L.pull φ).pull e.hom.left) 1) :=
    GlobalTheory.lbIso_lbPow (GlobalTheory.GenSpread.lbIso_pull_pull hL e.hom.left he.symm) 1
  have hH := (GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull A' A (L.pull φ') (L.pull φ) g' g u' u Hm' Hm χ' χ e.hom F hΛ 1
    one_pos (pull_isLB hL φ') (pull_isLB hL φ) hAH' hAH hF iso).1
  have coord : ∀ (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A') (c : Fin g → ℂ) (c' : Fin g' → ℂ), IsTangent v →
      v'.left ≫ φ' = v.left ≫ φ → u.IsDiff c v → u'.IsDiff c' v' → F c' = c := fun v v' c c' hv hvv dc dc' => by
    have h : v' ≫ e.hom = v := Over.OverMorphism.ext (hp.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, he, hvv]) (by rw [Over.w, Over.w]))
    have ht := tangent_of_iso e hv h
    exact (d₁ v hv).unique (h ▸ isDiff_comp u u' d₂ e.hom F hF ht dc') dc
  rw [hH, coord x x' a a' hx hxx da da', coord y y' b b' hy hyy db db']

end GlobalTheory.CompanionTheory.Ar.HodgeUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyProductDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo.GBack

variable {K : Type} [Field K] [NumberField K]

theorem exists_prodFam (B : Out.PolAV (Sp (𝓞 K))) : ∀ (n : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))),
    ∃ (Q : Out.PolAV (Sp (𝓞 K))) (a : ∀ k, Q.A ⟶ (C k).A), (∀ k, IsMonHom (a k)) ∧ Q.g = ∑ k, (C k).g ∧
      (∀ (T : Over (Sp (𝓞 K))) (x : ∀ k, T ⟶ (C k).A), ∃ z : T ⟶ Q.A, ∀ k, z ≫ a k = x k) ∧
      ∀ (T : Over (Sp (𝓞 K))) (z z' : T ⟶ Q.A), (∀ k, z ≫ a k = z' ≫ a k) → z = z' := by
  intro n
  induction n with
  | zero =>
    intro C
    obtain ⟨P, pP, hP⟩ := _root_.GlobalTheory.CM.exists_polAV_isPowGrp (𝓞 K) B 0
    refine ⟨P, fun k => Fin.elim0 k, fun k => Fin.elim0 k, by simp [hP], fun T x => ?_, fun T z z' _ => ?_⟩
    · exact ⟨pP.lim.lift (Fan.mk T fun i => Fin.elim0 i), fun k => Fin.elim0 k⟩
    · exact pP.lim.hom_ext fun j => Fin.elim0 j.as
  | succ n ih =>
    intro C
    obtain ⟨Q', a', ha', hg', hex', hext'⟩ := ih fun k => C k.succ
    obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := _root_.GlobalTheory.PolProd.exists_prod_polAV GlobalTheory.CMClaims.laws (𝓞 K) (C 0) Q'
    refine ⟨Q, Fin.cases u fun j => v ≫ a' j, fun k => ?_, ?_, fun T x => ?_, fun T z z' h => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) k
      · exact hu
      · haveI := hv; haveI := ha' j; show IsMonHom (v ≫ a' j); infer_instance
    · rw [hQ, hg', Fin.sum_univ_succ]
    · obtain ⟨z', hz'⟩ := hex' T fun j => x j.succ
      have e1 : inv (lift u v) ≫ u = fst _ _ := by rw [IsIso.inv_comp_eq, lift_fst]
      have e2 : inv (lift u v) ≫ v = snd _ _ := by rw [IsIso.inv_comp_eq, lift_snd]
      refine ⟨lift (x 0) z' ≫ inv (lift u v), fun k => Fin.cases ?_ (fun j => ?_) k⟩
      · show (lift (x 0) z' ≫ inv (lift u v)) ≫ u = x 0
        rw [Category.assoc, e1, lift_fst]
      · show (lift (x 0) z' ≫ inv (lift u v)) ≫ v ≫ a' j = x j.succ
        rw [Category.assoc, reassoc_of% e2, lift_snd_assoc, hz']
    · rw [← cancel_mono (lift u v)]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [Category.assoc, lift_fst]
        exact h 0
      · simp only [Category.assoc, lift_snd]
        exact hext' T _ _ fun j => by
          have := h j.succ
          simp only [Fin.cases_succ] at this
          simpa only [Category.assoc] using this

theorem isMonHom_pow {G H : Over (Sp (𝓞 K))} [GrpObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] (N : ℕ) :
    IsMonHom (f ^ N) :=
  GlobalTheory.LamF.IsogSum.isMonHom_of_points _ fun T x y => by
    rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_pow, MonObj.mul_comp, mul_pow]

end GlobalTheory.CompanionTheory.Ggeo.GBack

open GlobalTheory.CompanionTheory.Ggeo.GBack in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n N : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))) (B : Out.PolAV (Sp (𝓞 K))) (ψ : ∀ k, (C k).A ⟶ B.A), (∀ k, IsMonHom (ψ k)) → 0 < N → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, y = (List.ofFn fun k => x k ≫ ψ k).prod) → (∀ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, (List.ofFn fun k => x k ≫ ψ k).prod = 1 → ∀ k, x k ^ N = 1) → ∃ χ : ∀ k, B.A ⟶ (C k).A, (∀ k, IsMonHom (χ k)) ∧ (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) ∧ ∀ k k', k ≠ k' → ψ k ≫ χ k' = 1 := by
  intro K _ _ σ n N C B ψ hψ hN hon hker
  have hNo : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  obtain ⟨Q, a, ha, hQg, hex, hext⟩ := exists_prodFam B n C
  have := B.isAb.comm
  have := Q.isAb.comm
  have hCc : ∀ k, IsCommMonObj (C k).A := fun k => (C k).isAb.comm
  let Φ : Q.A ⟶ B.A := ∏ k, a k ≫ ψ k
  have hΦ : ∀ {T : Over (Sp (𝓞 K))} (x : T ⟶ Q.A), x ≫ Φ = ∏ k, (x ≫ a k) ≫ ψ k := by
    intro T x
    simp only [Φ, GlobalTheory.LamF.IsogSum.comp_prod, Category.assoc]
  have hm : IsMonHom Φ := GlobalTheory.LamF.IsogSum.isMonHom_of_points Φ fun T x y => by
    simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
  let t : Sp ℂ ⟶ Sp (𝓞 K) := spMap (σ.comp (algebraMap (𝓞 K) K))
  have onto : ∀ y : Over.mk t ⟶ B.A, ∃ z : Over.mk t ⟶ Q.A, y = z ≫ Φ := by
    intro y
    obtain ⟨x, hx⟩ := hon y
    obtain ⟨z, hz⟩ := hex _ x
    refine ⟨z, ?_⟩
    rw [hΦ, hx, List.prod_ofFn]
    simp only [hz]
  have kerN : ∀ z : Over.mk t ⟶ Q.A, z ≫ Φ = 1 → z ^ N = 1 := by
    intro z hz
    have h1 := hker (fun k => z ≫ a k) (by rw [List.prod_ofFn, ← hΦ]; exact hz)
    apply hext
    intro k
    rw [MonObj.pow_comp, h1 k, MonObj.one_comp]
  have hg : Q.g = B.g := by
    let F : (Over.mk t ⟶ Q.A) →* (Over.mk t ⟶ B.A) := MonoidHom.mk' (· ≫ Φ) fun x y => MonObj.mul_comp x y Φ
    obtain ⟨m, hmN⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have e := GlobalTheory.CMClaims.card_torsion_eq F (fun y => (onto y).imp fun _ h => h.symm) m
      (fun x hx => hmN ▸ kerN x hx)
    have h0 : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
    rw [(GlobalTheory.CMClaims.laws.mulN _ Q (m + 2) (by omega)).2.2.2.2 ℂ t h0,
      (GlobalTheory.CMClaims.laws.mulN _ B (m + 2) (by omega)).2.2.2.2 ℂ t h0] at e
    have := Nat.pow_right_injective (by omega : 2 ≤ m + 2) e
    omega
  obtain ⟨N₀, ψ₀, hN₀, hψ₀, h1, h2⟩ := GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers GlobalTheory.thetaUnifAV_all
    GlobalTheory.CMClaims.laws GlobalTheory.CMClaims.homExt K σ Q B Φ hg hm onto
  have divQ : ∀ q : Over.mk t ⟶ Q.A, ∃ q', q = q' ≫ (𝟙 Q.A ^ N₀) := by
    intro q
    have := (GlobalTheory.CMClaims.laws.mulN _ Q N₀ hN₀).1
    have := (GlobalTheory.CMClaims.laws.mulN _ Q N₀ hN₀).2.2.1
    exact GlobalTheory.CMClaims.onto_points (𝟙 Q.A ^ N₀) t q
  have cancel : ∀ (Z : Out.PolAV (Sp (𝓞 K))) (X Y : Q.A ⟶ Z.A), (𝟙 Q.A ^ N₀) ≫ X = (𝟙 Q.A ^ N₀) ≫ Y → X = Y := by
    intro Z X Y h
    have := Q.isAb.smooth
    have := Z.isAb.proper
    refine GlobalTheory.CMPointCompare.hom_ext_of_complexPoints (σ.comp (algebraMap (𝓞 K) K))
      (σ.injective.comp (IsFractionRing.injective (𝓞 K) K)) fun q => ?_
    obtain ⟨q', rfl⟩ := divQ q
    rw [Category.assoc, Category.assoc, h]
  have hf : ∀ k, IsMonHom ((ψ₀ ≫ a k) ^ N) := fun k => by
    have := ha k
    exact isMonHom_pow (ψ₀ ≫ a k) N
  have kill : ∀ k (b : Over.mk t ⟶ B.A), b ^ N₀ = 1 → b ≫ (ψ₀ ≫ a k) ^ N = 1 := by
    intro k b hb
    obtain ⟨z, rfl⟩ := onto b
    have e1 : (z ^ N₀) ≫ Φ = 1 := by rw [MonObj.pow_comp, hb]
    have e2 := kerN _ e1
    rw [MonObj.comp_pow]
    simp only [Category.assoc]
    rw [reassoc_of% h1, ← Category.assoc, MonObj.comp_pow, Category.comp_id, ← MonObj.pow_comp, e2, MonObj.one_comp]
  choose χ hχ hχe using fun k => _root_.PositivityTheory.Xgf.exists_nth_root_homomorphism K σ N₀ B (C k) ((ψ₀ ≫ a k) ^ N) (hf k) hN₀ (kill k)
  have key : ∀ k, Φ ≫ χ k = a k ^ N := by
    intro k
    apply cancel (C k)
    have := hχ k
    rw [← h1, Category.assoc, ← Category.assoc ψ₀, h2, MonObj.pow_comp, Category.id_comp, hχe k, MonObj.comp_pow,
      ← Category.assoc, h1, MonObj.comp_pow]
  refine ⟨χ, hχ, ?_⟩
  have inc : ∀ k, ∃ z : (C k).A ⟶ Q.A, ∀ j, z ≫ a j = if h : k = j then eqToHom (by rw [h]) else 1 :=
    fun k => hex _ fun j => if h : k = j then eqToHom (by rw [h]) else 1
  choose inc hinc using inc
  have hincPhi : ∀ k, inc k ≫ Φ = ψ k := by
    intro k
    rw [hΦ, Finset.prod_eq_single k]
    · rw [hinc, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    · intro j _ hj
      rw [hinc, dite_eq_right (Ne.symm hj), MonObj.one_comp]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hψχ : ∀ k k', ψ k ≫ χ k' = (inc k ≫ a k') ^ N := by
    intro k k'
    rw [← hincPhi, Category.assoc, key, MonObj.comp_pow]
  refine ⟨fun k => ?_, fun k k' hk => ?_⟩
  · rw [hψχ, hinc, dite_eq_left rfl, eqToHom_refl]
  · rw [hψχ, hinc, dite_eq_right hk, one_pow]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalGoodReductionExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TrivialModel

theorem exists_model_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) :=
  @PositivityTheory.Xgn.trivial_type_good_reduction

end GlobalTheory.CompanionTheory.Ar.TrivialModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalLieMultiplicityType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem obj_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t :=
  @PositivityTheory.Xgn.model_object_sections

end GlobalTheory.CompanionTheory.Ar.SabModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoDatumExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem datum_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] (t : SAB H (Sp L)), IsPrincipal t → ∀ (σ : L →+* ℂ) (p q : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult t.act (spMap σ) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult t.act (spMap σ) τ q)) → ∃ D : Datum H, D.p = p ∧ D.q = q ∧ Nonempty (TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :=
  @PositivityTheory.Xgn.shimura_datum_tate_isomorphism

end GlobalTheory.CompanionTheory.Ar.SabModel
end

