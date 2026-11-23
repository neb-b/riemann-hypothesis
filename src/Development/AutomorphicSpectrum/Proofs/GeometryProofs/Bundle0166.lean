module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PsJetTwistedSeriesOfLeOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0024
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {σ k : Type} [CommRing k] (j : ℕ) (q a : MvPolynomial σ k)
    (ha : ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff a e = 0) :
    ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff (q * a) e = 0 := by
  classical
  intro e he
  rw [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h2 : x.2.degree ≤ e.degree := by
    rw [← hx, map_add (f := _)]; exact Nat.le_add_left _ _
  rw [ha x.2 (lt_of_le_of_lt h2 he), mul_zero]

private theorem coeff_eq_zero_of_mem_span_X_pow_of_degree_lt {σ k : Type} [CommRing k] :
    ∀ (j : ℕ) (P : MvPolynomial σ k), P ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ j →
      ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff P e = 0 := by
  classical
  intro j
  induction j with
  | zero => intro P _ e he; exact absurd he (Nat.not_lt_zero _)
  | succ j ih =>
    let K : Ideal (MvPolynomial σ k) :=
      { carrier := {P | ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff P e = 0}
        add_mem' := fun {a b} ha hb e he => by rw [MvPolynomial.coeff_add, ha e he, hb e he, add_zero]
        zero_mem' := fun e _ => by simp
        smul_mem' := fun c a ha => coeff_mul_eq_zero_of_order_two_of_degree_le_two (j + 1) c a ha }
    have hle : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ (j + 1) ≤ K := by
      rw [pow_succ, Ideal.mul_le]
      intro r hr s hs
      refine Submodule.span_induction (p := fun s _ => r * s ∈ K) ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨i, rfl⟩
        show ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff (r * MvPolynomial.X i) e = 0
        intro e he
        rw [MvPolynomial.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [MvPolynomial.coeff_X']
        split_ifs with hxi
        · have hx1 : x.1.degree + 1 = e.degree := by
            rw [← hx, map_add (f := _), ← hxi, Finsupp.degree_single]
          rw [ih r hr x.1 (by omega), zero_mul]
        · rw [mul_zero]
      · rw [mul_zero]; exact K.zero_mem
      · intro a b _ _ ha hb; rw [mul_add]; exact K.add_mem ha hb
      · intro c a _ ha; rw [smul_eq_mul, mul_left_comm]; exact K.mul_mem_left c ha
    exact fun P hP => hle hP

theorem pderiv_eq_zero_of_jet_pow_sub : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv (R := k) q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv (R := k) q F = 0 := by
  intro k _ p _ _ d F f hf hF q
  classical
  ext e
  obtain ⟨v, hv⟩ := hF (e.degree + 1)
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hmem : psTrunc (e.degree + 1) F + psTrunc (e.degree + 1) f - P ^ p ∈
      orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), map_pow]
    have h1 : psJet (e.degree + 1) F =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) F) := rfl
    have h2 : psJet (e.degree + 1) f =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) f) := rfl
    rw [← h1, ← h2, hv]; ring
  have hdeg : (e + Finsupp.single q 1).degree < e.degree + 1 + 1 := by
    rw [map_add (f := _), Finsupp.degree_single]; omega
  have hz := coeff_eq_zero_of_mem_span_X_pow_of_degree_lt (e.degree + 1 + 1) _ hmem (e + Finsupp.single q 1) hdeg
  have hbd : ∀ i, (e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i ≤ (e + Finsupp.single q 1).degree := by
    intro i
    exact Finsupp.le_degree i _
  have hin : e + Finsupp.single q 1 ∈ degLE (e.degree + 1) := by
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · refine ⟨fun i => ⟨(e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i, ?_⟩, ?_⟩
      · have := hbd i
        rw [map_add (f := _), Finsupp.degree_single] at this
        omega
      · ext i; simp
    · show (e + Finsupp.single q 1).degree ≤ e.degree + 1
      rw [map_add (f := _), Finsupp.degree_single]
  have htr : ∀ g : MvPowerSeries (Fin 1 × Fin d) k,
      AddMonoidAlgebra.coeff (psTrunc (e.degree + 1) g) (e + Finsupp.single q 1) =
        MvPowerSeries.coeff (e + Finsupp.single q 1) g := by
    intro g
    simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hin]
  have hpow : MvPowerSeries.pderiv (R := k) q ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k) = 0 := by
    rw [MvPolynomial.coe_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have hG : MvPowerSeries.pderiv (R := k) q F = MvPowerSeries.pderiv (R := k) q
      (F + f - ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k)) := by
    rw [map_sub, map_add (f := _), hf q, hpow, add_zero, sub_zero]
  rw [hG, MvPowerSeries.coeff_pderiv, map_zero, map_sub, map_add (f := _), MvPolynomial.coeff_coe, ← htr F, ← htr f,
    ← MvPolynomial.coeff_add, ← MvPolynomial.coeff_sub, hz, zero_mul]

end GlobalTheory.CompanionTheory.Ar.Coc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LieTransport

private theorem mul_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact h.2 T x y x₀ y₀ hx hy

private theorem one_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  let o : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ)
    (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have hm : (o * o).left = o.left := by
    rw [mul_left_eq_of_isGrpPullback h T _ rfl 1 1 o o rfl rfl, _root_.mul_one]
    rfl
  have ho : o * o = o := Over.OverMorphism.ext hm
  have ho1 : o = 1 := by
    have := congrArg (· * o⁻¹) ho
    simpa [_root_.mul_assoc] using this
  rw [← ho1]
  rfl

private theorem specMap_fstHom_comp_algebraMap_eq_id (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp

private theorem exists_lieModel_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S') (x' : Spec (CommRingCat.of R) ⟶ S) (hx : x' = x ≫ f)
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) :
    ∃ N : LieModel G x' W, ∀ e, (N.pt e).left = (M.pt e).left ≫ φ := by
  subst hx
  have hw : ∀ e, ((M.pt e).left ≫ φ) ≫ G.hom = (epsAt (x ≫ f)).hom := by
    intro e
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    simp [epsAt]
  let P : W → (epsAt (x ≫ f) ⟶ G) := fun e =>
    Over.homMk (U := epsAt (x ≫ f)) (V := G) ((M.pt e).left ≫ φ) (hw e)
  have hP : ∀ e, (P e).left = (M.pt e).left ≫ φ := fun e => rfl
  have one_eq := one_left_eq_of_isGrpPullback h (Over.mk x) (x ≫ f) rfl
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x ≫ f =
      (epsAt x).hom ≫ f := by simp [epsAt]
  refine ⟨⟨P, ?_, ?_, ?_, ?_, ?_⟩, hP⟩
  · intro e
    have ht := M.tan e
    unfold IsTanAt at ht ⊢
    rw [hP, ← Category.assoc, ht]
    exact one_eq.symm
  · intro e e' hee
    apply M.inj
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · have := congrArg Over.Hom.left hee
      simpa [P] using this
    · rw [Over.w, Over.w]
  · intro v hv
    have hvw : v.left ≫ G.hom = (epsAt x).hom ≫ f := by
      rw [Over.w]; simp [epsAt]
    let v' : epsAt x ⟶ G' := Over.homMk (h.1.lift v.left (epsAt x).hom hvw) (h.1.lift_snd _ _ _)
    have hv' : IsTanAt G' x v' := by
      unfold IsTanAt at hv ⊢
      apply h.1.hom_ext
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_fst]
        rw [hv, one_eq]
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_snd]
        rw [Over.w]
        simp only [epsAt, Over.mk_hom]
        rw [← Category.assoc, specMap_fstHom_comp_algebraMap_eq_id, Category.id_comp]
    obtain ⟨e, he⟩ := M.onto v' hv'
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    show (M.pt e).left ≫ φ = v.left
    rw [he]
    exact h.1.lift_fst _ _ _
  · intro e e'
    apply Over.OverMorphism.ext
    have hm := mul_left_eq_of_isGrpPullback h (epsAt x) _ hg (M.pt e) (M.pt e') (P e) (P e') (hP e) (hP e')
    refine Eq.trans ?_ hm.symm
    rw [hP, M.add]
  · intro c e
    show (M.pt (c • e)).left ≫ φ = _
    rw [M.smul, Category.assoc]
    rfl

private theorem exists_isActOf_geometry {S : Scheme} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {W : Type} [AddCommGroup W] [Module R W]
    (M : LieModel G x W) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ ρ : O →+* Module.End R W, M.IsActOf a.act ρ := by
  have hpt0 : M.pt 0 = 1 := by
    have h0 := M.add 0 0
    rw [add_zero] at h0
    have := congrArg (· * (M.pt 0)⁻¹) h0
    simpa [_root_.mul_assoc] using this.symm
  have tan : ∀ (b : O) (e : W), IsTanAt G x (M.pt e ≫ a.act b) := by
    intro b e
    have ht := M.tan e
    have hh := a.hom b
    unfold IsTanAt at ht ⊢
    rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]
  choose A hA using fun (b : O) (e : W) => M.onto (M.pt e ≫ a.act b) (tan b e)
  have hadd : ∀ b e e', A b (e + e') = A b e + A b e' := by
    intro b e e'
    have hh := a.hom b
    apply M.inj
    rw [hA, M.add, M.add, hA, hA, MonObj.mul_comp]
  have hsmul : ∀ b (c : R) e, A b (c • e) = c • A b e := by
    intro b c e
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hA, Over.comp_left, M.smul, M.smul, hA, Over.comp_left, Category.assoc]
  let L : O → Module.End R W := fun b =>
    { toFun := A b, map_add' := hadd b, map_smul' := fun c e => by simpa using hsmul b c e }
  have hL : ∀ b e, L b e = A b e := fun _ _ => rfl
  have hone : L 1 = 1 := by
    ext e
    apply M.inj
    rw [hL, hA, a.one, Category.comp_id]
    rfl
  have hmul : ∀ b b', L (b * b') = L b * L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [Module.End.mul_apply, hL, hL, hL, hA, hA, hA, mul_comm, a.mul, Category.assoc]
  have haddL : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [LinearMap.add_apply, hL, hL, hL, hA, M.add, hA, hA, a.add, MonObj.comp_mul]
  let ρ : O →+* Module.End R W := RingHom.mk' ⟨⟨L, hone⟩, hmul⟩ haddL
  exact ⟨ρ, fun b e => hA b e⟩

private theorem isActOf_of_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {φ : G'.left ⟶ G.left} {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S'} {x' : Spec (CommRingCat.of R) ⟶ S}
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) (N : LieModel G x' W)
    (hN : ∀ e, (N.pt e).left = (M.pt e).left ≫ φ) {O : Type} [CommRing O]
    (act' : O → (G' ⟶ G')) (act : O → (G ⟶ G))
    (hact : ∀ b, (act' b).left ≫ φ = φ ≫ (act b).left)
    (ρ : O →+* Module.End R W) (hM : M.IsActOf act' ρ) : N.IsActOf act ρ := by
  intro b e
  apply Over.OverMorphism.ext
  have h1 := hM b e
  rw [hN, h1, Over.comp_left, Over.comp_left, hN, Category.assoc, hact, Category.assoc]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (Mu : LieModel Xo.univ.t.G (under y) W) (Mz : LieModel Y.t.G (y ≫ Y.j) W) (ρ : 𝓞 E →+* Module.End F W), Mu.IsActOf Xo.univ.t.act.act ρ ∧ Mz.IsActOf Y.t.act.act ρ ∧ ∀ e, SameVec Y y (Mu.pt e) (Mz.pt e) := by
  intro E _ _ _ H D l Xo c O _ β Y F _ y
  obtain ⟨W, i1, i2, ⟨M0⟩⟩ := lieModel_exists _ Y.oF.t.G F y
  obtain ⟨ρ, hρ⟩ := exists_isActOf_geometry M0 Y.oF.t.act
  obtain ⟨Mu, hMu⟩ := exists_lieModel_pullback Y.m0.toSABMap.cart y (under y) rfl M0
  obtain ⟨Mz, hMz⟩ := exists_lieModel_pullback Y.m.cart y (y ≫ Y.j) rfl M0
  refine ⟨W, i1, i2, Mu, Mz, ρ, ?_, ?_, ?_⟩
  · exact isActOf_of_pullback M0 Mu hMu _ _ (fun b => Y.m0.toSABMap.act b) ρ hρ
  · exact isActOf_of_pullback M0 Mz hMz _ _ (fun b => Y.m.act b) ρ hρ
  · intro e
    unfold SameVec
    exact ⟨(M0.pt e).left, Over.w (M0.pt e), (hMu e).symm, (hMz e).symm⟩

end GlobalTheory.CompanionTheory.Ar.LieTransport
end
end

