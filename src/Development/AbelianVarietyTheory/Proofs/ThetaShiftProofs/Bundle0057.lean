module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.EnlargeCf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FrameCut
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EvRBaseChangeOfFromTest
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace GlobalTheory.ArcQ

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frBor_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] [IsReduced S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (h : FrBor t y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y := by
  rw [← sub_eq_zero]
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : S →ₐ[c.F] S ⧸ P := Ideal.Quotient.mkₐ c.F P
  obtain ⟨z, hz⟩ := hL.bc _ _ φ y
  obtain ⟨z', hz'⟩ := hL.bc _ _ φ y'
  obtain ⟨g, hg1, hg2, hg⟩ := ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 t y y').1 h
  have hc := ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.1 _ φ g _ y y' z z' hg hz).1 hz'
  let t' : Ix Dw → (S ⧸ P)ˣ := fun i => Units.map (φ : S →* S ⧸ P) (t i)
  have hb : FrBor t' z z' :=
    ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c (S ⧸ P)).2.2.2 t' z z').2
      ⟨fun τ => (g τ).map φ, fun τ i => by simp [t', hg1], fun τ i j hij => by simp [hg2 τ i j hij], hc⟩
  have hw := evR_frBor_of_isDomain hL hF t' z z' hb
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y z hz,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y' z' hz'] at hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change φ _ = 0
  rw [map_sub, hw, map_mul, sub_eq_zero]
  congr 1
  simp [wchar, t']

theorem evR_scale_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {A T : Type} [CommRing A] [Algebra c.F A] [IsReduced A]
    [CommRing T] [Algebra c.F T] (φ : A →ₐ[c.F] T) (g : Tˣ) (y : FrPt Xo c A) (z z' : FrPt Xo c T)
    (hm : FrMap φ y z) (hb : FrBor (fun i => i.elim g fun _ => 1) z z') :
    evR Xo c F z' = (g : T) ^ n * φ (evR Xo c F y) := by
  classical
  obtain ⟨G, hG1, hG2, hG⟩ := ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c T).2.2.2 _ z z').1 hb
  let ι := Option (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ))
  let R := MvPolynomial ι A
  let B := Localization.Away (MvPolynomial.X none : R)
  let v : ι → T := fun i => i.elim (g : T) fun x => G x.1 x.2.1 x.2.2
  let k₀ : R →ₐ[c.F] T := MvPolynomial.aevalTower φ v
  have hk₀ : IsUnit (k₀ (MvPolynomial.X none)) := by simp [k₀, v, R]
  let k : B →ₐ[c.F] T := IsLocalization.liftAlgHom (M := Submonoid.powers (MvPolynomial.X none : R)) (f := k₀)
    (by rintro ⟨_, m, rfl⟩; simpa only [map_pow] using hk₀.pow m)
  have hk : ∀ r : R, k (algebraMap R B r) = k₀ r := fun r => IsLocalization.lift_eq _ r
  let π : A →ₐ[c.F] B := IsScalarTower.toAlgHom c.F A B
  have hπ : k.comp π = φ := by
    ext x
    change k (algebraMap A B x) = φ x
    rw [IsScalarTower.algebraMap_apply A R B, hk]
    simp [k₀, R]
  have hu : IsUnit (algebraMap R B (MvPolynomial.X none)) := IsLocalization.Away.algebraMap_isUnit _
  let M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B := fun τ => Matrix.of fun i j =>
    if i = j then 1 else if i < j then 0 else algebraMap R B (MvPolynomial.X (some ⟨τ, i, j⟩))
  have hM1 : ∀ τ i, M τ i i = 1 := fun τ i => by simp [M]
  have hM2 : ∀ τ i j, i < j → M τ i j = 0 := fun τ i j hij => by simp [M, hij, hij.ne]
  have hMk : ∀ τ, (M τ).map k = G τ := fun τ => by
    ext i j
    by_cases h1 : i = j
    · subst h1; simp [hM1, hG1]
    · by_cases h2 : i < j
      · simp [hM2 τ i j h2, hG2 τ i j h2]
      · simp only [M, Matrix.map_apply, Matrix.of_apply, if_neg h1, if_neg h2, hk]
        simp [k₀, v, R]
  have hdet : ∀ τ, IsUnit (M τ).det := fun τ => by
    rw [Matrix.det_of_isLowerTriangular (M τ) (fun i j hij => hM2 τ i j hij)]
    simp [hM1]
  obtain ⟨u₀, hu₀⟩ := hL.bc _ _ π y
  obtain ⟨u, hchg⟩ := (_root_.GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c B M _ u₀).1 hdet hu
  have h0 : FrMap k u₀ z := frMap_cancel (Xo := Xo) (c := c) _ _ _ π k y u₀ z hu₀ (by rw [hπ]; exact hm)
  have h1 : FrMap k u z' := by
    refine ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c B).2.2.1 _ k M _ u₀ u z z' hchg h0).2 ?_
    have e : k (algebraMap R B (MvPolynomial.X none)) = (g : T) := by rw [hk]; simp [k₀, v, R]
    rw [e, show (fun τ => (M τ).map k) = G from funext hMk]
    exact hG
  let t : Ix Dw → Bˣ := fun i => i.elim hu.unit fun _ => 1
  have hbu : FrBor t u₀ u :=
    ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c B).2.2.2 t u₀ u).2 ⟨M, fun τ i => by simp [t, hM1], hM2, hchg⟩
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF B _ k u z' h1,
    evR_frBor_of_isReduced hL hF t u₀ u hbu,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF A _ π y u₀ hu₀, map_mul, ← hπ]
  congr 1
  have e : wchar (ex Dw a n) t = algebraMap R B (MvPolynomial.X none) ^ n := by
    simp [wchar, t, ex, Fintype.prod_option]
  rw [e, map_pow, hk]
  simp [k₀, v, R]

end General

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj

namespace GlobalTheory.AbelianLetters


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory NumberField in
open CategoryTheory.MonObj in
theorem _root_.GlobalTheory.AbelianLetters.mul_comp_of_isGrpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (f : G' ⟶ G)
    (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') : (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  let e : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key := h.2 T x y (e ≫ x ≫ f) (e ≫ y ≫ f) (by simp [e]) (by simp [e])
  rw [← MonObj.comp_mul] at key
  ext1
  simpa [e] using key.symm


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory NumberField in
open CategoryTheory.MonObj in
theorem _root_.GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback :
    ∀ (P P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback P'.A P.A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) φ →
    ∀ (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g) (g : ℕ) (T : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ T.left), i ≫ T.hom = 𝟙 _ →
    ∀ G : (Fin g → ℂ) → (T ⟶ P.A), (∀ z z', G (z + z') = G z * G z') →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ (fun z => i ≫ (G z).left) →
    ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = i ≫ (G z).left) ∧
      (∀ z, G z = 1 → F z ∈ u.Λ) ∧ ∀ (z : Fin g → ℂ) (z' : Fin P'.g → ℂ) (η' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A),
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => i ≫ (G z).left) z (η'.left ≫ φ) → u.IsDiff z' η' → z' = F z := by
  intro P P' φ hφ u g T i hi G hG hhol
  obtain ⟨h1, h2, -⟩ :=
    _root_.GlobalTheory.AnyUnif.tangent_and_unimodular _root_.GlobalTheory.thetaUnifAV_all P' u
  have hlift := _root_.GlobalTheory.existsUnique_linear_lift_of_isHolTo P'.A P'.isAb P'.L P'.g g u h1 h2
  have hpb : IsPullback φ P'.A.hom P.A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) := hφ.1
  rw [_root_.GlobalTheory.Cris.spMap_id] at hpb
  haveI : IsIso φ := hpb.isIso_fst_of_isIso
  obtain ⟨e, he⟩ := _root_.GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ))) _ rfl
  let j : Over.mk ((𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ))).hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (RingHom.id ℂ)) ⟶ T :=
    Over.homMk i (by simp [hi, _root_.GlobalTheory.Cris.spMap_id, Over.tensorUnit_hom])
  let G' : (Fin g → ℂ) → (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ P'.A) := fun z => e.symm (j ≫ G z)
  have hG'φ : ∀ z, (G' z).left ≫ φ = i ≫ (G z).left := by
    intro z
    rw [← he]
    simp [G', j]
  have hG'add : ∀ z w, G' (z + w) = G' z * G' w := by
    intro z w
    simp only [G', hG, MonObj.comp_mul, map_mul]
  have hG'fun : (fun z => (G' z).left) = fun z => (i ≫ (G z).left) ≫ inv φ := by
    funext z
    rw [← hG'φ z, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hG'hol : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ fun z => (G' z).left := by
    rw [hG'fun]
    exact _root_.GlobalTheory.HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
      (_root_.GlobalTheory.HolHom.holAt_of_isHolTo hhol (Set.mem_univ z)).comp (inv φ)
  obtain ⟨F, hF, -⟩ := hlift G' hG'add hG'hol
  refine ⟨F, ?_, ?_, ?_⟩
  · intro z
    rw [hF]
    exact hG'φ z
  · intro z hz
    rw [← u.ker, hF]
    simp [G', hz, MonObj.comp_one]
  · intro z z' η' hder hdiff
    have hfam : (fun w => (u.ex (F w)).left) = fun w => (i ≫ (G w).left) ≫ inv φ := by
      funext w
      rw [hF, ← hG'φ w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have h3 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun w => (u.ex (F w)).left) z η'.left := by
      have hd := (_root_.GlobalTheory.HolHom.isDerivAt0_iff _ _ _).1 hder
      have hd' := hd.comp (inv φ)
      have hη : (η'.left ≫ φ) ≫ inv φ = η'.left := by simp
      rw [hη] at hd'
      rw [hfam, _root_.GlobalTheory.HolHom.isDerivAt0_iff]
      exact hd'
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 at h3
    obtain ⟨hbase, hdF⟩ := h3
    have hF0 : F 0 = 0 := map_zero F
    have htan : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent η' := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent
      rw [hbase]
      simp only [hF0]
      exact _root_.GlobalTheory.TangentOrigin.ex_zero_left u
    have hdiffF : u.IsDiff (F z) η' := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff
      intro U hU f
      rw [hdF U hU f]
      have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := _root_.GlobalTheory.HomLinear.top_le_ex_zero u htan U hU
      have hd : DifferentiableAt ℂ (fun w => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex w).left U f)
          (LinearMap.toContinuousLinearMap F 0) := by
        rw [map_zero]
        exact _root_.GlobalTheory.TangentOrigin.differentiableAt_val u h0 f
      have hc := hd.hasFDerivAt.comp (0 : Fin g → ℂ)
        (LinearMap.toContinuousLinearMap F).hasFDerivAt
      rw [map_zero] at hc
      have hfun : ((fun w => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex w).left U f) ∘ LinearMap.toContinuousLinearMap F) =
          fun w => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex (F w)).left U f := rfl
      rw [hfun] at hc
      rw [hc.fderiv]
      rfl
    obtain ⟨w, -, huniq⟩ := h1 η' htan
    exact (huniq z' hdiff).trans (huniq (F z) hdiffF).symm

end GlobalTheory.AbelianLetters
end

