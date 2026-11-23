module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.UniversalJetCoordinatesDimUnique
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsoIntegralModelsMatchingLieBasesStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FiniteTorsionAbelianGeomPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusExtTorsion

theorem finite_torsion_abelian_geomPoint {S : Scheme.{0}} (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (n : ℕ)
    (hn : 1 ≤ n) : Finite {x : Over.mk t ⟶ B // x ^ n = 1} := by
  have hA : IsAbelianScheme ((Over.pullback t).obj B) :=
    { comm := by have := hB.comm; infer_instance
      smooth := by have := hB.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hB.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have h := abelian_torsion_finite_and_mulN_surjective.1 Ω ((Over.pullback t).obj B) hA n hn
  have hp := isGrpPullback_pullback B t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp Ω)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst B.hom t = y.left ≫ pullback.fst B.hom t :=
        congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp Ω))).hom (Over.w y))
        (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ B // x ^ n = 1} := by
    refine Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

theorem finite_torsion_geomPoint : ∀ (S : Scheme.{0}) (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → IsAbelianScheme B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (N : ℕ), 1 ≤ N → Finite {x : Over.mk t ⟶ G // x ^ N = 1} := by
  intro S G B _ _ _ X _ _ _ q i hq hi hk hB Ω _ _ t n hn
  refine SemiAbTorsion.finite_pow_eq_one_of_extension (IsMonHom.monoidHom i (Over.mk t))
    (IsMonHom.monoidHom q (Over.mk t)) ?_ ?_ n ?_
    (finite_torsion_abelian_geomPoint B hB Ω t n hn)
  · intro a b h
    exact hk.hom_ext h (toUnit_unique _ _)
  · intro x hx
    have hx' : x ≫ q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · haveI : IsDomain Γ((Over.mk t).left, ⊤) := inferInstanceAs (IsDomain Γ(Sp Ω, ⊤))
    haveI := SemiAbTorsion.finite_chars_pow_eq_one X Γ((Over.mk t).left, ⊤) hn
    let e := splitTorusPointsEquiv S X (Over.mk t)
    refine Finite.of_injective (fun s => (⟨e s.1, by rw [← map_pow, s.2, map_one]⟩ :
      {s : Multiplicative X →* Γ((Over.mk t).left, ⊤)ˣ // s ^ n = 1})) ?_
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))

end GlobalTheory.TorusExtTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem nuAlg_le_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (t t' : SAB H (Sp T.V)) (n : SABMap t t' (𝟙 (Sp T.V)))
    (hsurj : Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom) (d d' : ℕ)
    (B : FB T.V d (𝓞 E)) (B' : FB T.V d' (𝓞 E))
    (tg : Fin d → (Sp (DualNumber T.V) ⟶ t.G.left)) (tg' : Fin d' → (Sp (DualNumber T.V) ⟶ t'.G.left))
    (uv : Fin d → Fin d → T.V) (uv' : Fin d' → Fin d' → T.V)
    (x : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp T.V)) d' m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp T.V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp T.V)) d' x' m)
    (hc : IsChartG t (𝟙 (Sp T.V)) d B.G.F B.A.act tg uv x)
    (hc' : IsChartG t' (𝟙 (Sp T.V)) d' B'.G.F B'.A.act tg' uv' x')
    (hu : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x) (hu' : GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d') x')
    (hf : IsFrameG t (𝟙 (Sp T.V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t' (𝟙 (Sp T.V)) d' x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    (h : PS T.Fr 2 d) (h' : PS T.Fr 2 d') (hg : B.IsCanonGauge T.Fr h) (hg' : B'.IsCanonGauge T.Fr h')
    (uT : Lt1 Dw → Fin d → T.V) (uT' : Lt1 Dw → Fin d' → T.V)
    (v : Lt1 Dw → (Sp (DualNumber T.V) ⟶ t.G.left))
    (hv : ∀ ℓ, IsCombAtG t (𝟙 (Sp T.V)) (dirs x) (uT ℓ) (v ℓ))
    (hv' : ∀ ℓ, IsCombAtG t' (𝟙 (Sp T.V)) (dirs x') (uT' ℓ) (v ℓ ≫ n.φ))
    (u : Lt1 Dw → Fin d → T.Fr) (u' : Lt1 Dw → Fin d' → T.Fr)
    (huT : ∀ ℓ i, u ℓ i = algebraMap T.V T.Fr (uT ℓ i)) (huT' : ∀ ℓ i, u' ℓ i = algebraMap T.V T.Fr (uT' ℓ i))
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr B' a).mulVec (u' ℓ) = io (embK c ℓ.1 a) • u' ℓ)
    (ε k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (N : ℕ) :
    nuAlg Dw T B h u ε k a N ≤ nuAlg Dw T B' h' u' ε k a N := by
  obtain ⟨x'', -, hx''u, -, -⟩ := _root_.GlobalTheory.PushChart.pushChart E H T.V t t' n d x
  have hd : d = d' := _root_.GlobalTheory.ChartCmp.univJ_dim_unique T.V t'.G d d' x'' x' (hx''u hu) hu'
  subst hd
  obtain ⟨φ, φi, hrel, hlin⟩ := _root_.GlobalTheory.ChartCmp.jrel_of_sabMap E H hs T.V t t' n hsurj d B B' (Fin d) (Fin d) tg tg' uv uv' x x' e e'
    hc hc' hu hu' hf hf'
  refine _root_.GlobalTheory.ChartCmp.nuAlg_le_of_jrel E H Dw l Xo c hs T io d B B' φ φi h h' u u' hrel hg hg' heig ?_ ε k a N
  intro ℓ
  have hu1 : u ℓ = fun i => algebraMap T.V T.Fr (uT ℓ i) := funext (huT ℓ)
  have hu2 : u' ℓ = fun j => algebraMap T.V T.Fr (uT' ℓ j) := funext (huT' ℓ)
  rw [hu1, hu2, hlin (uT ℓ) (uT' ℓ) (v ℓ) (hv ℓ) (hv' ℓ)]
  funext i
  exact RingHom.map_mulVec (algebraMap T.V T.Fr) (dLin φ) (uT' ℓ) i

theorem nuLocC_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing
    (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C C' : IntegralChartA3 Xo c T io y) (e k : ℕ)
      (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n ≤ nuLocC C' e k a n := by
  letI := H.starRing
  intro hs T io y C C' e k a n
  letI := io.toAlgebra
  obtain ⟨BT, hF, hA, hP1, hP2, hSy, hAd, hK⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨BT', hF', hA', hP1', hP2', hSy', hAd', hK'⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C'
  obtain ⟨hFK, hActK, hG, hGc⟩ := hK T.Fr
  obtain ⟨hFK', hActK', hG', hGc'⟩ := hK' T.Fr
  rw [GlobalTheory.T.localChartDepth_eq_integralBiextDepth E H Dw l Xo c T io y C BT hFK hActK e k a n,
    GlobalTheory.T.localChartDepth_eq_integralBiextDepth E H Dw l Xo c T io y C' BT' hFK' hActK' e k a n]
  obtain ⟨nm, hnm⟩ := GlobalTheory.T.exists_iso_integralModels_matching_lieBases E H Dw l Xo c T io _ C.I C'.I
  have hsurj := GlobalTheory.T.surjective_appTop_integralModel_square E H Dw l Xo c T io _ C'.I
  have hU := GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y
  have e1 : MvPowerSeries.map (algebraMap T.Fr T.Fr) C.ch.h = C.ch.h := by
    ext
    simp
  have e2 : MvPowerSeries.map (algebraMap T.Fr T.Fr) C'.ch.h = C'.ch.h := by
    ext
    simp
  rw [e1] at hGc
  rw [e2] at hGc'
  have gen := C.gen
  have gen' := C'.gen
  unfold IsGenFibreChart at gen gen'
  refine nuAlg_le_of_charts Xo c hs T io C.I.G C'.I.G nm hsurj (chD C.ch) (chD C'.ch) BT BT' C.tgT C'.tgT
    (fun j => Pi.single j 1) (fun j => Pi.single j 1) C.xT C'.xT C.eT C'.eT ?_ ?_ (hU C) (hU C') ?_ ?_
    C.ch.h C'.ch.h ((hG _).2 hGc) ((hG' _).2 hGc') C.uvecT C'.uvecT (fun ℓ => (C.I.ub ℓ.1 ℓ.2).left)
    (fun ℓ => C.dirT ℓ) ?_ C.ch.uvec C'.ch.uvec gen.1.2.2.2.2.2.2 gen'.1.2.2.2.2.2.2 ?_ e k a n
  · rw [hF, hA]
    exact C.chartT
  · rw [hF', hA']
    exact C'.chartT
  · rw [hF, hA, hP1, hP2, hSy, hAd]
    exact C.frameT
  · rw [hF', hA', hP1', hP2', hSy', hAd']
    exact C'.frameT
  · intro ℓ
    rw [hnm]
    exact C'.dirT ℓ
  · intro b ℓ
    have h2 : dAct T.Fr BT' b = dAct T.Fr C'.ch.B b := by
      funext i j
      simp only [dAct, hActK' b]
    rw [h2]
    exact GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y C' b ℓ

theorem chartIndep_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ChartIndep Xo c := by
  intro E _ _ _ H Dw l Xo c inst hs
  have hst : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hs
  subst hst
  intro T io y C C' e k a n
  exact le_antisymm (nuLocC_le Xo c hs T io y C C' e k a n) (nuLocC_le Xo c hs T io y C' C e k a n)

end GlobalTheory.ChartCmp
end
end

