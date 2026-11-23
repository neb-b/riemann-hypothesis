module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.WeilBound.CoreStatements.AmpleLineBundles.IntersectionNumberEqLineHeight

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def AbBound {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel t.G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (C : ℝ)
    (z : Sp ℂ ⟶ X) : Prop :=
  ∀ P : AbPart t z, IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ t.G) (c : ℂ),
    IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left →
    HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ C * (h.ip z v₀ v₀).re

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def GoodPt (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) : Prop :=
  ∃ τ : c.F →+* ℂ, z ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧
    (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem grp_mul {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (a : T ⟶ S') (b : T ⟶ S) (hb : b = a ≫ f)
    (x y : Over.mk a ⟶ G') (x₀ y₀ : Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hb
  exact h.2 (Over.mk a) x y x₀ y₀ hx hy

theorem exists_lift {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} (a : T ⟶ S') (w : T ⟶ G.left) (hw : w ≫ G.hom = a ≫ f) :
    ∃ v : Over.mk a ⟶ G', v.left ≫ φ = w :=
  ⟨Over.homMk (h.lift w a hw) (by simp), by simp⟩

theorem lift_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {a : T ⟶ S'} (v v' : Over.mk a ⟶ G')
    (e : v.left ≫ φ = v'.left ≫ φ) : v = v' :=
  Over.OverMorphism.ext (h.hom_ext e (by rw [Over.w, Over.w]))

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun a => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

def scale {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) : epsAt a ⟶ Y :=
  Over.homMk (spMap (epsMul c) ≫ v.left) (by
    have h := Over.w v
    simp only [Over.mk_left, Over.mk_hom, Category.assoc] at h ⊢
    rw [h, ← Category.assoc, LieTangent.spec_eps_alg])

@[simp] theorem scale_left {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) :
    (scale a c v).left = spMap (epsMul c) ≫ v.left := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem abPart_mul {S : Scheme.{0}} {t : SAB H S} {K : Type} [Field K] {z : Sp K ⟶ S} (P : AbPart t z) {T : Over (Sp K)}
    (x y : T ⟶ P.tK.G) :
    (x * y) ≫ P.τ.q ≫ P.e.hom = (x ≫ P.τ.q ≫ P.e.hom) * (y ≫ P.τ.q ≫ P.e.hom) := by
  letI := P.τ.grpB
  haveI := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  rw [← Category.assoc, mul_comp, mul_comp, Category.assoc, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TanCompare

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem tan_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left)) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, ((Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t'.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt e).left)) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' V₁ V₂ _ _ _ _ MB MB' f hf σ Pσ mKσ mBσ
    d1 d2 Mσ hMσ Mσ' hMσ' x v u hv hu
  have spec_dual_alg {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap R' (DualNumber R')) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hbase : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, spMap_comp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb1 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) ≫ z₁ := by
    rw [hbase, Category.comp_id]
  have hb2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, Category.comp_id, Category.assoc]
  have hb3 : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    rw [spMap_comp e₂ σ, Category.comp_id, Category.assoc]
  have base : ∀ e : V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro e
    obtain ⟨vL, hvL⟩ := exists_lift P₂.m.cart.1 (spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _)
      (spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) (by
        have hMe : (MB.pt e).left ≫ t.G.hom = spMap (algebraMap (𝓞 L) (DualNumber (𝓞 L))) ≫ z := Over.w (MB.pt e)
        rw [Category.assoc, hMe, ← Category.assoc, spec_dual_alg, Category.assoc, hz, Category.comp_id])
    have hfe : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w ≫ m'.φ =
        spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left := hf e vL hvL
    obtain ⟨v, hv⟩ := exists_lift Pσ.m.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _)
      (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left
      ((Over.w (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).trans hb1)
    obtain ⟨u, hu⟩ := exists_lift m'.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ)
      (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left
      ((Over.w (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e))).trans hb2)
    refine ⟨v, u, hv, hu, ?_⟩
    have hde : spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap σ) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := spMap_dual_comp _ _
    have hd : spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := spec_dual_alg σ
    have h1 : (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left :=
      (Category.comp_id _).symm.trans (hMσ e)
    have h1' : (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt (f e)).left :=
      (Category.comp_id _).symm.trans (hMσ' (f e))
    have hvd : v.left ≫ Pσ.m.φ = spMap (dualMap σ) ≫ vL.left ≫ P₂.m.φ := by
      rw [hv, h1, hde, Category.assoc, hvL]
    have wv : v.left ≫ Pσ.tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _ := Over.w v
    have wvL : vL.left ≫ P₂.tK.G.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w vL
    have star : v.left ≫ mKσ.φ = spMap (dualMap σ) ≫ vL.left ≫ mK2.φ := by
      refine P₁.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, d1, hvd, Category.assoc, Category.assoc, c1]
      · rw [Category.assoc, mKσ.cart.1.w, ← Category.assoc, wv, hb3]
        simp only [Category.assoc]
        rw [mK2.cart.1.w, ← Category.assoc vL.left, wvL, Category.comp_id]
        have hd2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ ≫ spMap e₂ =
            spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) ≫ spMap e₂ := by
          rw [← Category.assoc, ← hd, Category.assoc]
        exact hd2
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    have wq : (vL ≫ P₂.τ.q).left ≫ P₂.τ.B.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w (vL ≫ P₂.τ.q)
    have we : P₂.e.hom.left ≫ P₂.tB.G.hom = P₂.τ.B.hom := Over.w P₂.e.hom
    have hu2 : u.left = spMap (dualMap σ) ≫ (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w := by
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [hu, h1', hde]
        simp only [Category.assoc]
        rw [hfe]
      · rw [wu]
        simp only [Category.assoc]
        rw [hw', we, wq, Category.comp_id, hd]
    have e1 : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ mB2.φ = vL.left ≫ (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ := by
      simp only [Over.comp_left, Category.assoc]
    have e2 : (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ = v.left ≫ (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
      rw [Over.comp_left, Category.assoc]
    rw [hu2, e2, ← d2, ← Category.assoc v.left, star]
    simp only [Category.assoc]
    rw [hw, e1, ← c2]
  have tm : ∀ (c : GroundTheory.Heights₂.Heights.ComplexAt σ) (e : V₁), ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt (c ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) (c ⊗ₜ[𝓞 L] e))).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro c e
    obtain ⟨v, u, h, k, l⟩ := base e
    let c' : ℂ := c
    have hs : c' • (1 : GroundTheory.Heights₂.Heights.ComplexAt σ) = c := by
      rw [GroundTheory.Heights₂.Heights.ComplexAt.complex_smul_def, _root_.mul_one]
      rfl
    have hc : ∀ (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (a : W),
        c ⊗ₜ[𝓞 L] a = c' • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] a) := by
      intro W _ _ a
      rw [TensorProduct.smul_tmul', hs]
    refine ⟨scale _ c' v, scale _ c' u, ?_, ?_, ?_⟩
    · rw [hc, Mσ.smul, scale_left, Category.assoc, h]
    · rw [LinearMap.lTensor_tmul, hc, Mσ'.smul, scale_left, Category.assoc, k]
    · rw [scale_left, Category.assoc, l]
      simp only [Over.comp_left, scale_left, Category.assoc]
  have hx0 : ∀ u : epsAt (spMap σ) ⟶ tK.G, (u.left ≫ mP.φ) ≫ P₁.tB.G.hom =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    intro u
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    rw [Category.assoc, mP.cart.1.w, ← Category.assoc, wu]
  have key : ∀ x : GroundTheory.Heights₂.Heights.Fibre σ V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt x).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      have h0 := tm 0 0
      rwa [TensorProduct.zero_tmul] at h0
    | tmul c e => exact tm c e
    | add x y hx hy =>
      obtain ⟨v₁, u₁, h₁, k₁, l₁⟩ := hx
      obtain ⟨v₂, u₂, h₂, k₂, l₂⟩ := hy
      refine ⟨v₁ * v₂, u₁ * u₂, ?_, ?_, ?_⟩
      · rw [Mσ.add]
        exact (grp_mul Pσ.m.cart _ _ hb1 v₁ v₂ (Mσ.pt x) (Mσ.pt y) h₁.symm h₂.symm).symm
      · rw [map_add (f := _), Mσ'.add]
        exact (grp_mul m'.cart _ _ hb2 u₁ u₂ _ _ k₁.symm k₂.symm).symm
      · rw [abPart_mul]
        let x₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₁.left ≫ mP.φ) (hx0 u₁)
        let y₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₂.left ≫ mP.φ) (hx0 u₂)
        rw [← grp_mul mP.cart _ _ rfl u₁ u₂ x₀ y₀ rfl rfl]
        exact grp_mul mBσ.cart _ _ hb3.symm _ _ x₀ y₀ l₁ l₂
  obtain ⟨v₀, u₀, h₀, k₀, l₀⟩ := key x
  have hv' : v = v₀ := lift_unique Pσ.m.cart.1 _ _ (hv.trans h₀.symm)
  have hu' : u = u₀ := lift_unique m'.cart.1 _ _ (hu.trans k₀.symm)
  rw [hv', hu']
  exact l₀

end GlobalTheory.CompanionTheory.Ar.TanCompare
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationHolUnifTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.InvDer

theorem ev_pull {C : Type} [CommRing C] {Y Y' : Scheme.{0}} (x : Sp C ⟶ Y) (ψ : Y ⟶ Y') (U : Y'.Opens)
    (h : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (f : Γ(Y', U)) :
    ev x (ψ ⁻¹ᵁ U) h' (ψ.app U f) = ev (x ≫ ψ) U h f := by
  simp only [ev, RingHom.comp_apply, Scheme.Hom.comp_appLE, CommRingCat.hom_comp]

theorem valAt'_pull {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (ψ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (ψ ⁻¹ᵁ U) (ψ.app U f) = valAt' (x ≫ ψ) U f := by
  by_cases h : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U) := h
    rw [valAt', valAt', dite_eq_left h, dite_eq_left h']
    exact ev_pull x ψ U h h' f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U) := h
    rw [valAt', valAt', dite_eq_right h, dite_eq_right h']

theorem tr_eq_pull {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {A : Over (Sp ℂ)} [GrpObj A]
    {z : Sp ℂ ⟶ Sp R} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G)
    (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) (v' : epsR ℂ ⟶ A)
    (hv : v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left) :
    tr v₀ (a.left ≫ φ) = ((toUnit (epsR ℂ) ≫ a) * v').left ≫ φ := by
  have hb : (a.left ≫ φ) ≫ G.hom = z := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w a]
    exact Category.id_comp z
  let J : Over.mk ((epsR ℂ).hom ≫ z) ⟶ epsAt ((a.left ≫ φ) ≫ G.hom) :=
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (a.left ≫ φ) ≫ G.hom = (epsR ℂ).hom ≫ z
      rw [hb, Category.id_comp]
      rfl)
  let P := piE ((a.left ≫ φ) ≫ G.hom) ≫ (Over.homMk (a.left ≫ φ) rfl : Over.mk ((a.left ≫ φ) ≫ G.hom) ⟶ G)
  let Q := rhoE ((a.left ≫ φ) ≫ G.hom) ≫ v₀
  have e := h.2 (epsR ℂ) (toUnit (epsR ℂ) ≫ a) v' (J ≫ P) (J ≫ Q) ?_ ?_
  · rw [← MonObj.comp_mul] at e
    have e' : (J ≫ (P * Q)).left = (P * Q).left := Category.id_comp _
    rw [← e, e']
    rfl
  · have hu : (toUnit (epsR ℂ)).left = (epsR ℂ).hom := (Over.w (toUnit (epsR ℂ))).symm ▸ (Category.comp_id _).symm
    show 𝟙 _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ a.left ≫ φ = (toUnit (epsR ℂ) ≫ a).left ≫ φ
    rw [Over.comp_left, hu, Category.id_comp, Category.assoc]
    rfl
  · show 𝟙 _ ≫ spMap (dualMap (bmap ((a.left ≫ φ) ≫ G.hom))) ≫ v₀.left = v'.left ≫ φ
    rw [hb, Category.id_comp, hv]

theorem fderiv_valAt_eq_der (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left)
    (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ)
    (v' : epsR ℂ ⟶ A) (hv : v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left) (hd : u.IsDiff c v')
    (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)) (w : Fin g → ℂ)
    (hw : ⊤ ≤ ((u.ex w).left ≫ φ) ⁻¹ᵁ V) :
    fderiv ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V f) w c =
      valAt' ((u.ex w).left ≫ φ) V (der v₀ hv₀ hV f) := by
  let t : A ⟶ A := (toUnit A ≫ u.ex w) * 𝟙 A
  have hE : v' ≫ t = (toUnit (epsR ℂ) ≫ u.ex w) * v' := by
    have e : v' ≫ toUnit A = toUnit (epsR ℂ) := toUnit_unique _ _
    simp only [t, MonObj.comp_mul, Category.comp_id, ← Category.assoc, e]
  have ht : ∀ x, u.ex x ≫ t = u.ex (w + x) := by
    intro x
    have e : u.ex x ≫ toUnit A = 𝟙 _ := toUnit_unique _ _
    simp only [t, MonObj.comp_mul, Category.comp_id, ← Category.assoc, e, Category.id_comp, u.ex_add]
  have htr : tr v₀ ((u.ex w).left ≫ φ) = v'.left ≫ t.left ≫ φ := by
    rw [tr_eq_pull h v₀ (u.ex w) v' hv, ← hE, Over.comp_left, Category.assoc]
  have hT := tr_top v₀ hv₀ _ V hw
  have hU : ⊤ ≤ v'.left ⁻¹ᵁ ((t.left ≫ φ) ⁻¹ᵁ V) := by
    have h2 := hT
    rw [htr] at h2
    exact h2
  have key := hd ((t.left ≫ φ) ⁻¹ᵁ V) hU ((t.left ≫ φ).app V f)
  have hF : (fun x => valAt' (u.ex x).left ((t.left ≫ φ) ⁻¹ᵁ V) ((t.left ≫ φ).app V f)) =
      fun x => (fun x => valAt' ((u.ex x).left ≫ φ) V f) (w + x) := by
    funext x
    rw [valAt'_pull, ← Category.assoc, ← Over.comp_left, ht]
  have hG := fderiv_comp_add_left (𝕜 := ℂ) (f := fun x => valAt' ((u.ex x).left ≫ φ) V f) (x := 0) w
  rw [add_zero] at hG
  rw [hF, hG] at key
  rw [← key, valAt', dite_eq_left hw]
  have e1 := snd_ev_tr v₀ hv₀ hV ((u.ex w).left ≫ φ) hw hT f
  have hT' : ⊤ ≤ (v'.left ≫ t.left ≫ φ) ⁻¹ᵁ V := hU
  have e2 : ev (v'.left ≫ t.left ≫ φ) V hT' f = ev (tr v₀ ((u.ex w).left ≫ φ)) V hT f :=
    congrArg (fun m => m f) (ev_congr htr.symm V hT' hT)
  have e3 := ev_pull v'.left (t.left ≫ φ) V hT' hU f
  exact (congrArg TrivSqZeroExt.snd (e3.trans e2)).trans e1

end GlobalTheory.CompanionTheory.Ar.InvDer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem existsUnique_rat (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι :=
  (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers ℚ K ι).1

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusGeneratorCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem secZ_lift {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0) {m : ℕ}
    (y : Tm x m ⟶ G) (hy : homAt x (jetAug : Jet k Unit m →ₐ[k] k) ≫ y = 1) :
    secZ G x m ≫ (lift (fst (Tm x m) G ≫ y) (snd (Tm x m) G)).left =
      pullback.fst G.hom x ≫ (lift (1 : G ⟶ G) (𝟙 G)).left := by
  have hf : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
      dsimp
      rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
      simp [spMap]) : FinalForm G x ⟶ Tm x m) ≫ y = 1 := by
    have e : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
        dsimp
        rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
        simp [spMap]) : FinalForm G x ⟶ Tm x m) =
        (Over.homMk (pullback.snd G.hom x) (by simp [spMap]) : FinalForm G x ⟶ overAt x k) ≫ homAt x (jetAug : Jet k Unit m →ₐ[k] k) := by
      ext1
      rfl
    rw [e, Category.assoc, hy]
    simp [Hom.one_def]
  have e₂ : pullback.fst G.hom x ≫ (lift (1 : G ⟶ G) (𝟙 G)).left =
      ((Over.homMk (pullback.fst G.hom x) pullback.condition : FinalForm G x ⟶ G) ≫ lift (1 : G ⟶ G) (𝟙 G)).left := rfl
  rw [e₂, secZ, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_snd, hf]
  simp [Hom.one_def]

theorem red_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p) → ∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1 := by
  intro E _ _ _ H X0 t k _ x p y hy κ hκ τ hτ C hC j h
  refine fn_ext fun z hz => ?_
  refine (gs_appLE (secZ t.G x p) _ _ h z hz (C.s fun _ => j).val).trans ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good t.PP.L t.PP.isLB z (K := Unit) (fun _ => pullback.fst t.G.hom x) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  have eJ' : J (pullback.fst t.G.hom x) = j := eJ ()
  have hv := val_of C (secZ t.G x p) z J (fun _ => j) (Fin.forall_fin_two.2
    ⟨(congrArg J (secZ_pa t.G x y hy)).trans eJ', (congrArg J (secZ_snd t.G x p)).trans eJ'⟩)
  have h₁ : val κ (secZ t.G x p ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J = 1 := by
    rw [secZ_lift t.G x y hy, ← val_pull hJ, val_corr hJ hκ, val_one]
  have h₂ : val τ (secZ t.G x p ≫ (fst (Tm x p) t.G).left) z J = 1 := by
    rw [secZ_fst, hτ _ _ z J hJ]
  have hm : (secZ t.G x p) z ∈ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j) := h hz
  have hval : val C (secZ t.G x p) z J = 1 := by
    rw [hC _ _ z J hJ, h₁, h₂]
    simp
  refine (gs_unit _ z _ hm (C.s fun _ => j)).trans ((congrArg Units.val (hv.symm.trans hval)).trans ?_)
  rw [gs_eq (𝟙 _) z _ (show (𝟙 (pullback t.G.hom x)) z ∈ pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j from hz), map_one, map_one,
    Units.val_one]

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermTorsionLiftCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.TestPair

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (y : Tm x p ⟶ t.G), y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left = (homAt x (jq w p m)).left ≫ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left := by
  intro E _ _ _ H _ X0 t k _ p _ _ x d g w m y hy
  subst hy
  obtain ⟨h0, h1⟩ := GlobalTheory.CompanionTheory.Ar.Coc.JetPts.main E H X0 t k p x d g w m
  unfold rQ
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift, lift_fst_assoc, lift_snd, h0, h1]

end GlobalTheory.CompanionTheory.Ar.Coc.TestPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOfZeroDimVariety
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht

theorem height_eq_intersection_number :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (w : (Σ k, ι k) → L), W = mCoordIdeal w ∧ w ∈ ptsOver L W ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι W 1 ![A] / (degC W : ℝ) = lineHt A L w := by
  exact @CoverDenseAlt.intersection_number_eq_line_height

end GlobalTheory.CompanionTheory.Ar.Ht
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_augmentation_one_pth_power : ∀ (B : Type) [CommRing B] (p : ℕ) [Fact p.Prime], (p : B) = 0 → ∀ e : Jet B Unit p, (jetAug : Jet B Unit p →ₐ[B] B) e = 1 → ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | exact GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add <;> assumption)
end

