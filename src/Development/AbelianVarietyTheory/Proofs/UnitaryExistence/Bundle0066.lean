module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGenerators

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem secNZ_of_secGen : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecGen x s → SecNZ x s := by
  intro hbc E _ _ _ H Dw l Xo S _ x s hs p
  obtain ⟨g, hg, θ, hθ⟩ := _root_.GlobalTheory.Frames.exists_local_generator hbc E H Dw l Xo S x p
  have hid : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ Xo.X), z = spMap (RingHom.id R) ≫ z := by
    intro R _ z
    have : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨-, hc2, -, hc4⟩ := _root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo (Localization.Away g) (Localization.Away g)
    (Localization.Away g) (RingHom.id _) (RingHom.id _) (spMap (algebraMap S (Localization.Away g)) ≫ x)
    _ _ (hid _ _) (hid _ _)
  have hθθ : SecBC (RingHom.id (Localization.Away g)) 1 _ _ θ θ :=
    (hc2 1 θ θ).2 fun i => by rw [(hc4 1 1 i).2.2, _root_.one_mul]
  have hnz := (hθ _ (RingHom.id _) _ θ (hid _ _) hθθ).2
  obtain ⟨p', hp'⟩ : ∃ p' : PrimeSpectrum (Localization.Away g),
      PrimeSpectrum.comap (algebraMap S (Localization.Away g)) p' = p := by
    have h := PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
    have : (p : PrimeSpectrum S) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [h]; exact hg
    exact this
  obtain ⟨q, i, hq, hqi⟩ := hnz p'
  obtain ⟨N, s₀, s₁, h01, h1⟩ := _root_.GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul E H Dw l Xo S x g θ
  have hu : IsUnit (scal (spMap (algebraMap S (Localization.Away g)) ≫ x)
      ((algebraMap S (Localization.Away g)) g ^ N) i) := by
    obtain ⟨v, hv⟩ := ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow N).exists_right_inv
    refine IsUnit.of_mul_eq_one (scal _ v i) ?_
    rw [← (hc4 _ v i).1, hv, (hc4 1 1 i).2.2]
  have hq1 : q ∈ (Gx _).basicOpen (s₁.f i) := by
    rw [h1 i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
    exact ⟨Scheme.basicOpen_le _ _ hqi, hqi⟩
  obtain ⟨q₀, i₀, hq₀, hqi₀⟩ := (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S (Localization.Away g) _ x _ rfl s₀ s₁ h01 p').1
    ⟨q, i, hq, hq1⟩
  obtain ⟨b, hb, -⟩ := hs s₀
  rw [hb i₀, Scheme.basicOpen_mul] at hqi₀
  exact ⟨q₀, i₀, hq₀.trans hp', hqi₀.2⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem nonempty_frPt_complex : N1c → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, Nonempty (FrPt Xo c (CAt σ)) := by
  intro hN hT E _ _ _ H Dw l Xo c h σ
  classical
  obtain ⟨L, _, _, j, x, hx⟩ := _root_.GlobalTheory.moduli_exists_numberField_point hN E H Dw l Xo c h
  let _ : Algebra c.F L := j.toAlgebra
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic c.F L := by
    have : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let _ : Algebra L ℂ := φ.toRingHom.toAlgebra
  obtain ⟨_, y, _⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := L) (L' := ℂ) hT
    (fun r => (φ.commutes r).symm) x hx (fun τ i j => if i = j then 1 else 0)
    (fun τ i => by simp) (fun τ i j hij => by simp [hij.ne'])
  exact ⟨y⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valV_eq_one_integral_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (θ : LB.Sec G.PP.L) (θ₂ : LB.Sec G₂.PP.L), ((∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w2 : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)) (σ : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ2 : LB.Sec (G.PP.L.pull m₂.φ)), RigIso m₁ w1 ∧ RigIso m₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m₂.φ θ θ2 ∧ ∀ g : t.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m₁.φ → g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))) → ((∀ σ : LB.Sec G₂.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G₂.G.left (le_top : G₂.PP.L.U i ≤ ⊤) ((G₂.G.hom).appTop.hom (toΓ T.V a)) * θ₂.f i) ∧ ∃ (w1 : LB.Iso t₂.PP.L (Xo.univ.t.PP.L.pull n₁.φ)) (w2 : LB.Iso t₂.PP.L (G₂.PP.L.pull n₂.φ)) (σ : LB.Sec t₂.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull n₁.φ)) (θ2 : LB.Sec (G₂.PP.L.pull n₂.φ)), RigIso n₁ w1 ∧ RigIso n₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec n₂.φ θ₂ θ2 ∧ ∀ g : t₂.G.left ⟶ Gx y'.x, g ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = n₁.φ → g ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = t₂.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull n₁.φ).U j ≤ g ⁻¹ᵁ (PPx y'.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y'.s.f (fun _ => j PUnit.unit))) → ∀ a : T.Frˣ, SecBC (RingHom.id T.Fr) (a : T.Fr) y.x y'.x y.s y'.s → valV T.V (a : T.Fr) = 1 := by
  first | exact @GlobalTheory.IntegralGenerator.valV_eq_one | exact GlobalTheory.IntegralGenerator.valV_eq_one | (intros; apply GlobalTheory.IntegralGenerator.valV_eq_one <;> assumption)
end

