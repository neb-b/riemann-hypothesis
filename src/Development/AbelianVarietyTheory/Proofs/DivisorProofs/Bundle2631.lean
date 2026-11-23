module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperSetup
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationsTranslationPeriodMapsCorrespond
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslC

theorem exists_flat_transport : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := _root_.GlobalTheory.Mum.GenTransport.exists_transport

theorem formEq_twist : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := _root_.GlobalTheory.MumCmp.formEq_twist_cube

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def θpt (g : GtCoord I D e G) (C b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ G3 D.P.A :=
  lift g.pG (lift (toUnit _ ≫ C) (toUnit _ ≫ b))

theorem θpt_congr (g : GtCoord I D e G) (C b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) {Z : Scheme.{0}}
    (r r' : Z ⟶ (thickObj R I e G).left) (h : r ≫ g.pG.left = r' ≫ g.pG.left) :
    r ≫ (θpt g C b).left = r' ≫ (θpt g C b).left := by
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hw : r ≫ T.hom = r' ≫ T.hom := by rw [← Over.w g.pG, reassoc_of% h]
  let a : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r hw
  let a' : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r' rfl
  have ha : a ≫ g.pG = a' ≫ g.pG := Over.OverMorphism.ext h
  have hu : a ≫ toUnit T = a' ≫ toUnit T := toUnit_unique _ _
  have : a ≫ θpt g C b = a' ≫ θpt g C b := by
    simp only [θpt, comp_lift, ha, ← Category.assoc]
    rw [toUnit_unique (a ≫ toUnit _) (a' ≫ toUnit _)]
  exact congrArg (fun q => q.left) this

theorem exists_ratio_gen (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (hp : g₂.pG ≫ β = g.pG) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β b) twε)) (hw : w.IsGen) (χ₂ : D₂.X) (χ : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ CoordCompare.diffφ (D.prBe I e) (D₂.c χ₂ ≫ β) (D.c χ) k)
      ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
        Good D.P.L z J → Good D₂.P.L z J' →
        val u r z J = (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ twφ D₂ D β b i))
          (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' *
          val D.cub.t (r ≫ (θpt g (D₂.c χ₂ ≫ β) b).left) z J * (val (g.t χ) r z J)⁻¹ := by
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_flat_transport D.P.isLB D₂.P.isLB _ _ w hw _ _ (g₂.t χ₂) (g₂.t_gen χ₂)
  have hF := formEq_twist D₂ D ((Over.map (thick R I e)).map g.q) (D.prBe I e) g₂.pG β hp b χ₂ χ
  obtain ⟨u, hu, hv⟩ := exists_gen D.P.isLB hF
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (θpt g (D₂.c χ₂ ≫ β) b).left))
      (LB.invGen D.P.L _ _ (g.t χ)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁
      (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)) (DVR.invGen_isGen _ _ _ _ (g.t_gen χ)))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  exact (hv Z r z J hJ).trans ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ r).trans
    (congrArg₂ (· * ·) (hv₁ Z r z J J' hJ hJ') (val_pull hJ _ _ r))) (val_inv _ r)))

theorem rearr {U : Type} [CommGroup U] (W a θ c : U) : W * a * θ * c⁻¹ = W * θ * (a * c⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_desc_gen (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    [Mono β.left] (hp : g₂.pG ≫ β = g.pG) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β b) twε)) (hw : w.IsGen) (χ₂ : D₂.X) (χ : D.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A →
      val (g.t χ) r z J = val (g₂.t χ₂) r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (CoordCompare.diffφ (D.prBe I e) (D₂.c χ₂ ≫ β) (D.c χ)) ![1, -1, 1, -1]),
      v.IsGen := by
  obtain ⟨u, hu, hu'⟩ := exists_ratio_gen g g₂ β hp b w hw χ₂ χ
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := CoordCompare.exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.P.L D₂.P.isLB z
    obtain ⟨h₁, h₂⟩ := CoordCompare.ratio_invariant g g₂ β hp χ χ₂ hker r r' z J J' hJ hJ' h
    have h₀ : r ≫ g.pG.left = r' ≫ g.pG.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.prBe I e).left) h).trans (Category.assoc _ _ _))
    rw [hu' Z r z J J' hJ hJ', hu' Z r' z J J' hJ hJ', θpt_congr g _ b r r' h₀, rearr, rearr, h₂]
    congr 2
    exact Finset.prod_congr rfl fun k _ => by rw [CoordCompare.Oφ_congr χ₂ g₂.pG r r' h₁ k])
  exact ⟨v, hv⟩

end Level

theorem c_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ) := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hlift A₂ D₂ U₂ hL β hβ hp xe hker w hw χ
  obtain ⟨⟨_, -, -, _⟩, -⟩ := hR
  have : Mono β.hom.left := inferInstance
  have hp' : ∀ e, (U₂.gt e).pG ≫ β.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hp e)
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  have := D.toPre.P.isAb.proper
  have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
    D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ D₂.toPre.c χ ≫ β.hom) (toUnit _ ≫ D.toPre.c (xe χ)) fun n => by
      obtain ⟨v, hv⟩ := exists_desc_gen (U.gt n) (U₂.gt n) β.hom (hp' n) g.b w hw χ (xe χ)
        (fun Z r z J J' hJ hJ' h h' => hker n Z r z J J' hJ hJ' h h' χ)
      have h₁ := CoordCompare.thick_eq _ _ v hv
      have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
          pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
  simpa using congrArg (η[D.toPre.P.A] ≫ ·) h

end GlobalTheory.MumCmp.TranslC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperSetupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_transport_deeper_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀) (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ → IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ → LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) → (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) → (∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left) → ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.UPoinc.uTest_transport | exact GlobalTheory.UPoinc.uTest_transport | (intros; apply GlobalTheory.UPoinc.uTest_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀)
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧
    (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧
    (∀ x₂ x₂' E, x₂'.left ≫ u₂.φ = x₂.left ≫ u₂.φ ≫ (ε₂ E).left → (T x₂').left ≫ u.φ = (T x₂).left ≫ u.φ ≫ (ε' E).left) ∧
    (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.Poinc.GLift.transport | exact GlobalTheory.Poinc.GLift.transport | (intros; apply GlobalTheory.Poinc.GLift.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEndomorphismsTorsionExtendSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GFib

theorem endo_torsion_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → Y.pt ≫ q = X.M.pt → ∀ z : X.M.Z, X.S.TT X.M z ≤ X.S.HH X.M z → ∃ (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f ∧ GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ := by
  intro E _ _ _ H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO _ hq z hTH
  have hU : (U₀ : Set Y.Z).Nonempty := hO.ne
  have hr : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Y.top_le_preimage_pt hU (x := w) trivial
  let x : Sp X.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hr
  have hx : x ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ FinalForm.u₀ = spMap X.S.R.val.toRingHom := FinalForm.u₀_gen x hx
  have hwx : wi.α ≫ X.ρ.P.A.hom = (wi.G.hom ≫ x) ≫ FinalForm.u₀ := by
    rw [Category.assoc, hxu]; exact wi.hα.1.w
  let ν : wi.G.left ⟶ pullback X.ρ.P.A.hom FinalForm.u₀ := pullback.lift wi.α (wi.G.hom ≫ x) hwx
  have hν₁ : ν ≫ pullback.fst _ _ = wi.α := pullback.lift_fst _ _ _
  have hν₂ : ν ≫ pullback.snd _ _ = wi.G.hom ≫ x := pullback.lift_snd _ _ _
  let ψ : wi.G.left ⟶ FinalForm.G.left := ν ≫ FinalForm.φ
  have hQ := isGrpPullback_pullback X.ρ.P.A FinalForm.u₀
  have gα : IsGrpPullback wi.G X.ρ.P.A (x ≫ FinalForm.u₀) (ν ≫ pullback.fst X.ρ.P.A.hom FinalForm.u₀) :=
    wi.hα.congr hxu.symm hν₁.symm
  have gν : IsGrpPullback wi.G ((Over.pullback FinalForm.u₀).obj X.ρ.P.A) x ν := hQ.cancel gα hν₂
  have gW : IsGrpPullback wi.G FinalForm.G Y.pt ψ := (gν.comp FinalForm.cart).congr hx rfl

  have hxu' : ∀ (x₀ : Sp X.Ω₁ ⟶ U₀.toScheme), x₀ ≫ U₀.ι = Y.pt → x₀ = x := fun x₀ h₀ =>
    (cancel_mono U₀.ι).1 (h₀.trans hx.symm)

  let P := (Over.pullback Y.pt).obj FinalForm.G
  have gA := isGrpPullback_pullback FinalForm.G Y.pt
  let k : P.left ⟶ wi.G.left := gW.1.lift (pullback.fst FinalForm.G.hom Y.pt) P.hom pullback.condition
  have hk₁ : k ≫ ψ = pullback.fst FinalForm.G.hom Y.pt := gW.1.lift_fst _ _ _
  have hk₂ : k ≫ wi.G.hom = P.hom := gW.1.lift_snd _ _ _
  have gk : IsGrpPullback P wi.G (𝟙 _) k :=
    gW.cancel (gA.congr (Category.id_comp _).symm hk₁.symm) (by rw [hk₂, Category.comp_id])
  haveI : IsIso k := gk.1.isIso_fst_of_isIso

  have hE : ∀ a : 𝓞 E, ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₁ : wi.G ⟶ wi.G,
      e₁.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e₁.left ≫ ψ = ψ ≫ F.left := by
    intro a
    obtain ⟨e₀, he₀, pa⟩ := GlobalTheory.SymBaseChange.exists_endo wi.hβ (Xo.univ.t.act.act a)
    have he₀l : e₀.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left := by
      have := congrArg (fun z => z.left) (pa (𝟙 _))
      simpa [pushPt] using this
    haveI := he₀
    obtain ⟨w', hw', pw⟩ := GlobalTheory.SymBaseChange.exists_endo gk e₀
    have hw'l : w'.left ≫ k = k ≫ e₀.left := by
      have := congrArg (fun z => z.left) (pw (𝟙 _))
      simpa [pushPt] using this
    obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
    have hF' : w'.left ≫ pullback.fst FinalForm.G.hom Y.pt = pullback.fst FinalForm.G.hom Y.pt ≫ F.left := by
      rw [← hFw]
      simp only [Over.pullback_map_left, pullback.lift_fst]
    refine ⟨F, hF, fun e₁ he₁ => ?_⟩
    have h10 : e₁ = e₀ := GlobalTheory.TorusPart.hom_ext_of_pullback wi.hβ (he₁.trans he₀l.symm)
    subst h10
    have e1 : k ≫ e₁.left ≫ ψ = w'.left ≫ k ≫ ψ := by rw [← Category.assoc, ← hw'l, Category.assoc]
    rw [← cancel_epi k, e1, hk₁, hF', ← hk₁, Category.assoc]
  choose f hf using hE
  have hT : ∀ t : X.S.TT X.M z, ∃ g : Over.mk Y.pt ⟶ FinalForm.G, g ^ (X.S.r * X.S.N) = 1 ∧
      (∀ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.G.hom = 𝟙 _ →
        w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt (t : X.S.Gam)).left → w ≫ ψ = g.left) ∧
      ∀ w, q.base w = z → ExtNear g w := by
    intro t
    set b : X.S.Gam := (t : X.S.Gam) with hbdef
    have hb : (spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left) ≫ X.ρ.P.A.hom = 𝟙 _ ≫ spMap X.S.R.val.toRingHom := by
      rw [Category.assoc, Over.w (X.ρ.pt b)]; simp
    let w₀ := wi.hα.1.lift _ _ hb
    have hw₁ : w₀ ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left := wi.hα.1.lift_fst _ _ _
    have hw₂ : w₀ ≫ wi.G.hom = 𝟙 _ := wi.hα.1.lift_snd _ _ _
    let sec0 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G := Over.homMk w₀ hw₂
    let V : Over.mk Y.pt ⟶ Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt) := Over.homMk (𝟙 _) (by simp)
    let gγ : Over.mk Y.pt ⟶ FinalForm.G := V ≫ pushPt gW.1.w sec0
    have hgl : gγ.left = w₀ ≫ ψ := by simp [gγ, V, pushPt, sec0]
    refine ⟨gγ, ?_, ?_, ?_⟩
    · have h0 : X.ρ.pt 0 = 1 := by
        have := X.ρ.pt_add 0 0
        rw [add_zero] at this
        exact mul_eq_left.1 this.symm
      have hpt : ∀ n : ℕ, (X.ρ.pt b) ^ n = X.ρ.pt (n • b) := by
        intro n
        induction n with
        | zero => simp [h0]
        | succ k ih => rw [pow_succ, ih, ← X.ρ.pt_add, succ_nsmul]
      have hrN : (X.S.r * X.S.N) • b = 0 := by
        funext i
        simp
      let U : Over.mk (𝟙 (Sp X.Ω₁) ≫ spMap X.S.R.val.toRingHom) ⟶ baseOver (Sp X.S.R) :=
        Over.homMk (spMap X.S.R.val.toRingHom) (by simp)
      have hs : pushPt wi.hα.1.w sec0 = U ≫ X.ρ.pt b := by
        apply Over.OverMorphism.ext
        simp [pushPt, sec0, U, hw₁]
      have hsec : sec0 ^ (X.S.r * X.S.N) = 1 := by
        apply GlobalTheory.SymBaseChange.pushPt_injective wi.hα
        have e1 : pushPt wi.hα.1.w (sec0 ^ (X.S.r * X.S.N)) = (pushPt wi.hα.1.w sec0) ^ (X.S.r * X.S.N) :=
          map_pow (pushHom wi.hα _) sec0 _
        have e2 : pushPt wi.hα.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1 :=
          map_one (pushHom wi.hα _)
        have e3 : (U ≫ X.ρ.pt b) ^ (X.S.r * X.S.N) = U ≫ (X.ρ.pt b) ^ (X.S.r * X.S.N) :=
          (map_pow (preHom U) (X.ρ.pt b) _).symm
        have e4 : U ≫ (1 : baseOver (Sp X.S.R) ⟶ X.ρ.P.A) = 1 := map_one (preHom U)
        rw [e1, e2, hs, e3, hpt, hrN, h0, e4]
      have f1 : gγ ^ (X.S.r * X.S.N) = V ≫ (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N) :=
        map_pow (preHom V) _ _
      have f2 : (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N) = pushPt gW.1.w (sec0 ^ (X.S.r * X.S.N)) :=
        (map_pow (pushHom gW _) sec0 _).symm
      have f3 : pushPt gW.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1 :=
        map_one (pushHom gW _)
      have f4 : V ≫ (1 : Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt) ⟶ FinalForm.G) = 1 := map_one (preHom V)
      rw [f1, f2, hsec, f3, f4]
    · intro w h1 h2
      have : w = w₀ := wi.hα.1.hom_ext (by rw [h2, hw₁]) (by rw [hw₂]; exact h1)
      rw [this, hgl]
    · intro w hw
      have hb' : b ∈ X.S.HH Y w := by
        rw [GlobalTheory.Poinc.HHFibre.HH_eq_of_hom X.o₁ X.Ω₁ X.S X.M Y q hq X.hasDiv w]
        have e : q w = z := hw
        rw [e]
        exact hTH t.2
      obtain ⟨W, h, hzW, hh, hx'⟩ := FinalForm.sec w b hb'
      refine ⟨W, h, hzW, hh, fun y hy => ?_⟩
      rw [hgl, hx' y (w₀ ≫ ν) hy ?_ ?_]
      · simp only [ψ, Category.assoc]
      · have := gW.1.w
        simp only [ψ] at this
        rw [Category.assoc, ← Category.assoc ν, this, ← Category.assoc, hw₂, Category.id_comp]
      · rw [Category.assoc, hν₁, hw₁]
  choose gγ hg using hT
  refine ⟨f, gγ, fun a => ⟨(hf a).1, ?_⟩, fun t => ⟨(hg t).1, ?_, (hg t).2.2⟩⟩
  · intro x₀ h₀ hw e₀ he
    have h' := hxu' x₀ h₀
    subst h'
    exact (hf a).2 e₀ he
  · intro x₀ h₀ hw w h1 h2
    have h' := hxu' x₀ h₀
    subst h'
    exact (hg t).2.1 w h1 h2

end GlobalTheory.UPoinc.GFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingsCommonGeometricFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRechartings_common_geometricFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  first | exact @GlobalTheory.UPoinc.USpreadU.main | exact GlobalTheory.UPoinc.USpreadU.main | (intros; apply GlobalTheory.UPoinc.USpreadU.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnivEqOfLocalPreimageEq
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq : ∀ (M N : Type) [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] (π : N → M), Measurable π → ∀ (μ : Measure N) (ν : Measure M), (∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ T, MeasurableSet T → T ⊆ U → μ (π ⁻¹' T) = ν T) → μ Set.univ = ν Set.univ := by
  intro M N _ _ _ _ _ π hπ μ ν h
  choose U hUo hxU hU using h
  obtain ⟨S, hSc, hS⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  haveI : Countable S := hSc.to_subtype
  have hcov : ⋃ i : S, U i = Set.univ := by
    rw [← Set.biUnion_eq_iUnion S (fun i _ => U i), hS]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hxU x⟩
  have hmap : μ.map π = ν := by
    refine (Measure.ext_iff_of_iUnion_eq_univ hcov).2 fun i => ?_
    ext T hT
    have hm : MeasurableSet (T ∩ U i) := hT.inter (hUo i).measurableSet
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.map_apply hπ hm]
    exact hU i _ hm Set.inter_subset_right
  have : μ Set.univ = μ.map π Set.univ := by
    rw [Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ]
  rw [this, hmap]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpUUniqueOfLower
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_unique_of_lower : ∀ (K : Type) [Field K] (s : ℕ) (y y' : Low s → K) (b : Matrix (Fin s) (Fin s) K),
    (∀ i j, i < j → b i j = 0) → upU y = b * upU y' → y = y' := by
  intro K _ s y y' b hb h
  have key : ∀ i j : Fin s, (∀ k, k < j → b i k = 0) → upU y i j = b i j := by
    intro i j hk
    rw [h, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [upU]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with h1 | h1
      · rw [hk k h1, zero_mul]
      · simp [upU, not_lt.mpr h1.le, hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have low : ∀ (i : Fin s) (N : ℕ) (j : Fin s), j.1 < N → j < i → b i j = 0 := by
    intro i N
    induction N with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj hji
      rw [← key i j fun k hk => ih k (by have := Fin.lt_def.mp hk; omega) (hk.trans hji)]
      simp [upU, not_lt.mpr hji.le, hji.ne']
  have hb1 : b = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hb i j h1, Matrix.one_apply_ne h1.ne]
    · rw [← key i i fun k hk => low i (k.1 + 1) k (Nat.lt_succ_self _) hk]
      simp [upU]
    · rw [low i (j.1 + 1) j (Nat.lt_succ_self _) h1, Matrix.one_apply_ne h1.ne']
  rw [hb1, Matrix.one_mul] at h
  funext ⟨⟨c, a⟩, hac⟩
  have hac' : a < c := hac
  have := congrFun (congrFun h a) c
  simpa [upU, hac'] using this

end GlobalTheory.FlagCell2
end

