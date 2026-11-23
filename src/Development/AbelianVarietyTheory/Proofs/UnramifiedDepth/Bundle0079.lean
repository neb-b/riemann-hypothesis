module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CardTorsionOfPolarisedAbelianSchemeLift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem card_torsion_of_isGrpPullback : ∀ (R O C : Type) [CommRing R] [CommRing O] [Field C] [IsAlgClosed C] [Algebra R O] [Algebra O C] [Algebra R C] [IsScalarTower R O C] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : Out.PolAV (Geo.Tor.Sp O)) (ψ : P.A.left ⟶ G.left), Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom (algebraMap R O))) ψ → ∀ n : ℕ, (n : C) ≠ 0 → Nat.card {z : sp (R₀ := R) C ⟶ G // z ^ n = 1} = n ^ (2 * P.g) := by
  intro R O C _ _ _ _ _ _ _ _ G _ _ P ψ h n hn
  let t : Geo.Tor.Sp C ⟶ Geo.Tor.Sp O := Spec.map (CommRingCat.ofHom (algebraMap O C))
  rw [← GlobalTheory.ArcExt.card_torsion GlobalTheory.firstFiveLaws.1 P t hn]
  have hc : t ≫ Spec.map (CommRingCat.ofHom (algebraMap R O)) = (sp (R₀ := R) C).hom := by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [IsScalarTower.algebraMap_eq R O C, CommRingCat.ofHom_comp, Spec.map_comp]
  let ρ : sp (R₀ := R) C ⟶ Over.mk ((Over.mk t).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R O))) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hc)
  let Φ : (Over.mk t ⟶ P.A) →* (sp (R₀ := R) C ⟶ G) :=
    (Geo.Tor.preHom ρ).comp (Geo.Tor.pushHom h (Over.mk t))
  have hΦ : ∀ x, (Φ x).left = x.left ≫ ψ := fun x => Category.id_comp _
  have hb : Function.Bijective Φ := by
    refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm)), fun a => ?_⟩
    · rw [← hΦ, ← hΦ, e]
    · exact ⟨Over.homMk (h.1.lift a.left t ((Over.w a).trans hc.symm)) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext ((hΦ _).trans (h.1.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective Φ hb
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    show _ ↔ e x ^ n = 1
    rw [← map_pow, EmbeddingLike.map_eq_one_iff])).symm

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem exists_gen_theta_tensor_and_finite_flat_surjective_pow :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (M : LB G.left) (Q : LB (G ⊗ G).left), IsAbelianScheme G → M.IsLB → Out.RelAmple G M → Q.IsLB → (∃ θ : LB.Gen (Theta (G ⊗ G) Q), θ.IsGen) ∧ ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 G) ^ n : G ⟶ G).left ∧ Flat ((𝟙 G) ^ n : G ⟶ G).left ∧ Surjective ((𝟙 G) ^ n : G ⟶ G).left := by
  intro R _ G _ _ M Q hG hM hA hQ
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hp := (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ G M hG hM hA R
    (𝟙 _) G.left (𝟙 _) G.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  exact ⟨GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hL R (G ⊗ G)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG)
      (GlobalTheory.AbLaw.isProjBy_tensor R G G hp hp) Q hQ,
    GlobalTheory.MulAmple.finite_flat_surjective_pow hL R G hG M hM hA⟩

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPolarisedAbelianSchemeBaseChangeRingAction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_polBaseChange_oAct : ∀ (T O : Type) [CommRing T] [CommRing O] (io : T →+* O) (P₀ : Out.PolAV (Geo.Tor.Sp T)), ∃ (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ ∧ Geo.Tor.LBIso P.L (P₀.L.pull φ) ∧ P.g = P₀.g ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] (o₀ : P₀.OAct OE), ∃ o : P.OAct OE, ∀ a, (o.act a).left ≫ φ = φ ≫ (o₀.act a).left := by
  intro T O _ _ io P₀
  obtain ⟨P, φ, hφ, hg, hm, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (Geo.Tor.spMap io) P₀
  have gp : Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ := ⟨hφ, fun U x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y),
      ← hm]
    rfl⟩
  exact ⟨P, φ, gp, Geo.Tor.LBIso.symm ⟨t, ht⟩, hg, fun OE _ _ o₀ => Geo.Tor.polOActPull _ _ _ P₀ P φ gp ⟨t, ht⟩ OE o₀⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSiegPre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegelOverLocal

private theorem card_torsion {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (H : Geo.Tor.IsGrpPullback G' G f φ) (T : Over S') (n : ℕ) :
    Nat.card {x : T ⟶ G' // x ^ n = 1} = Nat.card {x : Over.mk (T.hom ≫ f) ⟶ G // x ^ n = 1} := by
  let F₀ : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, H.1.w, ← Category.assoc, Over.w])
  let F : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' F₀ fun x y => Over.OverMorphism.ext (H.2 T x y _ _ rfl rfl).symm
  have hF : Function.Bijective F := by
    refine ⟨fun x y e => Over.OverMorphism.ext (H.1.hom_ext (congrArg CommaMorphism.left e) ?_), fun y => ?_⟩
    · exact (Over.w x).trans (Over.w y).symm
    · exact ⟨Over.homMk (H.1.lift y.left T.hom (Over.w y)) (H.1.lift_snd _ _ _),
        Over.OverMorphism.ext (H.1.lift_fst _ _ _)⟩
  let e := MulEquiv.ofBijective F hF
  exact Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, e.map_eq_one_iff])


open GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm Geo.Tor in
theorem exists_siegPre : ∀ (O : Type) [CommRing O] [IsLocalRing O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → ∀ (o : Type) [CommRing o] (em : o →+* O) (h M : ℕ) (ζ : o) (ze : Oˣ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Geo.Tor.Sp O)) ⟶ P.A)), P.g = h → IsUnit (M : O) → (ze : O) = em ζ → (∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk ze) M) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ M = 1) → (∀ x y, Out.WeilIs P.A P.L M (lev x) (lev y) (Geo.Tor.unitOn (ze ^ Geo.Tor.omegaStd x y))) → ∃ (c : Geo.Tor.SiegPre h M ζ (Geo.Tor.spMap em)) (ψ : c.A ≅ P.A), IsMonHom ψ.hom ∧ c.Principal ∧ Geo.Tor.LBIso c.P ((abelian₂ P.A P.L).pull (lift (fst c.A c.A ≫ ψ.hom) (snd c.A c.A ≫ ψ.hom)).left) := by
  intro O _ _ T _ _ P₀ io P ϕ hpb _ hgg o _ em h k ζ ze lev hg hk hze hprim add tors weil
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  haveI := P.isAb.comm
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have diag := GlobalTheory.SiegelOfTheta.cls_diag hL.globalFns GlobalTheory.AbLaw.CubeAssembly.cube_gen P
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  let c : SiegPre h k ζ (Geo.Tor.spMap em) :=
    { A := P.A
      ab := P.isAb
      P := abelian₂ P.A P.L
      isLB := lam
      rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
      lev := lev
      lev_add := add
      lev_tors := tors
      geom := by
        intro k' _ _ x β z hx hz
        obtain ⟨φ₀, rfl⟩ := Spec.map_surjective x
        let φ : O →+* k' := φ₀.hom
        have hβ : φ.comp em = β := by
          have : CommRingCat.ofHom em ≫ φ₀ = CommRingCat.ofHom β := by
            rw [← Spec.map_inj, Spec.map_comp]; exact hx
          exact congrArg (fun q => q.hom) this
        obtain rfl : z = Units.map φ.toMonoidHom ze := Units.ext (by rw [hz, ← hβ]; simp [hze])
        have hz' : IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k :=
          IsPrimitiveRoot.coe_units_iff.1 (hprim k' φ)
        have hk' : (k : k') ≠ 0 := by rw [← map_natCast φ]; exact (hk.map φ).ne_zero
        have hk₀ : k ≠ 0 := fun e => hk' (by simp [e])
        have W : ∀ a b, Out.WeilIs P.A P.L k (toUnit (Over.mk (Spec.map φ₀)) ≫ lev a) (toUnit _ ≫ lev b)
            (unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b)) := fun a b => by
          have H := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (toUnit (Over.mk (Spec.map φ₀))) (weil a b)
          have e : Units.map (toUnit (Over.mk (Spec.map φ₀))).left.appTop.hom.toMonoidHom
              (unitOn (ze ^ omegaStd a b)) = unitOn (Units.map φ.toMonoidHom (ze ^ omegaStd a b)) :=
            Units.ext (congrArg (fun q => q.hom (ze ^ omegaStd a b).val) (Scheme.ΓSpecIso_inv_naturality φ₀)).symm
          rw [e, map_zpow] at H
          exact H
        have ker : ∀ a, toUnit (Over.mk (Spec.map φ₀)) ≫ lev a = 1 → ∃ b, a = k • b := fun a ha =>
          exists_smul_of_dvd fun b => by
            have w₁ := W a b
            have w₀ := W 0 b
            rw [ha] at w₁
            rw [lev0, MonObj.comp_one] at w₀
            have e := unitOn_inj (CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB w₁ w₀)
            rw [show omegaStd 0 b = 0 by simp [omegaStd], zpow_zero] at e
            exact (hz'.zpow_eq_one_iff_dvd _).1 e
        refine ⟨fun a => ⟨ker a, ?_⟩, onto_torsion hk₀ _ (fun a b => by rw [add, MonObj.comp_mul])
          (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) ker ?_, fun a b => ?_⟩
        · rintro ⟨b, rfl⟩
          have pw : ∀ n : ℕ, lev (n • b) = lev b ^ n := fun n => by
            induction n with
            | zero => rw [zero_smul, pow_zero, lev0]
            | succ n ih => rw [succ_nsmul, add, ih, pow_succ]
          rw [pw, tors, MonObj.comp_one]
        · refine (card_torsion hpb _ k).trans ?_
          refine ((hL.mulN _ P₀ k (Nat.pos_of_ne_zero hk₀)).2.2.2.2 k' _ hk').trans ?_
          rw [← hgg, hg]
          simp [two_mul]
        · have H := GlobalTheory.SiegelOfTheta.weilIs_of_pow hL.globalFns P.isAb P.isLB dg 2 diag (W a b)
          have e : unitOn (Units.map φ.toMonoidHom ze ^ (2 * omegaStd a b)) =
              unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b) ^ 2 := by
            rw [mul_comm, _root_.zpow_mul, zpow_ofNat]
            exact map_pow _ _ _
          rw [e]
          exact H }
  exact ⟨c, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 P.A)),
    ⟨GlobalTheory.SiegelOfTheta.relAmple_of_pow P.isAb P.isLB dg one_le_two diag P.ample,
      fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx⟩,
    lbIso_lam_pull P.isLB _ _ (congrArg₂ _ (Category.comp_id _) (Category.comp_id _))⟩

end GlobalTheory.SiegelOverLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsWeilFunction
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem unitOn_bijective (R : Type) [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.toMulEquiv).bijective

theorem unitOn_mul' {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v :=
  map_mul _ u v

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 :=
  map_one _

theorem exists_weil_function : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)), ∃ e : ℕ → Pts A.A → Pts A.A → Cˣ, ∀ k : ℕ, 1 ≤ k → (∀ z s : Pts A.A, z ^ k = 1 → s ^ k = 1 → ∀ w : Cˣ, Out.WeilIs A.A A.L (k : ℤ) z s (unitOn w) ↔ w = e k z s) ∧ (∀ z z' s : Pts A.A, z ^ k = 1 → z' ^ k = 1 → s ^ k = 1 → e k (z * z') s = e k z s * e k z' s ∧ e k s (z * z') = e k s z * e k s z') ∧ (∀ (l : ℕ) (z s : Pts A.A), 1 ≤ l → z ^ k = 1 → s ^ (k * l) = 1 → e (k * l) z s = e k z (s ^ l)) ∧ ∀ κ : Pts A.A → Cˣ, (∀ z z', z ^ k = 1 → z' ^ k = 1 → κ (z * z') = κ z * κ z') → ∃! s : Pts A.A, s ^ k = 1 ∧ ∀ z, z ^ k = 1 → e k z s = κ z := by
  intro C _ _ _ A
  classical
  have hW : Out.WeilSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.1
  have hP : Out.CharPairSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb := unitOn_bijective C
  have hex : ∀ (k : ℕ) (z s : Pts A.A), ∃ c : Cˣ, z ^ k = 1 → s ^ k = 1 →
      ∀ w : Cˣ, Out.WeilIs A.A A.L (k : ℤ) z s (unitOn w) ↔ w = c := by
    intro k z s
    by_cases h : z ^ k = 1 ∧ s ^ k = 1
    · obtain ⟨c, hc, hu⟩ := (hW _ A k _).1 z s h.1 h.2
      obtain ⟨c', rfl⟩ := hb.2 c
      exact ⟨c', fun _ _ w => ⟨fun hw => hb.1 (hu _ hw), fun hw => hw ▸ hc⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose e he using hex
  have hself : ∀ (k : ℕ) (z s : Pts A.A), z ^ k = 1 → s ^ k = 1 →
      Out.WeilIs A.A A.L (k : ℤ) z s (unitOn (e k z s)) := fun k z s hz hs => (he k z s hz hs _).2 rfl
  have hmk : ∀ (k : ℕ) (z z' : Pts A.A), z ^ k = 1 → z' ^ k = 1 → (z * z') ^ k = 1 := fun k z z' hz hz' => by
    rw [mul_pow, hz, hz', _root_.one_mul]
  have hl : ∀ (k : ℕ) (z z' s : Pts A.A), z ^ k = 1 → z' ^ k = 1 → s ^ k = 1 →
      e k (z * z') s = e k z s * e k z' s := by
    intro k z z' s hz hz' hs
    refine ((he k _ s (hmk k z z' hz hz') hs _).1 ?_).symm
    rw [unitOn_mul']
    exact (hW _ A k _).2.1 _ _ _ _ _ (hself k z s hz hs) (hself k z' s hz' hs)
  have halt : ∀ (k : ℕ) (z : Pts A.A), z ^ k = 1 → e k z z = 1 := by
    intro k z hz
    refine ((he k z z hz hz _).1 ?_).symm
    rw [unitOn_one']
    exact (hW _ A k _).2.2.1 z hz
  have hskew : ∀ (k : ℕ) (z s : Pts A.A), z ^ k = 1 → s ^ k = 1 → e k z s = (e k s z)⁻¹ := by
    intro k z s hz hs
    refine ((he k z s hz hs _).1 ?_).symm
    have h := GlobalTheory.CommPairing.weilIs_symm A.isLB (hself k s z hs hz)
    rwa [show (unitOn (e k s z))⁻¹ = unitOn (e k s z)⁻¹ from (map_inv _ _).symm] at h
  have hr : ∀ (k : ℕ) (z z' s : Pts A.A), z ^ k = 1 → z' ^ k = 1 → s ^ k = 1 →
      e k s (z * z') = e k s z * e k s z' := by
    intro k z z' s hz hz' hs
    rw [hskew k s _ hs (hmk k z z' hz hz'), hl k z z' s hz hz' hs, hskew k s z hs hz, hskew k s z' hs hz',
      mul_inv]
  refine ⟨e, fun k hk => ⟨he k, fun z z' s hz hz' hs => ⟨hl k z z' s hz hz' hs, hr k z z' s hz hz' hs⟩, ?_, ?_⟩⟩
  · intro l z s hl1 hz hs
    have hz' : z ^ (k * l) = 1 := by rw [pow_mul, hz, one_pow]
    have hs' : (s ^ l) ^ k = 1 := by rw [← pow_mul, mul_comm, hs]
    have hu : IsUnit ((k * l : ℕ) : Γ((Over.mk (𝟙 (Sp C)) : Over (Sp C)).left, ⊤)) := by
      have h0 : IsUnit ((k * l : ℕ) : C) := by
        refine IsUnit.mk0 _ ?_
        exact_mod_cast (Nat.mul_pos hk hl1).ne'
      have := h0.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
      rwa [map_natCast] at this
    have h1 := ((hW _ A k _).2.2.2 l s z _ hu hs hz).2 (hself k _ z hs' hz)
    have h2 := (he (k * l) s z hs hz' _).1 (by exact_mod_cast h1)
    rw [hskew _ z s hz' hs, hskew _ z _ hz hs', h2]
  · intro κ hκ
    have hkC : (k : C) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    obtain ⟨b, ⟨hb1, hb2⟩, hbu⟩ := hP C A k hkC (fun x => unitOn (κ x.1)) (fun x y => by
      change unitOn (κ (x.1 * y.1)) = _
      rw [hκ _ _ x.2 y.2, unitOn_mul'])
    refine ⟨b, ⟨hb1, fun z hz => ((he k z b hz hb1 _).1 (hb2 ⟨z, hz⟩)).symm⟩, fun s hs => hbu s ⟨hs.1, fun x => ?_⟩⟩
    exact (he k x.1 s x.2 hs.1 _).2 (hs.2 x.1 x.2).symm

end GlobalTheory.ChTor
end

