module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistWeightWellDefinedOnLatticeClass
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.WtWd

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkSub : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Y) (𝔪 : UMem X₁ z₁ act V ev Y t δ) (p p' : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N)) (x x' : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), p.y = p'.y → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p x → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p' x' → ∃ q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N), q.y = 0 ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q (x * x'⁻¹) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev Y _ m t δ 𝔪 p p' x x' hp hx hx'
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hB := 𝔪.D.tau_bimult
  obtain ⟨f, hto, -, -, hadd, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have e := (hto p x).1 hx
  have e' := (hto p' x').1 hx'
  have h0 : f (GlobalTheory.TorusExt.qkZero hB _ _) = 1 := by
    have := hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB (GlobalTheory.TorusExt.qkZero hB (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
      (GlobalTheory.TorusExt.qkZero hB _ _))
    rw [show GlobalTheory.TorusExt.qkAdd hB (GlobalTheory.TorusExt.qkZero hB (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
        (GlobalTheory.TorusExt.qkZero hB _ _) = GlobalTheory.TorusExt.qkZero hB _ _ from
      GlobalTheory.TorusExt.qk_ext (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkZero]) (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkZero])] at this
    exact left_eq_mul.1 this
  have hneg : f (GlobalTheory.TorusExt.qkNeg hB p') = (f p')⁻¹ := by
    have := hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB p' (GlobalTheory.TorusExt.qkNeg hB p'))
    rw [show GlobalTheory.TorusExt.qkAdd hB p' (GlobalTheory.TorusExt.qkNeg hB p') = GlobalTheory.TorusExt.qkZero hB _ _ from
      GlobalTheory.TorusExt.qk_ext (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, GlobalTheory.TorusExt.qkZero])
        (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, GlobalTheory.TorusExt.qkZero]), h0] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  refine ⟨GlobalTheory.TorusExt.qkAdd hB p (GlobalTheory.TorusExt.qkNeg hB p'), ?_, ?_⟩
  · simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, hp]
  · rw [hto, hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB _ _), hneg, e, e']

section
variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {Y : Type} [AddCommGroup Y] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ Y} (𝔪 : UMem X₁ z₁ act V ev Y t δ)

theorem yy_sub {a a' : X₁.S.Gam} {mu : Fin 8 → Y} (h : 𝔪.YY a mu) (h' : 𝔪.YY a' mu) : 𝔪.YY (a - a') 0 := by
  obtain ⟨p, x, hp, hx, hxa⟩ := h
  obtain ⟨p', x', hp', hx', hxa'⟩ := h'
  obtain ⟨q, hq, hqx⟩ := qkSub g n F W Z i X₁ z₁ act V ev Y m t δ 𝔪 p p' x x' (hp.trans hp'.symm) hx hx'
  refine ⟨q, x * x'⁻¹, by rw [hq, map_zero], hqx, ?_⟩
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      T.hom ≫ spMap 𝔪.yK := by
    simp [T, spMap, jFK, ← Spec.map_comp]
  let U : Over.mk (T.hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) := Over.homMk (T.hom ≫ spMap 𝔪.yK) (by simp)
  have hU : ∀ (b : X₁.S.Gam) (y : T ⟶ 𝔪.A.A),
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt b).left →
      pushHom 𝔪.cart T y = U ≫ X₁.ρ.pt b := fun b y hy => by
    apply Over.OverMorphism.ext
    show y.left ≫ 𝔪.φ = (U ≫ X₁.ρ.pt b).left
    rw [Over.comp_left, hy, e2]
    rfl
  have hpt : X₁.ρ.pt (a - a') = X₁.ρ.pt a * (X₁.ρ.pt a')⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← X₁.ρ.pt_add, sub_add_cancel]
  have key : pushHom 𝔪.cart T (x * x'⁻¹) = U ≫ X₁.ρ.pt (a - a') := by
    rw [map_mul, map_inv, hU a x hxa, hU a' x' hxa', hpt]
    show _ = preHom U _
    rw [map_mul, map_inv]
    rfl
  have e3 := congrArg (fun z => z.left) key
  rw [e2]
  exact e3.trans (Over.comp_left _ _ _ U _)

end

theorem wt_wd : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : (Fin 8 → Y1) → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  intro g n F W Z i X₁ z₁ act x₀ hD V1 _ _ _ ev1 Y1 _ m1 t1 δ1 𝔪1 sg τ hτ
  classical
  refine ⟨fun mu => if h : ∃ a, 𝔪1.YY a mu then (sg : ℤ) • eStd X₁.S.g _ τ h.choose else 0, ?_⟩
  intro a mu hY
  have h : ∃ a, 𝔪1.YY a mu := ⟨a, hY⟩
  simp only [dif_pos h]
  congr 1
  have hd := yy_sub 𝔪1 h.choose_spec hY
  have hH : h.choose - a ∈ X₁.S.HH X₁.M z₁ :=
    (_root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i X₁ z₁ act x₀ hD V1 ev1 Y1 m1 t1 δ1 𝔪1 _).2 hd
  have h0 : eStd X₁.S.g _ τ (h.choose - a) = 0 := hτ _ hH
  have hs : eStd X₁.S.g _ τ (h.choose - a) = eStd X₁.S.g _ τ h.choose - eStd X₁.S.g _ τ a := by
    simp only [eStd, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Poinc.Sep.WtWd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairs
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.Pair

theorem exists_ext {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    (hf : Function.Injective f) :
    ∃ j : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing V), Ext f j := by
  let g : R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) _).comp ((algebraMap V (FractionRing V)).comp f)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective.comp
      ((IsFractionRing.injective V (FractionRing V)).comp hf)
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) := (IsFractionRing.lift hg).toAlgebra
  refine ⟨(IsAlgClosed.lift : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R]
    AlgebraicClosure (FractionRing V)).toRingHom, fun r => ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap]
  rfl

theorem sq {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) (hj : Ext f j) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (hκ : κ ≫ jK R = jK V ≫ spMap f) :
    spMap j ≫ jFK (R := R) F₀ = jFK (R := V) F ≫ κ := by
  haveI : Mono (jK R) :=
    haveI := IsPreimmersion.of_isLocalization (R := CommRingCat.of R) (S := CommRingCat.of (FractionRing R))
      (nonZeroDivisors R)
    inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  rw [← cancel_mono (jK R), Category.assoc, Category.assoc, hκ]
  simp only [jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

end GlobalTheory.TInj.Pair

theorem GlobalTheory.TInj.pull_pair_match : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → J.map f₁ ≤ maximalIdeal V → J.map f₂ ≤ maximalIdeal V → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap f₁ → κ₂ ≫ jK R = jK V ≫ spMap f₂ → κ₁ ≫ y₀ = κ₂ ≫ y₀ → ∃ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ ∧ Ext f₂ j₂ ∧ Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ p₀ : QkPt D₀.toPre (AlgebraicClosure (FractionRing R)) n, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) := by
  intro X g n B _ ζ sX c hζ hn R _ _ _ J hJ D₀ A₀ G₀ _ _ U₀ hG₀ y₀ α₀ hO V _ _ _ _ hV f₁ f₂ hf₁ hf₂ hJ₁ hJ₂
    κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, hD₁, A₁, U₁, hG₁, hU₁, tr₁⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₁ hf₁ hJ₁
  obtain ⟨D₂, hD₂, A₂, U₂, hG₂, hU₂, tr₂⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₂ hf₂ hJ₂
  obtain ⟨α₁, hO₁, hα₁⟩ := _root_.GlobalTheory.TInj.overPt_genPull c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₁ D₁ hD₁ A₁ U₁ hU₁ y₀ α₀ hO κ₁ hκ₁
  obtain ⟨α₂, hO₂, hα₂⟩ := _root_.GlobalTheory.TInj.overPt_genPull c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₂ D₂ hD₂ A₂ U₂ hU₂ y₀ α₀ hO κ₂ hκ₂
  rw [← hy] at hO₂
  obtain ⟨b, φ, hM, hQ⟩ := GlobalTheory.T.two_trait_uniformisations_matching_data c V hV D₁ A₁ _ U₁ D₂ A₂ _ U₂ hG₁ hG₂ (κ₁ ≫ y₀) α₁ α₂ hO₁ hO₂
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.TInj.Pair.exists_ext f₁ hf₁
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.TInj.Pair.exists_ext f₂ hf₂
  refine ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ, hj₁, hj₂, hM, fun p₀ => ?_⟩
  obtain ⟨x₀, hx₀, hpow⟩ := (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv R J hJ D₀ A₀ G₀ U₀ hG₀ (AlgebraicClosure (FractionRing R)) n hn).1 p₀
  obtain ⟨l, hl⟩ := _root_.GlobalTheory.TInj.torsion_isLev c hζ A₀.A y₀ α₀ hO.1 (AlgebraicClosure (FractionRing R))
    (jFK (R := R) (AlgebraicClosure (FractionRing R))) x₀ hpow
  obtain ⟨p₁, x₁, hy₁, hT₁, hq₁, hc₁⟩ := tr₁ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₁ hj₁ n hn p₀ x₀ hx₀
  obtain ⟨p₂, x₂, hy₂, hT₂, hq₂, hc₂⟩ := tr₂ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₂ hj₂ n hn p₀ x₀ hx₀
  have e₁ := hα₁ _ x₁.left (spMap j₁ ≫ x₀.left) (hc₁.trans (Category.assoc _ _ _).symm)
  have e₂ := hα₂ _ x₂.left (spMap j₂ ≫ x₀.left) (hc₂.trans (Category.assoc _ _ _).symm)
  have s₁ := GlobalTheory.TInj.Pair.sq f₁ j₁ hj₁ κ₁ hκ₁
  have s₂ := GlobalTheory.TInj.Pair.sq f₂ j₂ hj₂ κ₂ hκ₂
  have key : x₁.left ≫ α₁ = x₂.left ≫ α₂ := by
    rw [e₁, e₂, Category.assoc, Category.assoc, hl, ← Category.assoc, ← Category.assoc (spMap j₂), s₁, s₂,
      Category.assoc, Category.assoc, ← Category.assoc κ₁, ← Category.assoc κ₂, hy]
  exact ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ n hn p₁ p₂ x₁ x₂ hq₁ hq₂ key⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedInnerProductDataDefiniteBottomLargeGri
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem mem_bottomPairFinitePlacesBelow_of_mem_exceptional {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {v : FinPl D} (hv : v ∈ G.pl.S0) : v ∈ sfB G t := by
  classical
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl GlobalTheory.ChiGrid.Places.W0
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨_, hw, G.pl.under_w hv⟩

theorem under_mem_sfB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ locPl G t) : w.under (𝓞 D.host.F) ∈ sfB G t := by
  classical
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨w, hw, rfl⟩

theorem unrOff_betaB_div_alphaB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)
    {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) :
    GlobalTheory.LFun.UnrOff (betaB G i j / alphaB Lc i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) := by
  classical
  intro w hw
  have hw' : w.under (𝓞 D.host.F) ∉ sfB G t := hw
  have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
  have hQ : ∀ P ∈ Lc.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
    hw' (e ▸ under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hv)
  have hμ0 : GlobalTheory.LFun.UnrAt (Lc.mu0 ((j : ℕ) + 1)) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 ((Lc.C.isMu0 j).unr w fun k hk => hv ?_)
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  have hξ : GlobalTheory.LFun.UnrAt (Lc.xi t) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hn
    rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ w hq rfl
    · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
  have e : betaB G i j / alphaB Lc i j t = G.ch.chi (D.R.m - i) * (Lc.mu0 ((j : ℕ) + 1) * Lc.xi t)⁻¹ := by
    unfold betaB alphaB
    rw [mul_div_mul_right_eq_div, div_eq_mul_inv]
    rfl
  rw [e]
  exact hχ.mul (hμ0.mul hξ).inv

theorem isSphOff_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : HSp D) (sS : RealMat S) (sT : RealMat T)
    (BS : RealMat S) (BT : RealMat T) (LS : Lat S) (LT : Lat T) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsVacO ψ θ S T sS sT LS LT f₀) {e : AE D} {Pset : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Pset)
    (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T LS LT fun _ => True) 1 f₀ Φ f)
    (Sf : Finset (FinPl D)) (hP : ∀ PP ∈ Pset, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sf)
    (hpt : ∀ φ, IsFockVec ψ θ S T sS sT (pureTensorO ψ θ S T sS sT BS BT f φ)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  GlobalTheory.FockSph.isLatVac_pureTensorO_off hvac.2.inf BS BT hvac he hth Sf hP (fun φ => (hpt φ).1) φ

theorem unram_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, Unram W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) X.rA.Λ X.rW.Λ (GlobalTheory.BottomIPData.sfB G t) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W i j A A' WW X hX t P
  have h := isBottomTri_is hX
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (h.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (h.rigW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst t) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock τ)
  have hpt := GlobalTheory.FockSph.isFockVec_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) (sS := fun τ => -X.rA.s τ) (sT := X.rW.s)
    hψ hθ cS cT X.rA.B X.rW.B hf hv
  have hs := isSphOff_pureTensorO (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.rA.Λ X.rW.Λ
    h.isVac (h.idem t) (h.fst t) (sfB G t) (fun PP hPP => under_mem_sfB G t hPP) hpt P
  exact ⟨GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1, h.rigW.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2,
    unrOff_betaB_div_alphaB G hL i j t, hs, hs⟩

end GlobalTheory.BottomIPData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZConn

theorem preconnectedSpace_of_isLocalRing (Z : Scheme.{0}) [IsLocalRing Γ(Z, ⊤)] : PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, hes⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z s hs
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    rw [← hes, Z.basicOpen_of_isUnit hu]
    simp
  · left
    have h0 : e = 0 := by
      have : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he, sub_self]
      exact hu.mul_left_eq_zero.1 this
    rw [← hes, h0, Z.basicOpen_zero]
    simp

theorem exists_complete_flat (R : Type) [CommRing R] [IsNoetherianRing R] (P : PrimeSpectrum R) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A) (φ : R →+* A),
      IsAdicComplete (maximalIdeal A) A ∧ φ.Flat ∧ (maximalIdeal A).comap φ = P.asIdeal := by
  let L := Localization.AtPrime P.asIdeal
  have fg : (maximalIdeal L).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal L) L) := AdicCompletion.isLocalRing_of_fg fg
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal L) L) := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let ψ := algebraMap L (AdicCompletion (maximalIdeal L) L)
  haveI : IsLocalHom ψ := ((IsLocalRing.local_hom_tfae ψ).out 1 3).mpr hm.symm.le
  refine ⟨AdicCompletion (maximalIdeal L) L, inferInstance, inferInstance, hloc, ψ.comp (algebraMap R L), ?_, ?_, ?_⟩
  · rw [hm]; exact AdicCompletion.isAdicComplete_self _ fg
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap ψ]
    exact Localization.AtPrime.under_maximalIdeal

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsLocallyNoetherian Y → IsProper a →
    (∀ V : Y.Opens, Function.Bijective (a.app V).hom) → ∀ y : Y, _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y a hY ha hbij y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsNoetherianRing Γ(Y, U) := hY.component_noetherian ⟨U, hU⟩
  let e := hU.isoSpec
  let P : PrimeSpectrum Γ(Y, U) := e.hom ⟨y, hyU⟩
  obtain ⟨A, _, _, _, φ, hAc, hφ, hφP⟩ := exists_complete_flat Γ(Y, U) P
  let π : (a ⁻¹ᵁ U).toScheme ⟶ Sp Γ(Y, U) := (a ∣_ U) ≫ e.hom
  let g : Sp A ⟶ Sp Γ(Y, U) := Spec.map (CommRingCat.ofHom φ)
  haveI : Flat g := HasRingHomProperty.Spec_iff.2 hφ
  haveI : IsProper π := inferInstance
  have hres : Function.Bijective ((a ∣_ U).app ⊤).hom := by
    rw [morphismRestrict_app]
    have h1 := hbij ((Scheme.Opens.ι U) ''ᵁ ⊤)
    have h2 := ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage a U ⊤)).op)
    exact h2.comp h1
  have hπ : Function.Bijective π.appTop.hom := by
    change Function.Bijective ((a ∣_ U) ≫ e.hom).appTop.hom
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    haveI : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact hres.comp (ConcreteCategory.bijective_of_isIso _)
  have hp := _root_.GlobalTheory.Mum.app_bijective_of_flat_baseChange Γ(Y, U) _ _ _ π g (pullback.snd π g) (pullback.fst π g) inferInstance inferInstance hπ
    inferInstance (IsPullback.of_hasPullback π g).flip
  let Z : Scheme.{0} := pullback π g
  let ψ : A →+* Γ(Z, ⊤) :=
    ((pullback.snd π g).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Bijective ψ := (hp ⊤).comp (ConcreteCategory.bijective_of_isIso _)
  haveI : Nontrivial Γ(Z, ⊤) := hψ.1.nontrivial
  haveI : IsLocalHom ψ := IsLocalHom.of_surjective ψ hψ.2
  haveI : IsLocalRing Γ(Z, ⊤) := IsLocalRing.of_surjective ψ hψ.2
  haveI : PreconnectedSpace Z := preconnectedSpace_of_isLocalRing Z
  have hfib := _root_.GlobalTheory.ClosedFibreConn.isPreconnected_closedFibre A hAc Z (pullback.snd π g) inferInstance inferInstance
  have hg : g (closedPoint A) = P := PrimeSpectrum.ext hφP
  have einj : Function.Injective e.hom := e.hom.isOpenEmbedding.injective
  have key : {x : X | a x = y} = (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) '' {z | pullback.snd π g z = closedPoint A} := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ a ⁻¹ᵁ U := by
        show a x ∈ U
        rw [hx]; exact hyU
      let x' : (a ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
      have h1 : (a ∣_ U) x' = ⟨y, hyU⟩ := Subtype.ext ((morphismRestrict_base_coe a U x').trans hx)
      have h2 : π x' = g (closedPoint A) := by
        rw [hg]
        change ((a ∣_ U) ≫ e.hom) x' = P
        rw [Scheme.Hom.comp_apply, h1]
      obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback π g) x' (closedPoint A) h2
      refine ⟨z, hz2, ?_⟩
      rw [Scheme.Hom.comp_apply, hz1]
      rfl
    · rintro ⟨z, hz, rfl⟩
      have h3 : π (pullback.fst π g z) = g (pullback.snd π g z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [hz, hg] at h3
      have h4 : (a ∣_ U) (pullback.fst π g z) = ⟨y, hyU⟩ := einj (by
        rw [← Scheme.Hom.comp_apply]; exact h3)
      show a ((pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) z) = y
      rw [Scheme.Hom.comp_apply]
      change a (pullback.fst π g z).1 = y
      rw [← morphismRestrict_base_coe a U, h4]
  rw [key]
  exact hfib.image _ (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι).continuous.continuousOn

end GlobalTheory.ZConn
end

