module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.CubeConst

section General

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem cubV_through (hG : GlobalFnsSt) (hA : IsAbelianScheme G') {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f F) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L')
    (w : LB.Iso L'.L (L.L.pull F)) (hw : w.IsGen) {T : Over S'} (z : T.left) {J J'} (hJ : Good L.L z J)
    (hJ' : Good L'.L z J') (x y u : T ⟶ G') :
    cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * cubV c' z J' x y u := by
  let Y : Over S' := G' ⊗ G' ⊗ G'
  let H : Over.mk (Y.hom ≫ f) ⟶ G ⊗ G ⊗ G :=
    lift (pushHom gp Y (x3 G' 0)) (lift (pushHom gp Y (x3 G' 1)) (pushHom gp Y (x3 G' 2)))
  have hψ : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ F = H.left ≫ thφ G (x3 G) I := fun I => by
    have e₁ := psum_hom (pushHom gp Y) (x3 G') I.down
    have e₂ := psum_hom (preHom H) (x3 G) I.down
    have e₃ : (fun i => pushHom gp Y (x3 G' i)) = fun i => preHom H (x3 G i) :=
      funext fun i => by fin_cases i <;> simp [preHom, x3, H]
    exact congrArg (fun q => q.left) (e₁.trans ((congrArg (fun q => psum G q I.down) e₃).trans e₂.symm))
  obtain ⟨a, ha, hv⟩ := GlobalTheory.ConstFam.exists_gen_through (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (h := H.left) hw L.isLB L'.isLB hψ c.t c.isGen
  have ev : ∀ {T : Over S'} (z : T.left) {J J'}, Good L.L z J → Good L'.L z J' → ∀ x y u : T ⟶ G',
      cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * val a (lift x (lift y u)).left z J' := by
    intro T z J J' hJ hJ' x y u
    have e := hv _ (lift x (lift y u)).left z J J' hJ hJ'
    refine Eq.trans ?_ (e.trans (congrArg (· * _) (prod_cub x y u (GlobalTheory.ConstFam.wVal w z J J'))))
    let R : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := (Over.map f).map (lift x (lift y u))
    have p : ∀ q : Y ⟶ G', R ≫ pushHom gp Y q = pushHom gp T (lift x (lift y u) ≫ q) := fun q =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    have q : lift (pushHom gp T x) (lift (pushHom gp T y) (pushHom gp T u)) = R ≫ H := by
      simp only [H, comp_lift, p]
      simp [x3]
    exact congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) (congrArg (fun q => q.left) q)
  have sj : Function.Surjective (Y.hom).appTop.hom := by
    have := surj_comp (surj_snd hG hA (G' ⊗ G')) (surj_comp (surj_snd hG hA G') (hG _ _ hA).2)
    rwa [Over.w, Over.w] at this
  have key := gen_unique (φ := thφ G' (x3 G')) (ε := thε) L'.isLB Y.hom
    (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left (Over.w _) sj ha c'.isGen
    (fun y I' hI' => by
      obtain ⟨I, hI⟩ := GlobalTheory.ConstFam.exists_good' L.isLB y
      have E := ev (T := 𝟙_ (Over S')) y hI hI' 1 1 1
      have C : IsCub (cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) y I) := isCub_cubV c hI
      rw [map_one, C.face] at E
      refine Eq.trans ?_ ((isCub_cubV (T := 𝟙_ (Over S')) c' hI').face 1 1).symm
      have fin : ∀ {A U : Type} [Group A] [CommGroup U] (h : A → U) (b : U), 1 = h (1 * 1 * 1) * (h (1 * 1))⁻¹ *
        (h (1 * 1))⁻¹ * (h (1 * 1))⁻¹ * h 1 * h 1 * h 1 * (h 1)⁻¹ * b → b = 1 := fun h b e => by
          simpa using e.symm
      exact fin (fun q : 𝟙_ (Over S') ⟶ G' => GlobalTheory.ConstFam.wVal w y I I' q.left) _ E) _
    (lift x (lift y u)).left z J' hJ'
  exact (ev z hJ hJ' x y u).trans (congrArg _ key)

theorem exists_cube_const {L : RigLB G} (c : CubicalStr G L) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (fr : ∀ a, LB.Gen (LB.LinComb L.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1))) (hfr : ∀ a, (fr a).IsGen) (a a' a'' : Γ') :
    ∃ k : Γ(T.left, ⊤), ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
      (cubV c z J (ρ ≫ pt a) (ρ ≫ pt a') (ρ ≫ pt a'') * ((val (fr (a + a')) ρ.left z J * val (fr (a + a'')) ρ.left z J *
        val (fr (a' + a'')) ρ.left z J * val (fr 0) ρ.left z J) * (val (fr (a + a' + a'')) ρ.left z J *
          val (fr a) ρ.left z J * val (fr a') ρ.left z J * val (fr a'') ρ.left z J)⁻¹)).val = gs ρ.left z ⊤ k := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have g4 := fun b₁ b₂ b₃ b₄ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (hfr b₁) (hfr b₂)) (hfr b₃)) (hfr b₄)
  obtain ⟨k, hk⟩ := H1.exists_const L.L L.isLB (𝟙 T.left) (fun b => ⟨b, rfl⟩) _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen L.L (thφ G (x3 G)) thε c.t c.isGen
      (lift (pt a) (lift (pt a') (pt a''))).left)
      (mulGen_isGen _ _ _ _ _ _ _ (g4 (a + a') (a + a'') (a' + a'') 0)
        (invGen_isGen _ _ _ _ (g4 (a + a' + a'') a a' a'')))) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_cub (pt a) (pt a') (pt a'') h) rfl)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, hadd, h0, zpow_neg, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨k, fun T' ρ z J hJ => ?_⟩
  have e := hk _ ρ.left z J hJ
  rw [Category.comp_id] at e
  refine Eq.trans (congrArg Units.val ?_) e
  have v4 := fun b₁ b₂ b₃ b₄ => (val_mul hJ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (fr b₁) (fr b₂)) (fr b₃)) (fr b₄)
    ρ.left).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_mul hJ _ _ _))))
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (v4 _ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (v4 _ _ _ _))))))).symm

end General

section Torsion

open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

theorem reg_cub {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) {y : T.left} {J}
    (hJ : Good L.L y J) (m₁ m₂ m₃ : T ⊗ A ⟶ A) :
    Reg L.L y J (fun _ _ h => h (m₁ * m₂ * m₃) * (h (m₁ * m₂))⁻¹ * (h (m₁ * m₃))⁻¹ * (h (m₂ * m₃))⁻¹ * h m₁ * h m₂ *
      h m₃ * (h 1)⁻¹) (fun z => cubV c y J (ptSecT A z ≫ m₁) (ptSecT A z ≫ m₂) (ptSecT A z ≫ m₃)) :=
  ⟨_, _, _, _, LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift m₁ (lift m₂ m₃)).left,
    pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub m₁ m₂ m₃ h, fun a => val_cub c (ptSecT A a) hJ _ _ _⟩

theorem cube_torsFrame_pow (hG : GlobalFnsSt) (P : PolAV S) [IsCommMonObj P.A] {rig : LB.Gen (P.L.pull (eSec P.A))}
    {hrig : rig.IsGen} (c : CubicalStr P.A ⟨P.L, rig, P.isLB, hrig⟩) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) {m : ℕ}
    (fr : ∀ a, LB.Gen (LB.LinComb P.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1)))
    (hfr : ∀ a, IsTorsFrame P rig m (pt a) (fr a)) (a a' a'' : Γ') (z : T.left) (J) (hJ : Good P.L z J) :
    (cubV c z J (pt a) (pt a') (pt a'') * ((val (fr (a + a')) (𝟙 _) z J * val (fr (a + a'')) (𝟙 _) z J *
        val (fr (a' + a'')) (𝟙 _) z J * val (fr 0) (𝟙 _) z J) * (val (fr (a + a' + a'')) (𝟙 _) z J *
          val (fr a) (𝟙 _) z J * val (fr a') (𝟙 _) z J * val (fr a'') (𝟙 _) z J)⁻¹)) ^ (m ^ 2) = 1 := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  have rα := Reg.two (y := z) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  obtain ⟨p, hp, hp'⟩ : ∃ p : T ⊗ P.A ⟶ P.A, p ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ p = pt a :=
    ⟨fst T P.A ≫ pt a, by rw [← SymLiftOdd.comp_pow', (hfr a).1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  obtain ⟨q, hq, hq'⟩ : ∃ q : T ⊗ P.A ⟶ P.A, q ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ q = pt a' :=
    ⟨fst T P.A ≫ pt a', by rw [← SymLiftOdd.comp_pow', (hfr a').1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  have r := (((reg_cub c hJ p q (snd T P.A)).pow hJ (m ^ 2)).mul hJ
    (((((rα.pull hJ (p * q)).mul hJ (rα.pull hJ (p * snd T P.A))).mul hJ (rα.pull hJ (q * snd T P.A))).mul hJ
      (rα.pull hJ 1)).mul hJ ((((rα.pull hJ (p * q * snd T P.A)).mul hJ (rα.pull hJ p)).mul hJ (rα.pull hJ q)).mul hJ
        rα).inv)).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, mul_pow, hp, hq, one_pow, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (pt a'') 1
  simp only [MonObj.comp_mul, MonObj.comp_one, pt_snd, hp', hq', _root_.mul_one] at r
  have C : IsCub (cubV c (T := T) z J) := isCub_cubV c hJ
  rw [C.face₃] at r
  have t := fun b => congrArg Additive.ofMul (torsFrame_pow hG P hα (hfr b) hJ)
  have t₁ := t (a + a' + a'')
  have t₂ := t (a + a')
  have t₃ := t (a + a'')
  have t₄ := t (a' + a'')
  have t₅ := t a
  have t₆ := t a'
  have t₇ := t a''
  have t₈ := t 0
  simp only [← hadd] at r
  rw [← h0] at r
  generalize val α (ptSecT P.A 1).left z J = e at t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
  apply Additive.ofMul.injective
  replace r := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at r t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ ⊢
  linear_combination (norm := module) r + t₂ + t₃ + t₄ + t₈ - t₁ - t₅ - t₆ - t₇

end Torsion

theorem exists_frame_cube_const : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  intro g n F W Z i X₁ z₁ act
  have := X₁.ar.ded
  have : IsNoetherianRing X₁.S.R := isNoetherianRing_of_fg X₁.S.fg
  have : IsLocallyNoetherian (Sp X₁.S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.S.R)))
  have := X₁.ρ.P.isAb.comm
  obtain ⟨c₀⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp X₁.S.R) X₁.ρ.P ⟨X₁.ρ.P.L, X₁.ρ.rig, X₁.ρ.P.isLB, X₁.ρ.rig_gen⟩ rfl).1
  choose k hk using exists_cube_const c₀ X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.fr (fun a => (X₁.ρ.fr_tors a).2.1)
  refine ⟨fun a a' a'' => (Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''), fun a a' a'' => ?_, ?_⟩
  · rw [← map_pow]
    refine Eq.trans (congrArg _ (fn_ext (b := 1) fun y _ => ?_)) (map_one _)
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB y
    have e := hk a a' a'' _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at e
    have e' := congrArg Units.val (cube_torsFrame_pow GlobalTheory.firstFiveLaws.1.globalFns X₁.ρ.P c₀ X₁.ρ.pt X₁.ρ.pt_add
      X₁.ρ.fr X₁.ρ.fr_tors a a' a'' y J hJ)
    have e'' := (congrArg (· ^ ((X₁.S.r * X₁.S.N) ^ 2)) e).symm.trans ((Units.val_pow_eq_pow_val _ _).symm.trans e')
    rw [gs_eq _ y ⊤ trivial, ← map_pow, ← map_pow] at e''
    rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_one, map_one]
    exact e''
  intro V _ _ _ ev X _ m t δ 𝔪 x fr hx hfr ρ hρ c a a' a'' z JA hJA
  have := 𝔪.A.isAb.comm
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB z
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have hp : ∀ b, pushHom 𝔪.cart (TFK (R := V) (FractionRing V)) (x b) = U ≫ X₁.ρ.pt b := fun b =>
    Over.OverMorphism.ext (hx b)
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.Poinc.PtAdd.x_add g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx b b' (x b') (hx b')
  have h0 : x 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have e₁ := cubV_through GlobalTheory.firstFiveLaws.1.globalFns 𝔪.A.isAb 𝔪.cart c₀ c 𝔪.wl 𝔪.wl_gen
    (T := TFK (R := V) (FractionRing V)) z hJ hJA (x a) (x a') (x a'')
  rw [hp, hp, hp, ← hadd, ← hadd, ← hadd, ← hadd, ← h0] at e₁
  have e₂ := hk a a' a'' _ U z J hJ
  have e₃ : gs U.left z ⊤ (k a a' a'') = GlobalTheory.UT.cst (FractionRing V) z
      (𝔪.yK ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''))) := by
    refine Eq.trans ?_ (Geo.Tor.cst_comp (𝟙 _) 𝔪.yK z _)
    rw [Category.id_comp]
    exact congrArg (gs (spMap 𝔪.yK) z ⊤) ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom_inv_id_apply _).symm
  have alg : ∀ {R : Type} [CommRing R] {κ : R} {c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ : Rˣ},
      c₀ = w₁ * w₂⁻¹ * w₃⁻¹ * w₄⁻¹ * w₅ * w₆ * w₇ * w₈⁻¹ * c →
      (c₀ * ((g₂ * g₃ * g₄ * g₈) * (g₁ * g₅ * g₆ * g₇)⁻¹)).val = κ →
      w₁ * f₁ = g₁ → w₂ * f₂ = g₂ → w₃ * f₃ = g₃ → w₄ * f₄ = g₄ → w₅ * f₅ = g₅ → w₆ * f₆ = g₆ → w₇ * f₇ = g₇ →
      w₈ * f₈ = g₈ → (c * (f₂ * f₃ * f₄ * f₈)).val = κ * (f₁ * f₅ * f₆ * f₇).val := by
    rintro R _ κ c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
    rw [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact alg e₁ (e₂.trans e₃) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA)

end GlobalTheory.Poinc.CubeConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_theta_local {S : Scheme.{0}} (G : Over S) [GrpObj G] (hA : IsAbelianScheme G)
    (L : LB G.left) (hL : L.IsLB) (U : Type) [CommRing U] [IsLocalRing U] (u : Sp U ⟶ S) (n : ℕ)
    (x : Over.mk u ⟶ G) (hx : x ^ n = 1) : ∃ θ : ThetaGrp G L (n : ℤ) (Over.mk u), θ.pt = x := by
  have := hA.comm
  set a : Over.mk u ⊗ G ⟶ G := fst (Over.mk u) G ≫ x with ha
  set y : Over.mk u ⊗ G ⟶ G := snd (Over.mk u) G with hy
  have cube := GlobalTheory.CubeTop.cubeTheorem S G hA L hL (Over.mk u ⊗ G)
  have key : ∀ m : ℕ, ∃ t : LB.Gen (LB.LinComb L
      ![(a ^ m * y).left, (a ^ m).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left]
      ![1, -1, -(m : ℤ), (m : ℤ), (m : ℤ) - 1, 1 - (m : ℤ)]), t.IsGen := by
    intro m
    induction m with
    | zero =>
      obtain ⟨t, ht⟩ := cube 1 a y
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ 0 * y).left, (a ^ 0).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ) - 1, 1 - ((0 : ℕ) : ℤ)]) (fun V _ g => by
          simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
            Matrix.cons_val_one, pow_zero, _root_.one_mul]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module) t ht
      exact ⟨t', ht'⟩
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨c, hc⟩ := cube (a ^ m) a y
      have e₁ : a ^ m * a * y = a ^ (m + 1) * y := by rw [pow_succ]
      have e₂ : a ^ m * a = a ^ (m + 1) := by rw [pow_succ]
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ (m + 1) * y).left, (a ^ (m + 1)).left, (a * y).left, a.left, y.left,
          (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ) - 1, 1 - ((m + 1 : ℕ) : ℤ)])
        (fun V _ g => by
          rw [Fintype.prod_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Matrix.cons_val_one, e₁, e₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module)
        (LB.mulGen L _ _ _ _ t c) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hc)
      exact ⟨t', ht'⟩
  obtain ⟨t, ht⟩ := key n
  have han : a ^ n = 1 := by rw [ha, ← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := U) L hL (K := Fin 2)
    ![x.left, (1 : Over.mk u ⟶ G).left] ![-(n : ℤ), n]
  have h1 : (fst (Over.mk u) G).left ≫ (1 : Over.mk u ⟶ G).left = (1 : Over.mk u ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk u) G).left ≫ x.left = a.left := rfl
  have h3 : translPt G x = a * y := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (Over.mk u) G).left, (translPt G x).left]) (ε' := ![(n : ℤ), -(n : ℤ)]) (fun V _ g => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, han, h1, h2, h3, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ e (fst (Over.mk u) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.WeilSpecialise

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem unitOn_surjective {R : Type} [CommRing R] : Function.Surjective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective.2

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_specialise : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (Lb : LB G.left), Lb.IsLB → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ (P Q : Over.mk u ⟶ G) (c : Uˣ), P ^ n = 1 → Q ^ n = 1 → ∀ (P' Q' : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), P'.left = spMap (algebraMap U Ω) ≫ P.left → Q'.left = spMap (algebraMap U Ω) ≫ Q.left → Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → ∀ (k : Type) [Field k] (h : U →+* k) (P₀ Q₀ : Over.mk (spMap h ≫ u) ⟶ G), P₀.left = spMap h ≫ P.left → Q₀.left = spMap h ≫ Q.left → Out.WeilIs G Lb n P₀ Q₀ (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω _ _ _ _ _ _ S G _ hA Lb hLb u n _ P Q c hP hQ P' Q' hP' hQ' HΩ k _ h P₀ Q₀ hP₀ hQ₀
  have hG := globalFns_holds
  have loc : ∀ z : Over.mk u ⟶ G, z ^ n = 1 → ∀ p : (Over.mk u).left, ∃ V : (Over.mk u).left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp G Lb (n : ℤ) (overRes V), θ.pt = overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_local G hA Lb hLb U u n z hz
    obtain ⟨θ', h'⟩ := GlobalTheory.CommutatorPairing.exists_pull hLb θ (overResι (⊤ : (Over.mk u).left.Opens))
    exact ⟨⊤, trivial, θ', h'.trans (by rw [hθ])⟩
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hLb (loc P hP) (loc Q hQ)
  obtain ⟨c₁, rfl⟩ := unitOn_surjective c₀
  let iΩ : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ Over.mk u := Over.homMk (spMap (algebraMap U Ω)) rfl
  have eP : P' = iΩ ≫ P := Over.OverMorphism.ext hP'
  have eQ : Q' = iΩ ≫ Q := Over.OverMorphism.ext hQ'
  have H₁ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb iΩ hc₀
  rw [← eP, ← eQ] at H₁
  have H₁' : Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω).toMonoidHom c₁)) := by
    rw [← map_unitOn]; exact H₁
  have e := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLb H₁' HΩ
  have e' := unitOn_inj e
  have hc : c₁ = c := Units.ext (IsFractionRing.injective U Ω (congrArg Units.val e'))
  subst hc
  let ik : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  have eP₀ : P₀ = ik ≫ P := Over.OverMorphism.ext hP₀
  have eQ₀ : Q₀ = ik ≫ Q := Over.OverMorphism.ext hQ₀
  have H₂ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb ik hc₀
  rw [← eP₀, ← eQ₀] at H₂
  have := map_unitOn h c₁
  exact this ▸ H₂

end GlobalTheory.WeilSpecialise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_torAt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  intro V _ _ _ hB G _ _ hG D A U F _ _ _ k z hk hz c
  obtain ⟨hAdm, hChar⟩ := hB
  haveI := hChar
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact zero_ne_one hz
  let u : Fˣ := Units.mk0 z hz0
  let τ : Multiplicative D.toPre.X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hu : u ^ k = 1 := by
    ext; simp [u, hz]
  have hτ : τ ^ k = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    simp only [τ, MonoidHom.comp_apply, zpowersHom_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  obtain ⟨q, hy, hq⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) D.tau_bimult τ hτ
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hAdm D A G hG U F k hk
  refine ⟨f q, τ, q, fun χ => ?_, hy, hq, (hf.1 q (f q)).2 rfl⟩
  simp [τ, u]

end GlobalTheory.Poinc.Sep.Spz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsFiniteExtensionGaloisEquivari
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_labels_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (n : ℕ), OneTrait D.toPre A lab → GalEqN n lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → 1 ≤ n → ∃ lab₁ : Labels D₁.toPre A₁, OneTrait D₁.toPre A₁ lab₁ ∧ GalEqN n lab₁ := by
  intro R _ _ _ hB D A lab n hOne hGal R₁ _ _ _ ρ hρ D₁ hD A₁ a hfib hn
  obtain ⟨hD⟩ := hD
  obtain ⟨_, em, lab₁, hc, hOne₁, hrel⟩ :=
    exists_labels_finExt_emb R hB D A lab hOne R₁ ρ hρ D₁ hD A₁ a hfib
  exact ⟨lab₁, hOne₁, LabBC.galEqN_of_rel ρ hρ D D₁ hD A A₁ a hfib lab n hn hGal em lab₁ hc hrel⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  first | exact @GlobalTheory.Mum.UpExt.torsion_from_closure | exact GlobalTheory.Mum.UpExt.torsion_from_closure | (intros; apply GlobalTheory.Mum.UpExt.torsion_from_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficientsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translated_expansion_coefficients : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.TrCoef.exists_translated_coef | exact GlobalTheory.MumCmp.TrCoef.exists_translated_coef | (intros; apply GlobalTheory.MumCmp.TrCoef.exists_translated_coef <;> assumption)
end

