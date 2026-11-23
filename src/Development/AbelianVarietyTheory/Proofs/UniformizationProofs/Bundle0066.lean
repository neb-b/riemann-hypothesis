module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ValueForm

theorem gen_unique_of_injective {X Y Y' S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (ρ : Y' ⟶ Y) (hρ : ∀ U : Y.Opens, Function.Injective (ρ.app U).hom)
    (p : Y' ⟶ S₀) (e : S₀ ⟶ Y') (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (e ≫ ρ) y J = val u' (e ≫ ρ) y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u' hu'
  have key := gen_unique hM p e he hp (DVR.pullGen_isGen _ _ _ _ hu ρ) (DVR.pullGen_isGen _ _ _ _ ht ρ)
    (fun y J hJ => (val_pull hJ _ _ _).trans (((h y J hJ).trans (hv _ _ y J hJ).symm).trans (val_pull hJ _ _ _).symm))
  have e₁ : ∀ j, u.s j = t.s j := fun j => by
    apply Units.map_injective (f := (ρ.app (LB.wchart M φ j)).hom.toMonoidHom) (hρ _)
    refine unit_ext fun y hy => ?_
    choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    have hy' : ρ y ∈ LB.wchart M φ j := hy
    have k := (val_pull hI _ _ _).symm.trans ((key _ (𝟙 Y') y I hI).trans (val_pull hI _ _ _))
    rw [Category.id_comp] at k
    refine (gm_pull (𝟙 Y') ρ y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') ρ y _ hy' _).symm)
    rw [Category.id_comp]
    exact (gen_trans hu ρ y hy' (Good.mem hI φ ρ)).trans ((congrArg _ k).trans
      (gen_trans ht ρ y hy' (Good.mem hI φ ρ)).symm)
  exact (congrArg (gm r z _) (e₁ _)).trans (hv Z r z J hJ)

theorem sym_cub_of_baseChange {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (hi : ∀ U, Function.Injective ((pullback.fst (G3 G).hom f).app U).hom)
    (h3 : Function.Surjective (pullback.snd (G3 G).hom f).appTop.hom) {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : sym.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L))
    (T : Over S) (x y u : T ⟶ G) (z : T.left) (J) (hJ : Good L.L z J) :
    cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J =
      cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J *
        val sym u.left z J := by
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let sy := fun p : G3 G ⟶ G => LB.pullGen L.L _ _ sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hs _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vs : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (sy p) σ.left z J = val sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a⁻¹ b⁻¹ d⁻¹) (sy (a * b)))
    (sy (a * d))) (sy (b * d))
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a b d)
    (sy (a * b * d))) (sy a)) (sy b)) (sy d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a)⁻¹ (σ ≫ b)⁻¹ (σ ≫ d)⁻¹ * val sym ((σ ≫ a) * (σ ≫ b)).left z J *
        val sym ((σ ≫ a) * (σ ≫ d)).left z J * val sym ((σ ≫ b) * (σ ≫ d)).left z J ∧
      val t₂ σ.left z J = cubV c z J (σ ≫ a) (σ ≫ b) (σ ≫ d) * val sym ((σ ≫ a) * (σ ≫ b) * (σ ≫ d)).left z J *
        val sym (σ ≫ a).left z J * val sym (σ ≫ b).left z J * val sym (σ ≫ d).left z J := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul, ← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv,
        ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
  let e : Over.mk f ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  let ρ : T ⟶ G3 G := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique_of_injective L.isLB (fun V _ k => ?_) (pullback.fst (G3 G).hom f) hi (pullback.snd _ _)
      (pullback.lift e.left (𝟙 _) ((Over.w e).trans (Category.id_comp f).symm)) (pullback.lift_snd _ _ _) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _))
        (gs _)) (gs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _)) (gs _)) (gs _)) (gs _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := ((thK ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a b d k) (prod_sym (a * b * d) k))
            (prod_sym a k)) (prod_sym b k)) (prod_sym d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a⁻¹ b⁻¹ d⁻¹ k) (prod_sym (a * b) k))
            (prod_sym (a * d) k)) (prod_sym (b * d) k)).symm)
      simp only [← mul_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val sym (1 : Over.mk f ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI sym (eSec G) _).symm.trans ((val_corr hI hr _).trans (val_one _))
      rw [pullback.lift_fst]
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, e₂]
      simp only [inv_one, _root_.mul_one, s1]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁, r₂] at this

theorem app_generic_injective {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p] (U : Y.Opens) :
    Function.Injective ((pullback.fst p (jK R)).app U).hom := by
  have hd : IsSchemeTheoreticallyDominant (jK R) := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have i : Function.Injective ((jK R).appTop ≫ (Scheme.ΓSpecIso _).hom).hom := by
      rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
      exact (IsFractionRing.injective R (FractionRing R)).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at i
    exact i.of_comp
  have pb := (IsPullback.of_hasPullback p (jK R)).flip
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) := .of_isPullback pb
  have : QuasiCompact (pullback.fst p (jK R)) := inferInstance
  exact (pullback.fst p (jK R)).app_injective U

theorem surjective_cube_baseChange (hG : GlobalFnsSt) {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {A : Over S'}
    [GrpObj A] (hA : IsAbelianScheme A) (gen : (Over.pullback f).obj G ≅ A) :
    Function.Surjective (pullback.snd (G3 G).hom f).appTop.hom := by
  have := hA.comm
  let e : (Over.pullback f).obj (G3 G) ≅ G3 A := (Functor.Monoidal.μIso (Over.pullback f) G (G ⊗ G)).symm ≪≫
    (gen ⊗ᵢ ((Functor.Monoidal.μIso (Over.pullback f) G G).symm ≪≫ (gen ⊗ᵢ gen)))
  have hw : e.hom.left ≫ (G3 A).hom = pullback.snd (G3 G).hom f := Over.w e.hom
  have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have : IsIso e.hom.left.appTop := inferInstanceAs (IsIso (e.hom.left.app ⊤))
  rw [← hw]
  exact surj_comp (ConcreteCategory.bijective_of_isIso e.hom.left.appTop).2 (surjective_cube hG hA)

section Clauses

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

def modelCP (hG : GlobalFnsSt) : CP G where
  L := U.LG
  c := U.cubG
  sym := U.symG
  sym_gen := U.symG_gen
  sym_rig := U.symG_rig
  sym_cub := by
    have := U.smooth
    have : Flat (G3 G).hom := by
      show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
      infer_instance
    exact sym_cub_of_baseChange (jK R) (app_generic_injective _) (surjective_cube_baseChange hG _ A.isAb U.gen)
      U.cubG U.symG U.symG_gen U.symG_rig

theorem rig_val (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) {z : T.left}
    {N : (T.left ⟶ G.left) → U.LG.L.ι} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hN : Good U.LG.L z N) (hJ : Good D.toPre.P.L z J) :
    val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
        (T.hom ≫ thick R I e) z J =
      TorusInvariance.wVal U e z J N (1 : T ⟶ thickObj R I e G).left *
        val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (T.hom ≫ thick R I e) z N := by
  have hp : (T.hom ≫ eSec (thickObj R I e G)) ≫ (U.gt e).pG.left = (T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (T.hom ≫ ·) (UnifPullRig.eSec_pG I (U.gt e))).trans
      (Category.assoc _ _ _).symm)
  have hf : (T.hom ≫ eSec (thickObj R I e G)) ≫ (fstG I e G).left = (T.hom ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (T.hom ≫ ·) (UnifPullRig.eSec_fstG I e G)).trans
      (Category.assoc _ _ _).symm)
  rw [one_left, TorusInvariance.wVal, hp, hf]
  obtain ⟨j, hj⟩ : ∃ j, J ((T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A) = j := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, N ((T.hom ≫ thick R I e) ≫ eSec G) = k := ⟨_, rfl⟩
  have mj : ((T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U j := hj ▸ hJ _
  have mk : ((T.hom ≫ thick R I e) ≫ eSec G) z ∈ U.LG.L.U k := hk ▸ hN _
  rw [val_of _ _ z J (fun _ => j) (fun _ => hj), val_of _ _ z N (fun _ => k) (fun _ => hk), hj, hk]
  have m₁ : T.hom z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U j) hp).mpr mj),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U k) hf).mpr mk)⟩
  have m₂ : T.hom z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => k) := mem_pull.2 mk
  have m₃ : T.hom z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => j) := mem_pull.2 mj
  have W := congrArg (gm T.hom z _) (U.w_rig e (fun _ => j, fun _ => k) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₃ _)).symm.trans (W.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₁ _))
      ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₂ _)))))

theorem compat_val (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (j : D.toPre.P.L.ι)
    (k : U.LG.L.ι) (hj : (U.gt e).pG.left (x z) ∈ D.toPre.P.L.U j) (hk : (fstG I e G).left (x z) ∈ U.LG.L.U k) :
    gw (U.w (e + 1)) (x ≫ thickMap R I e G) z j (fun _ => k) = gw (U.w e) x z j (fun _ => k) := by
  have m₁ : x z ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => j) ⊓
      (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g (x z) ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hj),
      mem_pull.2 ((congrArg (fun g => g (x z) ∈ U.LG.L.U k) (UnifPullRig.thickMap_fstG I e G)).mpr hk)⟩
  have m₂ : x z ∈ (D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓
      (U.LG.L.pull (fstG I e G).left).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  have W := congrArg (gm x z _) (U.w_compat e (fun _ => j, fun _ => k) (_ ⊓ _) inf_le_left inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨m₁, m₂⟩) _).trans (gm_pull _ _ z _ m₁ _)).symm.trans
    (W.trans (gm_res _ z _ (by exact ⟨m₁, m₂⟩) _))

def toPreU (hG : GlobalFnsSt) (hS : IsSemiAbelian G)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) :
    PreU I D.toPre A G where
  semi := hS
  gen := U.gen
  gen_hom := U.gen_hom
  P := modelCP U hG
  wA := w
  wA_gen := hw
  gt := U.gt
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals e T z N J hN hJ W hW := by
    obtain rfl : W = fun x => TorusInvariance.wVal U e z J N x.left := funext hW
    refine ⟨rig_val U e T hN hJ, fun x => TorusInvariance.even_val U x.left hJ hN, fun x y u => ?_⟩
    exact cub_alg ((TorusInvariance.cube_val U ![x, y, u] hJ hN).trans (congrArg₂ (· * ·)
      (TorusInvariance.prod_psum x y u (TorusInvariance.wVal U e z J N)) rfl))
  w_compat := compat_val U

end Clauses

theorem exists_preU_match :
    GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U' : UnifPre I D A G), IsSemiAbelian G → ∀ w : LB.Iso (A.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen → ∃ U : PreU I D.toPre A G, Match U U' ∧ HEq U.wA w :=
  fun hG _ _ _ _ _ _ _ _ _ U' hS w hw =>
    ⟨toPreU U' hG hS w hw, ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩, HEq.rfl⟩

end GlobalTheory.ValueForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaLin

theorem gs_scal_comp {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y)
    (z : Z) (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_linearEquiv {F : Type} [CommRing F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) (pr m : Y ⟶ X) (τ σ : Y ⟶ Y) (hm : τ ≫ pr = m) (h₁ : σ ≫ τ = 𝟙 Y)
    (h₂ : τ ≫ σ = 𝟙 Y) (hq : τ ≫ q = q) (k : ℤ)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![k, -k])) (hu : u.IsGen) :
    ∃ Φ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) ≃ₗ[F]
        SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ v (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval (Φ v).sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := by
  have ex : ∀ v : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∃ w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval w.sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := fun v => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k)
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
          hm, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
      (pullMulSec v.sec τ u hu)
    exact ⟨SecMod.mk q s', fun Z r z J hJ =>
      (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ u hu r z hJ).trans (_root_.mul_comm _ _))⟩
  choose f hf using ex
  have ext : ∀ v w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      (∀ y J, Good L y J → sval v.sec (𝟙 Y) y J = sval w.sec (𝟙 Y) y J) → v = w :=
    fun v w h => SecMod.ext (sec_ext_val hL h)
  let Φ₀ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) →ₗ[F]
      SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) :=
    { toFun := f
      map_add' := fun v w => ext _ _ fun y J hJ => by
        rw [SecMod.sval_add hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_add hJ, mul_add]
      map_smul' := fun c v => ext _ _ fun y J hJ => by
        rw [RingHom.id_apply, SecMod.sval_smul hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_smul hJ,
          gs_scal_comp q (𝟙 Y ≫ τ), Category.assoc, hq, Category.id_comp q, mul_left_comm] }
  refine ⟨LinearEquiv.ofBijective Φ₀ ⟨fun v w h => ext _ _ fun y J hJ => ?_, fun w => ?_⟩, hf⟩
  · have e : f v = f w := h
    have := (hf v _ σ y J hJ).symm.trans (e ▸ hf w _ σ y J hJ)
    rwa [h₁, Units.mul_right_inj] at this
  · have hv := DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _ hu) σ
    have h₃ : σ ≫ m = pr := by rw [← hm, ← Category.assoc, h₁, Category.id_comp]
    obtain ⟨s, hs⟩ := exists_sec (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k) hL (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        h₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv, mul_inv_cancel_left])
      (pullMulSec w.sec σ _ hv)
    refine ⟨SecMod.mk q s, ext _ _ fun y J hJ => (hf _ _ _ y J hJ).trans ?_⟩
    change (val u (𝟙 Y) y J).val * sval s (𝟙 Y ≫ τ) y J = sval w.sec (𝟙 Y) y J
    rw [hs _ _ y J hJ, sval_pullMulSec _ σ _ hv _ y hJ, val_pull hJ, val_inv, Category.assoc, h₂,
      Category.comp_id, mul_left_comm, Units.mul_inv, _root_.mul_one]

section Twist

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sval_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J = (val α r z J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sval (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm

end Twist

section Transl

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem lift_translT {T' : Over S} (ρ : T' ⟶ T) (x : T' ⟶ A) (c : T ⟶ A) :
    lift ρ x ≫ translT A c = lift ρ ((ρ ≫ c) * x) := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]

theorem translT_comp (c d : T ⟶ A) (h : d * c = 1) : translT A c ≫ translT A d = 𝟙 _ := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, lift_translT, e, ← _root_.mul_assoc, ← MonObj.comp_mul, h, MonObj.comp_one, _root_.one_mul,
    lift_fst_snd]

end Transl

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (θ : ThetaGrp P.A P.L (k : ℤ) (Over.mk p)), ∃ Φ : EA P p k ≃ₗ[F] EA P p k, (∀ v, IsActOf P.A P.L (k : ℤ) θ v.sec (Φ v).sec) ∧ (∀ v v', IsActOf P.A P.L (k : ℤ) θ v v' → v' = (Φ (SecMod.mk _ v)).sec) ∧ ∀ (v : EA P p k) (T : Over S) (ρ : T ⟶ Over.mk p) (x : T ⟶ P.A) (z : T.left) (J), Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) (Φ v).sec (lift ρ x).left z J = (val (L := P.L) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)]) θ.φ (lift ρ x).left z J).val * sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := by
  intro S P F _ p k θ
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv (F := F) P.isLB (fst (Over.mk p) P.A).left (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (translT P.A θ.pt⁻¹).left
    (by rw [← Over.comp_left, translT, lift_snd])
    (by rw [← Over.comp_left, translT_comp _ _ _ (mul_inv_cancel _), Over.id_left])
    (by rw [← Over.comp_left, translT_comp _ _ _ (inv_mul_cancel _), Over.id_left])
    (((Over.comp_left _ _ _ _ _).symm.trans (by rw [translT, lift_fst]))) (k : ℤ) θ.φ θ.isGen
  refine ⟨Φ, fun v => isTwistPull_of_sval P.A P.isLB θ.isGen fun y J hJ => hΦ v _ _ y J hJ, fun v v' h => ?_,
    fun v T ρ x z J hJ => ?_⟩
  · exact DVR.SecOps.sec_ext (sec_ext_val P.isLB fun y J hJ =>
      (sval_of_isTwistPull P.A h (𝟙 _) y hJ).trans (hΦ (SecMod.mk _ v) _ _ y J hJ).symm)
  · refine (hΦ v _ _ z J hJ).trans ?_
    rw [← Over.comp_left, lift_translT]
    rfl

end GlobalTheory.ThetaLin

end
end

