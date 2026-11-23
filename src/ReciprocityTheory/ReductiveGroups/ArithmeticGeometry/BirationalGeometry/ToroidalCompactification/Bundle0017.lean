module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MoveQkCore
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

def cU {F : Type} [Field F] (u : F) (hu : u ≠ 0) : Γ(Sp F, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 u hu)

theorem gm_cU {F : Type} [Field F] (u : F) (hu : u ≠ 0) (z : Sp F) : (gm (𝟙 (Sp F)) z ⊤ (cU u hu)).val = toStk z u := by
  simp [gm, cU, toStk, pullU]
  rfl

section Move

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
  {Φ : D'.P.A.left ⟶ D.P.A.left}

end Move

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  have hΔ : IsClosedImmersion (pullback.diagonal s) := inferInstance
  have hi : IsClosedImmersion (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    inferInstance
  have hj : (ι ≫ f) ≫ pullback.diagonal s = ι ≫ pullback.lift f g h := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd, hU]
  have hji : pullback.lift (ι ≫ f) ι hj ≫ pullback.snd (pullback.diagonal s) (pullback.lift f g h) = ι :=
    pullback.lift_snd _ _ _
  have hker : (pullback.snd (pullback.diagonal s) (pullback.lift f g h)).ker = ⊥ := by
    apply le_bot_iff.mp
    have h0 := Scheme.Hom.le_ker_comp (pullback.lift (ι ≫ f) ι hj)
      (pullback.snd (pullback.diagonal s) (pullback.lift f g h))
    rw [hji, (inferInstance : IsSchemeTheoreticallyDominant ι).1] at h0
    exact h0
  have hiso : IsIso (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hc := pullback.condition (f := pullback.diagonal s) (g := pullback.lift f g h)
  have h1 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ f := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.fst s s) hc
  have h2 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ g := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.snd s s) hc
  exact (cancel_epi _).mp (h1.symm.trans h2)

theorem schDom_spec_map {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := φ)).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]; exact bot_le)⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant _


set_option maxHeartbeats 800000 in
theorem over_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {K Y : Over (Spec (CommRingCat.of F))}
    [LocallyOfFiniteType K.hom] [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (u v : K ⟶ Y)
    (h : ∀ p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K, p ≫ u = p ≫ v) : u = v := by
  have hop : IsOpenImmersion (equalizer.ι u v).left := by
    refine MorphismProperty.of_isPullback ((Limits.isPullback_equalizer_prod u v).map (Over.forget _)).flip ?_
    show IsOpenImmersion (prod.lift (𝟙 Y) (𝟙 Y)).left
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ (Over.prodLeftIsoPullback Y Y).hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
    ext1 <;> simp [← Over.comp_left] <;> first | rw [prod.lift_fst, Over.id_left] | rw [prod.lift_snd, Over.id_left]
  have : JacobsonSpace K.left := LocallyOfFiniteType.jacobsonSpace K.hom
  have hcl : closedPoints K.left ⊆ Set.range (equalizer.ι u v).left := by
    intro x hx
    let p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K :=
      Over.homMk (pointOfClosedPoint K.hom x hx) (pointOfClosedPoint_comp K.hom x hx)
    let q := equalizer.lift p (h p)
    let pt : (𝟙_ (Over (Spec (CommRingCat.of F)))).left := IsLocalRing.closedPoint F
    refine ⟨q.left pt, ?_⟩
    have e : q.left ≫ (equalizer.ι u v).left = p.left := by rw [← Over.comp_left, equalizer.lift_ι]
    have e' : (q.left ≫ (equalizer.ι u v).left) pt = p.left pt := by rw [e]
    exact e'.trans (pointOfClosedPoint_apply K.hom x hx pt)
  have hsurj : Function.Surjective (equalizer.ι u v).left := by
    by_contra hns
    obtain ⟨x, hx⟩ := not_forall.1 hns
    have hC : IsClosed (Set.range (equalizer.ι u v).left)ᶜ :=
      (equalizer.ι u v).left.isOpenEmbedding.isOpen_range.isClosed_compl
    obtain ⟨y, hy1, hy2⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hC.isLocallyClosed
    exact hy1 (hcl hy2)
  have : Surjective (equalizer.ι u v).left := ⟨hsurj⟩
  have : IsIso (equalizer.ι u v).left := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hop, this⟩
  have h0 : IsIso ((Over.forget _).map (equalizer.ι u v)) := (inferInstance : IsIso (equalizer.ι u v).left)
  have : IsIso (equalizer.ι u v) := isIso_of_reflects_iso _ (Over.forget _)
  exact (cancel_epi (equalizer.ι u v)).1 (equalizer.condition u v)


open MonObj in
set_option maxHeartbeats 1600000 in
theorem fix_torsion (hMul : Out.MulNSt) {F : Type} [Field F] [IsAlgClosed F] (P : Out.PolAV (Spec (CommRingCat.of F)))
    (M : ℕ) (hM1 : 1 ≤ M) (hM : (M : F) ≠ 0) (σ : P.A ⟶ P.A) [IsMonHom σ]
    (hσ : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A, x ^ M = 1 → x ≫ σ = x)
    (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ σ = x := by
  obtain ⟨-, -, -, het, -⟩ := hMul _ P M hM1
  have hunit : IsUnit ((M : ℕ) : Γ(Spec (CommRingCat.of F), ⊤)) := by
    have e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    have : IsUnit (e.symm (M : F)) := (isUnit_iff_ne_zero.2 hM).map e.symm
    rwa [map_natCast] at this
  have : Etale (Out.mulA P.A M).left := het hunit
  have hpow : ∀ {Z : Over (Spec (CommRingCat.of F))} (z : Z ⟶ P.A), z ^ M = z ≫ Out.mulA P.A M := fun z =>
    (congrArg (· ^ M) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) M z).symm
  have hcomm : σ ≫ Out.mulA P.A M = Out.mulA P.A M ≫ σ := by
    rw [← hpow, Out.mulA, MonObj.pow_comp, Category.id_comp]
  let m := (Out.mulA P.A M).left
  let e := (η[P.A]).left
  let K : Over (Spec (CommRingCat.of F)) := Over.mk (show pullback m e ⟶ Spec (CommRingCat.of F) from pullback.snd m e)
  have hw : pullback.fst m e ≫ P.A.hom = pullback.snd m e := by
    rw [← Over.w (Out.mulA P.A M), ← Category.assoc, pullback.condition, Category.assoc, Over.w η[P.A]]
    exact Category.comp_id _
  have hσm : (pullback.fst m e ≫ σ.left) ≫ m = pullback.snd m e ≫ e := by
    have h1 : σ.left ≫ m = m ≫ σ.left := congrArg CommaMorphism.left hcomm
    have h2 : e ≫ σ.left = e := congrArg CommaMorphism.left (IsMonHom.one_hom σ)
    rw [Category.assoc, h1, ← Category.assoc, pullback.condition, Category.assoc, h2]
  let τ : K ⟶ K := Over.homMk (pullback.lift _ _ hσm) (pullback.lift_snd _ _ _)
  have hKe : Etale K.hom := by show Etale (pullback.snd m e); infer_instance
  have : LocallyOfFinitePresentation K.hom := inferInstance
  have : LocallyOfFiniteType K.hom := inferInstance
  have : FormallyUnramified K.hom := inferInstance
  have hτ : τ = 𝟙 K := by
    refine over_ext_of_points τ (𝟙 K) fun p => ?_
    rw [Category.comp_id]
    ext1
    apply pullback.hom_ext
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.fst m e = p.left ≫ pullback.fst m e
      rw [pullback.lift_fst]
      have hp1 : p.left ≫ pullback.snd m e = 𝟙 _ := Over.w p
      let q : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A := Over.homMk (p.left ≫ pullback.fst m e) (by
        rw [Category.assoc, hw, hp1]; rfl)
      have hq : q ^ M = 1 := by
        rw [hpow]
        ext1
        show (p.left ≫ pullback.fst m e) ≫ m = (toUnit _ ≫ η[P.A]).left
        rw [Category.assoc, pullback.condition, ← Category.assoc, hp1, Category.id_comp, Over.comp_left]
        have : toUnit (𝟙_ (Over (Spec (CommRingCat.of F)))) = 𝟙 _ := Subsingleton.elim _ _
        rw [this, Over.id_left, Category.id_comp]
      have := congrArg CommaMorphism.left (hσ q hq)
      rw [← Category.assoc]
      exact this
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.snd m e = p.left ≫ pullback.snd m e
      rw [pullback.lift_snd]
  have hxm : x.left ≫ m = T.hom ≫ e := by
    have := congrArg CommaMorphism.left ((hpow x).symm.trans hx)
    exact this
  let κ : T ⟶ K := Over.homMk (pullback.lift x.left T.hom hxm) (pullback.lift_snd _ _ _)
  have hτl : pullback.lift _ _ hσm = 𝟙 _ := congrArg CommaMorphism.left hτ
  ext1
  show x.left ≫ σ.left = x.left
  have k1 : x.left = κ.left ≫ pullback.fst m e := (pullback.lift_fst _ _ _).symm
  rw [k1, Category.assoc, ← pullback.lift_fst (pullback.fst m e ≫ σ.left) (pullback.snd m e) hσm, hτl,
    Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

theorem uwRQe_gen {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {Y Y' : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (g : Y' ⟶ Y) (hφ : ∀ k, φ' k = g ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        val t' r z J = val t (r ≫ g) z J := by
  obtain rfl : φ' = fun k => g ≫ φ k := funext hφ
  refine ⟨LB.pullGen L φ ε t g, LB.isGen_pullGen (φ := φ) (ε := ε) (c := t) (hc := ht) (h := g), ?_⟩
  intro Z r z J hg
  first
    | exact val_pull hg t g r
    | exact val_pull t g r

section QkExt

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {F F' : Type} [Field F]
  [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : ∀ r : FractionRing R, f (algebraMap _ F r) = algebraMap _ F' r)

include hf

theorem uwRQe_e : CommRingCat.ofHom (algebraMap (FractionRing R) F) ≫ CommRingCat.ofHom f =
    CommRingCat.ofHom (algebraMap (FractionRing R) F') := by
  ext x
  first
    | exact hf x
    | simpa using hf x

theorem uwRQe_rho_jFK : spMap f ≫ Out.jFK (R := R) F = Out.jFK (R := R) F' := by
  first
    | rw [← Spec.map_comp, uwRQe_e f hf]
    | (simp only [spMap, Out.jFK]; rw [← Spec.map_comp, uwRQe_e f hf])

def uwRQe_rho : Out.TF (R := R) F' ⟶ Out.TF (R := R) F :=
  Over.homMk (spMap f) (by
    show spMap f ≫ (Out.jFK (R := R) F ≫ Out.jK R) = Out.jFK (R := R) F' ≫ Out.jK R
    rw [← Category.assoc, uwRQe_rho_jFK f hf])

theorem uwRQe_cF (χ : D.X) : Out.DegPre.cF D F' χ = uwRQe_rho f hf ≫ Out.DegPre.cF D F χ := by
  first
    | simp [Out.DegPre.cF]
    | (show toUnit _ ≫ D.c χ = uwRQe_rho f hf ≫ toUnit _ ≫ D.c χ
       rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit])

theorem uwRQe_zeroF : Out.DegPre.zeroF D F' = uwRQe_rho f hf ≫ Out.DegPre.zeroF D F := by
  first
    | simp [Out.DegPre.zeroF]
    | (show toUnit _ ≫ η[D.P.A] = uwRQe_rho f hf ≫ toUnit _ ≫ η[D.P.A]
       rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit])

theorem uwRQe_padd (x y : Out.TF (R := R) F ⟶ D.P.A) :
    padd D.P.A (uwRQe_rho f hf ≫ x) (uwRQe_rho f hf ≫ y) = uwRQe_rho f hf ≫ padd D.P.A x y := by
  simp only [padd]
  rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]

theorem uwRQe_gtφ (b : Out.TF (R := R) F ⟶ D.P.A) (χ : D.X) (k : Fin 4) :
    Out.DegPre.gtφ D F' (uwRQe_rho f hf ≫ b) χ k = spMap f ≫ Out.DegPre.gtφ D F b χ k := by
  have e : ∀ m : Out.TF (R := R) F ⟶ D.P.A, (uwRQe_rho f hf ≫ m).left = spMap f ≫ m.left :=
    fun _ => rfl
  fin_cases k
  · change (padd D.P.A (Out.DegPre.cF D F' χ) (uwRQe_rho f hf ≫ b)).left =
      spMap f ≫ (padd D.P.A (Out.DegPre.cF D F χ) b).left
    rw [uwRQe_cF D f hf χ, uwRQe_padd D f hf]
    all_goals exact e _
  · change (Out.DegPre.cF D F' χ).left = spMap f ≫ (Out.DegPre.cF D F χ).left
    rw [uwRQe_cF D f hf χ]
    all_goals exact e _
  · exact e b
  · change (Out.DegPre.zeroF D F').left = spMap f ≫ (Out.DegPre.zeroF D F).left
    rw [uwRQe_zeroF D f hf]
    all_goals exact e _

theorem uwRQe_sgen (g : Out.GtPtF D F) (χ : D.X) :
    ∃ t' : LB.Gen (LB.LinComb D.P.L (Out.DegPre.gtφ D F' (uwRQe_rho f hf ≫ g.b) χ) Out.DegPre.gtε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.TF (R := R) F').left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
        Good D.P.L z J → val t' r z J = val (g.s χ) (r ≫ spMap f) z J :=
  uwRQe_gen D.P.isLB (spMap f) (fun k => uwRQe_gtφ D f hf g.b χ k) (g.s χ) (g.isGen χ)

theorem uwRQe_cub {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (x x' y : Out.TF (R := R) F' ⟶ D.P.A) (u u' v : Out.TF (R := R) F ⟶ D.P.A) (hx : x = uwRQe_rho f hf ≫ u)
    (hx' : x' = uwRQe_rho f hf ≫ u') (hy : y = uwRQe_rho f hf ≫ v) (r : Z ⟶ (Out.TF (R := R) F').left) :
    val (Out.DegPre.cubAt D F' x x' y) r z J = val (Out.DegPre.cubAt D F u u' v) (r ≫ spMap f) z J := by
  subst hx hx' hy
  have e : lift (uwRQe_rho f hf ≫ u) (lift (uwRQe_rho f hf ≫ u') (uwRQe_rho f hf ≫ v)) =
      uwRQe_rho f hf ≫ lift u (lift u' v) := by
    rw [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.comp_lift]
  simp only [Out.DegPre.cubAt]
  rw [e]
  first
    | exact (val_pull D.cub.t _ r).trans ((congrArg (fun q => val D.cub.t q z J)
        (Category.assoc r (spMap f) _).symm).trans (val_pull D.cub.t _ (r ≫ spMap f)).symm)
    | exact (val_pull hJ D.cub.t _ r).trans ((congrArg (fun q => val D.cub.t q z J)
        (Category.assoc r (spMap f) _).symm).trans (val_pull hJ D.cub.t _ (r ≫ spMap f)).symm)

def uwRQe_ext (g : Out.GtPtF D F) : Out.GtPtF D F' where
  b := uwRQe_rho f hf ≫ g.b
  s χ := (uwRQe_sgen D f hf g χ).choose
  isGen χ := (uwRQe_sgen D f hf g χ).choose_spec.1
  s_zero := corr_of_val D.P.isLB fun y J hJ => by
    rw [(uwRQe_sgen D f hf g 0).choose_spec.2 _ _ y J hJ, val_corr hJ g.s_zero, val_one, val_one]
  mult χ χ' := corr_of_val D.P.isLB fun y J hJ =>
    (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) ((uwRQe_sgen D f hf g (χ + χ')).choose_spec.2 _ _ y J hJ)
      (uwRQe_cub D f hf hJ _ _ _ _ _ _ (uwRQe_cF D f hf χ) (uwRQe_cF D f hf χ') rfl (𝟙 _))).trans
      ((val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult χ χ') _).trans ((val_mul hJ _ _ _).trans
        ((congrArg₂ (· * ·) ((uwRQe_sgen D f hf g χ).choose_spec.2 _ _ y J hJ)
          ((uwRQe_sgen D f hf g χ').choose_spec.2 _ _ y J hJ)).symm.trans (val_mul hJ _ _ _).symm)))))

theorem uwRQe_val (g : Out.GtPtF D F) (χ : D.X) {Z : Scheme.{0}} (r : Z ⟶ (Out.TF (R := R) F').left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val ((uwRQe_ext D f hf g).s χ) r z J = val (g.s χ) (r ≫ spMap f) z J :=
  (uwRQe_sgen D f hf g χ).choose_spec.2 Z r z J hJ

theorem uwRQe_isZero {g : Out.GtPtF D F} (h : g.IsZero) : (uwRQe_ext D f hf g).IsZero := by
  unfold Out.GtPtF.IsZero at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun p J hJ => ?_⟩
  · show uwRQe_rho f hf ≫ g.b = _
    rw [h1, uwRQe_zeroF D f hf]
  · rw [uwRQe_val D f hf g χ _ p J hJ, val_corr hJ (h2 χ), val_one, val_one]

theorem uwRQe_isAdd {g g' g'' : Out.GtPtF D F} (h : g.IsAdd g' g'') :
    (uwRQe_ext D f hf g).IsAdd (uwRQe_ext D f hf g') (uwRQe_ext D f hf g'') := by
  unfold Out.GtPtF.IsAdd at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun p J hJ => ?_⟩
  · show uwRQe_rho f hf ≫ g''.b = padd D.P.A (uwRQe_rho f hf ≫ g.b) (uwRQe_rho f hf ≫ g'.b)
    rw [h1, uwRQe_padd D f hf]
  · refine (val_mul hJ _ _ _).trans ?_
    refine Eq.trans ?_ (val_mul hJ _ _ _).symm
    rw [uwRQe_val D f hf g'' χ _ p J hJ, uwRQe_val D f hf g χ _ p J hJ, uwRQe_val D f hf g' χ _ p J hJ]
    refine (congrArg₂ (· * ·) rfl
      (uwRQe_cub D f hf hJ _ _ _ _ _ _ (uwRQe_cF D f hf χ) rfl rfl (𝟙 _))).trans ?_
    exact (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h2 χ) _).trans (val_mul hJ _ _ _))

theorem uwRQe_isIota {y : D.X} {g : Out.GtPtF D F} (h : g.IsIota y) : (uwRQe_ext D f hf g).IsIota y := by
  unfold Out.GtPtF.IsIota at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun p J hJ => ?_⟩
  · show uwRQe_rho f hf ≫ g.b = _
    rw [h1, uwRQe_cF D f hf y]
  · rw [uwRQe_val D f hf g χ _ p J hJ, val_corr hJ (h2 χ)]
    first
      | exact (val_pull _ _ _).trans ((congrArg (fun q => val (D.io y χ) q p J)
          (by rw [Category.assoc, uwRQe_rho_jFK f hf])).trans (val_pull _ _ _).symm)
      | exact (val_pull hJ _ _ _).trans ((congrArg (fun q => val (D.io y χ) q p J)
          (by rw [Category.assoc, uwRQe_rho_jFK f hf])).trans (val_pull hJ _ _ _).symm)

theorem uwRQe_isNsmul {k : ℕ} {g h : Out.GtPtF D F} (H : Out.GtPtF.IsNsmul k g h) :
    Out.GtPtF.IsNsmul k (uwRQe_ext D f hf g) (uwRQe_ext D f hf h) := by
  unfold Out.GtPtF.IsNsmul at H ⊢
  obtain ⟨gs, h0, hs, hl⟩ := H
  exact ⟨fun i => uwRQe_ext D f hf (gs i), uwRQe_isZero D f hf h0, fun i => uwRQe_isAdd D f hf (hs i),
    congrArg (uwRQe_ext D f hf) hl⟩

end QkExt

theorem qkExtExists : QkExtExistsSt := by
  unfold QkExtExistsSt
  intro R _ _ D F F' _ _ _ _ f hf k p
  obtain ⟨h, hn, hi⟩ := p.eq
  refine ⟨⟨p.y, uwRQe_ext D f hf p.g, ⟨uwRQe_ext D f hf h, uwRQe_isNsmul D f hf hn, uwRQe_isIota D f hf hi⟩⟩, ?_⟩
  unfold QkExt
  dsimp only
  refine ⟨rfl, rfl, fun χ => corr_of_val D.P.isLB fun q J hJ => ?_⟩
  rw [uwRQe_val D f hf p.g χ _ q J hJ]
  first
    | exact (val_pull _ _ _).symm
    | exact (val_pull hJ _ _ _).symm

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

