module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrAll
section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem dvrDataAt_all (hC : Out.CubePullSt) (hU : Out.UnramExtSt) (hB : Out.GtBaseChangeSt) (hS : Y.SplitFibres)
    (h3 : Y.N3) (P : ValPt Y) : DvrDataAt P :=
  dvrData_of_splitting h3 P (splitsAt hC hU hB hS P)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVCat
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem eta_eq_one (M : Over S) [MonObj M] : (η[M] : 𝟙_ (Over S) ⟶ M) = 1 := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem comp_psum {n : ℕ} {T T' : Over S} (g : T' ⟶ T) (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    g ≫ psum G x I = psum G (fun k => g ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    simp only [List.foldr_nil, pzero]
    rw [← Category.assoc, toUnit_unique (g ≫ toUnit T) (toUnit T')]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [padd, padd, ← Category.assoc, comp_lift, ih]

theorem psum_one {n : ℕ} {T : Over S} (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

theorem one_comp_proj_three (k : Fin 3) : (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ x3 G k = 1 := by
  fin_cases k
  · show (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ fst _ _ = 1
    exact MonObj.one_comp _
  · show (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ (snd _ _ ≫ fst _ _) = 1
    rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]
  · show (1 : 𝟙_ (Over S) ⟶ G3 G) ≫ (snd _ _ ≫ snd _ _) = 1
    rw [← Category.assoc, MonObj.one_comp, MonObj.one_comp]

theorem eSec_thφ (I : thK) : eSec (G3 G) ≫ thφ G (x3 G) I = eSec G := by
  show (η[G3 G]).left ≫ (psum G (x3 G) I.down).left = (η[G]).left
  rw [← Over.comp_left, eta_eq_one, eta_eq_one, comp_psum]
  simp only [one_comp_proj_three]
  rw [psum_one]

theorem one_comp_proj_two (k : Fin 2) : (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ x2 G k = 1 := by
  fin_cases k
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ fst _ _ = 1
    exact MonObj.one_comp _
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ snd _ _ = 1
    exact MonObj.one_comp _

theorem lift_one_one : lift (1 : 𝟙_ (Over S) ⟶ G) (lift (1 : 𝟙_ (Over S) ⟶ G) 1) = (1 : 𝟙_ (Over S) ⟶ G3 G) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, MonObj.one_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_snd, lift_fst, Category.assoc, MonObj.one_comp]
    · rw [lift_snd, lift_snd, Category.assoc, MonObj.one_comp]

theorem eSec_face (i : Fin 3) : eSec (G2 G) ≫ (faceMap G i).left = eSec (G3 G) := by
  show (η[G2 G]).left ≫ (faceMap G i).left = (η[G3 G]).left
  rw [← Over.comp_left, eta_eq_one, eta_eq_one]
  congr 1
  have hp : (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ pzero G (G2 G) = 1 := by
    rw [pzero, ← Category.assoc, toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G2 G) ≫ toUnit _) (toUnit _)]; rfl
  fin_cases i
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (pzero G _) (lift (x2 G 0) (x2 G 1)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (x2 G 0) (lift (pzero G _) (x2 G 1)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (x2 G 0) (lift (x2 G 1) (pzero G _)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]

theorem cub_at_one {L : RigLB G} (c : CubicalStr G L) (z : (𝟙_ (Over S)).left) (q₀ : L.L.ι)
    (hq₀ : eSec G z ∈ L.L.U q₀) :
    gm (eSec (G3 G)) z (LB.wchart L.L (thφ G (x3 G)) (fun _ => q₀)) (c.t.s (fun _ => q₀)) = 1 := by
  classical
  let J : ((𝟙_ (Over S)).left ⟶ G.left) → L.L.ι := fun χ =>
    if χ = eSec G then q₀ else (exists_chart L.isLB (χ z)).choose
  have hJ : Good L.L z J := fun χ => by
    by_cases h : χ = eSec G
    · subst h; simp only [J, if_pos rfl]; exact hq₀
    · simp only [J, if_neg h]; exact (exists_chart L.isLB (χ z)).choose_spec
  have hv := val_corr hJ (c.face 0) (eSec (G2 G))
  have hv2 : val (φ := thφ G (x3 G)) (ε := thε) c.t (eSec (G2 G) ≫ (faceMap G 0).left) z J = 1 :=
    (val_pull hJ (φ := thφ G (x3 G)) (ε := thε) c.t (faceMap G 0).left (eSec (G2 G))).symm.trans
      (hv.trans (val_one _))
  have hm : ∀ I, J ((eSec (G2 G) ≫ (faceMap G 0).left) ≫ thφ G (x3 G) I) = q₀ := fun I => by
    rw [eSec_face, eSec_thφ]; simp [J]
  rw [val_of (φ := thφ G (x3 G)) (ε := thε) c.t _ z J (fun _ => q₀) hm, eSec_face] at hv2
  exact hv2

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Units

variable {Y Z W : Scheme.{0}}

theorem appTop_eq_of_gm (τ₁ τ₂ : Z ⟶ Y) (c₁ c₂ : Γ(Y, ⊤)ˣ) (h : ∀ z, gm τ₁ z ⊤ c₁ = gm τ₂ z ⊤ c₂) :
    τ₁.appTop.hom c₁.val = τ₂.appTop.hom c₂.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have h1 := congrArg Units.val (h z)
  unfold gm pullU at h1
  have m1 : τ₁ z ∈ (⊤ : Y.Opens) := trivial
  have m2 : τ₂ z ∈ (⊤ : Y.Opens) := trivial
  rw [dite_eq_left m1, dite_eq_left m2] at h1
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h1
  exact h1

theorem gm_comp_top (r : W ⟶ Z) (τ : Z ⟶ Y) (w : W) (c : Γ(Y, ⊤)ˣ) (c' : Γ(Z, ⊤)ˣ)
    (h : τ.appTop.hom c.val = c'.val) : gm (r ≫ τ) w ⊤ c = gm r w ⊤ c' := by
  apply Units.ext
  unfold gm pullU
  have m1 : (r ≫ τ) w ∈ (⊤ : Y.Opens) := trivial
  have m2 : r w ∈ (⊤ : Z.Opens) := trivial
  rw [dite_eq_left m1, dite_eq_left m2]
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.comp_app,
    CommRingCat.comp_apply]
  rw [← h]
  rfl

theorem exists_ratio {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen)
    (ht' : t'.IsGen) : ∃ ρ : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      val t r z J = gm r z ⊤ ρ * val t' r z J := by
  subst hφ
  obtain ⟨ρ, hρ⟩ := TLinPf.ratio_glue _ (TLinPf.linComb_cover L hL φ ε) t t' ht ht'
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  unfold val
  erw [hρ (fun k => J (r ≫ φ k)), map_mul]
  congr 1
  unfold gm res pullU
  have hm : r z ∈ L.wchart φ (fun k => J (r ≫ φ k)) := by
    unfold LB.wchart
    simp
    exact fun i => hJ (r ≫ φ i)
  rw [dite_eq_left hm, dite_eq_left (show r z ∈ (⊤ : Y.Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  try erw [Function.comp_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_res_apply]

theorem val_charGen {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {L : LB Y} (χ : X)
    (w : W ⟶ (splitTorus S X ⊗ G).left) (z : W) (J : (W ⟶ Y) → L.ι) :
    val (charGen X G L χ) w z J = gm (w ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ) := by
  unfold val gm charGen res pullU
  have hm : w z ∈ L.wchart PEmpty.elim (fun k => J (w ≫ k.elim)) := by
    unfold LB.wchart
    simp
  rw [dite_eq_left hm, dite_eq_left (show (w ≫ (fst (splitTorus S X) G).left) z ∈
    (⊤ : (splitTorus S X).left.Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
    Scheme.Hom.comp_app, CommRingCat.comp_apply]
  erw [Function.comp_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

end Units

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem val_t_act (χ : D.X) {W : Scheme.{0}} (w : W ⟶ (WeightPf.Te D I e ⊗ thickObj R I e G).left) (z : W)
    {J : (W ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (g.t χ) (w ≫ (WeightPf.act g).left) z J =
      gm (w ≫ (fst (WeightPf.Te D I e) (thickObj R I e G)).left) z ⊤ (charUnit _ D.X χ) *
        val (g.t χ) (w ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left) z J := by
  have hc := val_corr hJ (g.t_weight χ) w
  rw [val_pull, val_mul, val_pull, val_charGen] at hc
  · exact hc
  all_goals exact hJ

end Weight

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLie
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Corr

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [Field k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)

abbrev viaT (X : Over (Spec (CommRingCat.of k))) : Over S' := Over.mk (X.hom ≫ tk)

def Rel {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) : Prop :=
  w.left ≫ F = v.left ≫ pullback.fst G.hom g

def liftT {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) : viaT tk Y ⟶ viaT tk X :=
  Over.homMk φ.left (by
    show φ.left ≫ X.hom ≫ tk = Y.hom ≫ tk
    rw [← Category.assoc, Over.w φ])

variable {tk g}

theorem one_left' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left]
  first | rfl | simp

theorem comp_one'' {T : Scheme.{0}} {X Y M : Over T} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc, comp_toUnit]

include hc in
theorem rel_uniq_w {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v) : w = w' := by
  apply Over.OverMorphism.ext
  exact hc.1.hom_ext (h.trans h'.symm) ((Over.w w).trans (Over.w w').symm)

theorem rel_uniq_v {X : Over (Spec (CommRingCat.of k))} {w : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w v') : v = v' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h.symm.trans h'
  · exact (Over.w v).trans (Over.w v').symm

include hc hg in
theorem rel_exists_w {X : Over (Spec (CommRingCat.of k))} (v : X ⟶ (Over.pullback g).obj G) :
    ∃ w : viaT tk X ⟶ G', Rel (F := F) tk g w v := by
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := Over.w v
  refine ⟨Over.homMk (hc.1.lift (v.left ≫ pullback.fst G.hom g) (X.hom ≫ tk) ?_) ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hv, Category.assoc, hg]
  · exact hc.1.lift_snd _ _ _
  · exact hc.1.lift_fst _ _ _

include hc hg in
theorem rel_exists_v {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  refine ⟨Over.homMk (pullback.lift (w.left ≫ F) X.hom ?_) ?_, ?_⟩
  · rw [Category.assoc, hc.1.w, ← Category.assoc, hw, Category.assoc, hg]
  · exact pullback.lift_snd _ _ _
  · exact (pullback.lift_fst _ _ _).symm

def iota2 (hg : tk ≫ f = g) (X : Over (Spec (CommRingCat.of k))) :
    Over.mk (X.hom ≫ g) ⟶ Over.mk ((viaT tk X).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (X.hom ≫ tk) ≫ f = X.hom ≫ g
    rw [Category.id_comp, Category.assoc, hg])

theorem rel_iff {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    show v.left ≫ pullback.fst G.hom g = 𝟙 _ ≫ w.left ≫ F
    rw [Category.id_comp]
    exact h.symm
  · intro h
    have h2 : v.left ≫ pullback.fst G.hom g = 𝟙 _ ≫ w.left ≫ F := congrArg (fun u => u.left) h
    rw [Category.id_comp] at h2
    exact h2.symm

include hc hg in
theorem rel_mul {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  have e := (rel_iff hc hg w v).1 h
  have e' := (rel_iff hc hg w' v').1 h'
  have h1 := (isGrpPullback_pullback G g).2 X v v' (pushPt (isGrpPullback_pullback G g).1.w v)
    (pushPt (isGrpPullback_pullback G g).1.w v') rfl rfl
  have h2 := hc.2 (viaT tk X) w w' (pushPt hc.1.w w) (pushPt hc.1.w w') rfl rfl
  show (w * w').left ≫ F = (v * v').left ≫ pullback.fst G.hom g
  rw [← h1, ← h2, e, e', CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, ← comp_lift,
    Category.assoc]
  exact (Category.id_comp _).symm

include hc hg in
theorem rel_one {X : Over (Spec (CommRingCat.of k))} : Rel (F := F) tk g (1 : viaT tk X ⟶ G') (1 : X ⟶ (Over.pullback g).obj G) := by
  have p1 : ∀ {T : Over S'} {T' : Over S} (e : T' ⟶ Over.mk (T.hom ≫ f)),
      e ≫ pushPt hc.1.w (1 : T ⟶ G') = 1 := by
    intro T T' e
    have hm := hc.2 T 1 1 (pushPt hc.1.w (1 : T ⟶ G')) (pushPt hc.1.w (1 : T ⟶ G')) rfl rfl
    rw [_root_.mul_one] at hm
    have hp : pushPt hc.1.w (1 : T ⟶ G') * pushPt hc.1.w (1 : T ⟶ G') = pushPt hc.1.w (1 : T ⟶ G') :=
      Over.OverMorphism.ext hm
    rw [mul_eq_left] at hp
    rw [hp, comp_one'']
  have p2 : pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) = 1 := by
    have hm := (isGrpPullback_pullback G g).2 X 1 1 (pushPt (isGrpPullback_pullback G g).1.w 1)
      (pushPt (isGrpPullback_pullback G g).1.w 1) rfl rfl
    rw [_root_.mul_one] at hm
    have hp : pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) *
        pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) =
        pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) :=
      Over.OverMorphism.ext hm
    rwa [mul_eq_left] at hp
  exact (rel_iff hc hg _ _).2 (p2.trans (p1 (iota2 hg X)).symm)

include hc hg in
theorem rel_prod : ∀ {N : ℕ} {X : Over (Spec (CommRingCat.of k))} (u : Fin N → (viaT tk X ⟶ G'))
    (u' : Fin N → (X ⟶ (Over.pullback g).obj G)), (∀ i, Rel (F := F) tk g (u i) (u' i)) →
    Rel (F := F) tk g (List.ofFn u).prod (List.ofFn u').prod
  | 0, X, u, u', _ => by simpa using rel_one hc hg (X := X)
  | N + 1, X, u, u', h => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact rel_mul hc hg (h 0) (rel_prod (fun i => u i.succ) (fun i => u' i.succ) fun i => h i.succ)

theorem rel_pre {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) {w : viaT tk X ⟶ G'}
    {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) : Rel (F := F) tk g (liftT tk φ ≫ w) (φ ≫ v) := by
  unfold Rel at h ⊢
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h]
  first | rfl | skip

theorem rel_act (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) {X : Over (Spec (CommRingCat.of k))}
    {w : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) :
    Rel (F := F) tk g (w ≫ a) (v ≫ (Over.pullback g).map b) := by
  unfold Rel at h ⊢
  rw [Over.comp_left, Category.assoc, hab, ← Category.assoc, h, Over.comp_left, Category.assoc,
    Category.assoc]
  congr 1
  exact (pullback.lift_fst _ _ _).symm

end Corr

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

