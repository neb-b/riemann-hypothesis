module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ObjPull

section Pts

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def pushEquiv (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.ofBijective (pushHom h T)
    ⟨fun x y hxy =>
      Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y])),
    fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem pushEquiv_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') :
    (pushEquiv h T x).left = x.left ≫ φ := rfl

theorem pushEquiv_symm_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : Over.mk (T.hom ≫ f) ⟶ G) :
    ((pushEquiv h T).symm x).left ≫ φ = x.left := by
  rw [← pushEquiv_left h, MulEquiv.apply_symm_apply]

def secPull (h : IsGrpPullback G' G f φ) : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S') ⟶ G') :=
  (pushEquiv h (𝟙_ (Over S'))).symm.toMonoidHom.comp (preHom (toUnit _))

theorem toUnit_left' (T : Over S) : (toUnit T).left = T.hom := by
  have := Over.w (toUnit T)
  exact (Category.comp_id _).symm.trans this

theorem secPull_left (h : IsGrpPullback G' G f φ) (e : 𝟙_ (Over S) ⟶ G) :
    (secPull h e).left ≫ φ = f ≫ e.left := by
  refine (pushEquiv_symm_left h _ _).trans ?_
  show (toUnit _ ≫ e).left = _
  rw [Over.comp_left, toUnit_left']
  exact congrArg (· ≫ e.left) (Category.id_comp f)

theorem pushEquiv_secPull (h : IsGrpPullback G' G f φ) (T : Over S') (e : 𝟙_ (Over S) ⟶ G) :
    pushEquiv h T (toUnit _ ≫ secPull h e) = toUnit _ ≫ e := by
  apply Over.OverMorphism.ext
  rw [pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, secPull_left, toUnit_left', toUnit_left']
  exact (Category.assoc _ _ _).symm

end Pts

def tateMove {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q' ≃* Q)
    (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : TateIso D k Q act e) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn a)
  onto := fun n hn x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm a]
  isom := fun n hn a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn a b)

theorem objPull_of_pol : (∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L')) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) := by
  intro hAb E _ _ _ H D l B B' _ _ b b' j S S' s s' f hρ hζ hs o
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H S', Nonempty (SABMap t' o.t f) := by
    let t := o.t
    have hC := Out.CubePf.cubePull
    have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
      refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
      · have := t.semi.comm
        infer_instance
      · have := t.semi.smooth
        change Smooth (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.separated
        change IsSeparated (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.quasiCompact
        change QuasiCompact (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.geomConnected
        change GeometricallyConnected (pullback.snd t.G.hom f)
        infer_instance
      · intro Ω _ _ q
        obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ f)
        exact ⟨torusExtOfIso (pullCompIso q f t.G) A⟩
    have hp : ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, hsemi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
      have h := isGrpPullback_pullback t.G f
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
      have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
          pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
          (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
        refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
          (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨_, _, _, _, _, m, -⟩ := hp
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  obtain ⟨-, hamp, hk⟩ := hAb S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  refine ⟨{ t := t'
            proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
            ample := hamp o.ample
            ktriv := hk o.ktriv
            eta := fun a => secPull m.cart (o.eta a)
            eta_add := fun a c => by rw [o.eta_add, map_mul]
            eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
            etaA := fun a => secPull m.cart (o.etaA a)
            etaA_add := fun a c => by rw [o.etaA_add, map_mul]
            etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨⟨m, fun a => secPull_left m.cart _, fun a => secPull_left m.cart _⟩⟩⟩
  obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) (β.comp j)
    (by rw [Category.assoc, hs, ← Category.assoc, hx, spMap_comp])
  rw [RingHom.comp_apply, hρ] at hdet
  rw [RingHom.comp_apply, hζ] at hI
  refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
    hI, fun a => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
      GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
    exact hdet τ
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB m.cart hL (Over.mk x) n g g'
      _ _ _ rfl rfl).2 hc
  · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
  · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha))

end GlobalTheory.ObjPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUniformizationIdentityPullback
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem mono_fst_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) :
    Mono (pullback.fst G.hom (thick R I e)) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem corr_pullGen_of_pmaps {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) :
    LB.Gen.Corr L _ _ _ _ a (LB.pullGen L _ _ t h) := by
  subst hF
  refine corr_of_val hL fun z J hJ => ?_
  have hk : ∀ k, (𝟙 Y' ≫ h) ≫ φ k = 𝟙 Y' ≫ φ' k := fun k => by
    rw [Category.assoc, ← hψ k, Category.comp_id]
  have hmem : ∀ k, (𝟙 Y' ≫ φ' k) z ∈ L.U (J (𝟙 Y' ≫ φ' k)) := fun k => hJ _
  have key := hm _ (𝟙 Y') z (fun k => J (𝟙 Y' ≫ φ' k)) (fun k => J (𝟙 Y' ≫ φ' k)) hmem hmem
  rw [Finset.prod_eq_one (fun k _ => by
    rw [hw _ _ z _ _ (hmem k) (hmem k), gm_self hL _ z (hmem k), one_zpow]), _root_.one_mul] at key
  rw [val_pull hJ, val_of t _ z J _ (fun k => congrArg J (hk k))]
  exact key.symm

theorem sameUnif_of_isPullUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre), IsIdPull hD → ∀ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U : Unif I D A G) (U' : Unif I D A G'), bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left → U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom → IsPullUnif (RingHom.id R) hD bc U U' → SameUnif ε U.toUnifPre U'.toUnifPre := by
  intro R _ _ I D A G G' _ _ _ _ ε hD hid bc U U' hF hgen H
  obtain ⟨hx, hΦ, hw₀⟩ := hid
  obtain ⟨wL, hg, he, hr, H⟩ := (isPullUnif_iff_stalks R R I I _ D D hD A A G G' bc U U').1 H
  have hr' := (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
    (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).1 hr
  clear hr he
  generalize bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = F at wL hg hr' H hF
  subst hF
  refine ⟨hgen, wL, ⟨hg, ?_⟩, fun e => ?_⟩
  · have hs := specOf_id R
    rw [hs] at hr'
    exact hr'
  obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
  have hh : h = ((Over.pullback (thick R I e)).map ε.hom).left := by
    have := mono_fst_thick I e G
    rw [← cancel_mono (pullback.fst G.hom (thick R I e))]
    refine hf.trans ?_
    exact (pullback.lift_fst _ _ _).symm
  subst hh
  rw [hΦ, Category.comp_id] at hp
  have hpt : ∀ y, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) y = y := fun y => by
    rw [hΦ]; rfl
  refine ⟨?_, fun χ => ?_, ?_⟩
  · ext1
    have := mono_fst_thick I e D.toPre.P.A
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e))]
    exact hp
  · obtain ⟨hψ, hm⟩ := ht χ
    rw [hx χ] at hψ hm
    exact corr_pullGen_of_pmaps D.toPre.P.isLB hΦ hD.w hw₀ hψ hm
  · intro Z r z jM jL jL' h₁ h₂ h₃
    have key := hw Z r z jM jM jL jL' (by rw [hpt]; exact h₁) h₁ h₂ h₃
    rw [hw₀ _ (r ≫ (U'.gt e).pG.left) z jM jM h₁ h₁, gm_self D.toPre.P.isLB (r ≫ (U'.gt e).pG.left) z h₁,
      _root_.one_mul] at key
    exact key

end GlobalTheory.TorsionFormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

open Topology Filter

theorem t2Space_ptsOver_of_isSeparated {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p] (s : Sp ℂ ⟶ S) :
    T2Space (Points.PtsOver p s) := by
  rw [t2_iff_isClosed_diagonal]
  let h := Points.PtsOver.prodHomeomorph (IsPullback.of_hasPullback p p) s
  have hd : pullback.diagonal p ≫ pullback.fst p p ≫ p = p := by simp
  have hc := (h.isClosedEmbedding.comp
    (Points.PtsOver.isClosedEmbedding_map (pullback.diagonal p) hd s)).isClosed_range
  convert hc using 1
  have key : ∀ x, h (Points.PtsOver.map (pullback.diagonal p) hd s x) = (x, x) := fun x =>
    Prod.ext (Subtype.ext (by simp [h, Points.PtsOver.prodHomeomorph, Points.PtsOver.map, Category.assoc]))
      (Subtype.ext (by simp [h, Points.PtsOver.prodHomeomorph, Points.PtsOver.map, Category.assoc]))
  ext ⟨a, b⟩
  constructor
  · intro hab
    obtain rfl : a = b := hab
    exact ⟨a, key a⟩
  · rintro ⟨x, hx⟩
    rw [Function.comp_apply, key] at hx
    rw [← hx]
    rfl

theorem exists_realLinear_lift {V W Q T : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Group Q] [TopologicalSpace T] [T2Space T] (j : Q → T)
    (hj : Function.Injective j) (e : W → Q) (e₀ : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (he₀ : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e) (Λ : Submodule ℤ W) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hc : Continuous (j ∘ e)) (hc₀ : Continuous (j ∘ e₀)) :
    ∃ L : V →L[ℝ] W, ∀ z, e (L z) = e₀ z := by
  have heq : ∀ z w, e z = e w ↔ z - w ∈ Λ := fun z w => by
    rw [← hk, ← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]
  have : CompactSpace (W ⧸ Λ) := by
    refine ⟨?_⟩
    rw [← (Submodule.mkQ_surjective Λ).range_eq]
    refine IsZLattice.isCompact_range_of_periodic Λ _ Λ.isOpenQuotientMap_mkQ.continuous fun z w hw => ?_
    rw [map_add (f := _), Submodule.mkQ_apply _ w, (Submodule.Quotient.mk_eq_zero Λ).2 hw, add_zero]
  let ē : W ⧸ Λ → T := Quotient.lift (j ∘ e) fun a b hab =>
    congrArg j ((heq a b).2 ((Submodule.quotientRel_def Λ).1 hab))
  have hē : ∀ w, ē (Λ.mkQ w) = j (e w) := fun _ => rfl
  have hemb : IsClosedEmbedding ē := by
    refine (hc.quotient_lift _).isClosedEmbedding fun a b hab => ?_
    obtain ⟨a, rfl⟩ := Λ.mkQ_surjective a
    obtain ⟨b, rfl⟩ := Λ.mkQ_surjective b
    exact (Submodule.Quotient.eq Λ).2 ((heq a b).1 (hj hab))
  choose σ hσ using hs
  let φ : V →+ W ⧸ Λ := AddMonoidHom.mk' (fun z => Λ.mkQ (σ (e₀ z))) fun a b => by
    rw [← map_add (f := _)]
    exact (Submodule.Quotient.eq Λ).2 ((heq _ _).1 (by rw [he, hσ, hσ, hσ, he₀]))
  have hφ : Continuous φ := hemb.isEmbedding.continuous_iff.2 (hc₀.congr fun z => by
    show j (e₀ z) = j (e (σ (e₀ z)))
    rw [hσ])
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_lift (ex := φ) (isDiscrete_ker_mkQ Λ)
    (Λ.isOpenMap_mkQ.nhds_le 0) hφ.continuousAt
  exact ⟨L, fun z => ((heq _ _).2 ((Submodule.Quotient.eq Λ).1 (hL z))).trans (hσ _)⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

def IsExp {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

theorem continuous_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) : Continuous a :=
  Points.continuous_of_differentiableOn fun U f => by simpa using h U f

theorem differentiableAt_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) (U : X.Opens) (f : Γ(X, U)) {z : V} (hz : ⊤ ≤ a z ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (a b) U f) z :=
  (h U f).2.differentiableAt ((h U f).1.mem_nhds ⟨trivial, hz⟩)

theorem IsExp.eq_of_fderiv {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e) {w w' : Fin g → ℂ}
    (h : ∀ (U : G.left.Opens) (f : Γ(G.left, U)), ⊤ ≤ (e 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e z).left U f) 0 w') : w = w' := by
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  refine (he.2.2.2.2 v hv.1).unique hv ⟨hv.1, fun U hU f => (hv.2 U hU f).trans (h U f ?_)⟩
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := hv.1
  rw [← h1]
  exact Points.le_preimage_comp _ _ hU (Points.le_preimage_top _)

theorem map_zero_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 := by
  have := he 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem eq_iff_sub_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  rw [← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]

theorem IsExp.exists_linearEquiv [IsSeparated G.hom] {g g₀ : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ G)} (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t2Space_ptsOver_of_isSeparated G.hom y
  obtain ⟨L, hL⟩ := exists_realLinear_lift (T := Points.PtsOver G.hom y) (fun x : Over.mk y ⟶ G => ⟨x.left, Over.w x⟩)
    (fun a b hab => Over.OverMorphism.ext (congrArg Subtype.val hab)) e e₀ he.1 ha he.2.1 Λ hk
    ((continuous_of_isHolTo he.2.2.1).subtype_mk _) ((continuous_of_isHolTo hh).subtype_mk _)
  have hsm : ∀ (c : ℂ) z, L (c • z) = c • L z := fun c z => he.eq_of_fderiv fun U f hU => by
    have h0 : (e₀ 0).left = (e 0).left := by rw [map_zero_of_add ha, map_zero_of_add he.1]
    have d := (differentiableAt_of_isHolTo he.2.2.1 U f hU).hasFDerivAt.restrictScalars ℝ
    have d₀ := (differentiableAt_of_isHolTo hh U f (z := 0) (by simpa only [h0] using hU)).hasFDerivAt.restrictScalars ℝ
    rw [← L.map_zero] at d
    have d₁ := d.comp 0 L.hasFDerivAt
    rw [L.map_zero] at d₁
    have e₁ : (fun b => valAt' (e b).left U f) ∘ L = fun b => valAt' (e₀ b).left U f := by
      funext b
      simp only [Function.comp_apply, hL]
    rw [e₁] at d₁
    have k := fun x => DFunLike.congr_fun (d₁.unique d₀) x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at k
    rw [k, map_smul, map_smul, k]
  have hi : Function.Injective L := realLinear_injective_of_countable_ker L.toLinearMap
    (hc.mono fun x (hx : L x = 0) => by
      show e₀ x = 1
      rw [← hL, hx, map_zero_of_add he.1])
  have hsu : Function.Surjective L := realLinear_surjective_of_mod_countable L.toLinearMap (Γ := Λ)
    (Set.countable_coe_iff.1 (inferInstanceAs (Countable Λ))) fun w => by
      obtain ⟨x, hx⟩ := hs (e w)
      exact ⟨x, (hk _).1 ((eq_iff_sub_of_add he.1 _ _).1 (hx.symm.trans (hL x).symm))⟩
  exact ⟨LinearEquiv.ofBijective ⟨⟨L, L.map_add⟩, hsm⟩ ⟨hi, hsu⟩, hL⟩

end GlobalTheory.UnifPoint
end
end

