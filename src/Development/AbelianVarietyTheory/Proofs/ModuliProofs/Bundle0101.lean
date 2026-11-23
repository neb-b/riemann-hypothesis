module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ZM.SiegPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lbIso_pull_comp {X Y Y' : Scheme.{0}} {L : LB X} {A : LB Y} {F : Y ⟶ X} (H : LBIso A (L.pull F))
    (h : Y' ⟶ Y) : LBIso (A.pull h) (L.pull (h ≫ F)) := by
  refine LBIso.chartPull (chartPullPull A h h rfl) ⟨id, fun J x hx => ?_, fun y J J' hJ hJ' => ?_⟩ H
  · have hx' := (mem_pull (F := h ≫ F)).1 hx
    exact (mem_pull (F := F)).2 hx'
  · have a1 := (mem_pull (F := h ≫ F)).1 hJ
    have a2 := (mem_pull (F := h ≫ F)).1 hJ'
    rw [gm_pull_g L (h ≫ F) (𝟙 Y') y J J' hJ hJ', Category.id_comp]
    exact (gm_pull_g L F h y J J' ((mem_pull (F := F)).2 a1) ((mem_pull (F := F)).2 a2)).symm

theorem exists_isSquare {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (w : φ ≫ G.hom = G'.hom ≫ f) :
    ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ := by
  let T : Over S := Over.mk ((G' ⊗ G').hom ≫ f)
  have w₁ : ((fst G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (fst G' G')]
    rfl
  have w₂ : ((snd G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (snd G' G')]
    rfl
  let x : T ⟶ G := Over.homMk ((fst G' G').left ≫ φ) w₁
  let y : T ⟶ G := Over.homMk ((snd G' G').left ≫ φ) w₂
  refine ⟨(lift x y).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Over.comp_left, lift_snd]
    rfl

theorem isSquare_tensor {G G' : Over S} (φ : G' ⟶ G) : IsSquare φ.left (φ ⊗ₘ φ).left := by
  constructor
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem isSquare_comp {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  constructor
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem isSquare_unique {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') (e : φ = φ') : φ₂ = φ₂' := by
  subst e
  have w : φ₂' ≫ (G ⊗ G).hom = φ₂ ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, h'.1, ← Category.assoc, h.1]
  let a : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let b : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' w
  have hab : a = b := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (fst G G).left = φ₂' ≫ (fst G G).left
      rw [h.1, h'.1]
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (snd G G).left = φ₂' ≫ (snd G G).left
      rw [h.2, h'.2]
  exact congrArg (fun m => m.left) hab

theorem lbIso_lam_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (h : IsGrpPullback G' G f φ)
    (hw : LBIso L' (L.pull φ)) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain ⟨w, hw'⟩ := hw
  have hP : PGen w := by
    unfold PGen gw
    intro Y g y j j' k k' h1 h2 h3 h4
    have m1 : g y ∈ (L.pull φ).U (fun _ => j) := (mem_pull (F := φ)).2 h1
    have m2 : g y ∈ (L.pull φ).U (fun _ => j') := (mem_pull (F := φ)).2 h2
    have hV : g y ∈ (L.pull φ).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull φ).U (fun _ => j') ⊓ L'.U k') :=
      ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
    have e := congrArg (gm g y _) (hw' (fun _ => j, k) (fun _ => j', k'))
    unfold LB.div at e
    simp only [map_mul, map_inv] at e
    simp only [gm_res g y _ hV] at e
    rw [gm_pull_g L φ g y (fun _ => j) (fun _ => j') m1 m2] at e
    exact e
  have e : ∀ I : ULift (Finset (Fin 2)),
      (psum G' (x2 G') I.down).left ≫ φ = φ₂ ≫ (psum G (x2 G) I.down).left := by
    let T : Over S' := G' ⊗ G'
    have hj : φ₂ ≫ (G ⊗ G).hom = T.hom ≫ f := by
      rw [← Over.w (fst G G), ← Category.assoc, hs.1, Category.assoc, h.1.w, ← Category.assoc,
        Over.w (fst G' G')]
    let U : Over S := Over.mk (T.hom ≫ f)
    let j : U ⟶ G ⊗ G := Over.homMk φ₂ hj
    have hΦ : ∀ u : T ⟶ G', (u.left ≫ φ) ≫ G.hom = U.hom := fun u => by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u]
      rfl
    let Φ : (T ⟶ G') → (U ⟶ G) := fun u => Over.homMk (u.left ≫ φ) (hΦ u)
    have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y =>
      Over.OverMorphism.ext (h.2 T x y (Φ x) (Φ y) rfl rfl).symm
    let Φh : (T ⟶ G') →* (U ⟶ G) := MonoidHom.mk' Φ Φmul
    have key : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), Φ u = j ≫ v → u.left ≫ φ = φ₂ ≫ v.left :=
      fun u v hh => congrArg (fun m => m.left) hh
    have key' : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), u.left ≫ φ = φ₂ ≫ v.left → Φ u = j ≫ v :=
      fun u v hh => Over.OverMorphism.ext (by exact hh)
    have base : ∀ k : Fin 2, Φ (x2 G' k) = j ≫ x2 G k := by
      intro k
      fin_cases k
      · exact key' _ _ hs.1.symm
      · exact key' _ _ hs.2.symm
    have fold : ∀ l : List (Fin 2),
        Φ (List.foldr (fun k acc => padd G' (x2 G' k) acc) (pzero G' (G2 G')) l) =
          j ≫ List.foldr (fun k acc => padd G (x2 G k) acc) (pzero G (G2 G)) l := by
      intro l
      induction l with
      | nil =>
        change Φh 1 = j ≫ 1
        rw [map_one, comp_one]
      | cons k l ih =>
        change Φ (x2 G' k * _) = j ≫ (x2 G k * _)
        rw [Φmul, comp_mul, base k, ih]
    intro I
    exact key _ _ (fold _)
  exact LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ₂ _ e) (iso_linComb hP _ _)

end GlobalTheory.ZM.SiegPull


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.WeilFieldExt

open GlobalTheory.CommPairing ReciprocityTheory.ChartRestriction.G.Out

theorem corr_of_val_epi {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (q : Y' ⟶ Y) [Epi q]
    (hq : ∀ U : Y.Opens, Function.Injective (q.app U).hom)
    (h : ∀ y J, Good L y J → val t q y J = val t' q y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have inj : Function.Injective (pullU q (LB.wchart L φ j ⊓ LB.wchart L φ' j')) := fun a b e =>
    Units.ext (hq _ (congrArg Units.val e))
  apply inj
  refine unit_ext fun y hy => ?_
  have hy' : q y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hy
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun k => q ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    intro a b e
    have e := (cancel_epi q).1 e
    rcases a with a | a <;> rcases b with b | b
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy'.1 a, Set.mem_iInter.1 hy'.2 a])
  have := h y J hJ
  rw [val_of t _ y J j (fun k => e (.inl k)), val_of t' _ y J j' (fun k => e (.inr k))] at this
  exact (gm_id_pull q y _ hy' _).trans ((gm_res _ y _ hy' _).trans (this.trans
    ((gm_res _ y _ hy' _).symm.trans (gm_id_pull q y _ hy' _).symm)))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  refine (IsPullback.of_right (h₁₁ := (h ▷ A).left) (v₁₁ := pullback.fst T'.hom A.hom)
    (h₁₂ := pullback.snd T.hom A.hom) (v₁₂ := pullback.fst T.hom A.hom) (h₂₁ := h.left) (h₂₂ := T.hom)
    (v₁₃ := A.hom) ?_ ?_ (IsPullback.of_hasPullback T.hom A.hom).flip)
  · have e : (h ▷ A).left ≫ pullback.snd T.hom A.hom = pullback.snd T'.hom A.hom :=
      congrArg (fun q => q.left) (whiskerRight_snd h A)
    rw [e, Over.w h]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  · exact congrArg (fun q => q.left) (whiskerRight_fst h A)

theorem commIsOf_descend (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    [Epi (h ▷ A).left] (hq : ∀ U, Function.Injective ((h ▷ A).left.app U).hom)
    {θx θy : ThetaGrp A L k T} {a b : ThetaGrp A L k T'} (ha : a.pt = h ≫ θx.pt) (hb : b.pt = h ≫ θy.pt)
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k a b (Units.map h.left.appTop.hom.toMonoidHom c)) :
    CommIsOf A L k θx θy c := by
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1
    (commIsOf_change globalFns_holds hA hL (hx.trans ha.symm) (hy.trans hb.symm) H)
  refine corr_of_val_epi hL (h ▷ A).left hq fun z J hJ => ?_
  have key : ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (h ▷ A).left z J =
        tval θ (h ▷ A).left z J * tval θ' ((h ▷ A).left ≫ (translT A θ.pt).left) z J := fun θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ (h ▷ A).left z J * ·) (val_pull hJ _ _ _))
  have e := H' _ (𝟙 _) z J hJ
  have t : ∀ x : T ⟶ A, (𝟙 _ ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (h ▷ A).left ≫ (translT A x).left := fun x => by
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (𝟙 _ ≫ (fst T' A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom c) =
      gm ((h ▷ A).left ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull (𝟙 _ ≫ (fst T' A).left) h.left z ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t, g, Category.id_comp] at e
  exact (key θx θy).trans (e.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key θy θx) (H1.val_constGen L c _ z J))).symm)

theorem weilIs_iff (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} [Unique T.left] (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k x y c ↔
      ∃ θx θy : ThetaGrp A L k T, θx.pt = x ∧ θy.pt = y ∧ CommIsOf A L k θx θy c := by
  constructor
  · intro H
    obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H default
    obtain rfl : V = ⊤ := eq_top_iff.2 fun p _ => by rwa [Unique.eq_default p]
    let s : T ⟶ overRes (⊤ : T.left.Opens) := Over.homMk T.left.topIso.inv (by
      show T.left.topIso.inv ≫ T.left.topIso.hom ≫ T.hom = T.hom
      rw [Iso.inv_hom_id_assoc])
    have w : s.left ≫ (⊤ : T.left.Opens).ι = 𝟙 _ := T.left.topIso.inv_hom_id
    have w' : s ≫ overResι ⊤ = 𝟙 T := Over.OverMorphism.ext w
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL s (hc θx θy hx hy)
    rw [hx, ← Category.assoc, w', Category.id_comp] at ha
    rw [hy, ← Category.assoc, w', Category.id_comp] at hb
    have e : Units.map s.left.appTop.hom.toMonoidHom (unitRes ⊤ c) = c := by
      apply Units.ext
      have := congrArg (fun q => q.appTop.hom c.val) w
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
      exact this
    rw [e] at H'
    exact ⟨a, b, ha, hb, H'⟩
  · rintro ⟨θx, θy, rfl, rfl, H⟩ p
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
    exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
      commIsOf_change globalFns_holds hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

theorem exists_lift_descend (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    (hd : ∀ M : LB (T ⊗ A).left, M.IsLB → (∃ t : (M.pull (h ▷ A).left).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (x : T ⟶ A) (a : ThetaGrp A L k T') (ha : a.pt = h ≫ x) : ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  obtain ⟨t, ht⟩ := hd (thetaLB A L k x) (DVR.linComb_isLB L hL _ _)
    (gen_chartPull (chartPullOut L ![(snd T A).left, (translPt A x).left] ![k, -k] (h ▷ A).left
      ![(snd T' A).left, (translPt A a.pt).left] (fun i => by
        fin_cases i
        · exact (congrArg (fun q => q.left) (whiskerRight_snd h A)).symm
        · show (translPt A a.pt).left = (h ▷ A).left ≫ (translPt A x).left
          rw [← Over.comp_left, whisker_translPt, ha])) a.φ a.isGen)
  exact ⟨⟨x, t, ht⟩, rfl⟩

theorem unitOn_map {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    unitOn (Units.map i.toMonoidHom c) = Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) := by
  apply Units.ext
  exact congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))

end GlobalTheory.WeilFieldExt

namespace GlobalTheory


open WeilFieldExt CommPairing in
theorem weilIs_fieldExt_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  intro S G _ K Ω _ _ i x L k y y' c hG hL
  rw [unitOn_map]
  let h : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  refine ⟨fun H => ?_, fun H => weilIs_pull globalFns_holds hG hL h H⟩
  letI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum K))
  letI : Unique (Over.mk (spMap i ≫ x)).left := inferInstanceAs (Unique (PrimeSpectrum Ω))
  obtain ⟨a, b, ha, hb, Hc⟩ := (weilIs_iff hG hL _ _ _).1 H
  have pb : IsPullback (h ▷ G).left (fst _ G).left (fst _ G).left (spMap i) := isPullback_whisker h
  obtain ⟨e, -, -, -, inj⟩ := (FieldBaseChange.epi_and_isMonHom_iff K Ω i).1 _ _ _ _ _ pb
  have hd := (_root_.GlobalTheory.lb_gen_iso_descend_field K Ω i _ _ _ _ _
    (by have := hG.smooth; exact inferInstanceAs (Smooth (pullback.fst x G.hom)))
    (by have := hG.proper; exact inferInstanceAs (IsProper (pullback.fst x G.hom)))
    (by have := hG.geomConnected; exact inferInstanceAs (GeometricallyConnected (pullback.fst x G.hom))) pb).1
  obtain ⟨θ, rfl⟩ := exists_lift_descend hL h hd y a ha
  obtain ⟨θ', rfl⟩ := exists_lift_descend hL h hd y' b hb
  exact (weilIs_iff hG hL _ _ _).2 ⟨θ, θ', rfl, rfl, commIsOf_descend hG hL h inj ha hb Hc⟩

end GlobalTheory
end
end

