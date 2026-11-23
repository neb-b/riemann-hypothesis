module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHkIsogEtaleUnique
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePointLaw

open GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_objMap_comp {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
    [IsAlgClosed k] [CharZero k]
    {o o₁ o₂ : Obj D l b s} {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ l.M') {C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)}
    (hC : ∀ x ∈ C, x ^ p ^ 2 = 1) {ψ₁ : o.t.G ⟶ o₁.t.G} {ψ₂ : o.t.G ⟶ o₂.t.G} (h₁ : IsHeckeIsog o o₁ p C ψ₁)
    [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left] (h₂ : IsHeckeIsog o o₂ p C ψ₂) :
    ∃ m : ObjMap o₁ o₂ (𝟙 _), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hfacts := obj_isAbelianScheme_dim_rigidified_sym
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
  obtain ⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩ := h₂
  obtain ⟨hab, hdim, -, -⟩ := hfacts E H D l B b _ s o
  obtain ⟨hab₁, hdim₁, -, -⟩ := hfacts E H D l B b _ s o₁
  obtain ⟨hab₂, hdim₂, -, -⟩ := hfacts E H D l B b _ s o₂
  let P := polOf o.t o.proper o.ample o.ktriv hdim
  let P₁ := polOf o₁.t o₁.proper o₁.ample o₁.ktriv hdim₁
  let P₂ := polOf o₂.t o₂.proper o₂.ample o₂.ktriv hdim₂
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, hα⟩ := exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)
  have homα : IsMonHom α := hL.rigidity _ _ _ hab₁ hab₂ α (by
    rw [← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  let ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  have hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    lam_iso_of_weil_pairings hL k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by
      have lift := exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)
      obtain ⟨x₀, tx, ex⟩ := lift x hx
      obtain ⟨y₀, ty, ey⟩ := lift y hy
      obtain rfl : x₀ ≫ ψ₁ = x := ex
      obtain rfl : y₀ ≫ ψ₁ = y := ey
      obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P n _).1 x₀ y₀ tx ty
      obtain ⟨c₀, rfl⟩ := (unitOn_bijective k).2 c₀
      have e : c = c₀ ^ p ^ 2 := (unitOn_bijective k).1
        (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))
      have w := weil₂ n x₀ y₀ c₀ hc hc₀
      rw [← hα, ← Category.assoc, ← Category.assoc, ← e] at w
      rw [pow_one]
      exact w
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have := mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv
  have : IsIso α := isIso_of_mono α hab₂.smooth fun y => by
    obtain ⟨x, rfl⟩ := sur₂ y
    exact ⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }, congrArg (fun q => q.left) hα⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

theorem exists_transfer_fst
    {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} (u : Obj D l b sX) {k : Type} [Field k]
    {s : Sp k ⟶ Sp B} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      e.hom ≫ pullback.fst _ _ = m.toSABMap.φ ∧
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c => weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart
      ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, m.cart.1.isoPullback_hom_fst, m.cart.1.isoPullback_hom_snd, fun x => ?_,
    fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

theorem exists_etale_isHkIsog (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (hC : Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C) :
    ∃ (y₁ : Sp k ⟶ Xo.X) (ψ₁ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
      (f₁ : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G)),
      IsHkIsog p y y₁ C ψ₁ f₁ ∧ IsFinite ψ₁ ∧ Etale ψ₁ ∧ Surjective ψ₁ ∧
      ∀ y₂ ψ₂ f₂, IsHkIsog p y y₂ C ψ₂ f₂ → y₂ = y₁ ∧ ψ₂ ≫ pullback.fst _ _ = ψ₁ ≫ pullback.fst _ _ := by
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hComp := ObjMaps.id_comp_cancel
  obtain ⟨c₁, c₂, c₃, c₄, c₅, -⟩ := hC
  have : CharZero k := charZero_of_injective_ringHom (Spec.preimage (y ≫ Xo.s)).hom.injective
  have pull : ∀ y' : Sp k ⟶ Xo.X, y' ≫ Xo.s = y ≫ Xo.s →
      ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') := fun y' h =>
    obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
      (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  obtain ⟨o, ⟨m⟩⟩ := pull y rfl
  obtain ⟨ρ, e, -, e₁, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_fst Xo.univ m
  let C' : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G) := C.comap ρ.toMonoidHom
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun _ => Iff.rfl
  obtain ⟨hC', o₁, ψ₁, h₁, hfin, het, hsur⟩ := exists_isHeckeIsog hL obj_isAbelianScheme_dim_rigidified_sym
    (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL)
    (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale o 𝔓 p h𝔓 hco hp
    hp𝔓 hpM C' (fun x hx a => (mem _).2 (by rw [e₃]; exact c₁ _ hx a))
    (fun J hJ x hx => c₂ J hJ fun a ha => (e₃ a x).symm.trans (by rw [hx a ha, map_one]))
    (fun x hx a ha => ρ.injective ((e₃ a x).trans ((c₃ hx a ha).trans (map_one ρ).symm)))
    (fun x hx x' hx' => by
      have := (e₄ ((p : ℤ) ^ 2) x x' 1).2
        ((congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) (ρ x) (ρ x')) unitOn_one).mpr (c₄ _ hx _ hx'))
      rw [Nat.cast_pow]
      exact (congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) x x') unitOn_one).mp this)
    ((Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)).trans c₅)
  obtain ⟨y₁, ⟨hy₁, ⟨m₁⟩⟩, huniq⟩ := Xo.rep _ (y ≫ Xo.s) inferInstance o₁
  obtain ⟨ρ₁, f, f₀, f₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_fst Xo.univ m₁
  have h₁' := h₁
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁'
  let σ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ ψ₁) := fun x => congrArg (fun z => ρ₁ (z ≫ ψ₁)) (ρ.symm_apply_apply x)
  refine ⟨y₁, e.inv ≫ ψ₁.left ≫ f.hom, ψp, ⟨hy₁, ?_, fun x => ?_, fun a x => ?_, fun z => ?_,
    Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩, inferInstance, inferInstance,
    inferInstance, ?_⟩
  · rw [Category.assoc, Category.assoc, f₁, Over.w, Iso.inv_comp_eq, e₁]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [hψ, e₂, f₂, Category.assoc, Iso.hom_inv_id_assoc, Over.comp_left, Category.assoc]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, lin₁, Category.assoc]
  · obtain ⟨z, rfl⟩ := ρ₁.surjective z
    obtain ⟨x, rfl⟩ := sur₁ z
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, ker₁, mem]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    exact (f₄ _ _ _ _).1 (weil₁ n x x' c hn ((e₄ _ _ _ _).2 h))
  · rw [← e₅, ← e₆, hψ, hψ, (lev₁ p' hp' a).1, (lev₁ p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩
  · rintro y₂ ψ ψq ⟨hy₂, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩
    obtain ⟨o₂, ⟨m₂⟩⟩ := pull y₂ hy₂
    obtain ⟨ρ₂, r, r₀, r₁, r₂, r₃, r₄, r₅, r₆⟩ := exists_transfer_fst Xo.univ m₂
    let ψ₂ : o.t.G ⟶ o₂.t.G := Over.homMk (e.hom ≫ ψ ≫ r.inv) (by
      rw [← r₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, g₁, e₁])
    have hψ : ∀ x, ρ₂ (x ≫ ψ₂) = ψq (ρ x) := fun x => fibPt_injective _ (by
      rw [r₂, ← g₂, e₂]
      show (x.left ≫ e.hom ≫ ψ ≫ r.inv) ≫ r.hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hab := isAbelianScheme_of_proper o.t o.proper
    have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
    have := o₂.proper
    have one : ∀ (G : Over (Sp k)) [GrpObj G], (1 : 𝟙_ (Over (Sp k)) ⟶ G) = η[G] := fun G _ => by
      rw [Hom.one_def]; simp
    have h₂ : IsHeckeIsog o o₂ p C' ψ₂ := by
      refine ⟨hL.rigidity _ _ _ hab hab₂ ψ₂ ?_, fun a => hom_ext_pts hab.smooth fun x => ρ₂.injective ?_,
        fun z => ?_, fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ⟨ρ₂.injective ?_, ρ₂.injective ?_⟩⟩
      · rw [← one, ← one]
        exact ρ₂.injective (by rw [hψ, map_one, map_one, map_one])
      · rw [← Category.assoc, ← Category.assoc, hψ, r₃, hψ, e₃, g₃]
      · obtain ⟨x, hx⟩ := g₄ (ρ₂ z)
        obtain ⟨x, rfl⟩ := ρ.surjective x
        exact ⟨x, ρ₂.injective ((hψ x).trans hx)⟩
      · rw [mem, ← g₅, MonoidHom.mem_ker, ← hψ, map_eq_one_iff _ ρ₂.injective]
      · refine (r₄ _ _ _ _).2 ?_
        rw [hψ, hψ]
        exact g₆ n _ _ c hn ((e₄ _ _ _ _).1 h)
      · rw [hψ, e₅, r₅]; exact (g₇ p' hp' a).1
      · rw [hψ, e₆, r₆]; exact (g₇ p' hp' a).2
    obtain ⟨m', hm'⟩ := exists_objMap_comp hp hpM hC' h₁ h₂
    obtain ⟨m'', hm''⟩ := ((hComp E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y₂ (𝟙 _) m₂).1 m'
    have hy : 𝟙 _ ≫ y₂ = y₁ := huniq _ ⟨by rw [Category.id_comp, hy₂], ⟨m''⟩⟩
    refine ⟨(Category.id_comp _).symm.trans hy, ?_⟩
    have hφ : m''.toSABMap.φ = m₁.toSABMap.φ := by
      clear_value ψp σ
      subst hy
      exact objMap_unique_of_field hL.serre m'' m₁
    rw [Category.assoc, Category.assoc, f₀, ← hφ, hm'', reassoc_of% hm', ← r₀]
    show _ = e.inv ≫ (e.hom ≫ ψ ≫ r.inv) ≫ _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem isHkIsog_etale_unique (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    {k : Type} [Field k] [IsAlgClosed k] {y y₁ : Sp k ⟶ Xo.X} {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)}
    (hC : Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C)
    {ψ₁ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁}
    {f₁ : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G)} (h₁ : IsHkIsog p y y₁ C ψ₁ f₁) :
    (IsFinite ψ₁ ∧ Etale ψ₁ ∧ Surjective ψ₁) ∧
      (∀ y₂ ψ₂ f₂, IsHkIsog p y y₂ C ψ₂ f₂ → y₂ = y₁) ∧ ∀ ψ₂ f₂, IsHkIsog p y y₁ C ψ₂ f₂ → ψ₂ = ψ₁ := by
  obtain ⟨y₀, ψ₀, f₀, h₀, a, b, c, hu⟩ := exists_etale_isHkIsog Xo h𝔓 hco hp hp𝔓 hpM y C hC
  obtain ⟨rfl, -⟩ := hu _ _ _ h₁
  have key : ∀ ψ₂ f₂, IsHkIsog p y y₁ C ψ₂ f₂ → ψ₂ = ψ₀ := fun ψ₂ f₂ h₂ =>
    pullback.hom_ext (hu _ _ _ h₂).2 (h₂.2.1.trans h₀.2.1.symm)
  obtain rfl := key _ _ h₁
  exact ⟨⟨a, b, c⟩, fun _ _ _ h => (hu _ _ _ h).1, key⟩

end GlobalTheory.HeckePointLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieImageCompatibleWithBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.LieImageBC

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epi_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (d : A →+* B)
    [IsLocalHom d] (hd : Function.Injective d) : Epi (spMap d) := by
  refine ⟨fun {X} a b h => ?_⟩
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective b
  have h1 : IsLocalHom (f ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d f.hom
  have h2 : IsLocalHom (g ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d g.hom
  have h3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, _, h1⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, _, h2⟩ := by
    simpa [SpecToEquivOfLocalRing] using h
  have h4 := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.injective h3
  obtain rfl : x = y := congrArg Sigma.fst h4
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h4).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

theorem epi_dualMap {K L : Type} [Field K] [Field L] (φ : K →+* L) : Epi (spMap (dualMap φ)) := by
  have : IsLocalHom (dualMap φ) := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at ha ⊢
    intro h
    exact ha (by simp [dualMap, h])⟩
  refine epi_of_local _ fun a b h => ?_
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  ext
  · exact φ.injective (by simpa [dualMap] using h1)
  · exact φ.injective (by simpa [dualMap] using h2)

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isLieImageH_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (p : ℕ) (v u : Sp (DualNumber K) ⟶ Xo.univ.t.G.left), IsBC φ f g → IsTanAt x v → (IsLieImageH p f.left v u ↔ IsLieImageH p g.left (spMap (dualMap φ) ≫ v) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g p v u hbc hv
  obtain ⟨rfl, rfl, hbc⟩ := hbc
  let π : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  let π' : pullback Xo.univ.t.G.hom (spMap φ ≫ x') ⟶ pullback Xo.univ.t.G.hom x' :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  have hπ1 : π ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2 : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hπ1' : π' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2' : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hc := hbc π π' hπ1 hπ2 hπ1' hπ2'
  generalize hF : (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = F at hc ⊢
  generalize hG : (g.left : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x')) = G
    at hc ⊢
  have key : ∀ (a : Sp (DualNumber K) ⟶ pullback Xo.univ.t.G.hom x)
      (b : Sp (DualNumber L) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x)),
      a ≫ pullback.fst _ _ = v → a ≫ pullback.snd _ _ = spMap (algebraMap K (DualNumber K)) →
      b ≫ pullback.fst _ _ = spMap (dualMap φ) ≫ v → b ≫ pullback.snd _ _ = spMap (algebraMap L (DualNumber L)) →
      spMap (dualMap φ) ≫ spMap (epsMul ((p : K)⁻¹)) ≫ a ≫ F ≫ pullback.fst _ _ =
        spMap (epsMul ((p : L)⁻¹)) ≫ b ≫ G ≫ pullback.fst _ _ := by
    intro a b ha1 ha2 hb1 hb2
    have hab : b ≫ π = spMap (dualMap φ) ≫ a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hπ1, hb1, Category.assoc, ha1]
      · rw [Category.assoc, hπ2, ← Category.assoc, hb2, Category.assoc, ha2, dual_alg]
    have hGF : G ≫ pullback.fst _ _ = π ≫ F ≫ pullback.fst _ _ := by
      rw [← hπ1', ← Category.assoc, hc, Category.assoc]
    rw [hGF, ← Category.assoc b, hab, ← Category.assoc, dual_eps, map_inv₀, map_natCast]
    simp only [Category.assoc]
  constructor
  · rintro ⟨a, ha1, ha2, rfl⟩
    refine ⟨pullback.lift (spMap (dualMap φ) ≫ v) (spMap (algebraMap L (DualNumber L))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      key a _ ha1 ha2 (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩
    rw [Category.assoc, hv.1, ← Category.assoc, dual_alg, Category.assoc]
  · rintro ⟨b, hb1, hb2, hu⟩
    refine ⟨pullback.lift v (spMap (algebraMap K (DualNumber K))) hv.1,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
    have := epi_dualMap φ
    rw [← cancel_epi (spMap (dualMap φ)), hu]
    exact (key _ b (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hb1 hb2).symm

end GlobalTheory.LieImageBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOnto
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkLie

open GlobalTheory.IntRebase

section Gen

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G G' : Over X0} [GrpObj G] [GrpObj G']

theorem smT_post' (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G') :
    smT x0 a (v ≫ φ) = smT x0 a v ≫ φ := (Category.assoc _ _ _).symm

theorem smT_comm (a b : S) (v : overAt x0 (DualNumber S) ⟶ G) :
    smT x0 a (smT x0 b v) = smT x0 b (smT x0 a v) := by
  rw [smT_smT, smT_smT, _root_.mul_comm]

theorem tan_image (q : S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (φ : G ⟶ G') [IsMonHom φ] :
    smT x0 0 (smT x0 q (v ≫ φ)) = 1 := by
  rw [smT_comm, smT_post', h0, MonObj.one_comp, smT_one']

theorem smT_natCast (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (n : ℕ) :
    smT x0 (n : S) v = v ^ n := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [Nat.cast_succ, smT_add x0 v h0, ih, smT_unit, pow_succ]

theorem comp_id_pow {P : Over X0} (v : P ⟶ G) (n : ℕ) : v ≫ (𝟙 G ^ n) = v ^ n := by
  have h := map_pow (IntRebase.preHom (G := G) v) (𝟙 G) n
  have h2 : IntRebase.preHom (G := G) v (𝟙 G) = v := Category.comp_id v
  rw [h2] at h
  exact h

variable [IsCommMonObj G] [IsCommMonObj G']

theorem combT_image {m : ℕ} (q : S) (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) (φ : G ⟶ G')
    [IsMonHom φ] : smT x0 q (combT x0 v a ≫ φ) = combT x0 (fun j => smT x0 q (v j ≫ φ)) a := by
  let ph : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G') :=
    { toFun := fun v => v ≫ φ
      map_one' := MonObj.one_comp φ
      map_mul' := fun u w => MonObj.mul_comp u w φ }
  have h : combT x0 v a ≫ φ = ∏ j, smT x0 (a j) (v j) ≫ φ :=
    map_prod ph (fun j => smT x0 (a j) (v j)) Finset.univ
  rw [h, smT_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_post', smT_comm]

theorem mul_eq_one_of_pair {m : ℕ} (p : ℕ) (q : S) (hq : q * p = 1) (U : Fin m → (overAt x0 (DualNumber S) ⟶ G))
    (U' : Fin m → (overAt x0 (DualNumber S) ⟶ G')) (hU' : ∀ j, smT x0 0 (U' j) = 1)
    (huniq : ∀ i (a b : Fin m → S), U' i = combT x0 U' a → U' i = combT x0 U' b → a = b)
    (F : G ⟶ G') (F' : G' ⟶ G) [IsMonHom F] (hF : F' ≫ F = 𝟙 _ ^ (p ^ 2)) (k k' : Matrix (Fin m) (Fin m) S)
    (hk : ∀ i, smT x0 q (U i ≫ F) = combT x0 U' (fun j => k j i))
    (hk' : ∀ i, smT x0 q (U' i ≫ F') = combT x0 U (fun j => k' j i)) : k * k' = 1 := by
  ext j i
  have h1 : smT x0 q (smT x0 q (U' i ≫ F') ≫ F) = U' i := by
    rw [← smT_post', Category.assoc, hF, comp_id_pow, ← smT_natCast x0 _ (hU' i), smT_smT, smT_smT]
    have e : q * q * ((p ^ 2 : ℕ) : S) = 1 := by
      push_cast
      linear_combination (q * p + 1) * hq
    rw [e, smT_unit]
  rw [hk', combT_image, funext hk, combT_combT x0 U' hU'] at h1
  have h2 := congrFun (huniq i _ _ h1.symm (combT_single x0 U' hU' i).symm) j
  rw [Matrix.one_apply, Matrix.mul_apply]
  rw [Pi.single_apply] at h2
  exact h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_coords {V Fr : Type} [CommRing V] [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) {G G' : SAB H (Sp V)}
    (τ : E →+* ℂ) (F : G.G ⟶ G'.G) [IsMonHom F] (hF : ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) (q : V) {m : ℕ}
    (ub' : Fin m → (epsOver V V ⟶ G'.G))
    (hb : ∀ w : epsOver V V ⟶ G'.G, IsTan w → IsEigV c io G' τ w → ∃! a : Fin m → V, IsComb ub' a w)
    (w : epsOver V V ⟶ G.G) (ht : IsTan w) (he : IsEigV c io G τ w) :
    ∃ a : Fin m → V, IsComb ub' a (kapI ≫ smT (𝟙 (Sp V)) q ((IntRebase.kap ≫ w) ≫ F)) := by
  refine (hb _ (isTan_kapI _ (tan_image _ q _ (smT_zero_kap w ht) F)) ?_).exists
  refine (isEigV_kapI_iff io G' τ _).2 fun a z hz => ?_
  have h1 := (isEigV_kapI_iff io G τ (IntRebase.kap ≫ w)).1 (by rw [kapI_kap_assoc]; exact he) a z hz
  rw [← smT_post', Category.assoc (IntRebase.kap ≫ w), ← hF, ← Category.assoc (IntRebase.kap ≫ w), h1, ← smT_post', smT_comm]

theorem lie_lattice_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  intro E _ _ _ H Dw l Xo c T io y y' I I' f F F' p v hp hF hF' hExt _ hFF hl hl'
  let _ := io.toAlgebra
  intro hv
  obtain ⟨q, hq⟩ := hp.exists_left_inv
  choose k hk using fun τ i => exists_coords io τ F hl q (I'.ub τ) (I'.basis τ) (I.ub τ i) (I.tan τ i) (I.eig τ i)
  choose k' hk' using fun τ i => exists_coords io τ F' hl' q (I.ub τ) (I.basis τ) (I'.ub τ i) (I'.tan τ i) (I'.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => k τ i j, fun τ => ?_, fun τ i => ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun j i => k' τ i j) ?_
    refine mul_eq_one_of_pair (𝟙 (Sp T.V)) p q hq (fun i => IntRebase.kap ≫ I.ub τ i) (fun i => IntRebase.kap ≫ I'.ub τ i)
      (fun i => smT_zero_kap _ (I'.tan τ i)) ?_ F F' hFF _ _ (fun i => (isComb_iff _ _ _).1 (hk τ i))
      (fun i => (isComb_iff _ _ _).1 (hk' τ i))
    intro i a b ha hb
    have ha' := (isComb_iff (I'.ub τ) a _).2 ha
    have hb' := (isComb_iff (I'.ub τ) b _).2 hb
    rw [kapI_kap_assoc] at ha' hb'
    exact (I'.basis τ _ (I'.tan τ i) (I'.eig τ i)).unique ha' hb'
  · obtain ⟨ψ, -, hψ, hg⟩ := hExt
    obtain ⟨u, hu1, hu2⟩ := I.lift τ i
    choose u' hu1' hu2' using I'.lift τ
    obtain ⟨w, hw1, hw2, hw3⟩ := hv τ i
    have hqp : algebraMap T.V T.Fr q = (p : T.Fr)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hq, map_one]
    have hov : u ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (I.ub τ i)]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
      show spMap ((dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [GlobalTheory.IntLie.dualMap_alg]
    have h := GlobalTheory.IntLie.comb_generic I'.m1 I'.m2 (I'.ub τ) u' hu2' _
      (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) (by
        simp only [Over.comp_left, kapI, IntRebase.kap, smT_left, Over.homMk_left, Category.id_comp, Category.assoc]
        rw [hψ, ← Category.assoc u, hu2, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _),
          GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_epsMul]) (k τ i) (hk τ i)
    let g : I.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y) := pullback.lift I.m1.φ I.t'.G.hom I.m1.cart.1.w
    let g' : I'.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y') := pullback.lift I'.m1.φ I'.t'.G.hom I'.m1.cart.1.w
    have hgg := hg g g' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have hw : w = u ≫ g := by
      apply pullback.hom_ext
      · rw [hw1, Category.assoc, pullback.lift_fst, hu1]
      · rw [hw2, Category.assoc, pullback.lift_snd, hov]
    have hg' : g' ≫ pullback.fst _ _ = I'.m1.φ := pullback.lift_fst _ _ _
    have hvv : v τ i = (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) ≫ I'.m1.φ := by
      rw [hw3, hqp, hw, ← hg', Category.assoc, Category.assoc, Category.assoc, ← Category.assoc ψ.left, ← hgg,
        Category.assoc]
    rw [funext hu1', ← hvv] at h
    exact h

end GlobalTheory.HkLie
end
end

