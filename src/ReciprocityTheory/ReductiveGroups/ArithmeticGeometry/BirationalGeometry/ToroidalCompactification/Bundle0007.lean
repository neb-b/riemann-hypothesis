module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVDefect
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
variable {K : Type} [Fintype K] {Y Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}

theorem gm_gen_change {Z : Scheme.{0}} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (hp : ∀ k, φ k (r z) ∈ L.U (p k)) (hp' : ∀ k, φ k (r z) ∈ L.U (p' k)) :
    gm r z (LB.wchart L φ p) (t.s p) =
      (∏ k, gm (r ≫ φ k) z (L.U (p k) ⊓ L.U (p' k)) (L.g (p k) (p' k)) ^ ε k) * gm r z (LB.wchart L φ p') (t.s p') := by
  have m : r z ∈ (LB.LinComb L φ ε).U p ⊓ (LB.LinComb L φ ε).U p' :=
    ⟨Set.mem_iInter.2 fun k => hp k, Set.mem_iInter.2 fun k => hp' k⟩
  have e := congrArg (gm r z _) (ht p p')
  rw [gm_res r z _ m, map_mul, gm_res r z _ m] at e
  refine e.trans ?_
  congr 1
  show gm r z _ (∏ k, (res _ (pullU (φ k) _ (L.g (p k) (p' k)))) ^ ε k) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) ((gm_res r z _ m _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (p' k)) ⟨hp k, hp' k⟩ _))

theorem exists_defect (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ k, F (φ' k (r z)) ∈ L.U (p k)) → (∀ k, φ' k (r z) ∈ L'.U (q k)) →
      gm (r ≫ h) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ u * ((∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  classical
  have pt : ∀ k y, F (φ' k y) = φ k (h y) := fun k y => congrArg (fun g => g y) (hc k)
  let O : (K → L.ι) × (K → L'.ι) → Y'.Opens := fun pq => h ⁻¹ᵁ (LB.wchart L φ pq.1) ⊓ LB.wchart L' φ' pq.2
  have memO : ∀ pq x, x ∈ O pq ↔ (∀ k, φ k (h x) ∈ L.U (pq.1 k)) ∧ (∀ k, φ' k x ∈ L'.U (pq.2 k)) := fun pq x =>
    ⟨fun hx => ⟨fun k => Set.mem_iInter.1 hx.1 k, fun k => Set.mem_iInter.1 hx.2 k⟩,
      fun hx => ⟨Set.mem_iInter.2 hx.1, Set.mem_iInter.2 hx.2⟩⟩
  have l1 : ∀ pq k, O pq ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => pq.1 k) ⊓ L'.U (pq.2 k)) := fun pq k x hx =>
    ⟨Set.mem_iInter.2 fun _ => show F (φ' k x) ∈ L.U (pq.1 k) by rw [pt k x]; exact ((memO pq x).1 hx).1 k,
      ((memO pq x).1 hx).2 k⟩
  have l2 : ∀ pq, O pq ≤ h ⁻¹ᵁ (LB.wchart L φ pq.1) := fun _ => inf_le_left
  have l3 : ∀ pq, O pq ≤ LB.wchart L' φ' pq.2 := fun _ => inf_le_right
  let v : ∀ pq, Γ(Y', O pq)ˣ := fun pq =>
    res (l2 pq) (pullU h _ (t.s pq.1)) *
      ((∏ k, (res (l1 pq k) (pullU (φ' k) _ (w.s (fun _ => pq.1 k, pq.2 k)))) ^ ε k) * res (l3 pq) (a.s pq.2))⁻¹
  have gv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (pq : (K → L.ι) × (K → L'.ι)), r z ∈ O pq →
      gm r z (O pq) (v pq) = gm (r ≫ h) z (LB.wchart L φ pq.1) (t.s pq.1) *
        ((∏ k, gw w (r ≫ φ' k) z (pq.1 k) (pq.2 k) ^ ε k) * gm r z (LB.wchart L' φ' pq.2) (a.s pq.2))⁻¹ := by
    intro Z r z pq hz
    show gm r z (O pq) (res _ _ * ((∏ k, (res _ _) ^ ε k) * res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r h z _ (l2 pq hz) _)) ?_)
    refine (map_inv _ _).trans (congrArg (·⁻¹) ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hz _))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans (gm_pull r (φ' k) z _ (l1 pq k hz) _)))
  obtain ⟨s, hs⟩ := glue_unit ⊤ O (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hL (φ k (h x))
      choose q hq using fun k => exists_chart hL' (φ' k x)
      exact Opens.mem_iSup.2 ⟨(p, q), (memO (p, q) x).2 ⟨hp, hq⟩⟩) v (fun pq pq' x hx => by
      rw [gv Y' (𝟙 Y') x pq hx.1, gv Y' (𝟙 Y') x pq' hx.2]
      have m := (memO pq x).1 hx.1
      have m' := (memO pq' x).1 hx.2
      rw [gm_gen_change hL t ht (𝟙 Y' ≫ h) x pq.1 pq'.1 m.1 m'.1,
        gm_gen_change hL' a ha (𝟙 Y') x pq.2 pq'.2 m.2 m'.2]
      have hW : ∀ k, gw w (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq.2 k) =
          gm ((𝟙 Y' ≫ h) ≫ φ k) x _ (L.g (pq.1 k) (pq'.1 k)) *
            (gm (𝟙 Y' ≫ φ' k) x _ (L'.g (pq.2 k) (pq'.2 k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) x (pq'.1 k) (pq'.2 k) := by
        intro k
        have e := hw Y' (𝟙 Y' ≫ φ' k) x (pq.1 k) (pq'.1 k) (pq.2 k) (pq'.2 k)
          (by show F (φ' k x) ∈ _; rw [pt]; exact m.1 k) (by show F (φ' k x) ∈ _; rw [pt]; exact m'.1 k)
          (m.2 k) (m'.2 k)
        rw [e, Category.assoc, Category.assoc, hc k]
      simp only [hW]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, inv_zpow', Finset.sum_add_distrib,
        smul_add, smul_neg, Finset.sum_neg_distrib, smul_eq_mul, neg_one_mul, neg_smul]
      abel)
  refine ⟨s, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ O (p, q) := (memO (p, q) (r z)).2 ⟨fun k => by rw [← pt]; exact hp k, hq⟩
  have e := gv Z r z (p, q) hz
  rw [← hs (p, q), gm_res r z _ hz] at e
  rw [e, inv_mul_cancel_right]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open ReciprocityTheory.ChartRestriction.G.Out

theorem globalFnsDvr_of_globalFns (hGF : GlobalFnsSt) : GlobalFnsDvrSt := by
  intro E _ _ _ H V _ _ _ _hcomp t hprop n
  letI : GrpObj t.G := t.grp
  have hsemi : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hsemi.smooth
  haveI : IsSeparated t.G.hom := hsemi.separated
  haveI : QuasiCompact t.G.hom := hsemi.quasiCompact
  have hpow : ∀ k : ℕ,
      Smooth (powObj t.G k).hom ∧ IsSeparated (powObj t.G k).hom ∧
        QuasiCompact (powObj t.G k).hom := by
    intro k
    induction k with
    | zero =>
      change Smooth (𝟙 (Sp V)) ∧ IsSeparated (𝟙 (Sp V)) ∧ QuasiCompact (𝟙 (Sp V))
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    | succ k ih =>
      obtain ⟨hsmooth, hsep, hqc⟩ := ih
      change Smooth (t.G ⊗ powObj t.G k).hom ∧ IsSeparated (t.G ⊗ powObj t.G k).hom ∧
        QuasiCompact (t.G ⊗ powObj t.G k).hom
      rw [Over.tensorObj_hom, pullback.condition]
      exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨h1, h2, h3⟩ := hpow n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := hprop
  have hK := GlobalFunctionsDvrPowers.pull_powObj_globalFns hGF
    (spMap (algebraMap V (FractionRing V))) t.G hsemi n
  exact GlobalFunctionsDvrGeneric.bij_of_generic (powObj t.G n) hK

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem val_exists {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s]
    (y : Sp (FractionRing R) ⟶ X) (r : Sp R ⟶ S) (h : y ≫ s = Out.jK R ≫ r) :
    ∃ x : Sp R ⟶ X, Out.jK R ≫ x = y ∧ x ≫ s = r := by
  obtain ⟨hE, -⟩ : ValuativeCriterion.Existence s ∧ QuasiCompact s := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact this
  obtain ⟨⟨l⟩⟩ := hE ⟨R, FractionRing R, y, r, ⟨h⟩⟩
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem val_unique {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s]
    (x x' : Sp R ⟶ X) (h : Out.jK R ≫ x = Out.jK R ≫ x') (h' : x ≫ s = x' ≫ s) : x = x' := by
  obtain ⟨hU, -⟩ : ValuativeCriterion.Uniqueness s ∧ QuasiSeparated s := by
    have : (ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated) s := by
      rw [← IsSeparated.eq_valuativeCriterion]; infer_instance
    exact this
  have hsq : CommSq (Out.jK R ≫ x) (Out.jK R) s (x ≫ s) := ⟨Category.assoc _ _ _⟩
  have hs := hU ⟨R, FractionRing R, Out.jK R ≫ x, x ≫ s, hsq⟩
  exact congrArg CommSq.LiftStruct.l (@Subsingleton.elim _ hs ⟨x, rfl, rfl⟩ ⟨x', h.symm, h'.symm⟩)

theorem abLocus_pullback (hA : AbLocusOneSt) {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by
  have key : ∀ (K : Type) [Field K] (t : Sp K ⟶ S'),
      IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f)) := by
    intro K _ t
    have hp := (IsPullback.of_hasPullback G'.hom t).paste_horiz h
    have e : pullback.snd G'.hom t = hp.isoPullback.hom ≫ pullback.snd G.hom (t ≫ f) :=
      hp.isoPullback_hom_snd.symm
    rw [e]
    constructor
    · intro hpr
      rw [← Iso.inv_hom_id_assoc hp.isoPullback (pullback.snd G.hom (t ≫ f))]
      infer_instance
    · intro hpr
      infer_instance
  constructor
  · intro hfx
    have hfx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), f x ∈ Set.range t →
        IsProper (pullback.snd G.hom t) := hfx
    intro K _ _ t hxt
    obtain ⟨p, hp⟩ := hxt
    exact (key K t).2 (hfx' K (t ≫ f) ⟨p, congrArg (fun y => f y) hp⟩)
  · intro hx
    have hx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S'), x ∈ Set.range t →
        IsProper (pullback.snd G'.hom t) := hx
    let κ := AlgebraicClosure (S'.residueField x)
    let t : Sp κ ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ)) ≫
      S'.fromSpecResidueField x
    have hxt : x ∈ Set.range t := by
      have hr := Scheme.range_fromSpecResidueField (X := S') x
      refine ⟨IsLocalRing.closedPoint κ, ?_⟩
      have hm : (S'.fromSpecResidueField x).base
          ((Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ))).base
            (IsLocalRing.closedPoint κ)) ∈ ({x} : Set S') := hr ▸ ⟨_, rfl⟩
      exact hm
    have hp := (key κ t).1 (hx' κ t hxt)
    obtain ⟨p, hp'⟩ := hxt
    exact hA S G hG κ (t ≫ f) hp ⟨p, congrArg (fun y => f y) hp'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem Model.j_s {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem dom_iff {O₀ O : Type} [CommRing O₀] [CommRing O] {β₀ : O₀ →+* c.F} {β : O →+* c.F} {b : O₀ →+* O}
    {Yg : Model Xo c β₀} {Y : Model Xo c β} {f : pullback Yg.s (spMap b) ⟶ Y.X} {t₁ : SAB H (pullback Yg.s (spMap b))}
    (m₁ : SABMap t₁ Yg.t (pullback.fst _ _)) (m₂ : SABMap t₁ Y.t f)
    (hc : ∀ (T : Scheme.{0}) (g : T ⟶ t₁.G.left) (g₁ : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Yg.m.φ → g₁ ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
      g₁ ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y.m.φ)
    (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)) (haF : aF ≫ pullback.fst _ _ = Yg.j) {T : Scheme.{0}}
    (g : T ⟶ t₁.G.left) (gg : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left)
    (h₀ : gg ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ) (h₁ : gg ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom)
    (hb : g ≫ t₁.G.hom = gg ≫ Yg.oF.t.G.hom ≫ aF) : g ≫ m₁.φ = gg ≫ Yg.m.φ ↔ g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  refine ⟨fun h => hc T g gg g₂ h h₀ h₁, fun h2 => ?_⟩
  have w1 : (gg ≫ Yg.m.φ) ≫ Yg.t.G.hom = (g ≫ t₁.G.hom) ≫ pullback.fst Yg.s (spMap b) := by
    have e1 := Yg.m.cart.1.w
    have e2 : aF ≫ pullback.fst Yg.s (spMap b) = Yg.jQ ≫ pullback.fst _ _ := haF
    simp only [SABMap.φ, Category.assoc] at e1 ⊢
    rw [e1, reassoc_of% hb, e2]
  let k := m₁.cart.1.lift (gg ≫ Yg.m.φ) (g ≫ t₁.G.hom) w1
  have hk1 : k ≫ m₁.φ = gg ≫ Yg.m.φ := m₁.cart.1.lift_fst _ _ _
  have hk2 : k ≫ t₁.G.hom = g ≫ t₁.G.hom := m₁.cart.1.lift_snd _ _ _
  have hk3 : k ≫ m₂.φ = g₂ ≫ Y.m.φ := hc T k gg g₂ hk1 h₀ h₁
  have hkg : k = g := m₂.cart.1.hom_ext (by rw [hk3, h2]) hk2
  rw [← hkg]
  exact hk1

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section Chart

variable {X X' Y Y' : Scheme.{0}}

structure ChartPull (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) where
  idx : A'.ι → A.ι
  le : ∀ i, A'.U i ≤ h ⁻¹ᵁ A.U (idx i)
  g : ∀ (y : Y') i j, y ∈ A'.U i → y ∈ A'.U j →
    gm (𝟙 Y') y (A'.U i ⊓ A'.U j) (A'.g i j) = gm h y (A.U (idx i) ⊓ A.U (idx j)) (A.g (idx i) (idx j))

theorem gm_div {Z : Scheme.{0}} (A B : LB Y) (r : Z ⟶ Y) (z : Z) (p q : B.ι × A.ι)
    (hm : r z ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) :
    gm r z (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) ((LB.div B A).g p q) =
      gm r z _ (B.g p.1 q.1) * (gm r z _ (A.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hm _))))

theorem LBIso.chartPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (H : LBIso A B) : LBIso A' B' := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ p : B'.ι × A'.ι, B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) := fun p y hy =>
    ⟨b.le _ hy.1, a.le _ hy.2⟩
  refine ⟨⟨fun p => res (le p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩, fun p q => unit_ext fun y hy => ?_⟩
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ (res (le p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))) =
        gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) := fun p hp =>
    (gm_res (𝟙 Y') y (le p) hp _).trans ((gm_pull (𝟙 Y') h y _ (le p hp) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2))))
    (hw (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hm) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val p hy.1)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div A' B' (𝟙 Y') y p q hy).trans ?_)
    ((gm_res (𝟙 Y') y _ hy _).trans (val q hy.2)))
  rw [a.g y _ _ hy.1.2 hy.2.2, b.g y _ _ hy.1.1 hy.2.1]

theorem gm_linComb {Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (j j' : K → L.ι) (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') =
      ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ (show r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' from ⟨hj, hj'⟩) _).trans
    (gm_pull r (φ k) z (L.U (j k) ⊓ L.U (j' k)) ⟨Set.mem_iInter.1 hj k, Set.mem_iInter.1 hj' k⟩ _)

theorem gm_pull_g {Z : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J J' : PUnit → L.ι)
    (hj : r z ∈ (L.pull F).U J) (hj' : r z ∈ (L.pull F).U J') :
    gm r z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) :=
  (gm_linComb L (fun _ : PUnit => F) (fun _ => 1) r z J J' hj hj').trans (by rw [Fintype.prod_unique, zpow_one])

def chartPullPull (L : LB X) (F h : X' ⟶ X) (e : h = F) : ChartPull (L.pull F) L h where
  idx J := J PUnit.unit
  le J y hy := by subst e; exact mem_pull.1 hy
  g y J J' hj hj' := by subst e; exact (gm_pull_g L h (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])

def chartPullLinComb (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) : ChartPull (LB.LinComb (L.pull F) φ' ε) (LB.LinComb L φ ε) h :=
  have le : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := mem_pull.1 (Set.mem_iInter.1 hy k)
      show φ k (h y) ∈ L.U (j k PUnit.unit)
      rw [pt_eq hc]; exact this
  { idx := fun j k => j k PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb (L.pull F) φ' ε (𝟙 Y') y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (gm_pull_g L F (𝟙 Y' ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k)).trans ?_
      rw [Category.id_comp, hc] }

end Chart

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem psum_hom {T : Over S} {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (I : Finset (Fin n)) : ρ (psum G' x I) = psum G (fun i => ρ (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact map_one ρ
  | cons k l ih => exact (map_mul ρ _ _).trans (congrArg (ρ (x k) * ·) ih)


omit [IsCommMonObj G] [IsCommMonObj G'] in
def pushHom (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm


omit [IsCommMonObj G] in
def preHom {T T' : Over S} (U : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (U ≫ ·) fun x y => MonObj.comp_mul U x y

theorem psum_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (I : Finset (Fin n)) : (psum G' x' I).left ≫ φ = U.left ≫ (psum G x I).left := by
  have e : pushPt h.1.w (psum G' x' I) = U ≫ psum G x I :=
    (psum_hom (pushHom h T') x' I).trans ((congrArg (fun z => psum G z I) (funext hx)).trans
      (psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

def cubeMapOf (h : IsGrpPullback G' G f φ) : CubeMap G' G where
  F := φ
  F3 := (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left
  e := f
  e_comm := by
    have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
    have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [e₁] at e
    refine e.trans ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  psum_comm I := psum_push h _ _ _ (fun i => by fin_cases i <;> simp [x3]) I

omit [IsCommMonObj G] in
theorem isGrpPullback_pullback (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left := fun a => pullback.lift_fst _ _ _
  refine ⟨IsPullback.of_hasPullback _ _, fun T x y x₀ y₀ hx hy => ?_⟩
  let z : T ⟶ (Over.pullback f).obj (G ⊗ G) := lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
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

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

