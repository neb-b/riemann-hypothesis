module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPoints
section
noncomputable section

namespace GlobalTheory.ArcLevel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have : Surjective (spMap β) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_genPt {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} {A : Over (Sp (FractionRing R))}
    (gen : (Over.pullback (jK R)).obj G ≅ A) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : Sp F ⟶ G.left) (hg : g ≫ G.hom = jFK (R := R) F ≫ jK R) :
    ∃ x : TFK (R := R) F ⟶ A, x.left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) = g := by
  let z : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift g (jFK (R := R) F) hg) (pullback.lift_snd _ _ _)
  refine ⟨z ≫ gen.hom, ?_⟩
  have hgi : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show (z.left ≫ gen.hom.left) ≫ _ = _
  rw [Category.assoc, ← Category.assoc gen.hom.left, hgi, Category.id_comp]
  exact pullback.lift_fst _ _ _

theorem genRel_of_heq {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ φ' : B ⟶ B₀} (h : φ' = φ)
    {w : LB.Iso M (M₀.pull φ)} {w' : LB.Iso M (M₀.pull φ')} (hw : HEq w' w)
    {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (H : GenRel w t t₀ x) :
    GenRel w' t t₀ x := by
  subst h
  obtain rfl := eq_of_heq hw
  exact H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_conj_part (v : D.La) : ∃ v' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {S : Scheme.{0}} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta v = o.eta v' := by
  have h : v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]; trivial
  obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := Submodule.mem_sup.1 h
  exact ⟨v₂, h₂, fun o => by rw [o.eta_add, o.eta_ker _ h₁, _root_.one_mul]⟩

variable {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}

theorem witData {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {χ : Sp (PowerSeries k) ⟶ Y.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) :
    WitData a W.P.D W.P.oD W.φ W.he W.w W.e := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  exact ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF h₁ h₂ => (s6 F uF h₁ h₂).1⟩


set_option maxHeartbeats 1600000 in
theorem level_core (hL : Laws) (hL2 : Laws2) (h5 : Laws5) {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
    {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre)
    (hφ : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ)
    (hxe : ∀ x, hD.xe (W.e x) = W'.e x)
    (w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫
      pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)))
    (hw₁ : HEq w₁ W.w) (T : Tri W'.w hD.w w₁) (ψ : W.t.G ≅ W'.t.G)
    (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G) (hbc : IsMonHom bc.hom)
    (hψ : bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left)
    (hPU : IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U)
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ)
    (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ') (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n)
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
    (hσ : (n = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨
      (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v))
    (g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left) (hg : g ≫ W.t.G.hom = jK (PowerSeries k))
    (hgm : g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ) : g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := by
  have hG : GlobalFnsSt := globalFns_holds
  have hR := admissibleBase_powerSeries k
  obtain ⟨F, _, _, _, _, hF⟩ := ArcTransport.exists_commonField k
  have hn : 1 ≤ n := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact l.A_pos
    · exact le_trans (by norm_num) l.three_le
  have hn' : n ∣ l.M' := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Nat.dvd_lcm_right _ _
    · exact Nat.dvd_lcm_left _ _
  obtain ⟨q₀, e1, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing k) F) (RingHom.comp_id _) p₀
  obtain ⟨q, e2, e3⟩ := ArcTransport.exists_transport (witData W) hF rfl hG hn' q₀
  have hF' : ∀ r : PowerSeries k, algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ r) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ ((RingHom.id _) r)) := fun _ => rfl
  obtain ⟨q', hq₁, hq₂⟩ := qkPullExists hG _ _ (RingHom.id _) W'.P.D.toPre W.P.D.toPre hD F hF' n q

  have hc : (y' ≫ σ'.left ≫ Y'.m.φ) ≫ Y'.t.G.hom = jK (PowerSeries k) ≫ χ' := by
    have a₁ : Y'.m.φ ≫ Y'.t.G.hom = Y'.oF.t.G.hom ≫ Y'.j := Y'.m.cart.1.w
    have a₂ : σ'.left ≫ Y'.oF.t.G.hom = 𝟙 _ := Over.w σ'
    rw [Category.assoc, Category.assoc, a₁, reassoc_of% a₂, hy']
  let g' : Sp (FractionRing (PowerSeries k)) ⟶ W'.t.G.left := W'.m.cart.1.lift _ _ hc
  have hg' : g' ≫ W'.t.G.hom = jK (PowerSeries k) := W'.m.cart.1.lift_snd _ _ _
  have hgm' : g' ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := W'.m.cart.1.lift_fst _ _ _
  have hih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨x, hx⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g) (by rw [Category.assoc, hg])
  obtain ⟨x', hx'⟩ := exists_genPt W'.P.U.gen (jFK (R := PowerSeries k) F ≫ g') (by rw [Category.assoc, hg'])
  obtain ⟨x'', hx''⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g' ≫ ψ.inv.left)
    (by rw [Category.assoc, Category.assoc, Over.w, hg'])
  have t₁ : QkToAkU W.P.U.toUnifPre F n q x := by
    refine (W.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y) (by rw [Category.assoc, hy]) n p₀ σ ?_
      q₀ q x e1 e2 e3 ?_
    · rcases hσ with ⟨h, v, h₁, h₂, -⟩ | ⟨h, v, hv, h₁, h₂, -⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · rw [reassoc_of% hx, hgm, Category.assoc]
  have t₂ : QkToAkU W'.P.U.toUnifPre F n q' x' := by
    refine (W'.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y') (by rw [Category.assoc, hy']) n p₀ σ' ?_
      q₀ q' x' e1 ?_ (fun z => ?_) ?_
    · rcases hσ with ⟨h, v, h₁, -, h₂⟩ | ⟨h, v, hv, h₁, -, h₂⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · have : hD.xe q.y = q'.y := by rw [hq₁, AddEquiv.apply_symm_apply]
      rw [← this, e2]; exact hxe _
    · obtain ⟨hψ', hm⟩ := hq₂.2 (W.e z)
      have pm := (maps_iff hD.w _ _ _ (q.g.s (W.e z)) (q'.g.s (hD.xe (W.e z))) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
      have k' := (genRel_transfer T W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB hψ' pm _ _).2
        (genRel_of_heq hφ hw₁ (e3 z))
      rw [hxe z] at k'
      exact k'
    · rw [reassoc_of% hx', hgm', Category.assoc]
  have t₃ : QkToAkU W.P.U.toUnifPre F n q x'' :=
    h5.qkBaseChange _ _ _ _ hR hR (RingHom.id _) W'.P.D W'.P.A W'.t.G W'.P.U W.t.G bc hbc W.P.A W.P.D hD W.P.U
      hPU F hF' n hn q' x' q x'' hq₁ hq₂ (by rw [hψ, reassoc_of% hx'', hih, Category.comp_id, hx']) t₂
  have hxx := TorsionImage.qkToAkU_unique hL hL2 _ _ hR W.P.D W.P.A W.t.G W.t.semi W.P.U F n hn q x x'' t₁ t₃
  have := epi_spMap (algebraMap (FractionRing (PowerSeries k)) F)
  have hgg : g = g' ≫ ψ.inv.left :=
    (cancel_epi (spMap (algebraMap (FractionRing (PowerSeries k)) F))).1 (hx.symm.trans (hxx ▸ hx''))
  rw [hgg, Category.assoc, reassoc_of% hih, hgm']

theorem level_match : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  intro hL hL2 h5 E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD ⟨hφ, hxe, w₁, hw₁, T⟩ ψ bc _ hbc hψ hPU _
    y y' hy hy' _ _ σ σ' hσ g hg hgm
  rcases hσ with ⟨v, h₁, h₂⟩ | ⟨v, h₁, h₂⟩
  · exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.A (a.etaA v) σ σ'
      (Or.inl ⟨rfl, v, HEq.rfl, h₁, h₂⟩) g hg hgm
  · obtain ⟨v', hv', e⟩ := exists_conj_part (l := l) v
    exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.M (a.eta v') σ σ'
      (Or.inr ⟨rfl, v', hv', HEq.rfl, h₁.trans (e _), h₂.trans (e _)⟩) g hg hgm

end GlobalTheory.ArcLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.VeryAmplePull

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem cst_eq_appLE (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) :
    cst f W r = (f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rfl

theorem appLE_cst {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (D : X.Opens) (W : X'.Opens)
    (e : W ≤ φ ⁻¹ᵁ D) (r : R) : (φ.appLE D W e).hom (cst f D r) = cst f' W (g r) := by
  have e₁ : f.appLE ⊤ D le_top ≫ φ.appLE D W e =
      (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top ≫ f'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ f ⊤ D W le_top e).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE f' (Spec.map (CommRingCat.ofHom g)) ⊤ ⊤ W le_top le_top).symm)
    simp only [h]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  have e₃ : (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom g)).appTop :=
    (Scheme.Hom.app_eq_appLE (Spec.map (CommRingCat.ofHom g)) (U := ⊤)).symm
  rw [cst_eq_appLE, cst_eq_appLE]
  refine (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e₁).trans ?_
  rw [e₃]
  exact congrArg (f'.appLE ⊤ W le_top).hom (congrArg (fun q => q.hom r) e₂).symm

theorem closure_eq_top {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) [IsClosedImmersion (pullback.lift φ f' h)]
    {D : X.Opens} (hD : IsAffineOpen D) {W : X'.Opens} (e : W = φ ⁻¹ᵁ D) (T : Subring Γ(X', W))
    (h₁ : ∀ a, (φ.appLE D W e.le).hom a ∈ T) (h₂ : ∀ c, cst f' W c ∈ T) (x : Γ(X', W)) : x ∈ T := by
  have H := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))
  set p := pullback.fst f (Spec.map (CommRingCat.ofHom g)) with hp
  set q := pullback.snd f (Spec.map (CommRingCat.ofHom g)) with hq
  set u := pullback.lift φ f' h with hu
  have up : u ≫ p = φ := pullback.lift_fst _ _ _
  have uq : u ≫ q = f' := pullback.lift_snd _ _ _
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have e' : W = u ⁻¹ᵁ (p ⁻¹ᵁ D) := by rw [e, ← up]; rfl
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := D) le_top le_top
      (UY := p ⁻¹ᵁ D) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hD)
  have hs : Function.Surjective (u.appLE (p ⁻¹ᵁ D) W e'.le).hom := by
    subst e'
    rw [← Scheme.Hom.app_eq_appLE]
    exact u.app_surjective _ (hD.preimage p)
  obtain ⟨y, rfl⟩ := hs x
  change y ∈ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom
  refine (show ⊤ ≤ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom from ?_) trivial
  rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
  · have e₁ := congrArg (fun k => k.hom d) (Scheme.Hom.appLE_comp_appLE u p D (p ⁻¹ᵁ D) W le_rfl e'.le)
    simp only [up] at e₁
    exact (congrArg (· ∈ T) e₁).mpr (h₁ d)
  · have e₁ := congrArg (fun k => k.hom c) (Scheme.Hom.appLE_comp_appLE u q ⊤ (p ⁻¹ᵁ D) W le_top e'.le)
    simp only [uq] at e₁
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c
    exact (congrArg (· ∈ T) e₁).mpr (h₂ c)

theorem veryAmpleBy_pull : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : X' ⟶ X) (h : φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g))), IsClosedImmersion (pullback.lift φ f' h) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull φ)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → VeryAmpleBy f' H' s' := by
  intro R _ X f H n s hP ⟨hcov, hs⟩ R' _ g X' f' φ h hcl H' W s' hP' _ hs'
  have : IsAffineHom φ := by
    have : IsAffineHom (pullback.fst f (Spec.map (CommRingCat.ofHom g))) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))).flip inferInstance
    rw [← pullback.lift_fst φ f' h]
    infer_instance
  have loc : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans
      (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (φ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (φ y)
      have e := hs' i y j k hj hk
      rw [gs_stalkMap φ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (φ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap φ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage φ, fun j => (φ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (φ y)
    have hm : φ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs φ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j y l k hl hy.2
    have e₂ := hs' i y l k hl hy.2
    have e₃ := (Geo.Tor.gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE φ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · intro x
    refine closure_eq_top h haff (loc i) (RingHom.range _) (fun d => ?_) (fun c => ?_) x
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map g p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (RingHom.ext fun c => (appLE_cst h _ _ _ c).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.AbLaw.VeryAmplePull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem weilQkIs_iff_of_comm (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (D : DegData R I) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    (p p' : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b) (w' : Frm D.toPre F k p'.g.b)
    (hw : w.IsGen) (hw' : w'.IsGen) (z : F)
    (H : ∀ s s₁ s₂ s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p' w' s s₁ → PhiRel D.toPre F k p w s₁ s₂ →
      PhiRel D.toPre F k p w s s₃ → PhiRel D.toPre F k p' w' s₃ s₄ → s₂ = z • s₄)
    (hne : ∃ s s₃ s₄ : Fam D.toPre F k, PhiRel D.toPre F k p w s s₃ ∧ PhiRel D.toPre F k p' w' s₃ s₄ ∧ s₄ ≠ 0)
    (hk : 1 ≤ k) (ζ : F) : WeilQkIs D.toPre F k p p' ζ ↔ ζ = z := by
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R I D F k hk p' w' hw'
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ s) := fun s => (hΦ _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ' s) := fun s => (hΦ' _ _).2 rfl
  constructor
  · intro h
    obtain ⟨s, s₃, s₄, h₃, h₄, h0⟩ := hne
    have a := (isSmul_iff _ _ _).1 (h w w' hw hw' s _ _ s₃ s₄ (r' s) (r _) h₃ h₄)
    have b := H s _ _ s₃ s₄ (r' s) (r _) h₃ h₄
    exact smul_left_injective F h0 (a.symm.trans b)
  · rintro rfl v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
    obtain ⟨c, -, hc⟩ := TorsionImage.exists_smul_of_phiVal p w v hw hv
    obtain ⟨c', -, hc'⟩ := TorsionImage.exists_smul_of_phiVal p' w' v' hw' hv'
    have q : ∀ s t, PhiRel D.toPre F k p v s t → t = c • Φ s := fun s t h =>
      hc s _ t ((phiRel_iff hG p w hw _ _).1 (r s)) ((phiRel_iff hG p v hv _ _).1 h)
    have q' : ∀ s t, PhiRel D.toPre F k p' v' s t → t = c' • Φ' s := fun s t h =>
      hc' s _ t ((phiRel_iff hG p' w' hw' _ _).1 (r' s)) ((phiRel_iff hG p' v' hv' _ _).1 h)
    rw [isSmul_iff, q _ _ h₂, q' _ _ h₁, q' _ _ h₄, q _ _ h₃, map_smul, map_smul,
      H s _ _ _ _ (r' s) (r _) (r s) (r' _), smul_comm c' ζ, smul_comm c ζ, smul_comm c c']

theorem weilQkIs_iff_weilIs : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ
  have hG := hL.1.globalFns
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  obtain ⟨ρ, hρ, hcomm, -⟩ := thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩
  let E : SecM A.A A.L (k : ℤ) (TFK (R := R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)
  have hE : ∀ s, ∃ v, E v = s := fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩
  have a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v)) := fun v =>
    h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v)) := fun v =>
    h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v) := fun v t H =>
    phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))
  have b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v) := fun v t H =>
    phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by
    obtain ⟨v, rfl⟩ := hE s
    obtain rfl := b' _ _ h₁
    obtain rfl := b _ _ h₂
    obtain rfl := b _ _ h₃
    obtain rfl := b' _ _ h₄
    rw [hcomm θ θ' _ hc v]
    exact e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by
    obtain ⟨B, hB, -⟩ := BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)
    have : Nontrivial Γ((TFK (R := R) F).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    have hne := hB.ne_zero ⟨0, pow_pos hk _⟩
    refine ⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩
    have h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _ := e.map_eq_zero_iff.1 h0
    have h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0 := congrArg (SecM.ofSec A.A) h1
    exact (ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)
  have hz := GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc
  rw [key]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))

end GlobalTheory.UT
end

