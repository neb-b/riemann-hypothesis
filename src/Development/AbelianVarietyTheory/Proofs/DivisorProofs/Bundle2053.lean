module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameTransportCartesianAutomorphism
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

open MonObj GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

theorem spMap_eps_alg {R : Type} [CommRing R] (a : R) :
    spMap (epsMul a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r <;> simp [epsMul]

theorem spMap_fst_alg {R : Type} [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 (Sp R) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]))

theorem cancel_g_ψ (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) {T : Scheme.{0}} {u₁ u₂ : T ⟶ G'.left}
    (h₁ : u₁ ≫ G'.hom = u₂ ≫ G'.hom) (h₂ : u₁ ≫ g ≫ ψ = u₂ ≫ g ≫ ψ) : u₁ = u₂ :=
  hg.hom_ext (hψ.hom_ext (by simpa using h₂) (by simp only [Category.assoc, hg.w, reassoc_of% h₁])) h₁

variable {R : Type} [CommRing R]

theorem one_g_ψ (hG : IsGrpPullback G' t.G p ψ) {b : X ⟶ X} {g : G'.left ⟶ G'.left} (hgb : IsGrpPullback G' G' b g)
    (q : Sp R ⟶ X) : (1 : Over.mk q ⟶ G').left ≫ g ≫ ψ = (1 : Over.mk ((q ≫ b) ≫ p) ⟶ t.G).left := by
  have h1 := grpPull_one hgb (Over.mk q)
  have h2 := grpPull_one hG (Over.mk (q ≫ b))
  rw [← Category.assoc, ← h1]
  exact h2.symm

theorem isTan_trv (hG : IsGrpPullback G' t.G p ψ) {b : X ⟶ X} {g : G'.left ⟶ G'.left} (hgb : IsGrpPullback G' G' b g)
    (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t (q ≫ p) v) :
    IsTanAtG t ((q ≫ b) ≫ p) (trv hG.1 g q v) := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hG.1 q hv.1
  refine ⟨trv_over hG.1 g hgb.1.w q hv.1, ?_⟩
  rw [trv_eq hG.1 g q w hw hw']
  have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w = (1 : Over.mk q ⟶ G').left :=
    hG.1.hom_ext (by rw [Category.assoc, hw, hv.2]; exact grpPull_one hG (Over.mk q))
      (by rw [Category.assoc, hw', ← Category.assoc, spMap_fst_alg, Category.id_comp]
          exact (Over.w (1 : Over.mk q ⟶ G')).symm)
  rw [← Category.assoc, e, one_g_ψ hG hgb q]

theorem trv_eig (hψ : IsPullback ψ G'.hom t.G.hom p) {act' : OAct (𝓞 E) G'}
    (hact : ∀ a, (act'.act a).left ≫ ψ = ψ ≫ (t.act.act a).left) {g : G'.left ⟶ G'.left}
    (hgc : ∀ a, (act'.act a).left ≫ g = g ≫ (act'.act a).left) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p)
    (a : 𝓞 E) (c : R) (he : v ≫ (t.act.act a).left = spMap (epsMul c) ≫ v) :
    trv hψ g q v ≫ (t.act.act a).left = spMap (epsMul c) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  have hwa : w ≫ (act'.act a).left = spMap (epsMul c) ≫ w :=
    hψ.hom_ext (by rw [Category.assoc, hact, ← Category.assoc, hw, he, Category.assoc, hw])
      (by rw [Category.assoc, Over.w, hw', Category.assoc, hw', ← Category.assoc, spMap_eps_alg])
  rw [trv_eq hψ g q w hw hw']
  simp only [Category.assoc]
  rw [← hact a, ← reassoc_of% (hgc a), reassoc_of% hwa]

theorem exists_trv_eq (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) (q : Sp R ⟶ X) {w' : Sp (DualNumber R) ⟶ t.G.left}
    (hw' : w' ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ (q ≫ b) ≫ p) :
    ∃ w₀ : Sp (DualNumber R) ⟶ G'.left, w₀ ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q ∧
      w₀ ≫ g ≫ ψ = w' := by
  obtain ⟨w'', h1, h2⟩ := exists_lift hψ (q ≫ b) hw'
  refine ⟨hg.lift w'' (spMap (algebraMap R (DualNumber R)) ≫ q) (by rw [h2, Category.assoc]), hg.lift_snd _ _ _, ?_⟩
  rw [← Category.assoc, hg.lift_fst, h1]

theorem trv_injective (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) (q : Sp R ⟶ X) {v₁ v₂ : Sp (DualNumber R) ⟶ t.G.left}
    (h₁ : v₁ ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p)
    (h₂ : v₂ ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) (h : trv hψ g q v₁ = trv hψ g q v₂) :
    v₁ = v₂ := by
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_lift hψ q h₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := exists_lift hψ q h₂
  rw [trv_eq hψ g q w₁ hw₁ hw₁', trv_eq hψ g q w₂ hw₂ hw₂'] at h
  rw [← hw₁, ← hw₂, cancel_g_ψ hψ hg (hw₁'.trans hw₂'.symm) h]

end

theorem isCombAtG_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Y : Scheme.{0}} {t : SAB H Y} {R : Type} [CommRing R] {x0 : Sp R ⟶ Y} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → R} {w₁ w₂ : Sp (DualNumber R) ⟶ t.G.left}
    (h₁ : IsCombAtG t x0 v a w₁) (h₂ : IsCombAtG t x0 v a w₂) : w₁ = w₂ := by
  obtain ⟨u, hu, e⟩ := h₁
  obtain ⟨u', hu', e'⟩ := h₂
  have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← e, ← e', this]


open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections in
theorem trv_eigFrame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {X' : Scheme.{0}} (p : X' ⟶ Y.X) (G' : Over X') [GrpObj G'] (ψ : G'.left ⟶ Y.t.G.left) (act' : OAct (𝓞 E) G') (b : X' ≅ X') (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' Y.t.G p ψ), (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (Y.t.act.act a).left) → IsGrpPullback G' G' b.hom g → (∀ a, (act'.act a).left ≫ g = g ≫ (act'.act a).left) → ∀ {R : Type} [CommRing R] (φR : c.F →+* R) (q : Sp R ⟶ X') (x' : Sp R ⟶ Y.X), x' = (q ≫ b.hom) ≫ p → ∀ e : GlobalTheory.ShFam.EigFrame Y φR (q ≫ p), ∃ e' : GlobalTheory.ShFam.EigFrame Y φR x', ∀ τ i, e'.v τ i = GlobalTheory.EqvTrans.trv hG.1 g q (e.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y X' p G' _ ψ act' b g hG hact hgb hgc R _ φR q x' hx' e
  subst hx'
  have hv : ∀ τ i, e.v τ i ≫ Y.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p := fun τ i => (e.tan τ i).1
  refine ⟨{ v := fun τ i => GlobalTheory.EqvTrans.trv hG.1 g q (e.v τ i)
            tan := fun τ i => GlobalTheory.EqvTrans.isTan_trv hG hgb q (e.tan τ i)
            eig := fun τ i a => GlobalTheory.EqvTrans.trv_eig hG.1 hact hgc q (hv τ i) a _ (e.eig τ i a)
            basis := ?_ }, fun τ i => rfl⟩
  intro τ w' hw' heig
  obtain ⟨w₀, hw₀, hw₀g⟩ := GlobalTheory.EqvTrans.exists_trv_eq hG.1 hgb.1 q hw'.1
  have htr : GlobalTheory.EqvTrans.trv hG.1 g q (w₀ ≫ ψ) = w' := (GlobalTheory.EqvTrans.trv_eq hG.1 g q w₀ rfl hw₀).trans hw₀g
  have hone : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w₀ = (1 : Over.mk q ⟶ G').left :=
    GlobalTheory.EqvTrans.cancel_g_ψ hG.1 hgb.1
      (by rw [Category.assoc, hw₀, ← Category.assoc, GlobalTheory.EqvTrans.spMap_fst_alg, Category.id_comp]
          exact (Over.w (1 : Over.mk q ⟶ G')).symm)
      (by rw [Category.assoc, hw₀g, hw'.2, GlobalTheory.EqvTrans.one_g_ψ hG hgb q])
  have hwt : IsTanAtG Y.t (q ≫ p) (w₀ ≫ ψ) :=
    ⟨by rw [Category.assoc, hG.1.w, ← Category.assoc, hw₀, Category.assoc],
      by rw [← Category.assoc, hone]; exact (grpPull_one hG (Over.mk q)).symm⟩
  have hwe : ∀ a : 𝓞 E, (w₀ ≫ ψ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (φR (embK c τ a))) ≫ (w₀ ≫ ψ) := fun a => by
    have h0 : w₀ ≫ (act'.act a).left = spMap (epsMul (φR (embK c τ a))) ≫ w₀ :=
      GlobalTheory.EqvTrans.cancel_g_ψ hG.1 hgb.1
        (by rw [Category.assoc, Over.w, hw₀, Category.assoc, hw₀, ← Category.assoc, GlobalTheory.EqvTrans.spMap_eps_alg])
        (by rw [Category.assoc, reassoc_of% (hgc a), hact a, ← Category.assoc w₀, ← Category.assoc (w₀ ≫ g),
              Category.assoc w₀, hw₀g, heig a, Category.assoc, hw₀g])
    rw [Category.assoc, ← hact a, ← Category.assoc, h0, Category.assoc]
  obtain ⟨a, ha, huniq⟩ := e.basis τ (w₀ ≫ ψ) hwt hwe
  refine ⟨a, ?_, fun a' ha' => ?_⟩
  · have h := _root_.GlobalTheory.EqvTrans.trv_comb Y.t p G' ψ b.hom g hG hgb q (e.v τ) a (w₀ ≫ ψ) (e.tan τ) hwt ha
    rwa [htr] at h
  · obtain ⟨u, hut, huc⟩ : ∃ u : Sp (DualNumber R) ⟶ Y.t.G.left, IsTanAtG Y.t (q ≫ p) u ∧
        IsCombAtG Y.t (q ≫ p) (e.v τ) a' u :=
      ⟨(tv (∑ i, a' i • tanOf (e.tan τ i))).left, isTan_tv _, (isComb_iff (fun i => tanOf (e.tan τ i)) a' _).2 rfl⟩
    have h1 := _root_.GlobalTheory.EqvTrans.trv_comb Y.t p G' ψ b.hom g hG hgb q (e.v τ) a' u (e.tan τ) hut huc
    have h2 : GlobalTheory.EqvTrans.trv hG.1 g q u = w' := GlobalTheory.EqvTrans.isCombAtG_unique h1 ha'
    have h3 : u = w₀ ≫ ψ := GlobalTheory.EqvTrans.trv_injective hG.1 hgb.1 q hut.1 hwt.1 (h2.trans htr.symm)
    exact huniq a' (h3 ▸ huc)

end GlobalTheory.EqvTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
section
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.Extend

def filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {F | ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree)}
  add_mem' {F G} hF hG α := by simpa using Ideal.add_mem _ (hF α) (hG α)
  zero_mem' α := by simp
  smul_mem' c F hF α := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have : p.2.degree ≤ α.degree := by rw [← h, map_add (f := _)]; omega
    exact Ideal.pow_le_pow_right (by omega) (hF p.2)

theorem mem_filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (F : MvPowerSeries σ R) :
    F ∈ filt I k ↔ ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree) := Iff.rfl

theorem eq_zero_of_forall_mem_filt {σ R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (F : MvPowerSeries σ R) (h : ∀ k, F ∈ filt I k) : F = 0 := by
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun m => ?_
  have := h (m + α.degree) α
  rw [Nat.add_sub_cancel] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

end GlobalTheory.FormalOrigin.Extend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory CartesianMonoidalCategory MonObj

open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem act_natCast {E : Type} [Field E] {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (act : OAct (𝓞 E) G) (n : ℕ) :
    act.act (n : 𝓞 E) = mulN G n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    have h0 : act.act 0 = 1 := mul_eq_left.mp h.symm
    rw [Nat.cast_zero, h0, Hom.one_def]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, act.add, ih, act.one, Hom.mul_def]
    rfl

theorem eta_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw : (η[G'].left ≫ φ) ≫ G.hom = (Over.mk ((𝟙_ (Over S')).hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w η[G']]
    rfl
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) hw
  have h1 : (η[G'] : 𝟙_ (Over S') ⟶ G') * η[G'] = η[G'] := by
    have e : (η[G'] : 𝟙_ (Over S') ⟶ G') = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ η[G']) (toUnit_unique _ _))
    rw [e, _root_.mul_one]
  have h2 := h.2 (𝟙_ (Over S')) η[G'] η[G'] x₀ x₀ rfl rfl
  rw [h1] at h2
  have h3 : x₀ * x₀ = x₀ := Over.OverMorphism.ext h2
  have h4 : x₀ = 1 := mul_eq_left.mp h3
  have h5 := congrArg (fun q => q.left) h4
  simp only [x₀, Over.homMk_left] at h5
  rw [h5, Hom.one_def, Over.comp_left]
  congr 1

theorem exists_lift_torsion {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ G)
    (h : a ≫ mulN G n = 1) : ∃ aT : Y ⟶ torsion G n, aT ≫ torsion.ι G n = a :=
  ⟨pullback.lift a (toUnit Y) (by rw [h, Hom.one_def]), pullback.lift_fst _ _ _⟩

theorem mono_torsion_ι {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) : Mono (torsion.ι G n).left := by
  have : Mono (η[G] : 𝟙_ (Over X') ⟶ G) := ⟨fun g h _ => toUnit_unique g h⟩
  have : Mono (torsion.ι G n) := ⟨fun a b hab => pullback.hom_ext hab (toUnit_unique _ _)⟩
  infer_instance

theorem isDomain_stalk_of_etale {X' W : Scheme.{0}} [GlobalTheory.IsNormalScheme X'] (h : W ⟶ X') [Etale h] (q : W) :
    IsDomain (W.presheaf.stalk q) :=
  (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth h
    (fun y => ⟨GlobalTheory.IsNormalScheme.isDomain_stalk y, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk y⟩) q).1

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPtMemMaximalIdeal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

noncomputable section
namespace GlobalTheory.CuspOnTor

theorem evalPt_mem_maximalIdeal {Y : Scheme.{0}} {V : Type} [CommRing V] [IsLocalRing V] (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W)
    (hg : ger _ hy g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (x (IsLocalRing.closedPoint V)))) :
    TangentOrigin.evalPt x W h g ∈ IsLocalRing.maximalIdeal V := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have e : (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (ger _ hy g) = TangentOrigin.evalPt x W h g := by
    have := congrArg (fun φ => φ.hom g) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.trans ?_
    simp only [TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
    congr!
  intro hu
  exact hg (isUnit_of_map_unit (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom _ (e ▸ hu))

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} {R : Type} [CommRing R]

theorem val_restr (h : O' ≤ O) (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

theorem val_congr {x x' : Sp R ⟶ Y} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_spMap {R' : Type} [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (hO' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ O) (hi' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val (spMap ψ ≫ x) i hO' hi' f = ψ (H0.val x i hO hi f) :=
  DFunLike.congr_fun (GlobalTheory.FlagMod.ev_spMap ψ x _ (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi')) (f.loc i)

open GlobalTheory.ShFam GlobalTheory.ShFam.Descent GlobalTheory.CuspFrom GlobalTheory.Toroidal

theorem evR_mem_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : AllWt.Weight Dw) (s : H0 (str₀ X Z) (L₀ X Z la) ⊤), s ∈ vanBd X Z la → ∀ f : GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0), sec₀ X Z _ f = H0.restr le_top s → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → GlobalTheory.AllWt.LiesOn Z y → GlobalTheory.CuspFrom.BdExt Y φ y → ∃ v ∈ IsLocalRing.maximalIdeal V, evR Xo c f.1 y = algebraMap V K v := by
  intro E _ _ _ H Dw l Xo c Y X Z la s hs f hfs V K _ _ _ _ _ _ _ φ y hφ hZ hB
  classical
  obtain ⟨χ, g, hχ, hpt, hw, hbd⟩ := hB
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  have hfr : GlobalTheory.AllWt.ptF y = GlobalTheory.FlagMod.frX y := GlobalTheory.FlagMod.eq_frX y (Descent.ptF_fst y) (Descent.ptF_snd y)
  have hl := X.lies_ptY y
  have hp : X.ptY y ≫ X.π = spMap (algebraMap V K) ≫ χ ≫ genι Y := by
    rw [hl.1, ← hfr, Model.j, ← Category.assoc, hpt, Category.assoc]
  have : IsProper X.π := X.proper
  have hv : ValuativeCriterion.Existence X.π := by
    have h : UniversallyClosed X.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨q, q1, q2⟩ : ∃ q : Sp V ⟶ X.YY, spMap (algebraMap V K) ≫ q = X.ptY y ∧ q ≫ X.π = χ ≫ genι Y := by
    obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨V, K, X.ptY y, χ ≫ genι Y, ⟨hp⟩⟩).exists_lift
    exact ⟨q, q1, q2⟩
  have hzy : spMap (algebraMap V K) ≫ q = X.ptY y := q1
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover q
  have hzk : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ X.F.U k := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have hl' : X.F.Lies (spMap (algebraMap V K) ≫ q) y := hzy ▸ hl
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hl'.1 k hzk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl'

  have hsp : ∀ a : Sp V, a ⤳ IsLocalRing.closedPoint V := fun a => IsLocalRing.specializes_closedPoint a
  let s₀ : Sp K := IsLocalRing.closedPoint K
  have hxe : GlobalTheory.AllWt.ptF y ≫ Y.j = spMap (algebraMap V K) ≫ χ ≫ genι Y := by
    rw [Model.j, ← Category.assoc, hpt, Category.assoc]
  have hb : (χ ≫ genι Y) (IsLocalRing.closedPoint V) ∈ barComp Y Z := by
    refine _root_.GlobalTheory.CompHS.mem_barComp_of_specializes E H Dw l Xo c Y Z (GlobalTheory.AllWt.ptF y s₀) (hZ s₀) _ ?_
    have h1 := (hsp (spMap (algebraMap V K) s₀)).map (χ ≫ genι Y).continuous
    have h2 : Y.j (GlobalTheory.AllWt.ptF y s₀) = (χ ≫ genι Y) (spMap (algebraMap V K) s₀) := by
      have := congrArg (fun m => m s₀) hxe
      simpa only [Scheme.Hom.comp_apply] using this
    rw [h2]
    exact h1
  have hq0 : ∀ a : Sp V, q a ∈ X.π ⁻¹ᵁ barComp Y Z := fun a => by
    have h1 : X.π (q (IsLocalRing.closedPoint V)) ∈ barComp Y Z := by
      have h0 : (q ≫ X.π) (IsLocalRing.closedPoint V) ∈ barComp Y Z := q2 ▸ hb
      exact h0
    exact ((hsp a).map q.continuous).mem_open (X.π ⁻¹ᵁ barComp Y Z).isOpen h1
  have hr : Set.range q ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, hq0 a⟩, rfl⟩
  let w := IsOpenImmersion.lift (inc₀ X Z) q hr
  have hwq : w ≫ inc₀ X Z = q := IsOpenImmersion.lift_fac _ _ _

  have hbdy : w (IsLocalRing.closedPoint V) ∈ bd₀ X Z := by
    intro hU
    have h1 : X.π (inc₀ X Z (w (IsLocalRing.closedPoint V))) ∈ LogKS.interior Y := hU
    obtain ⟨x₀, hx₀⟩ := h1
    have h2 : (w ≫ inc₀ X Z ≫ X.π) (IsLocalRing.closedPoint V) = (χ ≫ genι Y) (IsLocalRing.closedPoint V) := by
      rw [← Category.assoc, hwq, q2]
    simp only [Scheme.Hom.comp_apply] at h2
    have h3 : genι Y (Y.jQ x₀) = genι Y (χ (IsLocalRing.closedPoint V)) := hx₀.trans h2
    refine (mem_genBd_iff.1 hbd) ?_
    rw [← h3]
    have h4 : Y.jQ x₀ ∈ pullback.fst Y.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨x₀, rfl⟩
    exact h4

  have hO : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ flagOpen X := by
    rw [hzy, ← X.pt_inc y]; exact GlobalTheory.FlagMod.le_preimage_map (z := X.pt y) X.inc (top_le_inc X) le_top
  have a := evR_eq_val_secOf f hO hQ ht
  have hwK : (spMap (algebraMap V K) ≫ w) ≫ inc₀ X Z = spMap (algebraMap V K) ≫ q := by rw [Category.assoc, hwq]
  have hk' : ⊤ ≤ ((spMap (algebraMap V K) ≫ w) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := hwK ▸ hzk
  have hO' : ⊤ ≤ ((spMap (algebraMap V K) ≫ w) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hwK ▸ hO
  have hk₀ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := hwq ▸ hz
  have hU₀ : ⊤ ≤ (spMap (algebraMap V K) ≫ w) ⁻¹ᵁ U₀ X Z := fun a ha => hO' ha
  have hjK : ⊤ ≤ (spMap (algebraMap V K) ≫ w) ⁻¹ᵁ (LL₀ X Z (GlobalTheory.AllWt.exOf Dw la 0)).U (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) :=
    fun a ha => mem_pIdx.2 (hk' ha)
  have hj₀ : ⊤ ≤ w ⁻¹ᵁ (LL₀ X Z (GlobalTheory.AllWt.exOf Dw la 0)).U (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) :=
    fun a ha => mem_pIdx.2 (hk₀ ha)
  have b1 := H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) (spMap (algebraMap V K) ≫ w)
    (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) hU₀ hjK hO' hk' (secOf X _ f)
  have b2 : H0.val (spMap (algebraMap V K) ≫ w) (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) hU₀ hjK (sec₀ X Z _ f) =
      algebraMap V K (H0.val w (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) le_top hj₀ s) := by
    rw [hfs, val_restr le_top _ _ le_top hU₀ hjK s]
    exact val_spMap _ w _ le_top hj₀ le_top hjK s
  have b3 : H0.val w (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) le_top hj₀ s ∈ IsLocalRing.maximalIdeal V := by
    have hi : w (IsLocalRing.closedPoint V) ∈ (LL₀ X Z (GlobalTheory.AllWt.exOf Dw la 0)).U (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) :=
      hj₀ (Set.mem_univ _)
    exact evalPt_mem_maximalIdeal w _ _ _ ⟨trivial, hi⟩ (hs _ hbdy _ hi)

  have hbc : Vanish.FrameBC Y := _root_.GlobalTheory.CuspFrom.exists_eigFrame_baseChange E H Dw l Xo c _ _ Y
  obtain ⟨fC, hfC⟩ := _root_.GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt E H Dw l Xo c _ _ Y X V K φ hφ q k hz (GlobalTheory.FlagMod.frX y) (GlobalTheory.FlagMod.frX_snd y) hl'.1
  obtain ⟨g', hg'⟩ : ∃ g' : EigFrame Y φ (q ≫ X.π), ∀ τ i, g'.v τ i = g.v τ i := by
    rw [q2]; exact ⟨g, fun _ _ => rfl⟩
  obtain ⟨gk, hgk⟩ := hbc.at g' (algebraMap V K) (x' := spMap (algebraMap V K) ≫ q ≫ X.π) rfl
  obtain ⟨fK, hfK⟩ := hbc.at fC (algebraMap V K) (x' := spMap (algebraMap V K) ≫ q ≫ X.π) rfl
  have hTy : Comparison₂ y gk := ⟨hφ, by rw [q2]; exact hxe, fun τ i => by
    rw [hgk, hg']
    obtain ⟨w₁, w₂, w₃, w₄⟩ := hw τ i
    exact ⟨w₁, w₂, w₃, w₄⟩⟩
  have hQx : GlobalTheory.FlagMod.frX Q ≫ Y.j = spMap (algebraMap V K) ≫ q ≫ X.π := by
    rw [hQ.over, Category.assoc]
  have hfrQ : GlobalTheory.AllWt.ptF Q = GlobalTheory.FlagMod.frX Q := GlobalTheory.FlagMod.eq_frX Q (Descent.ptF_fst Q) (Descent.ptF_snd Q)
  have hTQ : Comparison₂ Q fK := ⟨hφ, by rw [hfrQ]; exact hQx, fun τ i => by
    have e1 : fK.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (GlobalTheory.FlagMod.frVec Y Q hQx τ i)).left := by
      rw [hfK, hfC, ← GlobalTheory.FlagMod.tanPull_left (algebraMap V K) rfl,
        GlobalTheory.FlagMod.Frames.tanPull_vecAt X.F k (algebraMap V K) q hz hzk rfl (Category.assoc _ _ _) rfl τ i,
        hQ.frVec_eq (Category.assoc _ _ _) hQx]
    rw [e1, hfrQ]
    obtain ⟨u, u₁, u₂, u₃⟩ := (GlobalTheory.FlagMod.toModel_eq_iff (GlobalTheory.FlagMod.frX Q) (GlobalTheory.FlagMod.frX_fst Q) hQx (Q.tan τ i) _).1 rfl
    exact ⟨u, u₁, u₂, u₃⟩⟩
  have hT1 := Comparison₂.tri_of_bm hTQ hTy (BM.of_frBor ht)
  have hd1 : spMap (dualMap (AlgHom.id c.F K).toRingHom) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have hF : fC.Tri (algebraMap V K) gk fun τ i => t (some ⟨τ, i⟩) := by
    refine ⟨rfl, rfl, fun τ i => ?_⟩
    obtain ⟨cf, c1, c2, c3⟩ := hT1.2.2 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun j => spMap (dualMap (algebraMap V K)) ≫ fC.v τ j) =
        fun j => spMap (dualMap (AlgHom.id c.F K).toRingHom) ≫ fK.v τ j := by
      funext j
      rw [hd1, Category.id_comp, hfK]
    rw [e]
    exact c3
  have hG : g'.Tri (algebraMap V K) gk 1 := by
    refine ⟨rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩⟩
    have e : (fun j => spMap (dualMap (algebraMap V K)) ≫ g'.v τ j) = gk.v τ := funext fun j => (hgk τ j).symm
    rw [e]
    exact isCombAtG_single Y.t _ (gk.tan τ) i
  obtain ⟨uu, huu⟩ := CoordUniq.exists_unit_ratio fC g' hinj hF hG
  have hu' := huu (algebraMap V K) gk _ _ hF hG
  let Wn : Vˣ := ∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), uu x.1 x.2 ^ GlobalTheory.AllWt.exOf Dw la 0 (some x)
  have hW : ((∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix : Kˣ) : K) = algebraMap V K (Wn : V) := by
    have h0 : GlobalTheory.AllWt.exOf Dw la 0 none = 0 := rfl
    have : (∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix : Kˣ) = Units.map (algebraMap V K : V →* K) Wn := by
      simp only [Fintype.prod_option, h0, zpow_zero, one_mul, Wn, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [show t (some x) = _ from hu' x.1 x.2]
      simp
    rw [this]; rfl
  refine ⟨Wn * H0.val w (pIdx (X.LL (GlobalTheory.AllWt.exOf Dw la 0)) (inc₀ X Z) k) le_top hj₀ s, Ideal.mul_mem_left _ _ b3, ?_⟩
  rw [a, hW, map_mul, ← b2]
  congr 1
  exact (val_congr hwK.symm _ _ _ _ _ _).trans (b1.symm)

end GlobalTheory.CuspOnTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogOrdFracComapFormallyUnramifiedDvrStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)], (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) → ∀ g : K, g ≠ 0 → WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  first | exact @GlobalTheory.RestrictOrd.log_ordFrac_comap | exact GlobalTheory.RestrictOrd.log_ordFrac_comap | (intros; apply GlobalTheory.RestrictOrd.log_ordFrac_comap <;> assumption)
end

