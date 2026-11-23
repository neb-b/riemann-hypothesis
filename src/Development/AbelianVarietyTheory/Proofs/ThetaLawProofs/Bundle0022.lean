module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ProdCompEqOfFiniteFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem prod_comp_eq_of_finite_family {S : Type} (A : Finset (S → ℂ)) (a : S → S)
    (h : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ a) (w : ℂ) (x : S) :
    ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A, (w - f x) := by
  classical
  choose! φ hφA hφ using h
  have hinj : Set.InjOn φ A := fun f hf k hk hfk => by rw [hφ f hf, hφ k hk, hfk]
  have himg : A.image φ = A := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      exact hφA f hf
    · rw [Finset.card_image_of_injOn hinj]
  calc ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A.image φ, (w - f (a x)) := by rw [himg]
    _ = ∏ f ∈ A, (w - φ f (a x)) := Finset.prod_image hinj
    _ = ∏ f ∈ A, (w - f x) :=
        Finset.prod_congr rfl (fun f hf => congrArg (w - ·) (congrFun (hφ f hf) x).symm)

theorem differentiableOn_finite_prod {K E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set E} (A : Finset K) {f : K → E → ℂ} (h : ∀ i ∈ A, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun x => ∏ i ∈ A, f i x) s := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert j B hj ih =>
    simp only [Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self j B)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem const_of_finite_family_spAct :
    Key.PhHoloStatement → ∀ (g : ℕ) (I : Type) [Finite I] (F : I → Matrix (Fin g) (Fin g) ℂ → ℂ), 2 ≤ g → (∀ i, Key.IsHoloSiegel g (F i)) → (∀ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ i, ∃ j, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = F j (Key.Chi.spAct sp τ)) → ∀ i, ∃ c, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = c := by
  intro hPh g I _ F hg hF h i
  classical
  have : Fintype I := Fintype.ofFinite I
  let S := ReciprocityTheory.PTheta.SiegelH (Fin g)
  have hmem : ∀ τ ∈ S, τ.IsSymm ∧ (τ.map Complex.im).PosDef := fun τ hτ => hτ
  let G : I → (S → ℂ) := fun j τ => F j τ
  let A : Finset (S → ℂ) := Finset.univ.image G
  have hGA : ∀ j, G j ∈ A := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hA : ∀ f ∈ A, ∃ j, G j = f := fun f hf => by simpa [A] using hf
  have : Nonempty I := ⟨i⟩
  choose! rep hrep using hA
  have heval : ∀ f ∈ A, ∀ τ (hτ : τ ∈ S), F (rep f) τ = f ⟨τ, hτ⟩ :=
    fun f hf τ hτ => congrFun (hrep f hf) ⟨τ, hτ⟩
  have hsym : ∀ τ ∈ S, Key.phSym τ = τ := by
    intro τ hτ
    have ht : Matrix.transpose τ = τ := (hmem τ hτ).1.eq
    simp only [Key.phSym, ht]
    ext p q
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hholo : ∀ w : ℂ, Key.IsHoloSiegel g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w
    exact differentiableOn_finite_prod A
      (f := fun f x => w - F (rep f) (Key.phSym (Matrix.of x)))
      (fun f _ => (differentiableOn_const w).sub (hF (rep f)))
  have hinv : ∀ w : ℂ, Key.IsSpInvariant g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w gm hgm τ hτ
    choose J hJ using h gm hgm
    let act : S → S := fun σ => ⟨Key.Chi.spAct gm σ, Key.Chi.spAct_mem hgm σ.2⟩
    have hfam : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ act := by
      intro f hf
      refine ⟨G (J (rep f)), hGA _, ?_⟩
      funext σ
      exact (congrFun (hrep f hf) σ).symm.trans (hJ (rep f) σ.1 σ.2)
    have hstep := prod_comp_eq_of_finite_family A act hfam w ⟨τ, hτ⟩
    have hact : Key.phAct gm τ = Key.Chi.spAct gm τ := rfl
    show ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - F (rep f) τ)
    calc ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - f (act ⟨τ, hτ⟩)) :=
          Finset.prod_congr rfl (fun f hf => by rw [hact, heval f hf _ (Key.Chi.spAct_mem hgm hτ)])
      _ = ∏ f ∈ A, (w - f ⟨τ, hτ⟩) := hstep
      _ = ∏ f ∈ A, (w - F (rep f) τ) :=
          Finset.prod_congr rfl (fun f hf => by rw [heval f hf τ hτ])
  by_cases hne : S.Nonempty
  swap
  · exact ⟨0, fun τ hτ => (hne ⟨τ, hτ⟩).elim⟩
  obtain ⟨τ0, hτ0⟩ := hne
  refine ⟨F i τ0, fun τ hτ => ?_⟩
  have hval : ∀ τ ∈ S, F i τ ∈ ((A.image (fun f => F (rep f) τ0) : Finset ℂ) : Set ℂ) := by
    intro τ hτ
    obtain ⟨c, hc⟩ := hPh g hg _ (hholo (F i τ)) (hinv (F i τ))
    have h0 : ∏ f ∈ A, (F i τ - F (rep f) τ) = 0 := by
      apply Finset.prod_eq_zero (hGA i)
      rw [heval _ (hGA i) τ hτ]
      exact sub_self _
    have h1 : ∏ f ∈ A, (F i τ - F (rep f) τ0) = 0 := (hc τ0 hτ0).trans ((hc τ hτ).symm.trans h0)
    obtain ⟨f, hf, hz⟩ := Finset.prod_eq_zero_iff.1 h1
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨f, hf, (sub_eq_zero.1 hz).symm⟩)
  have hcont : ContinuousOn (F i) S := by
    have hc0 := (hF i).continuousOn
    refine (hc0.mono (fun σ hσ => ?_)).congr (fun σ hσ => ?_)
    · show Key.phSym σ ∈ S
      rw [hsym σ hσ]
      exact hσ
    · show F i σ = F i (Key.phSym σ)
      rw [hsym σ hσ]
  have hconv : Convex ℝ S := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2⟩ := hmem x hx
    obtain ⟨hy1, hy2⟩ := hmem y hy
    change Matrix.IsSymm (s • x + t • y) ∧ ((s • x + t • y).map Complex.im).PosDef
    refine ⟨(hx1.smul s).add (hy1.smul t), ?_⟩
    have hm : (s • x + t • y).map Complex.im = s • x.map Complex.im + t • y.map Complex.im := by
      ext p q
      simp
    rw [hm]
    rcases hs.lt_or_eq with hs' | hs'
    · exact (hx2.smul hs').add_posSemidef (hy2.posSemidef.smul ht)
    · subst hs'
      rw [zero_add] at hst
      subst hst
      simpa using hy2
  exact hconv.isPreconnected.constant_of_mapsTo DiscreteTopology.isDiscrete hcont
    (fun σ hσ => hval σ hσ) hτ hτ0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyVia

variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}

def Via (w : LB.Iso L' (L.pull φ)) (l : ℕ) (a' : ∀ i, Γ(Y, L'.U i)) (a : ∀ j, Γ(X, L.U j)) : Prop :=
  ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
    (φ.appLE _ _ h).hom (a (j PUnit.unit)) =
      (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l * resG _ inf_le_right (a' i)

theorem chart_le (j : (L.pull φ).ι) : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) :=
  LB.wchart_le L (fun _ => φ) j PUnit.unit

theorem Via.unique (hL : L.IsLB) {w : LB.Iso L' (L.pull φ)} {l : ℕ} {a' b' : ∀ i, Γ(Y, L'.U i)}
    {a : ∀ j, Γ(X, L.U j)} (ha : Via w l a' a) (hb : Via w l b' a) : a' = b' := by
  funext i
  apply TopCat.Presheaf.section_ext Y.sheaf (L'.U i) (a' i) (b' i)
  intro y hy
  have hc := (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)).cover
  have hyc : y ∈ ⨆ j, (L.pull φ).U j := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hyc
  have h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) := inf_le_left.trans (chart_le j)
  have e := (ha j i h).symm.trans (hb j i h)
  have hu : IsUnit ((show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l) :=
    (Units.isUnit (w.s (j, i))).pow l
  have e' := hu.mul_left_cancel e
  have hm : y ∈ (L.pull φ).U j ⊓ L'.U i := ⟨hj, hy⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) y hm,
      ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) y hm]
  exact congrArg (fun v => (Y.presheaf.germ _ y hm).hom v) e'

def pwIso {A B : LB Y} (w : LB.Iso A B) (t : ℤ) : LB.Iso (pw A t) (pw B t) := ⟨fun p => w.s p ^ t⟩

theorem pwIso_isGen {A B : LB Y} {w : LB.Iso A B} (hw : w.IsGen) (t : ℤ) : (pwIso w t).IsGen := by
  intro p q
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem res_appLE {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem appLE_res {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem pull_g (j j' : (L.pull φ).ι) (h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) :
    (L.pull φ).g j j' = Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit)) := by
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique]
  exact (zpow_one (Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit))))

def pullSec (φ : Y ⟶ X) {t : ℤ} (s : LB.Sec (pw L t)) : LB.Sec (pw (L.pull φ) t) where
  f j := (φ.appLE _ _ (chart_le j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun _ hy => ⟨chart_le j hy.1, chart_le j' hy.2⟩
    have e := (congrArg (φ.appLE _ _ h).hom (s.compat (j PUnit.unit) (j' PUnit.unit))).trans (map_mul _ _ _)
    refine (res_appLE _ _ _).trans ((appLE_res h _ _).symm.trans (e.trans (congrArg₂ (· * ·) ?_
      ((appLE_res h _ _).trans (res_appLE _ _ _).symm))))
    exact (congrArg Units.val ((congrArg (· ^ t) (pull_g j j' h)).trans (map_zpow _ _ t).symm)).symm

theorem exists_via (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) (l : ℕ)
    (s : LB.Sec (pw L (l : ℤ))) : ∃ s' : LB.Sec (pw L' (l : ℤ)), Via w l s'.f s.f := by
  have isLB_pw {Z : Scheme.{0}} {H : LB Z} (hH : H.IsLB) (t : ℤ) : (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have e := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at e
      exact e
    · intro i j k
      have e := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at e
      exact e
  have hu := pwIso_isGen hw (l : ℤ)
  have hA := isLB_pw hL' (l : ℤ)
  have hB := isLB_pw (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) (l : ℤ)
  refine ⟨DVR.secOfIso (pullSec φ s) hu hA hB, fun j i h => ?_⟩
  have hV : (L.pull φ).U j ⊓ L'.U i ≤ (pw L' (l : ℤ)).U i ⊓ (pw (L.pull φ) (l : ℤ)).U j := fun _ hy => ⟨hy.2, hy.1⟩
  have h₁ := congrArg (DVR.rs hV) (DVR.secOfIso_spec (pullSec φ s) hu hA hB i j)
  have h₂ := ((DVR.rs_rs _ _ _).symm.trans h₁).trans (DVR.isoCand_rs (pwIso w l) (pullSec φ s) i j hV)
  let u : Γ(Y, (L.pull φ).U j ⊓ L'.U i)ˣ := w.s (j, i)
  have h₃ : res (hV.trans (DVR.divLe i j)) ((pwIso w (l : ℤ)).s (j, i)) = u ^ l :=
    (Units.ext (rs_self le_rfl (u ^ (l : ℤ)).val)).trans (zpow_natCast u l)
  have h₄ : resG Y (inf_le_right : (L.pull φ).U j ⊓ L'.U i ≤ L'.U i) ((DVR.secOfIso (pullSec φ s) hu hA hB).f i) =
      ((u ^ l)⁻¹).val * (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) :=
    h₂.trans (congrArg₂ (· * ·) (congrArg (fun v => (v⁻¹).val) h₃) (res_appLE _ _ _))
  exact ((congrArg₂ (· * ·) (Units.val_pow_eq_pow_val u l).symm h₄).trans (Units.mul_inv_cancel_left _ _)).symm

theorem appLE_cst {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (cst p U r) = cst p' V (f r) := by
  refine (appLE_res h le_top _).trans ?_
  have e₁ : p.appTop ≫ φ.appTop = (spMap f).appTop ≫ p'.appTop := by
    rw [← Scheme.Hom.comp_appTop, hφ, Scheme.Hom.comp_appTop]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ φ.appTop =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p'.appTop := by
    rw [e₁, ← Category.assoc, ← e₂, Category.assoc]
  exact congrArg (fun q => rs Y (le_top : V ≤ ⊤) (q.hom r)) e₃

theorem Via.comb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {w : LB.Iso L' (L.pull φ)} {l N : ℕ} {b' : Fin N → ∀ i, Γ(Y, L'.U i)}
    {b : Fin N → ∀ j, Γ(X, L.U j)} (hb : ∀ k, Via w l (b' k) (b k)) (c : Fin N → R) :
    Via w l (fun i => ∑ k, cst p' _ (f (c k)) * b' k i) (fun j => ∑ k, cst p _ (c k) * b k j) := by
  intro j i h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, hb k j i h, appLE_cst f p p' hφ, rs_cst, mul_left_comm]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R'), (KeyPB x' x f ↔ ∃ φ w, KeyVia x' x f φ w) ∧ ∀ φ w, KeyVia x' x f φ w → (∀ (l : ℕ) (s : RR x l), ∃! s' : RR x' l, SecVia x' x φ w s' s) ∧ (∀ z : Pt x, ∃! z' : Pt x', z'.left ≫ φ = spMap f ≫ z.left) ∧ ∀ (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l) (s : RR x l) (s' : RR x' l) (c : Fin N → R), (∀ k, SecVia x' x φ w (b' k) (b k)) → SecVia x' x φ w s' s → Coords x b c s.f → Coords x' b' (fun k => f (c k)) s'.f := by
  intro R R' _ _ x x' f
  refine ⟨⟨fun ⟨φ, he, w, hg, F, H⟩ => ⟨φ, w, he, hg, F, H⟩, fun ⟨φ, w, he, hg, F, H⟩ => ⟨φ, he, w, hg, F, H⟩⟩, ?_⟩
  rintro φ w ⟨he, hg, F, ⟨hP, -⟩, hw, -⟩
  refine ⟨fun l s => ?_, fun z => ?_, fun l N b b' s s' c hb hs hc => ?_⟩
  · obtain ⟨s', hs'⟩ := exists_via x.P.isLB x'.P.isLB hw l s
    refine ⟨s', hs', fun t ht => ?_⟩
    have e : t.f = s'.f := Via.unique (w := w) (l := l) x.P.isLB ht hs'
    obtain ⟨tf, _⟩ := t
    obtain ⟨sf, _⟩ := s'
    obtain rfl : tf = sf := e
    rfl
  · have hz : z.left ≫ x.P.A.hom = 𝟙 (Sp R) := Over.w z
    have hc : (spMap f ≫ z.left) ≫ x.P.A.hom = 𝟙 (Sp R') ≫ spMap f := by
      rw [Category.assoc, hz, Category.comp_id, Category.id_comp]
    refine ⟨Over.homMk (hP.lift _ _ hc) (hP.lift_snd _ _ hc), hP.lift_fst _ _ hc, fun t ht => ?_⟩
    ext1
    exact hP.hom_ext (ht.trans (hP.lift_fst _ _ hc).symm) ((Over.w t).trans (hP.lift_snd _ _ hc).symm)
  · have H := Via.comb (w := w) (l := l) (b' := fun k => (b' k).f) (b := fun k => (b k).f) f x.P.A.hom x'.P.A.hom hP.w hb c
    have e : s.f = fun j => ∑ k, cst x.P.A.hom (x.P.L.U j) (c k) * (show Γ(x.P.A.left, x.P.L.U j) from (b k).f j) :=
      funext hc
    have hs' : Via w l s'.f s.f := hs
    have hs'' := (congrArg (Via w l s'.f) e).mp hs'
    have e' := Via.unique x.P.isLB hs'' H
    exact fun i => congrFun e' i

end GlobalTheory.KeyVia
end
end

