module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleCocycleOneAddEps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsCocycle

noncomputable section

lemma res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma cocycle_on {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  simpa only [map_mul, res_res] using this

def regauge {X : Scheme.{0}} (L : LB X) (u : ∀ i, Γ(X, L.U i)ˣ) : LB X :=
  ⟨L.ι, L.U, fun i i' => (res inf_le_left (u i))⁻¹ * L.g i i' * res inf_le_right (u i')⟩

lemma regauge_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    (regauge L u).IsLB := {
  cover := hL.cover
  g_self := fun i => by
    have := hL.g_self i
    change res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i)
      ((res inf_le_left (u i))⁻¹ * L.g i i * res inf_le_right (u i)) = 1
    simp only [map_mul, map_inv, res_res, this, _root_.mul_one, inv_mul_cancel]
  cocycle := fun i j k => by
    have := hL.cocycle i j k
    change res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j)
        ((res inf_le_left (u i))⁻¹ * L.g i j * res inf_le_right (u j)) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k)
        ((res inf_le_left (u j))⁻¹ * L.g j k * res inf_le_right (u k)) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k)
        ((res inf_le_left (u i))⁻¹ * L.g i k * res inf_le_right (u k))
    simp only [map_mul, map_inv, res_res, ← this]
    group }

lemma regauge_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    LBIso L (regauge L u) := by
  refine ⟨⟨fun p : L.ι × L.ι => ((res inf_le_left (u p.1))⁻¹ * L.g p.1 p.2 :
    Γ(X, L.U p.1 ⊓ L.U p.2)ˣ)⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩
  let W : X.Opens := L.U a ⊓ L.U b ⊓ (L.U a' ⊓ L.U b')
  have ha : W ≤ L.U a := inf_le_left.trans inf_le_left
  have hb : W ≤ L.U b := inf_le_left.trans inf_le_right
  have ha' : W ≤ L.U a' := inf_le_right.trans inf_le_left
  have hb' : W ≤ L.U b' := inf_le_right.trans inf_le_right
  change res (le_inf ha hb) ((res inf_le_left (u a))⁻¹ * L.g a b) =
    (res (le_inf ha ha') ((res inf_le_left (u a))⁻¹ * L.g a a' * res inf_le_right (u a')) *
      (res (le_inf hb hb') (L.g b b'))⁻¹) *
      res (le_inf ha' hb') ((res inf_le_left (u a'))⁻¹ * L.g a' b')
  have e₁ := cocycle_on hL a a' b' (le_inf ha ha') (le_inf ha' hb') (le_inf ha hb')
  have e₂ := cocycle_on hL a b b' (le_inf ha hb) (le_inf hb hb') (le_inf ha hb')
  have e₃ : res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') *
      res (le_inf ha' hb') (L.g a' b') * (res (le_inf hb hb') (L.g b b'))⁻¹ := by
    rw [e₁, ← e₂, mul_inv_cancel_right]
  simp only [map_mul, map_inv, res_res, e₃]
  generalize res ha (u a) = x
  generalize res ha' (u a') = y
  generalize res (le_inf ha ha') (L.g a a') = z
  generalize res (le_inf ha' hb') (L.g a' b') = w
  generalize res (le_inf hb hb') (L.g b b') = v
  rw [mul_mul_mul_comm _ v⁻¹, mul_inv_cancel_right]
  ac_rfl

lemma appLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)) :
    (j.appLE O' O₂ h').hom ((ρ.appLE O O' h).hom a) = resG Y h'' a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Y) (_ : f = 𝟙 Y) (e : O₂ ≤ f ⁻¹ᵁ O), (f.appLE O O₂ e).hom a = resG Y h'' a := by
    intro f hf e
    subst hf
    simp [Scheme.Hom.appLE]
    rfl
  exact key _ hj _

lemma appLE_constFn_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)}
    {j : Y ⟶ Y'} (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    {O : Y.Opens} {O' : Y'.Opens} (h : O ≤ j ⁻¹ᵁ O') :
    (j.appLE O' O h).hom (constFn π O' DualNumber.eps) = 0 := by
  have h0 : O' ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  change (j.appLE O' O h).hom ((π.appLE ⊤ O' h0).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps)) = 0
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Sp (DualNumber ℂ))
      (_ : f = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (e : O ≤ f ⁻¹ᵁ ⊤),
      (f.appLE ⊤ O e).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = 0 := by
    intro f hf e
    subst hf
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have e2 := congrArg (fun φ => φ.hom DualNumber.eps) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    have e3 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom DualNumber.eps = 0 := by
      simp
    rw [e3, map_zero] at e2
    exact (congrArg _ e2.symm).trans (map_zero _)
  exact key _ hq _

lemma eq_one_add_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}
    {j : Y ⟶ Y'} (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (O' : Y'.Opens)
    (F : Γ(Y', O')) (hF : (j.appLE O' _ le_rfl).hom F = 1) :
    ∃ k : Γ(Y, j ⁻¹ᵁ O'), ∀ h : O' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ O'),
      F = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom k := by
  obtain ⟨h₁, -, h₃⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have key : ∀ (O : Y.Opens) (O' : Y'.Opens) (_ : ρ ⁻¹ᵁ O = O') (F : Γ(Y', O')), ∃ a b : Γ(Y, O),
      ∀ h : O' ≤ ρ ⁻¹ᵁ O,
        F = (ρ.appLE _ _ h).hom a + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom b := by
    intro O O' e F
    subst e
    obtain ⟨ab, hab, -⟩ := h₃ O F
    refine ⟨ab.1, ab.2, fun h => ?_⟩
    rw [Scheme.Hom.appLE_eq_app]
    exact hab
  obtain ⟨a, b, hab⟩ := key _ O' (h₁ O') F
  refine ⟨b, fun h => ?_⟩
  have ha : a = 1 := by
    rw [hab h, map_add (f := _), map_mul, appLE_constFn_eps hq, zero_mul, add_zero,
      appLE_section hj h le_rfl le_rfl] at hF
    have e : resG Y (le_refl (j ⁻¹ᵁ O')) a = a := by
      change (Y.presheaf.map (𝟙 _)).hom a = a
      rw [Y.presheaf.map_id]
      rfl
    exact e.symm.trans hF
  rw [hab h, ha, map_one]

def pullLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, V)ˣ := Units.map (f.appLE U V h).hom

lemma pullLE_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) : pullLE f h x = res h (pullU f U x) := by
  ext
  rfl

lemma pullLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U')
    (h' : U' ≤ U) (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullLE f h (res h' x) = pullLE f h'' x := by
  ext
  simp only [pullLE, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma pullLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)ˣ) : pullLE j h' (pullLE ρ h a) = res h'' a := by
  ext
  exact appLE_section hj h h' h'' a.val

theorem exists_cocycle_one_add_eps : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  intro Y Y' q π ρ j hp hj hq Q hQ ⟨t, ht⟩
  obtain ⟨h₁, -, -⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have hw : ∀ i : Q.ι, j ⁻¹ᵁ Q.U i ≤ (Q.pull j).U (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let s : ∀ i : Q.ι, Γ(Y, j ⁻¹ᵁ Q.U i)ˣ := fun i => res (hw i) (t.s fun _ => i)
  let u : ∀ i, Γ(Y', Q.U i)ˣ := fun i => pullLE ρ (h₁ (Q.U i)).ge (s i)
  have main : ∀ i i' : Q.ι, (j.appLE (Q.U i ⊓ Q.U i') _ le_rfl).hom ((regauge Q u).g i i').val = 1 := by
    intro i i'
    have hl : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have hr : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have e := congrArg (res (le_inf (hl.trans (hw i)) (hr.trans (hw i'))))
      (ht (fun _ => i) (fun _ => i'))
    have eg : res (le_inf (hl.trans (hw i)) (hr.trans (hw i')))
        ((Q.pull j).g (fun _ => i) (fun _ => i')) =
        pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (Q.g i i') := by
      rw [pullLE_eq]
      change res _ (∏ _k : PUnit.{1}, (res _ (pullU j _ (Q.g i i'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact res_res _ _ _
    rw [map_mul, res_res, res_res, eg] at e
    have : pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')))
        ((res inf_le_left (u i))⁻¹ * Q.g i i' * res inf_le_right (u i')) = 1 := by
      rw [map_mul, map_mul, map_inv, pullLE_res j _ _ hl, pullLE_res j _ _ hr,
        pullLE_section hj _ _ hl, pullLE_section hj _ _ hr, res_res, res_res, _root_.mul_assoc, ← e,
        inv_mul_cancel]
    exact congrArg Units.val this
  choose k hk using fun i i' : Q.ι => eq_one_add_eps hp hj hq _ _ (main i i')
  exact ⟨regauge Q u, k, regauge_isLB hQ u, regauge_iso hQ u, hk⟩

end

end GlobalTheory.EpsCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

noncomputable def liftConstHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem liftConstHom_apply {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    liftConstHom p U a = constFn p U a := rfl

theorem liftConstHom_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens)
    (hp : Smooth p) (hU : IsAffineOpen U) : (liftConstHom p U).Smooth := by
  have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (fun _ _ => trivial)
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) h1

theorem app_constFn_of_comm {R S : Type} [CommRing R] [CommRing S] (x₀ : R →+* S) {Y X : Scheme.{0}}
    (q : Y ⟶ Sp S) (p : X ⟶ Sp R) (m : Y ⟶ X) (h : m ≫ p = q ≫ spMap x₀) (W : X.Opens) (a : R) :
    (m.app W).hom (constFn p W a) = constFn q (m ⁻¹ᵁ W) (x₀ a) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W =
      CommRingCat.ofHom x₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
    rw [← Category.assoc (CommRingCat.ofHom x₀), Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
    have e1 : p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W = (m ≫ p).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : (q ≫ spMap x₀).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) =
        (Spec.map (CommRingCat.ofHom x₀)).appTop ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    rw [e1, ← e2]
    simp only [h]
  exact congrArg (fun φ => φ.hom a) key

theorem exists_locDer_of_smooth : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by
  intro R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHom p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHom_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHom q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_comm x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := _root_.GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHom q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add (f := _)])
    (fun a b => by rw [hD.2, hc, hc, map_add (f := _), map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := _root_.GlobalTheory.LocDerExt.exists_locDer R Y X q p m D W₀ hW d₀ h1 h2 h3
  exact ⟨d, hd⟩

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationOfDualNumberThickening
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.EpsDer

variable {X Y Z : Scheme.{0}}

theorem pull_pull (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (e : f ≫ g = h) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = (h.appLE U W e₃).hom a := by
  subst e
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem pull_congr {f g : Y ⟶ X} (e : f = g) {U : X.Opens} {V : Y.Opens}
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE U V e₁).hom a = (g.appLE U V e₂).hom a := by
  subst e
  rfl

theorem res_pull (φ : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a := congrArg (fun ψ => ψ.hom a) (φ.appLE_map h (homOfLE h').op)

theorem pull_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a := congrArg (fun ψ => ψ.hom a) (φ.map_appLE h (homOfLE h').op)

theorem app_res (φ : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.app U').hom (resG X h' a) = resG Y (fun _ hy => h' hy) ((φ.app U).hom a) := congrArg (fun ψ => ψ.hom a) (φ.naturality (homOfLE h').op)

theorem id_pull {U : X.Opens} (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (a : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom a = a := by
  have key : (𝟙 X : X ⟶ X).appLE U ((𝟙 X : X ⟶ X) ⁻¹ᵁ U) le_rfl = 𝟙 _ :=
    (Scheme.Hom.app_eq_appLE (f := 𝟙 X) (U := U)).symm.trans (Scheme.Hom.id_app U)
  exact congrArg (fun ψ => ψ.hom a) key

theorem spec_pull {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (((spMap f).appLE ⊤ ⊤ e).hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  have key : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop :=
    (Scheme.Hom.app_eq_appLE (f := spMap f) (U := ⊤)).symm
  rw [key]
  exact congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem spec_pull_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (r : R) :
    ((spMap f).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f r) := by
  have key : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop :=
    (Scheme.Hom.app_eq_appLE (f := spMap f) (U := ⊤)).symm
  rw [key]
  exact (congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem pull_const {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (φ : Y ⟶ X) (p : X ⟶ Sp R)
    (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (constFn p U r) = constFn p' V (f r) := by
  unfold constFn
  rw [pull_pull φ p (φ ≫ p) rfl (U := ⊤) (V := U) (W := V) (by simp) h (by simp),
    pull_congr hφ (U := ⊤) (V := V) (by simp) (by simp),
    ← pull_pull p' (spMap f) (p' ≫ spMap f) rfl (U := ⊤) (V := ⊤) (W := V) (by simp) (by simp) (by simp),
    spec_pull_inv f (by simp)]

theorem res_const {R : Type} [CommRing R] (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn q U a) = constFn q V a := by
  unfold constFn
  exact res_pull q (U := ⊤) (by simp) h _

def constHom {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (q.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem const_eq {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn q U a = constHom q U a := rfl

theorem dual_decomp (x : DualNumber ℂ) :
    x = algebraMap ℂ (DualNumber ℂ) x.fst + DualNumber.eps * algebraMap ℂ (DualNumber ℂ) x.snd := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
private theorem appLE_app_of_comp_eq {A B C : Scheme.{0}} (f : C ⟶ B) (g : B ⟶ A) (k : C ⟶ A) (e : f ≫ g = k)
    {O : A.Opens} {V : C.Opens} (e₁ : V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ O)) (e₂ : V ≤ k ⁻¹ᵁ O) (a : Γ(A, O)) :
    (f.appLE (g ⁻¹ᵁ O) V e₁).hom ((g.app O).hom a) = (k.appLE O V e₂).hom a := by
  rw [Scheme.Hom.app_eq_appLE]
  exact pull_pull f g k e le_rfl e₁ e₂ a
private theorem constFn_eps_mul_self {A : Scheme.{0}} (π : A ⟶ Sp (DualNumber ℂ)) (V : A.Opens) :
    constFn π V DualNumber.eps * constFn π V DualNumber.eps = 0 := by
  rw [const_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]
private theorem appLE_app_of_section' {A B : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ A) (e : f ≫ g = 𝟙 A) {O : A.Opens}
    (e₁ : O ≤ f ⁻¹ᵁ (g ⁻¹ᵁ O)) (a : Γ(A, O)) : (f.appLE (g ⁻¹ᵁ O) O e₁).hom ((g.app O).hom a) = a := by
  rw [appLE_app_of_comp_eq f g (𝟙 A) e e₁ le_rfl]
  exact id_pull _ a

theorem exists_locDer : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (Φ : Y' ⟶ X), j ≫ Φ = m → Φ ≫ p = π ≫ spMap xD → ∃ d, LocDer q p m (fun r => (xD r).snd) ⊤ d ∧ ∀ (y : Sp ℂ ⟶ Y) (yt : Sp (DualNumber ℂ) ⟶ Y'), yt ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y → yt ≫ π = 𝟙 _ → ∀ (W : X.Opens) (h : ⊤ ≤ (yt ≫ Φ) ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom (((yt ≫ Φ).appLE W ⊤ h).hom f)) = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  intro Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m Φ hm hΦ
  obtain ⟨hO, -, hdec⟩ := _root_.GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hpb hjρ hjπ

  have hW : ∀ W : X.Opens, ρ ⁻¹ᵁ (m ⁻¹ᵁ W) = Φ ⁻¹ᵁ W := fun W => by
    subst hm
    exact hO (Φ ⁻¹ᵁ W)
  have hjO : ∀ O : Y.Opens, j ⁻¹ᵁ (ρ ⁻¹ᵁ O) = O := fun O => by
    show (j ≫ ρ) ⁻¹ᵁ O = O
    rw [hjρ]
    rfl

  have uniq : ∀ (O : Y.Opens) (a b a' b' : Γ(Y, O)),
      (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b =
        (ρ.app O).hom a' + constFn π _ DualNumber.eps * (ρ.app O).hom b' → a = a' ∧ b = b' := by
    intro O a b a' b' e
    have := (hdec O ((ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b)).unique
      (y₁ := (a, b)) (y₂ := (a', b')) rfl e
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hex : ∀ (W : X.Opens) (f : Γ(X, W)), ∃ ab : Γ(Y, m ⁻¹ᵁ W) × Γ(Y, m ⁻¹ᵁ W),
      (Φ.appLE W (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (hW W).le).hom f =
        (ρ.app _).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app _).hom ab.2 :=
    fun W f => (hdec (m ⁻¹ᵁ W) _).exists
  choose AB hAB using hex

  have Aeq : ∀ (W : X.Opens) (f : Γ(X, W)), (AB W f).1 = (m.app W).hom f := by
    intro W f
    have e := congrArg (j.appLE (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (m ⁻¹ᵁ W) (hjO _).ge).hom (hAB W f)
    rw [map_add (f := _), map_mul, pull_pull j Φ m hm (hW W).le (hjO _).ge le_rfl f,
      appLE_app_of_section' j ρ hjρ (hjO _).ge, appLE_app_of_section' j ρ hjρ (hjO _).ge, pull_const (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom j π q hjπ] at e
    have h0 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom DualNumber.eps = 0 := by simp
    rw [h0, const_eq, map_zero, zero_mul, add_zero] at e
    rw [← e, Scheme.Hom.app_eq_appLE]
  refine ⟨fun W f => (AB W f).2, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W _ f f'
    refine (uniq _ (AB W (f + f')).1 _ ((AB W f).1 + (AB W f').1) ((AB W f).2 + (AB W f').2) ?_).2
    rw [← hAB W (f + f')]
    simp only [map_add (f := _)]
    rw [hAB W f, hAB W f']
    ring
  · intro W _ f f'
    rw [← Aeq W f, ← Aeq W f']
    refine (uniq _ (AB W (f * f')).1 _ ((AB W f).1 * (AB W f').1) ((AB W f).1 * (AB W f').2 + (AB W f').1 * (AB W f).2) ?_).2
    rw [← hAB W (f * f')]
    simp only [map_mul, map_add (f := _)]
    rw [hAB W f, hAB W f']
    linear_combination ((ρ.app _).hom (AB W f).2 * (ρ.app _).hom (AB W f').2) * constFn_eps_mul_self π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W))
  · intro W W' h _ f
    have hOO : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W := fun _ hy => h hy
    have hV : ρ ⁻¹ᵁ (m ⁻¹ᵁ W') ≤ ρ ⁻¹ᵁ (m ⁻¹ᵁ W) := fun _ hy => hOO hy
    refine (uniq _ (AB W' (resG X h f)).1 _ (resG Y hOO (AB W f).1) (resG Y hOO (AB W f).2) ?_).2
    rw [← hAB W' (resG X h f), pull_res Φ (hW W').le h f, ← res_pull Φ (hW W).le hV f, hAB W f,
      map_add, map_mul, res_const, ← app_res ρ hOO (AB W f).1, ← app_res ρ hOO (AB W f).2]
  · intro W _ r
    have hc : ∀ c : ℂ, (ρ.app (m ⁻¹ᵁ W)).hom (constFn q (m ⁻¹ᵁ W) c) =
        constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (algebraMap ℂ (DualNumber ℂ) c) := fun c => by
      rw [Scheme.Hom.app_eq_appLE]
      exact pull_const (algebraMap ℂ (DualNumber ℂ)) ρ q π hpb.w le_rfl c
    have e1 : constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (xD r) =
        constFn π _ (algebraMap ℂ (DualNumber ℂ) (xD r).fst) +
          constFn π _ DualNumber.eps * constFn π _ (algebraMap ℂ (DualNumber ℂ) (xD r).snd) := by
      simp only [const_eq]
      rw [← map_mul, ← map_add (f := _), ← dual_decomp]
    refine (uniq _ (AB W (constFn p W r)).1 _ (constFn q _ (xD r).fst) (constFn q _ (xD r).snd) ?_).2
    rw [← hAB W (constFn p W r), pull_const xD Φ p π hΦ, e1, hc, hc]
  · intro y yt hy1 hy2 W h f
    have h2 : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := by
      intro s _
      have ht : yt ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s) ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ W) := by
        rw [hW W]
        exact h trivial
      have e : ρ (yt ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) =
          y ((spMap (algebraMap ℂ (DualNumber ℂ))) ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) :=
        congrArg (fun g : Sp (DualNumber ℂ) ⟶ Y => g ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s)) hy1
      have hs : (spMap (algebraMap ℂ (DualNumber ℂ))) ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) s) = s :=
        Subsingleton.elim _ _
      show y s ∈ m ⁻¹ᵁ W
      rw [← hs, ← e]
      exact ht
    have h' : ⊤ ≤ yt ⁻¹ᵁ (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) := by
      rw [hW W]
      exact h
    have e1 : ((yt ≫ Φ).appLE W ⊤ h).hom f = (yt.appLE _ ⊤ h').hom ((Φ.appLE W _ (hW W).le).hom f) :=
      (pull_pull yt Φ (yt ≫ Φ) rfl (hW W).le h' h f).symm
    have e2 : ∀ a : Γ(Y, m ⁻¹ᵁ W), (yt.appLE _ ⊤ h').hom ((ρ.app (m ⁻¹ᵁ W)).hom a) =
        ((spMap (algebraMap ℂ (DualNumber ℂ))).appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((y.appLE _ ⊤ h2).hom a) := by
      intro a
      rw [appLE_app_of_comp_eq yt ρ _ hy1 h' (fun x _ => h2 trivial),
        pull_pull (spMap (algebraMap ℂ (DualNumber ℂ))) y _ rfl h2 (fun _ _ => trivial) (fun x _ => h2 trivial)]
    have e3 : (yt.appLE _ ⊤ h').hom (constFn π (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps) =
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps := by
      unfold constFn
      rw [pull_pull yt π (𝟙 _) hy2 (U := ⊤) (V := ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (W := ⊤) (fun _ _ => trivial) h'
        (fun _ _ => trivial)]
      exact id_pull _ _
    have e4 : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = DualNumber.eps :=
      congrArg (fun g => CommRingCat.Hom.hom g DualNumber.eps)
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv_hom_id
    show TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
      (((yt ≫ Φ).appLE W ⊤ h).hom f)) = valAt' y (m ⁻¹ᵁ W) (AB W f).2
    unfold valAt' valAt
    rw [dite_eq_left h2, e1, hAB W f, map_add (f := _), map_mul, e2, e2, e3, map_add (f := _), map_mul, e4]
    clear e1 e2 e3 e4 uniq hdec Aeq hAB hO hjO hpb hjρ hjπ hΦ hm
    have s1 := spec_pull (algebraMap ℂ (DualNumber ℂ)) (fun _ _ => trivial) ((y.appLE _ ⊤ h2).hom (AB W f).1)
    have s2 := spec_pull (algebraMap ℂ (DualNumber ℂ)) (fun _ _ => trivial) ((y.appLE _ ⊤ h2).hom (AB W f).2)
    rw [s1, s2]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KS.EpsDer
end
end

