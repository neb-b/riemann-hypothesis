module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfComp
section
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DPLoc

variable {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
  [IsLocalization M S] {J : Ideal B} (δ : DividedPowers J)


include M in
theorem wellDef {u v : S} {j j' : B} (hj : j ∈ J) (hj' : j' ∈ J)
    (h : u * algebraMap B S j = v * algebraMap B S j') (n : ℕ) :
    u ^ n * algebraMap B S (δ.dpow n j) = v ^ n * algebraMap B S (δ.dpow n j') := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M u
  obtain ⟨⟨c, t⟩, hc⟩ := IsLocalization.surj M v
  simp only at ha hc
  have h1 : algebraMap B S (a * t * j) = algebraMap B S (c * s * j') := by
    simp only [map_mul, ← ha, ← hc]
    linear_combination (algebraMap B S s * algebraMap B S t) * h
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M S).1 h1
  have h2 : ((m : B) * (a * t)) ^ n * δ.dpow n j = ((m : B) * (c * s)) ^ n * δ.dpow n j' := by
    rw [← δ.dpow_mul hj, ← δ.dpow_mul hj']
    congr 1
    linear_combination hm
  have h3 := congrArg (algebraMap B S) h2
  simp only [map_mul, map_pow, ← ha, ← hc, mul_pow] at h3
  have hu : IsUnit ((algebraMap B S m) ^ n * (algebraMap B S s) ^ n * (algebraMap B S t) ^ n) :=
    (((IsLocalization.map_units S m).pow n).mul ((IsLocalization.map_units S s).pow n)).mul
      ((IsLocalization.map_units S t).pow n)
  apply hu.mul_left_cancel
  linear_combination h3


include M in
theorem rep₂ {x y : S} (hx : x ∈ J.map (algebraMap B S)) (hy : y ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j j' : B), j ∈ J ∧ j' ∈ J ∧ x = u * algebraMap B S j ∧
      y = u * algebraMap B S j' := by
  obtain ⟨⟨j, s⟩, hj⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  obtain ⟨⟨j', t⟩, hj'⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hy
  simp only at hj hj'
  obtain ⟨u, hu⟩ := (IsLocalization.map_units S (s * t)).exists_left_inv
  simp only [Submonoid.coe_mul, map_mul] at hu
  refine ⟨u, t * j, s * j', J.mul_mem_left _ j.2, J.mul_mem_left _ j'.2, ?_, ?_⟩
  · rw [map_mul, ← hj]; linear_combination (-x) * hu
  · rw [map_mul, ← hj']; linear_combination (-y) * hu


include M in
theorem rep {x : S} (hx : x ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j : B), j ∈ J ∧ x = u * algebraMap B S j := by
  obtain ⟨u, j, _, hj, _, e, _⟩ := rep₂ M hx hx
  exact ⟨u, j, hj, e⟩


open Classical in
def ext (n : ℕ) (x : S) : S :=
  if h : ∃ p : S × B, p.2 ∈ J ∧ x = p.1 * algebraMap B S p.2 then
    h.choose.1 ^ n * algebraMap B S (δ.dpow n h.choose.2) else 0


include M in
theorem ext_eq (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    ext δ n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) := by
  have h : ∃ p : S × B, p.2 ∈ J ∧ u * algebraMap B S j = p.1 * algebraMap B S p.2 :=
    ⟨(u, j), hj, rfl⟩
  rw [ext, dite_eq_left h]
  exact (wellDef M δ hj h.choose_spec.1 h.choose_spec.2 n).symm

def dp : DividedPowers (J.map (algebraMap B S)) where
  dpow := ext δ
  dpow_null {n x} hx := by
    rw [ext, dite_eq_right]
    rintro ⟨p, hp, rfl⟩
    exact hx (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hp))
  dpow_zero hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_zero hj]
  dpow_one hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_one hj]
  dpow_mem hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (δ.dpow_mem hn hj))
  dpow_add hx hy := by
    obtain ⟨u, j, j', hj, hj', rfl, rfl⟩ := rep₂ M hx hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← mul_add, ← map_add (f := _), ext_eq M δ _ _ (J.add_mem hj hj'), δ.dpow_add hj hj', map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj', ← (Finset.HasAntidiagonal.mem_antidiagonal.1 hk : k.1 + k.2 = _), map_mul]
    ring
  dpow_mul hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [← mul_assoc, ext_eq M δ _ _ hj, ext_eq M δ _ _ hj]
    ring
  mul_dpow {m n x} hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    have := congrArg (algebraMap B S) (δ.mul_dpow (m := m) (n := n) hj)
    rw [map_mul, map_mul, map_natCast] at this
    simp only [ext_eq M δ _ _ hj]
    linear_combination u ^ (m + n) * this
  dpow_comp {m n x} hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj, ext_eq M δ _ _ (δ.dpow_mem hn hj),
      δ.dpow_comp hn hj, map_mul, map_natCast]
    ring

theorem dp_dpow (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    (dp M δ).dpow n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) :=
  ext_eq M δ n u hj

theorem isDPMorphism : IsDPMorphism δ (dp (S := S) M δ) (algebraMap B S) :=
  ⟨le_rfl, fun {n} a ha ↦ by simpa using dp_dpow M δ n (1 : S) ha⟩

theorem isNilDP (h : IsNilDP δ) : IsNilDP (dp (S := S) M δ) := by
  obtain ⟨N, h⟩ := h
  have key : ∀ l : List (ℕ × S), (∀ p ∈ l, p.2 ∈ J.map (algebraMap B S)) →
      ∃ (c : S) (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) ∧
        (l'.map Prod.fst).sum = (l.map Prod.fst).sum ∧
        (l.map fun p ↦ (dp M δ).dpow p.1 p.2).prod =
          c * algebraMap B S (l'.map fun p ↦ δ.dpow p.1 p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ ↦ ⟨1, [], by simp⟩
    | cons p l ih =>
      intro hl
      obtain ⟨c, l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (by simp [hq])
      obtain ⟨u, j, hj, e⟩ := rep M (hl p (by simp))
      refine ⟨u ^ p.1 * c, (p.1, j) :: l', ?_, by simp [h2], ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        exacts [hj, h1 q hq]
      · simp only [List.map_cons, List.prod_cons, map_mul]
        rw [h3, e, dp_dpow M δ _ _ hj]
        ring
  refine ⟨N, fun l hl hN ↦ ?_⟩
  obtain ⟨c, l', h1, h2, h3⟩ := key l hl
  rw [h3, h l' h1 (h2 ▸ hN), map_zero, mul_zero]

theorem isDPMorphism_of_comp {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'')
    (g : S →+* C) (h : IsDPMorphism δ δ'' (g.comp (algebraMap B S))) :
    IsDPMorphism (dp M δ) δ'' g := by
  refine ⟨by rw [Ideal.map_map]; exact h.1, fun {n} x hx ↦ ?_⟩
  obtain ⟨u, j, hj, rfl⟩ := rep M hx
  have hm : g (algebraMap B S j) ∈ J'' := h.1 (Ideal.mem_map_of_mem _ hj)
  have e : δ''.dpow n (g (algebraMap B S j)) = g (algebraMap B S (δ.dpow n j)) := h.2 j hj
  rw [dp_dpow M δ _ _ hj, map_mul, δ''.dpow_mul hm, e, map_mul, map_pow]

theorem exists_away : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (b : B), IsNilDP δ → ∃ δ' : DividedPowers (J.map (algebraMap B (Localization.Away b))), IsNilDP δ' ∧ IsDPMorphism δ δ' (algebraMap B (Localization.Away b)) ∧ ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : Localization.Away b →+* C), IsDPMorphism δ δ'' (g.comp (algebraMap B _)) → IsDPMorphism δ' δ'' g :=
  fun _ _ _ δ b h ↦ ⟨dp (Submonoid.powers b) δ, isNilDP _ δ h, isDPMorphism _ δ,
    fun _ _ _ δ'' g hg ↦ isDPMorphism_of_comp _ δ δ'' g hg⟩

end GlobalTheory.DPLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.PullPt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S T : Scheme.{0}} {s : S ⟶ Sp R} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s} {o₁ : Obj b N s₁}

def ptOver (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : Over.mk (U.hom ≫ t) ⟶ o.A :=
  Over.homMk (g.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w g]
    rfl)

@[simp] theorem ptOver_left (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) :
    (ptOver m g).left = g.left ≫ m.φ := rfl

theorem ptOver_injective (m : ObjMap o₁ o t) {U : Over T} : Function.Injective (ptOver m (U := U)) := by
  intro g h e
  have e' : g.left ≫ m.φ = h.left ≫ m.φ := by
    rw [← ptOver_left m g, ← ptOver_left m h, e]
  ext
  exact m.cart.1.hom_ext e' (by rw [Over.w g, Over.w h])

theorem ptOver_surjective (m : ObjMap o₁ o t) {U : Over T} : Function.Surjective (ptOver m (U := U)) := by
  intro g₀
  refine ⟨Over.homMk (m.cart.1.lift g₀.left U.hom (by rw [Over.w g₀]; rfl)) (m.cart.1.lift_snd _ _ _), ?_⟩
  ext
  simp [ptOver, m.cart.1.lift_fst]

theorem ptOver_mul (m : ObjMap o₁ o t) {U : Over T} (g h : U ⟶ o₁.A) :
    ptOver m (g * h) = ptOver m g * ptOver m h := by
  ext
  exact (m.cart.2 U g h (ptOver m g) (ptOver m h) rfl rfl).symm

theorem ptOver_one (m : ObjMap o₁ o t) {U : Over T} : ptOver m (1 : U ⟶ o₁.A) = 1 := by
  have h := ptOver_mul m (1 : U ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOver_eq_one (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) : ptOver m g = 1 ↔ g = 1 := by
  rw [← ptOver_one m]
  exact (ptOver_injective m).eq_iff

theorem ptOver_act (m : ObjMap o₁ o t) {U : Over T} (g : U ⟶ o₁.A) (c : D.O) :
    ptOver m (g ≫ o₁.act.act c) = ptOver m g ≫ o.act.act c := by
  ext
  simp [ptOver, m.act]

theorem ptOf_eq (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk (𝟙 T) (by simp) : Over.mk ((𝟙_ (Over T)).hom ≫ t) ⟶ Over.mk t) ≫ ptOf m g = ptOver m g := by
  ext
  simp [ptOf, ptOver]

theorem ptOf_injective (m : ObjMap o₁ o t) : Function.Injective (ptOf m) := by
  intro g h e
  apply ptOver_injective m
  rw [← ptOf_eq, ← ptOf_eq, e]

theorem ptOf_mul (m : ObjMap o₁ o t) (g h : 𝟙_ (Over T) ⟶ o₁.A) :
    ptOf m (g * h) = ptOf m g * ptOf m h := by
  have e := ptOf_eq m (g * h)
  rw [ptOver_mul, ← ptOf_eq, ← ptOf_eq, ← comp_mul] at e
  ext
  have e' := congrArg CommaMorphism.left e
  simpa using e'

theorem ptOf_one (m : ObjMap o₁ o t) : ptOf m (1 : 𝟙_ (Over T) ⟶ o₁.A) = 1 := by
  have h := ptOf_mul m (1 : 𝟙_ (Over T) ⟶ o₁.A) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem ptOf_act (m : ObjMap o₁ o t) (g : 𝟙_ (Over T) ⟶ o₁.A) (c : D.O) :
    ptOf m (g ≫ o₁.act.act c) = ptOf m g ≫ o.act.act c := by
  ext
  simp [ptOf, m.act]

theorem homMk_ptOf (m : ObjMap o₁ o t) {k : Type} [Field k] (x : Sp k ⟶ T) (g : 𝟙_ (Over T) ⟶ o₁.A) :
    (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m g =
      ptOver m (toUnit (Over.mk x) ≫ g) := by
  ext
  simp [ptOf, ptOver]

end GlobalTheory.UPel.HT.EtLev.PullPt

namespace GlobalTheory.UPel.HT.EtLev

open PullPt

theorem isEtLev_iff_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S T : Scheme.{0}) (s : S ⟶ Sp R) (t : T ⟶ S) (s₁ : T ⟶ Sp R) (o : Obj b N s) (o₁ : Obj b N s₁)
    (m : ObjMap o₁ o t) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)),
    IsEtLev o₁ w0 r l ↔ IsEtLevOver o w0 r (T := Over.mk t) (fun y => ptOf m (l y)) := by
  intro p _ D R _ b N S T s t s₁ o o₁ m w0 r l
  have hadd : (∀ x y, l (x + y) = l x * l y) ↔ (∀ x y, ptOf m (l (x + y)) = ptOf m (l x) * ptOf m (l y)) := by
    refine forall₂_congr fun x y => ?_
    rw [← ptOf_mul, (ptOf_injective m).eq_iff]
  have hlin : (∀ (c : D.O) x, l (c • x) = l x ≫ o₁.act.act c) ↔
      (∀ (c : D.O) x, ptOf m (l (c • x)) = ptOf m (l x) ≫ o.act.act c) := by
    refine forall₂_congr fun c x => ?_
    rw [← ptOf_act, (ptOf_injective m).eq_iff]
  have hker : (∀ x ∈ wSub D w0 r, l x = 1) ↔ (∀ x ∈ wSub D w0 r, ptOf m (l x) = 1) := by
    refine forall₂_congr fun x _ => ?_
    rw [← ptOf_one m, (ptOf_injective m).eq_iff]
  have hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T),
      ((∀ y, toUnit (Over.mk x) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk x ⟶ o₁.A, (∀ c ∈ w0 ^ r, g ≫ o₁.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, toUnit (Over.mk x) ≫ l y = g) ↔
      ((∀ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = 1 → y ∈ wSub D w0 r) ∧
        ∀ g : Over.mk (x ≫ (Over.mk t).hom) ⟶ o.A,
          (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, (Over.homMk x rfl : Over.mk (x ≫ (Over.mk t).hom) ⟶ Over.mk t) ≫ ptOf m (l y) = g) := by
    intro k _ _ x
    simp only [homMk_ptOf]
    refine and_congr (forall_congr' fun y => by rw [ptOver_eq_one]) ?_
    constructor
    · intro h g₀ hg₀
      obtain ⟨g, rfl⟩ := ptOver_surjective m (U := Over.mk x) g₀
      obtain ⟨y, hy⟩ := h g (fun c hc => by rw [← ptOver_eq_one m, ptOver_act]; exact hg₀ c hc)
      exact ⟨y, by rw [hy]⟩
    · intro h g hg
      obtain ⟨y, hy⟩ := h (ptOver m g) (fun c hc => by rw [← ptOver_act, ptOver_eq_one]; exact hg c hc)
      exact ⟨y, ptOver_injective m hy⟩
  unfold IsEtLev IsEtLevOver
  rw [hadd, hlin, hker]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun x => hgeom k x)))

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesSectionQuotients
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

section QuotEtale

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {B : La} {t0 : ι → Y → ℂ} {t : Fin n → ι → Y → ℂ}

end QuotEtale

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] in
private lemma sec_eq_transition_mul {A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La} {B : La} {s : ι → Y → ℂ}
    (hs : A.IsSec B s) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : s i y = A.g B i j y * s j y := by
  have h := hs
  unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at h
  exact h.2 i j y (Set.mem_univ y) hi hj

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.etale_zmap_main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y),
    A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U →
    (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → _root_.GlobalTheory.OTY.Etale A U (A.zmap t0 t) := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t U h0 ht hU hcoord
  have hne : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source → t0 i y ≠ 0 := by
    intro i y hy hi
    rw [sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne B i _ y hi (A.mem_pick y)) (hcoord y hy).1
  have hz : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source →
      A.zmap t0 t y = A.zLoc t0 t i (A.chart i y) := by
    intro i y hy hi
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zmap _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    rw [(A.chart i).left_inv hi]
    congr 1
    funext k
    rw [sec_eq_transition_mul (ht k) hi (A.mem_pick y),
      sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact (mul_div_mul_left _ _ (A.g_ne B i _ y hi (A.mem_pick y))).symm
  have hloc : ∀ i, DifferentiableOn ℂ (A.zLoc t0 t i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
    intro i
    apply (differentiableOn_piLp (𝕜 := ℂ) 2).2
    intro k
    have hk := ht k
    have h0' := h0
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at hk h0'
    have hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
        (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, Set.mem_univ _⟩
    have hnum : DifferentiableOn ℂ (fun v => t k i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hk.1 i).mono hsub
    have hden : DifferentiableOn ℂ (fun v => t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (h0'.1 i).mono hsub
    have hdiv : DifferentiableOn ℂ
        (fun v => t k i ((A.chart i).symm v) / t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
      simp only [div_eq_mul_inv]
      exact hnum.mul (hden.inv fun v hv => hne i _ hv.2 ((A.chart i).map_target hv.1))
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    exact hdiv
  refine ⟨hU, ?_, ?_⟩
  · intro i
    refine (hloc i).congr ?_
    intro v hv
    simp only [Function.comp_apply]
    rw [hz i _ hv.2 ((A.chart i).map_target hv.1), (A.chart i).right_inv hv.1]
  · intro i y hy hi
    unfold _root_.GlobalTheory.OTY.jdet _root_.GlobalTheory.OTY.jz
    set j := A.pick y with hj_def
    have hj : y ∈ (A.chart j).source := A.mem_pick y
    have hV : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ (A.chart j).source) ∈
        𝓝 (A.chart i y) := by
      refine ((A.chart i).isOpen_inter_preimage_symm (hU.inter (A.chart j).open_source)).mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact ⟨hy, hj⟩
    have heq : A.zmap t0 t ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        A.zLoc t0 t j ∘ ((A.chart j) ∘ (A.chart i).symm) := by
      filter_upwards [hV] with v hv
      simp only [Function.comp_apply]
      exact hz j _ hv.2.1 hv.2.2
    rw [heq.fderiv_eq]
    have hT : DifferentiableAt ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) := by
      refine (A.holo_trans i j).differentiableAt ?_
      have ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
      refine ho.mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact hj
    have hTy : ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
    have hL : DifferentiableAt ℂ (A.zLoc t0 t j) (((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hTy]
      refine (hloc j).differentiableAt ?_
      refine ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ?_
      refine ⟨(A.chart j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.chart j).left_inv hj]
      exact hy
    rw [fderiv_comp _ hL hT, hTy]
    have hdet : LinearMap.det (((fderiv ℂ (A.zLoc t0 t j) (A.chart j y)).comp
        (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :
          _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) =
        LinearMap.det (fderiv ℂ (A.zLoc t0 t j) (A.chart j y) : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) *
          LinearMap.det (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) :
            _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :=
      LinearMap.det_comp _ _
    rw [ContinuousLinearMap.det, hdet]
    refine mul_ne_zero ?_ ?_
    · have hc := (hcoord y hy).2
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsCoordAt at hc
      exact hc
    · have hk := A.g_kap i j y hi hj
      have hg := A.g_ne A.kap i j y hi hj
      rw [hk] at hg
      exact hg

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenAtlasSectionNonvanishingSetAndMemIff
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isOpen_nz_and_mem_nz_iff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → IsOpen (nz A τ) ∧ ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ h
  have key : ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
    intro i y hy
    have e := h.2 i (A.pick y) y (Set.mem_univ _) hy (A.mem_pick y)
    have g := A.g_ne Λ i (A.pick y) y hy (A.mem_pick y)
    simp only [nz, Set.mem_setOf_eq, e, ne_eq, mul_eq_zero, g, false_or]
  refine ⟨?_, key⟩
  have cont : ∀ i, ContinuousOn (τ i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (τ i ∘ (A.chart i).symm) (A.chart i).target := by
      simpa using (h.1 i).continuousOn
    have h2 := h1.comp (A.chart i).continuousOn (A.chart i).mapsTo
    refine h2.congr ?_
    intro y hy
    simp [(A.chart i).left_inv hy]
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hs := (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousAt (τ (A.pick y)) y := (cont _).continuousAt hs
  have hne : τ (A.pick y) y ≠ 0 := hy
  filter_upwards [hs, hc.eventually_ne hne] with x hx hx'
  exact (key _ x hx).2 hx'

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubInStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) → In (J * N) (subst (up Q u) f - subst (up Q v) f) := by
  first | exact @GlobalTheory.KatzCongr.subst_sub_in | exact GlobalTheory.KatzCongr.subst_sub_in | (intros; apply GlobalTheory.KatzCongr.subst_sub_in <;> assumption)
end

