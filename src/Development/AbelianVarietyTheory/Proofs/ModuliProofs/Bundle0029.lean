module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sab_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) {e : S'' ⟶ S} (he : g ≫ f = e) :
    ∃ n : SABMap t'' t e, n.φ = m'.φ ≫ m.φ := by
  subst he
  exact sabComp pullCubComp E H S S' S'' t t' t'' f g m m'

theorem sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {e : S'' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t e) (g : S'' ⟶ S') (he : g ≫ f = e) :
    ∃ m' : SABMap t'' t' g, m'.φ ≫ m.φ = n.φ := by
  subst he
  obtain ⟨m', h⟩ := sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n
  exact ⟨m', h.symm⟩

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) (x : 𝟙_ (Over S'') ⟶ t''.G) (y : 𝟙_ (Over S') ⟶ t'.G)
    (h : x.left ≫ m'.φ ≫ m.φ = g ≫ y.left ≫ m.φ) : x.left ≫ m'.φ = g ≫ y.left := by
  apply m.cart.1.hom_ext
  · simpa only [Category.assoc] using h
  · have a₁ : x.left ≫ t''.G.hom = 𝟙 _ := Over.w x
    have a₂ : y.left ≫ t'.G.hom = 𝟙 _ := Over.w y
    rw [Category.assoc, m'.cart.1.w, ← Category.assoc, a₁, Category.assoc, a₂]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_pow {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (x : 𝟙_ (Over S') ⟶ t'.G) (y : 𝟙_ (Over S) ⟶ t.G)
    (h : x.left ≫ m.φ = f ≫ y.left) (k : ℕ) : (x ^ k).left ≫ m.φ = f ≫ (y ^ k).left := by
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e : pushHom m.cart _ x = preHom U y := Over.OverMorphism.ext h
  have e' : pushHom m.cart _ (x ^ k) = preHom U (y ^ k) := by rw [map_pow, map_pow, e]
  exact congrArg (fun z => z.left) e'

theorem zeta_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := by rintro rfl; simp at hb
  have hk : k ≠ 0 := by rintro rfl; simp at hb
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp

noncomputable def baseOf (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) : Base l F where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := (IntermediateField.inclusion h).toRingHom (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := (IntermediateField.inclusion h).toRingHom (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (RingHom.injective _)

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem spMap_inclusion_self {F : IntermediateField ℚ ℂ} (h : F ≤ F) :
    spMap (IntermediateField.inclusion h).toRingHom = 𝟙 (Sp F) := by
  rw [← spMap_id']
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext (IntermediateField.coe_inclusion h x))

theorem baseOf_rho_coe (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) :
    (((baseOf l F h).ρ : F) : ℂ) = H.rt0 := IntermediateField.coe_inclusion h (baseKA l).ρ

theorem baseOf_rho (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) :
    (baseOf l F h).ρ = (baseOf l₂ F h₂).ρ :=
  Subtype.ext ((baseOf_rho_coe l F h).trans (baseOf_rho_coe l₂ F h₂).symm)

theorem baseOf_zeta (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) (hd : l.A ∣ l₂.A) :
    (baseOf l F h).ζ = (baseOf l₂ F h₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (IntermediateField.coe_inclusion h _).trans ((zeta_dvd l₂.A_pos hd).trans
    (congrArg (· ^ (l₂.A / l.A)) (IntermediateField.coe_inclusion h₂ (baseKA l₂).ζ).symm)))

def ObjCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)

variable {D : Datum H} {l l₂ : Level H}

def Represents {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B} (o : Obj D l b s) : Prop :=
  ∀ (S : Scheme.{0}) (s' : S ⟶ Sp B) (o' : Obj D l b s'), IsReduced S →
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o' o f)

theorem represents_pullback (hC : ObjCompSt) (Xo : Moduli D l) {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B)
    (hR : ∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S →
      ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    {s : pullback Xo.s (spMap j) ⟶ Sp B} (hs : s = pullback.snd _ _) (o : Obj D l b s)
    (mo : ObjMap o Xo.univ (pullback.fst _ _)) : Represents o := by
  subst hs
  intro S s' o' hS
  obtain ⟨g, ⟨hg, ⟨u⟩⟩, huniq⟩ := hR S s' o' hS
  have hl : pullback.lift g s' hg ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  refine ⟨pullback.lift g s' hg, ⟨pullback.lift_snd _ _ _, ?_⟩, ?_⟩
  · obtain ⟨u', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ (pullback.lift g s' hg) mo).2
      (hl.symm ▸ u)
    exact ⟨u'⟩
  · rintro f ⟨hf, ⟨v⟩⟩
    apply pullback.hom_ext
    · rw [hl]
      obtain ⟨v', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ f mo).1 v
      exact huniq _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hf], ⟨v'⟩⟩
    · rw [hf, pullback.lift_snd]

theorem iso_cover (hC : ObjCompSt) {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} (k k' : ℕ)
    {X X₂ Y : Scheme.{0}} {s : X ⟶ Sp B} {r : X₂ ⟶ X} {π : Y ⟶ X} (o : Obj D l b s) (o₂ : Obj D l₂ b₂ (r ≫ s))
    (oc : Obj D l₂ b₂ (π ≫ s)) (o₁ : Obj D l b (π ≫ s)) (n : ObjMap o₁ o π)
    (m : SABMap o₂.t o.t r) (mc : SABMap oc.t o.t π)
    (hm : (∀ a, (o₂.eta a ^ k).left ≫ m.φ = r ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ k').left ≫ m.φ = r ≫ (o.etaA a).left))
    (hmc : (∀ a, (oc.eta a ^ k).left ≫ mc.φ = π ≫ (o.eta a).left) ∧
      (∀ a, (oc.etaA a ^ k').left ≫ mc.φ = π ≫ (o.etaA a).left))
    (hX : Represents o) (hX₂ : Represents o₂) (rX₂ : IsReduced X₂) (rY : IsReduced Y)
    (rig : ∀ m m' : SABMap o₁.t o.t π, (∀ a, ∃ σ, (o₁.eta a).left ≫ m.φ = σ ∧ (o₁.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (univ : ∀ (T : Scheme.{0}) (f : T ⟶ X) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f),
      (∀ a, (o'.eta a ^ k).left ≫ m'.φ = f ≫ (o.eta a).left) ∧
        (∀ a, (o'.etaA a ^ k').left ≫ m'.φ = f ≫ (o.etaA a).left) →
      ∃! h : T ⟶ Y, h ≫ π = f ∧ ∃ u : ObjMap o' oc h, u.toSABMap.φ ≫ mc.φ = m'.φ) :
    ∃ h : X₂ ⟶ Y, IsIso h ∧ h ≫ π = r := by
  obtain ⟨h, ⟨hh, u, hu⟩, -⟩ := univ X₂ r o₂ m hm
  obtain ⟨g, ⟨hg, ⟨w⟩⟩, -⟩ := hX₂ Y (π ≫ s) oc rY
  obtain ⟨v, hv⟩ := sab_cancel mc n.toSABMap (𝟙 Y) (Category.id_comp _)
  have v₁ : ∀ a, (o₁.eta a).left ≫ v.φ = (oc.eta a ^ k).left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.1, Category.id_comp]; exact n.eta a)).trans (Category.id_comp _)
  have v₂ : ∀ a, (o₁.etaA a).left ≫ v.φ = (oc.etaA a ^ k').left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.2, Category.id_comp]; exact n.etaA a)).trans (Category.id_comp _)
  obtain ⟨vw, hvw⟩ := sab_comp v w.toSABMap (Category.id_comp g)
  have key : ∀ (e : Y ⟶ X) (he : g ≫ r = e), ∃ z : ObjMap o₁ o e, z.toSABMap.φ = v.φ ≫ w.toSABMap.φ ≫ m.φ := by
    intro e he
    obtain ⟨z, hz⟩ := sab_comp vw m he
    rw [hvw, Category.assoc] at hz
    refine ⟨⟨z, fun a => ?_, fun a => ?_⟩, hz⟩
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₁, ← Category.assoc, sec_pow w.toSABMap _ _ (w.eta a), Category.assoc, hm.1,
        ← Category.assoc, he]
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₂, ← Category.assoc, sec_pow w.toSABMap _ _ (w.etaA a), Category.assoc, hm.2,
        ← Category.assoc, he]
  have hgr : g ≫ r = π := by
    obtain ⟨z, -⟩ := key _ rfl
    exact (hX Y (π ≫ s) o₁ rY).unique ⟨by rw [Category.assoc, hg], ⟨z⟩⟩ ⟨rfl, ⟨n⟩⟩
  obtain ⟨z, hz⟩ := key _ hgr
  have hzn : z.toSABMap.φ = n.toSABMap.φ := rig _ _ fun a => ⟨_, z.eta a, n.eta a⟩
  have : IsIso v.φ := v.cart.1.isIso_fst_of_isIso
  have hwm : w.toSABMap.φ ≫ m.φ = mc.φ := by
    rw [← cancel_epi v.φ, ← hz, hzn, hv]
  refine ⟨h, ⟨g, ?_, ?_⟩, hh⟩
  · obtain ⟨x, -⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ oc o₂).2 g h w).1 u
    obtain ⟨y, -⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₂ o₂).1
    exact (hX₂ X₂ (r ≫ s) o₂ rX₂).unique
      ⟨by rw [Category.assoc, hg, ← Category.assoc, hh], ⟨x⟩⟩ ⟨Category.id_comp _, ⟨y⟩⟩
  · obtain ⟨x, hx⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc o₂ oc).2 h g u).1 w
    obtain ⟨y, hy⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc oc oc).1
    exact (univ Y π oc mc hmc).unique
      ⟨by rw [Category.assoc, hh, hgr], x, by rw [hx, Category.assoc, hu, hwm]⟩
      ⟨Category.id_comp _, y, by rw [hy, Category.id_comp]⟩

end GlobalTheory.LevelCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MinkowskiDivisible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace MinkDiv

variable {A : Type} [AddCommGroup A]

theorem iterate_eq (f g : A →+ A) (hfg : ∀ z, f z = z + g z) (y : A) (hy : g (g (g y)) = 0)
    (n : ℕ) : f^[n] y = y + n • g y + (n.choose 2) • g (g y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, hfg y,
      hfg (g y), hfg (g (g y)), hy, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    simp only [add_nsmul, smul_add, one_nsmul, add_zero]
    abel

theorem prime_case (l p : ℕ) (hl : l.Prime) (ho : Odd l) (hp : p.Prime) (f : A →+ A)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x)
    (hord : ∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[p] x = x)
    (hfix : ∀ x : A, l • x = 0 → f x = x) :
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  set g : A →+ A := f - AddMonoidHom.id A with hg
  have hfg : ∀ z, f z = z + g z := fun z => by simp [hg]
  have key : ∀ k : ℕ, ∀ x : A, l ^ (k + 1) • x = 0 → g x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have := hfix x (by simpa using hx)
      simp [hg, this]
    | succ k ih =>
      intro x hx
      have h1 : ∀ z : A, l • z = 0 → g z = 0 := fun z hz =>
        ih z (by rw [pow_succ, mul_smul, hz, smul_zero])
      have h2 : ∀ z : A, l ^ (k + 1 + 1) • z = 0 → l • g z = 0 := fun z hz => by
        rw [← map_nsmul]
        exact ih _ (by rw [← mul_smul, ← pow_succ]; exact hz)
      by_cases hpl : p = l
      · subst hpl
        obtain ⟨y, rfl⟩ := hdiv x
        have hy : p ^ (k + 1 + 1 + 1) • y = 0 := by rw [pow_succ, mul_smul]; exact hx
        have e1 : p • p • g y = 0 := by
          rw [← map_nsmul g p y]; exact h2 _ hx
        have e2 : p • g (g y) = 0 := by
          apply h2
          rw [pow_succ, pow_succ, mul_smul, mul_smul, e1, smul_zero]
        have e3 : g (g (g y)) = 0 := h1 _ e2
        have e4 := iterate_eq f g hfg y e3 p
        rw [hord y _ hy] at e4
        have h3 : 2 < p := by
          rcases hp.two_le.lt_or_eq with h | h
          · exact h
          · subst h; exact absurd ho (by decide)
        obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) (by norm_num) h3
        rw [hc, mul_comm, mul_smul, e2, smul_zero, add_zero] at e4
        rw [map_nsmul]
        exact (add_eq_left.mp e4.symm)
      · have e1 : l • g x = 0 := h2 x hx
        have e2 : g (g x) = 0 := h1 _ e1
        have e4 := iterate_eq f g hfg x (by rw [e2, map_zero]) p
        rw [hord x _ hx, e2, smul_zero, add_zero] at e4
        have e5 : p • g x = 0 := add_eq_left.mp e4.symm
        have hc : Nat.Coprime p l := (Nat.coprime_primes hp hl).mpr hpl
        have d1 := addOrderOf_dvd_of_nsmul_eq_zero e5
        have d2 := addOrderOf_dvd_of_nsmul_eq_zero e1
        have d3 := Nat.dvd_gcd d1 d2
        rw [hc, Nat.dvd_one] at d3
        exact AddMonoid.addOrderOf_eq_one_iff.mp d3
  intro a x hx
  have := key a x (by rw [pow_succ', mul_smul, hx, smul_zero])
  rw [hfg, this, add_zero]

theorem add_case (l : ℕ) (hl : l.Prime) (ho : Odd l)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x) (r : ℕ) (hr : r ≠ 0) :
    ∀ f : AddMonoid.End A, (∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[r] x = x) →
    (∀ x : A, l • x = 0 → f x = x) →
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  induction r using induction_on_primes with
  | zero => exact absurd rfl hr
  | one => intro f h _ a x hx; exact h x a hx
  | prime_mul p b hp ih =>
    intro f hord hfix
    have hb : b ≠ 0 := by rintro rfl; simp at hr
    have hc : ((f ^ p : AddMonoid.End A) : A → A) = f^[p] := AddMonoid.End.coe_pow _ _ _
    have := ih hb (f ^ p)
      (fun x a hx => by rw [hc, ← Function.iterate_mul]; exact hord x a hx)
      (fun x hx => by rw [hc]; exact Function.iterate_fixed (hfix x hx) p)
    exact prime_case l p hl ho hp f hdiv
      (fun x a hx => by have h := this a x hx; rw [hc] at h; exact h) hfix

end MinkDiv

theorem minkowski_divisible : ∀ (Q : Type) [CommGroup Q] (l : ℕ) (u : Q ≃* Q) (r : ℕ), l.Prime → Odd l → 0 < r → (∀ x : Q, ∃ y : Q, y ^ l = x) → (∀ x, u^[r] x = x) → (∀ x, x ^ l = 1 → u x = x) → ∀ (x : Q) (a : ℕ), x ^ (l ^ a) = 1 → u x = x := by
  intro Q _ l u r hl ho hr hdiv hord hfix x a hx
  exact MinkDiv.add_case (A := Additive Q) l hl ho (fun x => hdiv x.toMul) r hr.ne'
    (MonoidHom.toAdditive u.toMonoidHom) (fun x _ _ => hord x.toMul) (fun x hx => hfix x.toMul hx)
    a (Additive.ofMul x) hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ObjLower

section Identity

variable {X : Scheme.{0}}

def idIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)

theorem gw_idIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gw (idIso L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _

theorem pgen_idIso {L : LB X} (hL : L.IsLB) : PGen (idIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_idIso L f y j k hj hk, gw_idIso L f y j' k' hj' hk', Category.comp_id,
    ← gm_cocycle hL f y hj' hk hk', ← gm_cocycle hL f y hj hj' hk]
  generalize gm f y _ (L.g j j') = A
  generalize gm f y _ (L.g j' k) = B
  generalize gm f y _ (L.g k k') = C
  rw [_root_.mul_assoc, mul_comm B C, inv_mul_cancel_left]

theorem pmaps_idIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans ?_))
  refine congrArg₂ (· * ·) ?_ (gm_res r z _ hm _)
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idIso L (r ≫ φ k) z (p k) (q k) (hp k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp k, hq k⟩ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def cubeId (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

def sabId (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeId t.G
  cart := by
    refine ⟨(IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 t.G.left) t.G.hom t.G.hom (𝟙 S)),
      fun T x y x₀ y₀ hx hy => ?_⟩
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))
  base := rfl
  act := fun a => by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
  lin := (isPullCubical_iff _ _ _).2 ⟨idIso t.PP.L, pgen_idIso t.PP.isLB,
    pmaps_idIso _ _ _ _ t.PP.rigGen, pmaps_idIso _ _ _ _ t.cub.isGen⟩

end Identity

section Ideals

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem quot_mul_mem {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E} (hx : x ∈ l.Mb) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb := by
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 h.2.1
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
  have e : Ideal.span {(l.M : 𝓞 E)} * (J * J.map (H.bar : 𝓞 E →+* 𝓞 E)) =
      Ideal.span {(l.M : 𝓞 E)} * Ideal.span {((l₂.M / l.M : ℕ) : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, Nat.mul_div_cancel' h.1, ← l₂.prod, ← l.prod, hJ,
      Ideal.map_mul]
    ring
  have hk : ((l₂.M / l.M : ℕ) : 𝓞 E) ∈ J := by
    apply (Ideal.mul_le_left : J * J.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ J)
    rw [mul_left_cancel₀ h0 e]
    exact Ideal.mem_span_singleton_self _
  rw [hJ, mul_comm _ x]
  exact Ideal.mul_mem_mul hx hk

theorem quot_mul_mem_map {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E}
    (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hx
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (quot_mul_mem h hy)
  rwa [map_mul, map_natCast] at this

theorem nsmul_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R} {n : ℕ}
    (h : ∀ x ∈ I, (n : R) * x ∈ J) {a : M} (ha : a ∈ I • (⊤ : Submodule R M)) :
    n • a ∈ J • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on ha (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [← Nat.cast_smul_eq_nsmul R, smul_smul]
    exact Submodule.smul_mem_smul (h r hr) trivial
  · rw [smul_add]; exact add_mem hx hy

end Ideals

theorem map_nsmul_of_add {A Q : Type*} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : A) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}
  {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def lower (o₂ : Obj D l₂ b₂ s) (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) : Obj D l b s where
  t := o₂.t
  proper := o₂.proper
  ample := o₂.ample
  ktriv := o₂.ktriv
  eta a := o₂.eta a ^ (l₂.M / l.M)
  eta_add a c := by rw [o₂.eta_add, mul_pow]
  eta_ker a ha := by
    rw [← map_nsmul_of_add _ o₂.eta_add]
    exact o₂.eta_ker _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem h hx) ha)
  etaA a := o₂.etaA a ^ (l₂.A / l.A)
  etaA_add a c := by rw [o₂.etaA_add, mul_pow]
  etaA_ker a := by
    rw [← map_nsmul_of_add _ o₂.etaA_add, smul_smul, Nat.div_mul_cancel h.2.2, o₂.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, h₁, h₂, h₃⟩ := o₂.geom k x β hx
    have hA : 0 < l₂.A / l.A := Nat.div_pos (Nat.le_of_dvd l₂.A_pos h.2.2) l.A_pos
    have hM₁ : 0 < l.M := by have := l.three_le; omega
    have hM₂ : 0 < l₂.M := by have := l₂.three_le; omega
    have hM : 0 < l₂.M / l.M := Nat.div_pos (Nat.le_of_dvd hM₂ h.1) hM₁
    refine ⟨hρ ▸ hd, I, ?_, fun a => ?_, fun a ha => ?_⟩
    · rw [hζ, map_pow, ← h₁, ← I.ζ_pow l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2, Units.val_pow_eq_pow_val]
    · rw [MonObj.comp_pow, h₂, ← I.tower l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2]
    · rw [← map_nsmul_of_add _ o₂.eta_add,
        h₃ _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem_map h hx) ha),
        map_nsmul_of_add _ (I.add _), ← I.tower l.M _ hM₁ hM, Nat.mul_div_cancel' h.1]

end GlobalTheory.ObjLower

namespace GlobalTheory

theorem obj_lower_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) →
    ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)),
      (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left) := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o₂ h hρ hζ
  exact ⟨ObjLower.lower o₂ h hρ hζ, ObjLower.sabId o₂.t,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩

end GlobalTheory
end
end

