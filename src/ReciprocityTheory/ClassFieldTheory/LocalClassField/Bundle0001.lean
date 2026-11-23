module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA
public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandA

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandB
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

section Abstract

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {DA NA : A →+ A} {DB NB : B →+ B} {f : A →+ B}

def cokerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : B ⧸ f.range →+ B ⧸ f.range :=
  QuotientAddGroup.map _ _ DB (by
    rintro _ ⟨a, rfl⟩
    exact ⟨DA a, fD a⟩)

theorem ses_coker (hf : Injective f)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) :
    SES DA NA DB NB (cokerMap f fD) (cokerMap f fN) f (QuotientAddGroup.mk' f.range) := by
  refine ⟨hf, ?_, QuotientAddGroup.mk'_surjective _, fD, fN, fun _ => rfl, fun _ => rfl, DN, ND⟩
  intro b
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  rfl

theorem isFin_iff_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) : IsFin DA NA ↔ IsFin DB NB :=
  ⟨fun hA => isFin_mid (ses_coker hf fD fN DN ND) hA (isFin_of_finite _ _),
    fun hB => isFin_left (ses_coker hf fD fN DN ND) hB (isFin_of_finite _ _)⟩

theorem q_eq_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) (hA : IsFin DA NA) :
    q DA NA = q DB NB := by
  have h := ses_coker hf fD fN DN ND
  rw [q_mul h hA (isFin_of_finite _ _), q_of_finite _ _ h.DN_C h.swap.DN_C, mul_one]

end Abstract

section Cyclic

variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]

def dHom (ρ : Representation k G M) (g : G) : M →+ M := (ρ g - 1 : Module.End k M).toAddMonoidHom

def nHom (ρ : Representation k G M) : M →+ M := (ρ.norm : Module.End k M).toAddMonoidHom

@[simp] theorem dHom_apply (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g x = ρ g x - x := rfl

theorem nHom_apply (ρ : Representation k G M) (x : M) : nHom ρ x = ∑ c : G, ρ c x := by
  change ρ.norm x = _
  simp [Representation.norm]

theorem dHom_nHom (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g (nHom ρ x) = 0 := by
  change ρ g (ρ.norm x) - ρ.norm x = 0
  rw [Representation.self_norm_apply, sub_self]

theorem nHom_dHom (ρ : Representation k G M) (g : G) (x : M) : nHom ρ (dHom ρ g x) = 0 := by
  change ρ.norm (ρ g x - x) = 0
  rw [map_sub, Representation.norm_self_apply, sub_self]

theorem mem_ker_dHom_iff (ρ : Representation k G M) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : M) :
    x ∈ (dHom ρ g).ker ↔ ∀ c : G, ρ c x = x := by
  rw [AddMonoidHom.mem_ker, dHom_apply, sub_eq_zero,
    ← Representation.mem_invariants_iff_of_forall_mem_zpowers ρ g hg x]
  rfl

abbrev TateZerothCohomology (ρ : Representation k G M) (g : G) : Type _ := T (dHom ρ g) (nHom ρ)

abbrev H1 (ρ : Representation k G M) (g : G) : Type _ := T (nHom ρ) (dHom ρ g)

def HFin (ρ : Representation k G M) (g : G) : Prop := IsFin (dHom ρ g) (nHom ρ)

noncomputable def h (ρ : Representation k G M) (g : G) : ℚ := q (dHom ρ g) (nHom ρ)

theorem h_eq (ρ : Representation k G M) (g : G) :
    h ρ g = (Nat.card (TateZerothCohomology ρ g) : ℚ) / (Nat.card (H1 ρ g) : ℚ) := rfl

variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

theorem map_dHom (ρA : Representation k G A) (ρB : Representation k G B) (g : G) (i : A →+ B)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (a : A) : i (dHom ρA g a) = dHom ρB g (i a) := by
  rw [dHom_apply, dHom_apply, map_sub, hiG]

theorem map_nHom (ρA : Representation k G A) (ρB : Representation k G B) (i : A →+ B)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (a : A) : i (nHom ρA a) = nHom ρB (i a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [nHom_apply, nHom_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => hiG c a

theorem ses_of_rep (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b)) :
    SES (dHom ρA g) (nHom ρA) (dHom ρB g) (nHom ρB) (dHom ρC g) (nHom ρC) i p :=
  ⟨hi, hip, hp, map_dHom ρA ρB g i hiG, map_nHom ρA ρB i hiG, map_dHom ρB ρC g p hpG,
    map_nHom ρB ρC p hpG, dHom_nHom ρB g, nHom_dHom ρB g⟩

theorem h_mul (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b))
    (hA : HFin ρA g) (hC : HFin ρC g) : HFin ρB g ∧ h ρB g = h ρA g * h ρC g :=
  have hs := ses_of_rep ρA ρB ρC g i p hi hip hp hiG hpG
  ⟨isFin_mid hs hA hC, q_mul hs hA hC⟩

theorem h_eq_of_finiteIndex (ρA : Representation k G A) (ρB : Representation k G B) (g : G) (i : A →+ B)
    (hi : Injective i) (hfi : i.range.FiniteIndex) (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) :
    (HFin ρA g ↔ HFin ρB g) ∧ (HFin ρA g → h ρA g = h ρB g) :=
  ⟨isFin_iff_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g),
    q_eq_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g)⟩

theorem h_of_subsingleton (ρ : Representation k G M) (g : G) [Subsingleton (TateZerothCohomology ρ g)]
    [Subsingleton (H1 ρ g)] : HFin ρ g ∧ h ρ g = 1 := by
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rw [h_eq, Nat.card_of_subsingleton (0 : TateZerothCohomology ρ g), Nat.card_of_subsingleton (0 : H1 ρ g)]
  norm_num

theorem h_eq_card_H0hat (ρ : Representation k G M) (g : G) [Subsingleton (H1 ρ g)] :
    h ρ g = Nat.card (TateZerothCohomology ρ g) := by
  rw [h_eq, Nat.card_of_subsingleton (0 : H1 ρ g)]
  norm_num

theorem h_int (ρ : Representation ℤ G ℤ) (hρ : ∀ c x, ρ c x = x) (g : G) :
    HFin ρ g ∧ Nat.card (TateZerothCohomology ρ g) = Nat.card G ∧ Subsingleton (H1 ρ g) ∧ h ρ g = Nat.card G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hD : (dHom ρ g).ker = ⊤ := by
    ext x; simp [AddMonoidHom.mem_ker, hρ]
  have hNx : ∀ x, nHom ρ x = (Nat.card G : ℤ) * x := fun x => by
    rw [nHom_apply]; simp [hρ]
  have hN : (nHom ρ).range = AddSubgroup.zmultiples (Nat.card G : ℤ) := by
    ext x
    rw [Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
  have h0 : Nat.card (TateZerothCohomology ρ g) = Nat.card G := by
    change ((nHom ρ).range.addSubgroupOf (dHom ρ g).ker).index = _
    change (nHom ρ).range.relIndex (dHom ρ g).ker = _
    rw [hD, AddSubgroup.relIndex_top_right, hN, Int.index_zmultiples]
    simp
  have h1 : Subsingleton (H1 ρ g) := by
    have : Subsingleton (nHom ρ).ker := ⟨fun x y => by
      have hx : nHom ρ x = 0 := x.2
      have hy : nHom ρ y = 0 := y.2
      rw [hNx] at hx hy
      apply Subtype.ext
      have hne : (Nat.card G : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [(mul_eq_zero.1 hx).resolve_left hne, (mul_eq_zero.1 hy).resolve_left hne]⟩
    exact (QuotientAddGroup.mk_surjective).subsingleton
  refine ⟨⟨Nat.finite_of_card_ne_zero (by rw [h0]; exact hpos.ne'), inferInstance⟩, h0, h1, ?_⟩
  rw [h_eq_card_H0hat, h0]

end Cyclic

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandB
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]

def act (g : G) : Rˣ →* Rˣ := Units.map (MulSemiringAction.toRingHom G R g : R →* R)

theorem act_val (g : G) (u : Rˣ) : ((act g u : Rˣ) : R) = g • (u : R) := rfl


variable (G) in
def normU : Rˣ →* Rˣ := ∏ g : G, act g

theorem normU_val (u : Rˣ) : ((normU G u : Rˣ) : R) = ∏ g : G, g • (u : R) := by
  simp [normU, Units.coe_prod, act_val]

theorem smul_prod_univ (g : G) (x : R) : g • ∏ g' : G, g' • x = ∏ g' : G, g' • x := by
  rw [← MulSemiringAction.toRingHom_apply, map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

theorem prod_smul_smul (g : G) (x : R) : ∏ g' : G, g' • g • x = ∏ g' : G, g' • x := by
  simp only [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ fun _ => rfl

theorem sum_pow_eq {g₀ : G} (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (f : G → R) :
    ∑ k ∈ range (orderOf g₀), f (g₀ ^ k) = ∑ g, f g := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, sum_image]
  intro a ha b hb hab
  exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab

theorem telescope (g₀ : G) (z : R) (k : ℕ) :
    g₀ • ∑ j ∈ range k, g₀ ^ j • z - ∑ j ∈ range k, g₀ ^ j • z = g₀ ^ k • z - z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, smul_add, smul_smul, ← pow_succ']
    linear_combination ih

namespace Filt

variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem act_mem {n : ℕ} (g : G) {u : Rˣ} (hu : u ∈ h.V n) : act g u ∈ h.V n := by
  rw [mem_V, act_val]
  have := h.smul n g _ hu
  rwa [smul_sub, smul_one] at this

theorem normU_mem {n : ℕ} {u : Rˣ} (hu : u ∈ h.V n) : normU G u ∈ h.V n := by
  rw [normU, MonoidHom.finsetProd_apply]
  exact (h.V n).prod_mem fun g _ => h.act_mem g hu

theorem norm_surj (u : Rˣ) (hu : (u : R) - 1 ∈ I 0) (hfix : ∀ g : G, g • (u : R) = u) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ ∏ g : G, g • (v : R) = u := by
  let Z : Subgroup Rˣ :=
    { carrier := {u | ∀ g : G, act g u = u}
      one_mem' := fun g => map_one _
      mul_mem' := fun {a b} ha hb g => by rw [map_mul, ha g, hb g]
      inv_mem' := fun {a} ha g => by rw [map_inv, ha g] }
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ Z → ∃ v ∈ h.V n, u / normU G v ∈ h.V (n + 1) := by
    intro n u hu hZ
    have hx : ∀ g : G, g • ((u : R) - 1) = (u : R) - 1 := fun g => by
      rw [smul_sub, smul_one, ← act_val, hZ g]
    have hy : e ((u : R) - 1) ∈ I n := h.e_mem n _ hu
    have htr : ∑ g : G, g • e ((u : R) - 1) = (u : R) - 1 := by
      conv_rhs => rw [← h.e_sum ((u : R) - 1)]
      exact Finset.sum_congr rfl fun g _ => by rw [hx]
    refine ⟨h.mkU _ (h.le_zero n hy), h.mkU_mem _ hy, h.div_mem_V (h.normU_mem (h.mkU_mem _ (h.le_zero n hy))) ?_⟩
    have hp := h.prod_one_add (n := n) univ (fun g : G => g • e ((u : R) - 1)) (fun g _ => h.smul n g _ hy)
    rw [htr] at hp
    rw [normU_val, mkU_val]
    simp only [smul_add, smul_one]
    have := (I (n + 1)).neg_mem hp
    convert this using 1
    ring
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep Z (normU G)
    (fun n u hu => h.normU_mem hu)
    (fun u g => Units.ext (by rw [act_val, normU_val, smul_prod_univ])) step u hu
    (fun g => Units.ext (hfix g))
  exact ⟨v, hv, by rw [← normU_val, hvu]⟩

theorem hilbert90_matrix_subalgebra_norm_one (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (u : Rˣ) (hu : (u : R) - 1 ∈ I 0)
    (hN : ∏ g : G, g • (u : R) = 1) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ g₀ • (v : R) = u * v := by
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ (normU G).ker →
      ∃ v ∈ h.V n, u / (act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) v ∈ h.V (n + 1) := by
    intro n u hu hZ
    set x : R := (u : R) - 1 with hxdef
    have hx : x ∈ I n := hu
    have hux : (u : R) = 1 + x := by rw [hxdef]; ring
    have htr : ∑ g : G, g • x ∈ I (n + 1) := by
      have hp := h.prod_one_add (n := n) univ (fun g : G => g • x) (fun g _ => h.smul n g _ hx)
      have h1 : ∏ g : G, (1 + g • x) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.1 hZ)
        rw [normU_val, hux] at this
        simpa only [smul_add, smul_one, Units.val_one] using this
      rw [h1, sub_self, zero_sub] at hp
      simpa using (I (n + 1)).neg_mem hp
    set y : R := ∑ k ∈ range (orderOf g₀), ∑ j ∈ range k, g₀ ^ j • e ((g₀ ^ k)⁻¹ • x) with hydef
    have hy : y ∈ I n := (I n).sum_mem fun k _ => (I n).sum_mem fun j _ =>
      h.smul n _ _ (h.e_mem n _ (h.smul n _ _ hx))
    have hd : g₀ • y - y = x - e (∑ g : G, g • x) := by
      rw [hydef, smul_sum, ← sum_sub_distrib]
      simp only [telescope]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [sum_sub_distrib, sum_pow_eq hg (fun g => g • e (g⁻¹ • x)), h.e_sum, ← map_sum,
        sum_pow_eq hg (fun g => g⁻¹ • x)]
      congr 2
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
    have hy0 := h.le_zero n hy
    have hvV : h.mkU y hy0 ∈ h.V n := h.mkU_mem y hy
    refine ⟨h.mkU y hy0, hvV, h.div_mem_V
      ((h.V 0).div_mem (h.act_mem g₀ (h.V_le_zero n hvV)) (h.V_le_zero n hvV)) ?_⟩
    set z : R := (1 + y)⁻¹ - 1 with hzdef
    have hz : z ∈ I n := h.inv n y hy
    have hyz : (1 + y) * (1 + z) = 1 := by
      rw [hzdef, add_sub_cancel, mul_inv_cancel₀ (h.one_add_ne_zero hy0)]
    have hval : (((act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) (h.mkU y hy0) : Rˣ) : R) = (1 + g₀ • y) * (1 + z) := by
      rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, act_val,
        Units.val_inv_eq_inv_val, mkU_val, smul_add, smul_one, hzdef, add_sub_cancel]
    rw [hval, hux]
    have : 1 + x - (1 + g₀ • y) * (1 + z) = e (∑ g : G, g • x) - (g₀ • y - y) * z := by
      linear_combination -hyz - hd
    rw [this]
    exact (I (n + 1)).sub_mem (h.e_mem _ _ htr)
      (h.mul n _ _ ((I n).sub_mem (h.smul n _ _ hy) hy) (h.le_zero n hz))
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep (normU G).ker (act g₀ / MonoidHom.id _)
    (fun n u hu => (h.V n).div_mem (h.act_mem g₀ hu) hu)
    (fun u => by
      rw [MonoidHom.mem_ker, MonoidHom.div_apply, MonoidHom.id_apply, map_div, div_eq_one]
      exact Units.ext (by rw [normU_val, normU_val, act_val, prod_smul_smul])) step u hu
    (Units.ext (by rw [normU_val, hN]; rfl))
  refine ⟨v, hv, ?_⟩
  rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul] at hvu
  rw [← act_val, hvu, Units.val_mul]

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end

