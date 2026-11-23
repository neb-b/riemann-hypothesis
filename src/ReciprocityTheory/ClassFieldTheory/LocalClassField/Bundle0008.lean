module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0006
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsA

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandF
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

def uval [(subG p K L).Normal] (w : (layerU p K L).V) : PadicAlgCl p :=
  ((Additive.toMul (Subtype.val (p := fun x => x ∈ Ubar p) w.1) : (PadicAlgCl p)ˣ) : PadicAlgCl p)

section

variable [(subG p K L).Normal]

theorem uval_add (a b : (layerU p K L).V) : uval (a + b) = uval a * uval b := rfl

theorem uval_neg (a : (layerU p K L).V) : uval (-a) = (uval a)⁻¹ := Units.val_inv_eq_inv_val _

theorem uval_sub (a b : (layerU p K L).V) : uval (a - b) = uval a * (uval b)⁻¹ := by
  rw [sub_eq_add_neg, uval_add, uval_neg]

theorem uval_sum {ι : Type*} (s : Finset ι) (f : ι → (layerU p K L).V) :
    uval (∑ i ∈ s, f i) = ∏ i ∈ s, uval (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, uval_add, ih]

theorem uval_rho (σ : GK p K) (w : (layerU p K L).V) :
    uval ((layerU p K L).rho (QuotientGroup.mk σ) w) = σ (uval w) := rfl

theorem uval_injective : Injective (uval : (layerU p K L).V → PadicAlgCl p) := fun _ _ hab =>
  Subtype.ext (Subtype.ext (Units.ext hab))

theorem uval_ne_zero (w : (layerU p K L).V) : uval w ≠ 0 := Units.ne_zero _

theorem vbar_eq_zero_iff (x : KbarMult p) :
    vbar p x = 0 ↔ ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos : 0 < ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ :=
    norm_pos_iff.2 (Units.ne_zero _)
  rw [vbar_apply, neg_eq_zero, Real.logb_eq_zero]
  constructor
  · rintro (h | h | h | h | h | h) <;> linarith
  · intro h; right; right; right; right; left; exact h

theorem norm_uval (w : (layerU p K L).V) : ‖uval w‖ = 1 :=
  (vbar_eq_zero_iff _).1 ((mem_Ubar_iff p _).1 (Subtype.property (p := fun x => x ∈ Ubar p) w.1))

theorem uval_mem (h : K ≤ L) (w : (layerU p K L).V) : uval w ∈ L :=
  (mem_iff_fixed h _).2 fun σ hσ =>
    congrArg (fun y : Ubar p => ((Additive.toMul (y : KbarMult p) : (PadicAlgCl p)ˣ) : PadicAlgCl p))
      (w.2 ⟨σ, hσ⟩)

theorem exists_uval {x : PadicAlgCl p} (hx : x ∈ L) (h1 : ‖x‖ = 1) : ∃ w : (layerU p K L).V, uval w = x := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
  let y : KbarMult p := Additive.ofMul (Units.mk0 x hx0)
  have hy : y ∈ Ubar p := (mem_Ubar_iff p y).2 ((vbar_eq_zero_iff y).2 h1)
  refine ⟨⟨(⟨y, hy⟩ : Ubar p), fun g => Subtype.ext (Units.ext ?_)⟩, rfl⟩
  exact g.2 x hx

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

def divHom (e : ℕ) : ℤ →+ ℝ := zmultiplesHom ℝ ((e : ℝ)⁻¹)

theorem divHom_apply (e : ℕ) (n : ℤ) : divHom e n = n * (e : ℝ)⁻¹ := by simp [divHom]

theorem divHom_injective {e : ℕ} (he : 0 < e) : Function.Injective (divHom e) := by
  have he' : (e : ℝ) ≠ 0 := by positivity
  intro a b hab
  rw [divHom_apply, divHom_apply] at hab
  exact_mod_cast mul_right_cancel₀ (inv_ne_zero he') hab

theorem map_divHom_zmultiples {e : ℕ} (he : 0 < e) :
    (AddSubgroup.zmultiples (e : ℤ)).map (divHom e) = AddSubgroup.zmultiples (1 : ℝ) := by
  have he' : (e : ℝ) ≠ 0 := by positivity
  rw [AddMonoidHom.map_zmultiples, divHom_apply]
  congr 1
  rw [Int.cast_natCast, mul_inv_cancel₀ he']

theorem map_divHom_top (e : ℕ) : (⊤ : AddSubgroup ℤ).map (divHom e) = AddSubgroup.zmultiples ((e : ℝ)⁻¹) := by
  rw [← AddMonoidHom.range_eq_map, divHom, AddSubgroup.range_zmultiplesHom]

theorem relIndex_zmultiples_one_inv {n : ℕ} (hn : 0 < n) :
    (AddSubgroup.zmultiples (1 : ℝ)).relIndex (AddSubgroup.zmultiples ((n : ℝ)⁻¹)) = n := by
  rw [← map_divHom_zmultiples hn, ← map_divHom_top,
    AddSubgroup.relIndex_map_map_of_injective _ _ (divHom_injective hn), AddSubgroup.relIndex_top_right,
    Int.index_zmultiples, Int.natAbs_natCast]

theorem real_subgroup_eq_zmultiples (V : AddSubgroup ℝ) (h1 : (1 : ℝ) ∈ V) {e : ℕ}
    (hee : (AddSubgroup.zmultiples (1 : ℝ)).relIndex V = e) (he : 0 < e) :
    V = AddSubgroup.zmultiples ((e : ℝ)⁻¹) := by
  have he' : (e : ℝ) ≠ 0 := by positivity
  have hV : (V.comap (divHom e)).map (divHom e) = V := by
    rw [AddSubgroup.map_comap_eq, inf_eq_right]
    intro v hv
    have h2 := AddSubgroup.nsmul_relIndex_mem (AddSubgroup.zmultiples (1 : ℝ)) hv
    rw [hee] at h2
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h2
    refine ⟨k, ?_⟩
    rw [divHom_apply]
    have hk' : (k : ℝ) = e * v := by simpa using hk
    rw [hk']; field_simp
  have hle : AddSubgroup.zmultiples (e : ℤ) ≤ V.comap (divHom e) := by
    rw [← AddSubgroup.map_le_iff_le_comap, map_divHom_zmultiples he]
    exact AddSubgroup.zmultiples_le_of_mem h1
  have h3 : (AddSubgroup.zmultiples (e : ℤ)).relIndex (V.comap (divHom e)) = e := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (divHom_injective he), map_divHom_zmultiples he, hV, hee]
  have h4 := AddSubgroup.relIndex_mul_index hle
  rw [h3, Int.index_zmultiples, Int.natAbs_natCast] at h4
  have h5 : (V.comap (divHom e)).index = 1 := by
    have : e * (V.comap (divHom e)).index = e * 1 := by rw [h4, mul_one]
    exact Nat.eq_of_mul_eq_mul_left he this
  rw [AddSubgroup.index_eq_one] at h5
  rw [← hV, h5, map_divHom_top]

theorem relIndex_pos_of_le_zmultiples (V : AddSubgroup ℝ) (h1 : (1 : ℝ) ∈ V) {n : ℕ} (hn : 0 < n)
    (hV : V ≤ AddSubgroup.zmultiples ((n : ℝ)⁻¹)) : 0 < (AddSubgroup.zmultiples (1 : ℝ)).relIndex V := by
  have h2 := AddSubgroup.relIndex_mul_relIndex (AddSubgroup.zmultiples (1 : ℝ)) V _
    (AddSubgroup.zmultiples_le_of_mem h1) hV
  rw [relIndex_zmultiples_one_inv hn] at h2
  exact Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at h2; omega

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem norm_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have h : (p : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem logb_norm_p : Real.logb p ‖(p : PadicAlgCl p)‖ = -1 := by
  rw [norm_p, Real.logb_inv, Real.logb_self_eq_one (one_lt_p_real p)]

def pUnit : KbarMult p :=
  Additive.ofMul (Units.mk0 (p : PadicAlgCl p) (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

theorem pUnit_mem : pUnit p ∈ multOf p K := by
  show (p : PadicAlgCl p) ∈ K
  exact natCast_mem K p

theorem vbar_pUnit : vbar p (pUnit p) = 1 := by
  rw [vbar_apply]
  show - Real.logb p ‖(p : PadicAlgCl p)‖ = 1
  rw [logb_norm_p, neg_neg]

theorem one_mem_valueGroup : (1 : ℝ) ∈ valueGroup p K := ⟨pUnit p, pUnit_mem p K, vbar_pUnit p⟩

theorem valueGroup_eq_zmultiples_of_pos (he : 0 < eK p K) :
    valueGroup p K = AddSubgroup.zmultiples ((eK p K : ℝ)⁻¹) :=
  real_subgroup_eq_zmultiples _ (one_mem_valueGroup p K) rfl he

theorem valueGroup_le_of_finiteDimensional (hK : FiniteDimensional ℚ_[p] K) :
    valueGroup p K ≤ AddSubgroup.zmultiples
      ((Module.finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (IntermediateField.extendScalars (bot_le : ⊥ ≤ K)) : ℝ)⁻¹) := by
  rintro _ ⟨x, hx, rfl⟩
  have := finDim_extendScalars_of_le p hK (bot_le : ⊥ ≤ K)
  set n := Module.finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (IntermediateField.extendScalars (bot_le : ⊥ ≤ K)) with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hn' : (n : ℝ) ≠ 0 := by positivity
  set y : PadicAlgCl p := ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) with hy
  have hy0 : y ≠ 0 := Units.ne_zero _
  have h1 := norm_algebraNorm p hK (bot_le : ⊥ ≤ K) ⟨y, hx⟩
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 (Algebra.norm (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
    (⟨y, hx⟩ : IntermediateField.extendScalars (bot_le : ⊥ ≤ K))).2
  rw [← ha, PadicAlgCl.norm_extends] at h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h1
    exact (pow_ne_zero _ (norm_ne_zero_iff.2 hy0)) h1.symm
  rw [Padic.norm_eq_zpow_neg_valuation ha0] at h1
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨a.valuation, ?_⟩
  rw [vbar_apply]
  have h2 := congrArg (Real.logb p) h1
  rw [← Real.rpow_intCast, Real.logb_rpow (by linarith [one_lt_p_real p]) (one_lt_p_real p).ne', Real.logb_pow] at h2
  change _ = (n : ℝ) * Real.logb p ‖y‖ at h2
  rw [zsmul_eq_mul]
  push_cast at h2
  field_simp
  linarith

theorem eK_pos (hK : FiniteDimensional ℚ_[p] K) : 0 < eK p K := by
  have := finDim_extendScalars_of_le p hK (bot_le : ⊥ ≤ K)
  exact relIndex_pos_of_le_zmultiples _ (one_mem_valueGroup p K) Module.finrank_pos
    (valueGroup_le_of_finiteDimensional p K hK)

theorem vOn_surjective_of_pos (he : 0 < eK p K) : Function.Surjective (vOn p K) := by
  have he' : (eK p K : ℝ) ≠ 0 := by positivity
  have h1 : ((eK p K : ℝ)⁻¹) ∈ valueGroup p K := by
    rw [valueGroup_eq_zmultiples_of_pos p K he]; exact AddSubgroup.mem_zmultiples _
  obtain ⟨x, hx, hxv⟩ := h1
  have h2 : vOn p K ⟨x, hx⟩ = 1 := by
    apply Int.cast_injective (α := ℝ)
    rw [vOn_spec, hxv, Int.cast_one, mul_inv_cancel₀ he']
  intro n
  exact ⟨n • ⟨x, hx⟩, by rw [map_zsmul, h2, smul_eq_mul, mul_one]⟩

theorem vOn_surjective (hK : FiniteDimensional ℚ_[p] K) : Function.Surjective (vOn p K) :=
  vOn_surjective_of_pos p K (eK_pos p K hK)

def unitOf (x : multOf p K) : Kˣ :=
  Units.mk0 ⟨((Additive.toMul x.1 : (PadicAlgCl p)ˣ) : PadicAlgCl p), x.2⟩
    (fun h => (Additive.toMul x.1 : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h))

theorem vK_unitOf (x : multOf p K) : vK p K (unitOf p K x) = vOn p K x := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec, vOn_spec, vbar_apply]
  show - ((eK p K : ℝ) * Real.logb p ‖((Additive.toMul x.1 : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖) = _
  ring

theorem vK_surjective_of_pos (he : 0 < eK p K) : Function.Surjective (vK p K) := fun n => by
  obtain ⟨x, hx⟩ := vOn_surjective_of_pos p K he n
  exact ⟨unitOf p K x, by rw [vK_unitOf, hx]⟩

theorem vK_surjective (hK : FiniteDimensional ℚ_[p] K) : Function.Surjective (vK p K) :=
  vK_surjective_of_pos p K (eK_pos p K hK)

theorem exists_vK_eq_one (hK : FiniteDimensional ℚ_[p] K) : ∃ π : Kˣ, vK p K π = 1 := vK_surjective p K hK 1

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

