module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0004
public import Formalism.ConjugateSelfDual.Statement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzApprox
section
open IsDedekindDomain NumberField

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem exists_int_approx (e : E) (he : w.valuation E e ≤ 1) :
    ∃ x : 𝓞 E, w.valuation E (e - algebraMap (𝓞 E) E x) < 1 := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) e
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hν0 : w.intValuation b ≠ 0 := w.intValuation_ne_zero b hb0
  set m : ℕ := (-(w.intValuation b).log).toNat with hm
  have hνm : w.intValuation b = WithZero.exp (-(m : ℤ)) := by
    have hlog : (w.intValuation b).log ≤ 0 := by
      have h1 : WithZero.exp (w.intValuation b).log ≤ WithZero.exp 0 := by
        rw [WithZero.exp_log hν0, WithZero.exp_zero]; exact w.intValuation_le_one b
      exact WithZero.exp_le_exp.mp h1
    rw [hm, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hν0]
  have hbm : b ∈ w.asIdeal ^ m := (w.intValuation_le_pow_iff_mem b m).mp hνm.le
  have hbm1 : b ∉ w.asIdeal ^ (m + 1) := by
    intro h
    have h2 := (w.intValuation_le_pow_iff_mem b (m + 1)).mpr h
    rw [hνm, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have hva : w.intValuation a ≤ w.intValuation b := by
    have h1 : w.valuation E (algebraMap (𝓞 E) E a) =
        w.valuation E (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) * w.valuation E (algebraMap (𝓞 E) E b) := by
      rw [← map_mul, div_mul_cancel₀ _ hbE]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [h1]
    exact mul_le_of_le_one_left' he
  have ham : a ∈ w.asIdeal ^ m := (w.intValuation_le_pow_iff_mem a m).mp (hva.trans hνm.le)
  obtain ⟨B, hB⟩ : w.asIdeal ^ m ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  have hBw : ¬ B ≤ w.asIdeal := by
    intro hle
    apply hbm1
    have : Ideal.span {b} ≤ w.asIdeal ^ (m + 1) := by
      rw [hB, pow_succ]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp this
  obtain ⟨s, hsB, hsw⟩ := SetLike.not_le_iff_exists.mp hBw
  have hsa : s * a ∈ Ideal.span {b} := by
    rw [hB, mul_comm s a]; exact Ideal.mul_mem_mul ham hsB
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hsa
  haveI := w.isMaximal
  have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨s'', hs''⟩ := Ideal.Quotient.exists_inv hs0
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s''
  have hss : s * s' - 1 ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hs'', map_one, sub_self]
  have hsne : s ≠ 0 := fun h => hsw (h ▸ w.asIdeal.zero_mem)
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hsne
  refine ⟨c * s', ?_⟩
  have hcE : algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E a := by
    rw [← map_mul, ← map_mul, hc]
  have hab : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E c / algebraMap (𝓞 E) E s := by
    rw [div_eq_div_iff hbE hsE]; linear_combination (-1 : E) * hcE
  have e1 : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b - algebraMap (𝓞 E) E (c * s') =
      algebraMap (𝓞 E) E c * (-algebraMap (𝓞 E) E (s * s' - 1)) / algebraMap (𝓞 E) E s := by
    rw [hab]
    simp only [map_mul, map_sub, map_one]
    field_simp
    ring
  have hs1 : w.intValuation s = 1 :=
    le_antisymm (w.intValuation_le_one s) (not_lt.mp fun h => hsw ((w.intValuation_lt_one_iff_mem s).mp h))
  have hss1 : w.intValuation (s * s' - 1) < 1 := (w.intValuation_lt_one_iff_mem _).mpr hss
  rw [e1, map_div₀, map_mul, Valuation.map_neg, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hs1, div_one]
  calc w.intValuation c * w.intValuation (s * s' - 1) ≤ 1 * w.intValuation (s * s' - 1) :=
        mul_le_mul_left (w.intValuation_le_one c) _
    _ = w.intValuation (s * s' - 1) := one_mul _
    _ < 1 := hss1

theorem exists_int_approx_compl (u : w.adicCompletion E) (hu : Valued.v u ≤ 1) :
    ∃ x : 𝓞 E, Valued.v (u - algebraMap E (w.adicCompletion E) (x : E)) < 1 := by
  have hvF : ∀ e : E, Valued.v (algebraMap E (w.adicCompletion E) e) = w.valuation E e :=
    fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w e
  obtain ⟨e, he⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt u one_pos
  rw [dist_eq_norm, Valued.toNormedField.norm_lt_one_iff] at he
  have hve : w.valuation E e ≤ 1 := by
    rw [← hvF]
    have e2 : algebraMap E (w.adicCompletion E) e = u - (u - algebraMap E (w.adicCompletion E) e) := by ring
    rw [e2]
    exact (Valuation.map_sub _ _ _).trans (max_le hu he.le)
  obtain ⟨x, hx⟩ := exists_int_approx w e hve
  refine ⟨x, ?_⟩
  have e3 : u - algebraMap E (w.adicCompletion E) (x : E) =
      (u - algebraMap E (w.adicCompletion E) e) + algebraMap E (w.adicCompletion E) (e - algebraMap (𝓞 E) E x) := by
    rw [map_sub]; ring
  rw [e3]
  exact Valuation.map_add_lt _ he (by rw [hvF]; exact hx)

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

theorem exists_int_lift {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ_[g]) (h : ∀ a b, ‖M a b‖ ≤ 1) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ_[g], (algebraMap ℤ_[g] ℚ_[g]).mapMatrix A = M :=
  ⟨fun a b => ⟨M a b, h a b⟩, by ext a b; rfl⟩

theorem mapMatrix_int_injective {n : ℕ} :
    Function.Injective ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix : Matrix (Fin n) (Fin n) ℤ_[g] → _) :=
  fun _ _ h => Matrix.ext fun a b => PadicInt.ext (congrFun (congrFun h a) b)

include hi

theorem mem_integer_iff (x : ℚ_[g]) : i x ∈ 𝒪[w.adicCompletion E] ↔ ‖x‖ ≤ 1 :=
  (Valuation.mem_integer_iff _ _).trans (valuation_le_iff i hi x)

theorem map_inc_mem_KO {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) ∈ KO (w.adicCompletion E) (Fin n) := by
  rw [mem_KO]
  refine ⟨fun a b => (mem_integer_iff i hi _).2 (k.val a b).2, fun a b => ?_⟩
  rw [← map_inv, ← map_inv]
  exact (mem_integer_iff i hi _).2 ((k⁻¹).val a b).2

theorem exists_of_mem_KO {n : ℕ} {m : GL (Fin n) (w.adicCompletion E)} (hm : m ∈ KO (w.adicCompletion E) (Fin n)) :
    ∃ k : GL (Fin n) ℤ_[g], Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) = m := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hm
  have hint : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), IntM M →
      ∀ a b, ‖i.symm.toRingHom.mapMatrix M a b‖ ≤ 1 := by
    intro M hM a b
    rw [← norm_le_iff i hi]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 (hM a b))
  obtain ⟨A, hA⟩ := exists_int_lift _ (hint _ h1)
  obtain ⟨B, hB⟩ := exists_int_lift _ (hint _ h2)
  have hAB : A * B = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.mul_inv, map_one, map_one])
  have hBA : B * A = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.inv_mul, map_one, map_one])
  refine ⟨⟨A, B, hAB, hBA⟩, Units.ext (Matrix.ext fun a b => ?_)⟩
  change i ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix A a b) = m.val a b
  rw [hA]
  simp

def toKO (n : ℕ) : GL (Fin n) ℤ_[g] →* KO (w.adicCompletion E) (Fin n) :=
  ((Matrix.GeneralLinearGroup.map i.toRingHom).comp (inc g n)).codRestrict _ fun k => map_inc_mem_KO i hi k

theorem coe_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) :
    ((toKO i hi n k : KO (w.adicCompletion E) (Fin n)) : GL (Fin n) (w.adicCompletion E)) =
      Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) := rfl

theorem toKO_injective (n : ℕ) : Function.Injective (toKO i hi n) := by
  intro k k' h
  have h' := congrArg (fun x : KO (w.adicCompletion E) (Fin n) =>
    ((x : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h
  refine Units.ext (Matrix.ext fun a b => PadicInt.ext (i.injective ?_))
  exact congrFun (congrFun h' a) b

theorem toKO_surjective (n : ℕ) : Function.Surjective (toKO i hi n) := by
  intro m
  obtain ⟨k, hk⟩ := exists_of_mem_KO i hi m.2
  exact ⟨k, Subtype.ext hk⟩

def equivKO (n : ℕ) : GL (Fin n) ℤ_[g] ≃* KO (w.adicCompletion E) (Fin n) :=
  MulEquiv.ofBijective (toKO i hi n) ⟨toKO_injective i hi n, toKO_surjective i hi n⟩

def redKO (n : ℕ) : KO (w.adicCompletion E) (Fin n) →* Gn g n :=
  (red g n).comp (equivKO i hi n).symm.toMonoidHom

theorem redKO_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) : redKO i hi n (toKO i hi n k) = red g n k := by
  show red g n ((equivKO i hi n).symm (equivKO i hi n k)) = red g n k
  rw [MulEquiv.symm_apply_apply]

theorem redKO_surjective (n : ℕ) : Function.Surjective (redKO i hi n) :=
  (GlobalTheory.GLp.Model.red_surjective n).comp (equivKO i hi n).symm.surjective

theorem ker_redKO (n : ℕ) :
    (redKO i hi n).ker = (KOne (w.adicCompletion E) (Fin n)).subgroupOf (KO (w.adicCompletion E) (Fin n)) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨k, rfl⟩ := toKO_surjective i hi n m
  rw [redKO_toKO, coe_toKO]
  constructor
  · intro hk
    exact map_mem_KOne i hi k hk
  · intro hm
    obtain ⟨k', hk', he⟩ := exists_of_mem_KOne i hi hm
    have : k' = k := toKO_injective i hi n (Subtype.ext he)
    rw [← this]
    exact hk'

end DiscreteGroups.sglob.DzIso
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

theorem norm_symm_le (y : 𝒪[w.adicCompletion E]) : ‖i.symm (y : w.adicCompletion E)‖ ≤ 1 := by
  rw [← norm_le_iff i hi, RingEquiv.apply_symm_apply]
  exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 y.2)

def toIntFun (y : 𝒪[w.adicCompletion E]) : ℤ_[g] := ⟨i.symm y, norm_symm_le i hi y⟩

theorem coe_toIntFun (y : 𝒪[w.adicCompletion E]) : ((toIntFun i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def toInt : 𝒪[w.adicCompletion E] →+* ℤ_[g] where
  toFun := toIntFun i hi
  map_one' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_one]; simp)
  map_mul' a b := PadicInt.ext (by rw [PadicInt.coe_mul, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)
  map_zero' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_zero]; simp)
  map_add' a b := PadicInt.ext (by rw [PadicInt.coe_add, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)

theorem coe_toInt (y : 𝒪[w.adicCompletion E]) : ((toInt i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def redO : 𝒪[w.adicCompletion E] →+* ZMod g := (PadicInt.toZMod (p := g)).comp (toInt i hi)

theorem redO_surjective : Function.Surjective (redO i hi) := by
  intro a
  refine ⟨(a.val : 𝒪[w.adicCompletion E]), ?_⟩
  show PadicInt.toZMod (toInt i hi (a.val : 𝒪[w.adicCompletion E])) = a
  rw [map_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem ker_redO : RingHom.ker (redO i hi) = IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := by
  ext y
  rw [← IsLocalRing.residue_eq_zero_iff, residue_eq_zero_iff_lt, RingHom.mem_ker]
  show PadicInt.toZMod (toInt i hi y) = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
    coe_toInt, ← valuation_lt_iff i hi, RingEquiv.apply_symm_apply]

end DiscreteGroups.sglob.DzIso
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzLDepth
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lDepth : LDepth := by
  intro E _ _ w g _ i hi n τ σ hs
  obtain ⟨φ, hφ, hφe⟩ := hs
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun u => not_not.1 fun hne => h ⟨u, hne⟩)
  let e := equivRep σ
  have hfix : ∀ m ∈ KOne (w.adicCompletion E) (Fin n), σ.ρ m (φ u) = φ u := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hm
    have := hφe k u
    rw [hk, map_one, Module.End.one_apply] at this
    exact this.symm
  intro hbot
  have hv : e.toIntertwiningMap (φ u) ∈ fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) := by
    intro m
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [← e.toIntertwiningMap.isIntertwining, hfix m m.2]
  rw [hbot, Submodule.mem_bot] at hv
  have h2 : e.toLinearEquiv (φ u) = 0 := hv
  exact hu (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzNormV
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Filter Topology

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem val_lt_one_of_norm_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (u : ℚ_[g])
    (hu : ‖u‖ < 1) : Valued.v (i u) < 1 := by
  have := DiscreteGroups.sglob.DzIso.norm_lt_of_lt i hi hu
  rwa [Valued.toNormedField.norm_lt_one_iff] at this

theorem mem_of_val_lt_one (y : 𝓞 E) (h : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) < 1) :
    y ∈ w.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rwa [e] at h

theorem val_le_one_int (y : 𝓞 E) : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≤ 1 := by
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rw [e]
  exact w.valuation_le_one y

theorem alg_sub_natCast (y : 𝓞 E) (a : ℕ) : algebraMap E (w.adicCompletion E) (((y - (a : 𝓞 E) : 𝓞 E)) : E) =
    algebraMap E (w.adicCompletion E) (y : E) - (a : w.adicCompletion E) := by
  simp

theorem alg_natCast (a : ℕ) : algebraMap E (w.adicCompletion E) (((a : 𝓞 E)) : E) = (a : w.adicCompletion E) := by
  simp

theorem normV_eq_of_padic (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g := by
  classical
  have hres : ∀ y : 𝓞 E, ∃ a : ℕ, y - (a : 𝓞 E) ∈ w.asIdeal := by
    intro y
    set x := i.symm (algebraMap E (w.adicCompletion E) (y : E)) with hx
    have hxy : i x = algebraMap E (w.adicCompletion E) (y : E) := by rw [hx, RingEquiv.apply_symm_apply]
    have hxn : ‖x‖ ≤ 1 := by
      by_contra hc
      push Not at hc
      have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact absurd hc (by norm_num)
      have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
      have h2 := val_lt_one_of_norm_lt_one w g i hi _ h1
      rw [map_inv₀, hxy, map_inv₀] at h2
      have h3 := val_le_one_int w y
      have hy0 : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≠ 0 := by
        intro h0
        rw [h0, inv_zero] at h2
        have : i x ≠ 0 := (map_ne_zero i).mpr hx0
        rw [hxy] at this
        exact this ((Valuation.zero_iff _).mp h0)
      have h4 : 1 ≤ (Valued.v (algebraMap E (w.adicCompletion E) (y : E)))⁻¹ := one_le_inv₀ (zero_lt_iff.mpr hy0) |>.mpr h3
      exact absurd h2 (not_lt.mpr h4)
    let xz : ℤ_[g] := ⟨x, hxn⟩
    obtain ⟨a, -, ha⟩ := PadicInt.exists_mem_range xz
    refine ⟨a, mem_of_val_lt_one w _ ?_⟩
    have h5 : ‖x - a‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp ha
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hxy, map_natCast] at h6
    rw [alg_sub_natCast]
    exact h6
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    apply mem_of_val_lt_one w
    have := val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
    rw [map_natCast] at this
    rw [alg_natCast]
    exact this
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hgQ : ((g : ℕ) : 𝓞 E ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hgw
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := (CharP.charP_iff_prime_eq_zero hg.out).mpr hgQ
  let f : ZMod g →+* 𝓞 E ⧸ w.asIdeal := ZMod.castHom (dvd_refl g) _
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := hres y
    refine ⟨(a : ZMod g), ?_⟩
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_refl g), ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact ha
  unfold normV
  rw [← Nat.card_congr (RingEquiv.ofBijective f ⟨hinj, hsurj⟩).toEquiv, Nat.card_zmod]

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzRankBound
section
namespace DiscreteGroups.sglob.DzType

theorem sixteen_sq_lt_g (D : Formalism.BasicNotions.D7) (k : Fin 2) : 16 * D.R.r ^ 2 < D.host.g k :=
  big_of_le_nV D k (by unfold Formalism.BasicNotions.Ranks.nV; omega)

end DiscreteGroups.sglob.DzType
end

