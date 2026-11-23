module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoeffEqZeroOfSumEqZero
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.WeierD

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def wd (g : O⟦X⟧) : ℕ := (g.map (IsLocalRing.residue O)).order.toNat

theorem constantCoeff_mem {g : O⟦X⟧} (hD : 1 ≤ wd g) :
    constantCoeff g ∈ IsLocalRing.maximalIdeal O := by
  have h0 : coeff 0 (g.map (IsLocalRing.residue O)) = 0 :=
    coeff_of_lt_order_toNat 0 (by unfold wd at hD; omega)
  rw [coeff_map, coeff_zero_eq_constantCoeff_apply] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

noncomputable def poly {D : ℕ} (a : Fin D → O) : Polynomial O :=
  ∑ i : Fin D, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

theorem coeff_poly {D : ℕ} (a : Fin D → O) (n : ℕ) :
    (poly a).coeff n = if h : n < D then a ⟨n, h⟩ else 0 := by
  simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩ (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm)))
      (by simp)]
    simp
  · exact Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem coe_poly {D : ℕ} (a : Fin D → O) :
    ((poly a : Polynomial O) : O⟦X⟧) = ∑ i : Fin D, C (a i) * X ^ (i : ℕ) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.coeff_coe, poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    map_sum, PowerSeries.coeff_C_mul_X_pow]

theorem degree_poly_lt {D : ℕ} (a : Fin D → O) : (poly a).degree < D :=
  Polynomial.degree_sum_fin_lt a

theorem poly_of_degree {D : ℕ} {p : Polynomial O} (hp : p.degree < D) :
    poly (fun i : Fin D => p.coeff i) = p := by
  ext n
  rw [coeff_poly]
  split_ifs with h
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hp (by exact_mod_cast (not_lt.mp h)))).symm

theorem h_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  simpa [PowerSeries.algebraMap_apply] using h.commutes a

theorem sum_split {D : ℕ} (h : O⟦X⟧ →ₐ[O] O⟦X⟧) {g : O⟦X⟧} (hX : h X = g)
    (c : Fin D → O⟦X⟧) :
    ∑ i : Fin D, X ^ (i : ℕ) * h (c i) =
      ((poly fun i => constantCoeff (c i) : Polynomial O) : O⟦X⟧) +
        g * ∑ i : Fin D, X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i)) := by
  rw [coe_poly, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [eq_X_mul_shift_add_const (c i)]
  rw [map_add (f := _), map_mul, hX, h_C]
  ring

variable {g : O⟦X⟧} (hg : g.map (IsLocalRing.residue O) ≠ 0)
include hg

theorem coeff_eq_zero_of_sum_eq_zero (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) :
    ∀ n, ∀ c : Fin (wd g) → O⟦X⟧, ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0 → ∀ i, coeff n (c i) = 0 := by
  have HW := IsWeierstrassDivisor.of_map_ne_zero hg
  have step : ∀ c : Fin (wd g) → O⟦X⟧, ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0 →
      (∀ i, constantCoeff (c i) = 0) ∧
        ∑ i : Fin (wd g), X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i)) = 0 := by
    intro c hc
    rw [sum_split h hX] at hc
    have h2 : g * (∑ i : Fin (wd g), X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i))) =
        ((-poly fun i => constantCoeff (c i) : Polynomial O) : O⟦X⟧) := by
      rw [Polynomial.coe_neg]
      exact eq_neg_of_add_eq_zero_right hc
    obtain ⟨hq, hr⟩ := HW.eq_zero_of_mul_eq
      (by rw [Polynomial.degree_neg]; exact degree_poly_lt (D := wd g) _) h2
    refine ⟨fun i => ?_, hq⟩
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) (neg_eq_zero.mp hr)
    simpa [coeff_poly] using this
  intro n
  induction n with
  | zero =>
    intro c hc i
    rw [coeff_zero_eq_constantCoeff_apply]
    exact (step c hc).1 i
  | succ n ih =>
    intro c hc i
    have := ih _ (step c hc).2 i
    rwa [coeff_mk] at this

theorem eq_zero_of_sum_eq_zero (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (c : Fin (wd g) → O⟦X⟧)
    (hc : ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0) : c = 0 :=
  funext fun i => PowerSeries.ext fun n => by
    simpa using coeff_eq_zero_of_sum_eq_zero hg h hX n c hc i

theorem decomp_unique (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (c c' : Fin (wd g) → O⟦X⟧)
    (hc : ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c' i)) : c = c' := by
  have := eq_zero_of_sum_eq_zero hg h hX (c - c') (by
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, hc, sub_self])
  exact sub_eq_zero.mp this

theorem injective (hD : 1 ≤ wd g) (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) :
    Function.Injective h := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have := eq_zero_of_sum_eq_zero hg h hX (fun i => if (i : ℕ) = 0 then a else 0) (by
    rw [Finset.sum_eq_single ⟨0, hD⟩ (fun j _ hj => by
      rw [if_neg (fun e => hj (Fin.ext e)), map_zero, mul_zero]) (by simp)]
    simp [ha])
  simpa using congrFun this ⟨0, hD⟩


omit hg in
noncomputable def cf (g : O⟦X⟧) (f : O⟦X⟧) (i : ℕ) : O⟦X⟧ :=
  mk fun n => ((fun q => q /ʷ g)^[n] f %ʷ g).coeff i

omit hg in
theorem constantCoeff_cf (f : O⟦X⟧) (i : ℕ) : constantCoeff (cf g f i) = (f %ʷ g).coeff i := by
  rw [← coeff_zero_eq_constantCoeff_apply, cf, coeff_mk, Function.iterate_zero_apply]

omit hg in
theorem shift_cf (f : O⟦X⟧) (i : ℕ) :
    (mk fun p => coeff (p + 1) (cf g f i)) = cf g (f /ʷ g) i := by
  ext n
  simp only [cf, coeff_mk, Function.iterate_succ_apply]

theorem exists_decomp (hD : 1 ≤ wd g) (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (f : O⟦X⟧) :
    ∃ c : Fin (wd g) → O⟦X⟧, f = ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) := by
  have hg0 := constantCoeff_mem hD
  let E : O⟦X⟧ → O⟦X⟧ := fun f => f - ∑ i : Fin (wd g), X ^ (i : ℕ) * h (cf g f i)
  have hE : ∀ f, E f = g * E (f /ʷ g) := by
    intro f
    have hs := sum_split h hX (fun i : Fin (wd g) => cf g f i)
    simp only [constantCoeff_cf, shift_cf] at hs
    rw [poly_of_degree (D := wd g) (degree_weierstrassMod_lt f g)] at hs
    have hf := eq_mul_weierstrassDiv_add_weierstrassMod f hg
    simp only [E]
    rw [hs]
    linear_combination hf
  have hmem : ∀ N f, E f ∈ Ideal.span {g ^ N} := by
    intro N
    induction N with
    | zero => intro f; simp
    | succ N ih =>
      intro f
      rw [hE, Ideal.mem_span_singleton, pow_succ']
      exact mul_dvd_mul_left g (Ideal.mem_span_singleton.mp (ih _))
  have h0 : E f = 0 := eq_zero_of_forall_mem_coeffFiltration fun N =>
    (Ideal.span_singleton_le_iff_mem _).mpr (pow_mem_coeffFiltration hg0 N) (hmem N f)
  exact ⟨fun i => cf g f i, sub_eq_zero.mp h0⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.WeierD
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRootAlt
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTB

open PowerSeries

section Roots

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

theorem root_eq (l : ℕ) [hp : Fact l.Prime] {x₀ y w : O} (hx : x₀ ≠ 0)
    (hrx : (1 + x₀) ^ l = 1) (hry : (1 + y) ^ l = 1)
    (hw : w ∈ IsLocalRing.maximalIdeal O) (hyw : y - x₀ = x₀ * w) : y = x₀ := by
  have hl0 : 0 < l := hp.out.pos
  have hζ1 : (1 + x₀) ≠ 1 := fun h => hx (by linear_combination h)
  have hprim : IsPrimitiveRoot (1 + x₀) l := by
    have h := IsPrimitiveRoot.orderOf (1 + x₀)
    rwa [orderOf_eq_prime hrx hζ1] at h
  have hζu : IsUnit (1 + x₀) := by
    first
    | exact hprim.isUnit hl0
    | exact hprim.isUnit hl0.ne'
  have hwu : ¬ IsUnit w := (IsLocalRing.mem_maximalIdeal w).1 hw
  obtain ⟨i, hil, hi⟩ : ∃ i < l, (1 + x₀) ^ i = 1 + y := by
    first
    | exact hprim.eq_pow_of_pow_eq_one hry
    | exact hprim.eq_pow_of_pow_eq_one hry hl0
  rcases i with _ | j
  · exfalso
    have hy0 : y = 0 := by linear_combination -hi
    have hxw : x₀ * (1 + w) = 0 := by linear_combination -hyw + hy0
    rcases mul_eq_zero.1 hxw with h | h
    · exact hx h
    · apply hwu
      have hw1 : w = -1 := by linear_combination h
      rw [hw1]
      exact isUnit_one.neg
  · rcases j with _ | j
    · linear_combination -hi
    · exfalso
      have hk0 : 0 < j + 1 := Nat.succ_pos j
      have hkl : j + 1 < l := by omega
      have hcop : (j + 1).Coprime l :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt hk0 hkl))
      have hprim' := hprim.pow_of_coprime (j + 1) hcop
      obtain ⟨m, -, hm⟩ : ∃ m < l, ((1 + x₀) ^ (j + 1)) ^ m = 1 + x₀ := by
        first
        | exact hprim'.eq_pow_of_pow_eq_one hrx
        | exact hprim'.eq_pow_of_pow_eq_one hrx hl0
      have e1 := geom_sum_mul ((1 + x₀) ^ (j + 1)) m
      have e2 := geom_sum_mul (1 + x₀) (j + 1)
      rw [hm] at e1
      set S := ∑ i ∈ Finset.range m, ((1 + x₀) ^ (j + 1)) ^ i with hS
      set v := ∑ i ∈ Finset.range (j + 1), (1 + x₀) ^ i with hv
      have hSv0 : x₀ * (S * v - 1) = 0 := by linear_combination S * e2 + e1
      have hSv : S * v = 1 := by
        have := (mul_eq_zero.1 hSv0).resolve_left hx
        linear_combination this
      have hvu : IsUnit v := ⟨⟨v, S, by rw [mul_comm]; exact hSv, hSv⟩, rfl⟩
      have hwz : x₀ * (w - (1 + x₀) * v) = 0 := by
        linear_combination -hyw - hi - (1 + x₀) * e2
      have hw' : w = (1 + x₀) * v := by
        have := (mul_eq_zero.1 hwz).resolve_left hx
        linear_combination this
      exact hwu (hw' ▸ hζu.mul hvu)

end Roots

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem mem_max (l : ℕ) [hp : Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    {x₀ : O} (hroot : (1 + x₀) ^ l = 1) : x₀ ∈ IsLocalRing.maximalIdeal O := by
  have hk : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField O) l := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hp.out).2 hk
    | exact ringChar.of_eq ((hp.out.eq_one_or_self_of_dvd _ (ringChar.dvd hk)).resolve_left
        CharP.ringChar_ne_one)
  have h := congrArg (IsLocalRing.residue O) hroot
  simp only [map_pow, map_add (f := _), map_one] at h
  rw [add_pow_char, one_pow] at h
  have h2 : (IsLocalRing.residue O x₀) ^ l = 0 := by linear_combination h
  exact (IsLocalRing.residue_eq_zero_iff _).1 (pow_eq_zero_iff hp.out.ne_zero |>.1 h2)

theorem map_res {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (IsLocalRing.residue O) (X - C x₀) = X := by
  have h : IsLocalRing.residue O x₀ = 0 := (IsLocalRing.residue_eq_zero_iff x₀).2 hx
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, h, map_zero, sub_zero]

theorem map_mk {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (X - C x₀) = X := by
  have h : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) x₀ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hx
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, h, map_zero, sub_zero]

theorem decomp {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) (p : O⟦X⟧) :
    ∃ c : O, ∃ q : O⟦X⟧, p = (X - C x₀) * q + C c := by
  have hord : PowerSeries.map (IsLocalRing.residue O) (X - C x₀) ≠ 0 := by
    rw [map_res hx]; exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hqr⟩ := PowerSeries.exists_isWeierstrassDivision (f := p) (g := X - C x₀) hord
  have hdeg := hqr.1
  first
  | rw [map_mk hx, PowerSeries.order_X] at hdeg
  | rw [map_res hx, PowerSeries.order_X] at hdeg
  simp at hdeg
  have hrc : (r : O⟦X⟧) = C (r.coeff 0) := by
    first
    | (have hr0 : r.degree ≤ 0 := by
          first
          | exact Nat.WithBot.lt_one_iff_le_zero.1 hdeg
          | exact Order.le_of_lt_succ hdeg
       conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero hr0]
       exact Polynomial.coe_C _)
    | (ext n
       rcases n with _ | n
       · simp
       · rw [Polynomial.coeff_coe, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]
         exact Polynomial.coeff_eq_zero_of_degree_lt
           (lt_of_lt_of_le hdeg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))))
  refine ⟨r.coeff 0, q, ?_⟩
  rw [← hrc]
  exact hqr.2

theorem uniq {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) {c : O}
    (hc : C c ∈ Ideal.span {X - C x₀}) : c = 0 := by
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 hc
  have hrec : ∀ n, coeff n f = x₀ * coeff (n + 1) f := by
    intro n
    have h := congrArg (fun g => coeff (n + 1) g) hf
    simp only [mul_sub, map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_C, Nat.succ_ne_zero, if_false] at h
    linear_combination h
  have hpow : ∀ n, coeff 0 f = x₀ ^ n * coeff n f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hrec n]; ring
  have hall : ∀ n : ℕ, coeff 0 f ≡ 0 [SMOD ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O)] := by
    intro n
    rw [SModEq.zero]
    have hmem := Submodule.smul_mem_smul
      (Ideal.mul_mem_right (coeff n f) _ (Ideal.pow_mem_pow hx n)) (Submodule.mem_top : (1 : O) ∈ ⊤)
    rw [hpow n]
    simpa using hmem
  have hcoef0 : coeff 0 f = 0 := by
    first
    | exact IsHausdorff.haus inferInstance _ hall
    | exact IsHausdorff.haus' _ hall
  have h0 := congrArg (fun g => coeff 0 g) hf
  simp only [mul_sub, map_sub, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mul_C, hcoef0,
    PowerSeries.coeff_zero_C] at h0
  linear_combination -h0

def Fs (l : ℕ) (x₀ : O) (a : O⟦X⟧) : O⟦X⟧ :=
  ∑ i ∈ Finset.range l, (1 + a) ^ i * (1 + C x₀) ^ (l - 1 - i)

theorem Fs_mul (l : ℕ) {x₀ : O} (hroot : (1 + x₀) ^ l = 1) (a : O⟦X⟧) :
    (1 + a) ^ l - 1 = Fs l x₀ a * (a - C x₀) := by
  have hy : (1 + C x₀ : O⟦X⟧) ^ l = 1 := by
    simpa [map_pow, map_add (f := _), map_one] using congrArg (C : O →+* O⟦X⟧) hroot
  have h := geom_sum₂_mul (1 + a) (1 + C x₀) l
  rw [hy] at h
  unfold Fs
  rw [← h]
  congr 1
  ring

end Main

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTB
end
end

