module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GroupAlgebraOperatorConvolutionCalculus
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

section
variable {G : Type} [Group G] [Fintype G]

theorem convCalc_assoc (a b c : G → ℂ) : conv (conv a b) c = conv a (conv b c) := by
  funext x
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft z)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_assoc]

theorem convCalc_sub_left (a b c : G → ℂ) : conv (a - b) c = conv a c - conv b c := by
  funext x
  simp [conv, sub_mul, Finset.sum_sub_distrib]

theorem convCalc_sub_right (a b c : G → ℂ) : conv c (a - b) = conv c a - conv c b := by
  funext x
  simp [conv, mul_sub, Finset.sum_sub_distrib]

theorem convCalc_dirac_left (a : G → ℂ) : conv dirac a = a := by
  funext x
  simp [conv, dirac]

theorem convCalc_dirac_right (a : G → ℂ) : conv a dirac = a := by
  funext x
  simp [conv, dirac, inv_mul_eq_one]

theorem convCalc_star (a b : G → ℂ) (ha : ∀ x, a x⁻¹ = (starRingEnd ℂ) (a x))
    (hb : ∀ x, b x⁻¹ = (starRingEnd ℂ) (b x)) (x : G) :
    conv a b x⁻¹ = (starRingEnd ℂ) (conv b a x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [conv, map_sum, map_mul, ← ha, ← hb]
  rw [← Equiv.sum_comp (Equiv.mulLeft x⁻¹)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_comm, mul_assoc]

theorem convCalc_isProj_conv (a b : G → ℂ) (ha : IsProj a) (hb : IsProj b) (h : conv a b = conv b a) :
    IsProj (conv a b) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [convCalc_assoc, ← convCalc_assoc b a b, ← h, convCalc_assoc a b b, hb.1, ← convCalc_assoc, ha.1]
  · rw [convCalc_star a b ha.2 hb.2, h]

theorem convCalc_isProj_compl (a : G → ℂ) (ha : IsProj a) : IsProj (dirac - a) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [convCalc_sub_left, convCalc_sub_right, convCalc_sub_right, convCalc_dirac_left, convCalc_dirac_left,
      convCalc_dirac_right, ha.1]
    simp
  · simp only [Pi.sub_apply, map_sub, ha.2, dirac, inv_eq_one]
    split_ifs <;> simp

variable {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)

theorem convCalc_op_conv (a b : G → ℂ) : op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [smul_smul, mul_comm]

theorem convCalc_op_sub (a b : G → ℂ) : op ρ (a - b) = op ρ a - op ρ b := by
  simp [op, sub_smul, Finset.sum_sub_distrib]

theorem convCalc_op_add (a b : G → ℂ) : op ρ (a + b) = op ρ a + op ρ b := by
  simp [op, add_smul, Finset.sum_add_distrib]

theorem convCalc_op_dirac : op ρ dirac = 1 := by
  simp [op, dirac]

theorem convCalc_rk [FiniteDimensional ℂ M] (e : G → ℂ) (he : conv e e = e) :
    (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have h1 : op ρ e * op ρ e = op ρ e := by rw [← convCalc_op_conv, he]
  have hp : LinearMap.IsProj (LinearMap.range (op ρ e)) (op ρ e) :=
    ⟨fun x => LinearMap.mem_range_self _ x, by
      rintro x ⟨y, rfl⟩
      exact LinearMap.congr_fun h1 y⟩
  rw [rk, ← hp.trace]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [op, map_sum]

end

theorem convCalc : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), (∀ a b : G → ℂ, op ρ (conv a b) = op ρ a * op ρ b ∧ op ρ (a - b) = op ρ a - op ρ b ∧ op ρ (a + b) = op ρ a + op ρ b) ∧ op ρ dirac = 1 ∧ (∀ a b c : G → ℂ, conv (conv a b) c = conv a (conv b c) ∧ conv (a - b) c = conv a c - conv b c ∧ conv c (a - b) = conv c a - conv c b) ∧ (∀ a : G → ℂ, conv dirac a = a ∧ conv a dirac = a) ∧ (∀ a b : G → ℂ, IsProj a → IsProj b → conv a b = conv b a → IsProj (conv a b)) ∧ (∀ a : G → ℂ, IsProj a → IsProj (dirac - a)) ∧ ∀ e : G → ℂ, conv e e = e → (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  intro G _ _ M _ _ _ ρ
  exact ⟨fun a b => ⟨convCalc_op_conv ρ a b, convCalc_op_sub ρ a b, convCalc_op_add ρ a b⟩, convCalc_op_dirac ρ,
    fun a b c => ⟨convCalc_assoc a b c, convCalc_sub_left a b c, convCalc_sub_right a b c⟩,
    fun a => ⟨convCalc_dirac_left a, convCalc_dirac_right a⟩, convCalc_isProj_conv, convCalc_isProj_compl,
    convCalc_rk ρ⟩

end GlobalTheory.BadShare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInv
section
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory

theorem hahn_pow_neg_one_lead {R : Type} [CommRing R] (x : HahnSeries ℚ R)
    (h1 : x.coeff (-1) = 1) (hlt : ∀ r : ℚ, r < -1 → x.coeff r = 0) :
    ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  intro m
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, fun r _ => Subsingleton.elim _ _⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hxo : x.order = -1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [h1]; exact one_ne_zero)) ?_
    by_contra hc
    push_neg at hc
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hlt _ hc))
  have hxl : x.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, hxo, h1]
  have key : ∀ n : ℕ, (x ^ n).order = -(n : ℚ) ∧ (x ^ n).leadingCoeff = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : (x ^ n).leadingCoeff * x.leadingCoeff ≠ 0 := by
        rw [ih.2, hxl, one_mul]; exact one_ne_zero
      rw [pow_succ, HahnSeries.order_mul_of_ne_zero hne, HahnSeries.leadingCoeff_mul_of_ne_zero hne,
        ih.1, ih.2, hxo, hxl]
      constructor
      · push_cast; ring
      · simp
  obtain ⟨ho, hl⟩ := key m
  refine ⟨?_, fun r hr => ?_⟩
  · rw [← ho, ← HahnSeries.leadingCoeff_eq, hl]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [ho]; exact hr)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariant
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.HeckeUNormInv

theorem coe_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  simp [toGQ, h]

theorem coe_ofSL (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  simp [ofSL]

theorem det_mj (j l : ℤ) (hl : 0 < l) : 0 < (!![1, j; 0, l] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  simp [Matrix.det_fin_two]; exact hl

theorem key (N l n : ℕ) (hn : 0 < n) (hl : 0 < l) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n))
    (j : ℕ) : ∃ γ' ∈ CongruenceSubgroup.Gamma1 (N * l ^ n),
      toGQ !![1, (j : ℤ); 0, (l : ℤ)] * ofSL γ =
        ofSL γ' * toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)] := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨ha, hd, hc⟩ := (CongruenceSubgroup.Gamma1_mem _ _).1 hγ
  have hdvd : l ∣ N * l ^ n := dvd_mul_of_dvd_right (dvd_pow_self l hn.ne') N
  have ha' : ((γ 0 0 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) ha; rwa [map_intCast, map_one] at this
  have hd' : ((γ 1 1 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hd; rwa [map_intCast, map_one] at this
  have hc' : ((γ 1 0 : ℤ) : ZMod l) = 0 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hc; rwa [map_intCast, map_zero] at this
  have hk : ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ) = (γ 0 1 + j) % (l : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [hk]
  set k : ℤ := (γ 0 1 + j) % (l : ℤ) with hkdef
  obtain ⟨b', hb'⟩ : (l : ℤ) ∣ γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha', hd', hc', hkdef, ZMod.intCast_mod]
    push_cast; ring
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0 + j * γ 1 0, b'; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + γ 1 0 * hb'⟩
  have hbq : ((γ 0 1 : ℚ) + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) = l * b' := by exact_mod_cast hb'
  refine ⟨γ', ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [γ'] <;> push_cast <;> simp [ha, hd, hc]
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [coe_toGQ _ (det_mj _ _ (by omega)), coe_toGQ _ (det_mj _ _ (by omega)), coe_ofSL, coe_ofSL]
    ext i i'
    fin_cases i <;> fin_cases i' <;> simp [Matrix.mul_apply, γ'] <;> push_cast <;> first | linear_combination | linear_combination hbq

theorem emod_toNat_lt (x : ℤ) {l : ℕ} (hl : 0 < l) : (x % (l : ℤ)).toNat < l := by
  have h1 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by omega)
  omega

theorem emod_inv (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((((((b + a) % (l : ℤ)).toNat : ℕ) : ℤ) - b) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.sub_emod, Int.emod_emod, ← Int.sub_emod,
    add_sub_cancel_left, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem emod_inv' (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((b + ((((a : ℤ) - b) % (l : ℤ)).toNat : ℤ)) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.add_emod, Int.emod_emod, ← Int.add_emod,
    add_sub_cancel, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

end GlobalTheory.HeckeUNormInv


open GlobalTheory.HeckeUNormInv in
theorem GlobalTheory.normInv_gamma1 : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ g : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g →
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) := by
  intro Ω _ _ ε X N l _ n hn g hg γ hγ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  rw [map_prod]
  have step : ∀ j : ℕ, X.sl (ofSL γ) (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) =
      X.sl (toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)]) g := by
    intro j
    obtain ⟨γ', hγ', heq⟩ := key N l n hn hl γ hγ j
    rw [← X.sl_mul, heq, X.sl_mul, hg γ' hγ']
  rw [Finset.prod_congr rfl (fun j _ => step j)]
  exact Finset.prod_nbij' (fun j => ((γ 0 1 + j) % (l : ℤ)).toNat) (fun k => (((k : ℤ) - γ 0 1) % (l : ℤ)).toNat)
    (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl)) (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl))
    (fun a ha => emod_inv _ hl a (Finset.mem_range.1 ha)) (fun a ha => emod_inv' _ hl a (Finset.mem_range.1 ha))
    (fun _ _ => rfl)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTCoeffFormulaCommDistinctPrimes
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma isDia_mul_of_isDia {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ)
    (hτ : IsDia N l e τ) : IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) h1
    simpa using this
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]; ring

lemma heckeT_congr_dia {N l q : ℕ} {k : ℤ} {σ τ : SL(2, ℤ)} (hN : 0 < N)
    (hσ : IsDia N l q σ) (hτ : IsDia N l q τ) (f : ModularForm (lev N l) k) :
    heckeT k q σ ⇑f = heckeT k q τ ⇑f := by
  have := _root_.GlobalTheory.Hk.dia_congr N l k q σ τ hN hσ hτ f
  unfold dia at this
  unfold heckeT
  rw [this]

lemma heckeT_coeff_formula_comm_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (kq kr : ℂ)
    (a b c e : ℕ → ℂ) (n : ℕ) :
    a (r * (q * n)) + kr * (if r ∣ q * n then b (q * n / r) else 0)
      + kq * (if q ∣ n then c (r * (n / q)) + kr * (if r ∣ n / q then e (n / q / r) else 0)
        else 0)
    = a (q * (r * n)) + kq * (if q ∣ r * n then c (r * n / q) else 0)
      + kr * (if r ∣ n then b (q * (n / r)) + kq * (if q ∣ n / r then e (n / r / q) else 0)
        else 0) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  have i1 : r ∣ q * n ↔ r ∣ n := hcop.symm.dvd_mul_left
  have i2 : q ∣ r * n ↔ q ∣ n := hcop.dvd_mul_left
  have ha : r * (q * n) = q * (r * n) := by ring
  simp only [ha, i1, i2]
  by_cases hqn : q ∣ n <;> by_cases hrn : r ∣ n
  · have i3 : r ∣ n / q := by
      obtain ⟨m, rfl⟩ := hqn
      rw [Nat.mul_div_cancel_left _ hq.pos]
      exact (hcop.symm.dvd_mul_left).1 hrn
    have i4 : q ∣ n / r := by
      obtain ⟨m, rfl⟩ := hrn
      rw [Nat.mul_div_cancel_left _ hr.pos]
      exact (hcop.dvd_mul_left).1 hqn
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    have d3 : n / r / q = n / q / r := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    simp only [hqn, hrn, i3, i4, if_true, d1, d2, d3]
    ring
  · have i3 : ¬ r ∣ n / q := by
      intro h
      exact hrn (h.trans (Nat.div_dvd_of_dvd hqn))
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    simp only [hqn, hrn, i3, if_true, if_false, d2]
    ring
  · have i4 : ¬ q ∣ n / r := by
      intro h
      exact hqn (h.trans (Nat.div_dvd_of_dvd hrn))
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    simp only [hqn, hrn, i4, if_true, if_false, d1]
    ring
  · simp only [hqn, hrn, if_false]
    ring

theorem heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ τ : SL(2, ℤ)), 0 < N → q.Prime → r.Prime →
    ¬ q ∣ N * l → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l r τ →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.heckeT k r τ ⇑f) = GlobalTheory.Hk.heckeT k r τ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  intro N l q r k σ τ hN hq hr hqN hrN hσ hτ f
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.Hk.heckeT_modularForm N l q k τ hN hq hqN hτ f
    rw [heckeT_congr_dia hN hσ hτ f, ← hg, heckeT_congr_dia hN hσ hτ g]
  · obtain ⟨gr, hgr⟩ := _root_.GlobalTheory.Hk.heckeT_modularForm N l r k τ hN hr hrN hτ f
    obtain ⟨gq, hgq⟩ := _root_.GlobalTheory.Hk.heckeT_modularForm N l q k σ hN hq hqN hσ f
    obtain ⟨h1, hh1⟩ := _root_.GlobalTheory.Hk.heckeT_modularForm N l q k σ hN hq hqN hσ gr
    obtain ⟨h2, hh2⟩ := _root_.GlobalTheory.Hk.heckeT_modularForm N l r k τ hN hr hrN hτ gq
    obtain ⟨fσ, hfσ⟩ := _root_.GlobalTheory.Hk.dia_modularForm N l k q σ hN hσ f
    obtain ⟨fτ, hfτ⟩ := _root_.GlobalTheory.Hk.dia_modularForm N l k r τ hN hτ f
    have dσ : dia k σ ⇑gr = heckeT k r τ ⇑fσ := by
      rw [hgr, hfσ, _root_.GlobalTheory.Hk.heckeT_dia_comm N l r k q τ σ hN hr hrN hτ hσ f]
    have dτ : dia k τ ⇑gq = heckeT k q σ ⇑fτ := by
      rw [hgq, hfτ, _root_.GlobalTheory.Hk.heckeT_dia_comm N l q k r σ τ hN hq hqN hσ hτ f]
    have dd : dia k τ ⇑fσ = dia k σ ⇑fτ := by
      have h' : IsDia N l ((r : ℤ) * q) (σ * τ) := by
        rw [mul_comm]; exact isDia_mul_of_isDia hσ hτ
      rw [hfσ, hfτ, _root_.GlobalTheory.Hk.dia_mul N l k q r σ τ (σ * τ) hN hσ hτ (isDia_mul_of_isDia hσ hτ) f,
        _root_.GlobalTheory.Hk.dia_mul N l k r q τ σ (σ * τ) hN hτ hσ h' f]
    have key : h1 = h2 := by
      apply _root_.GlobalTheory.Hk.eq_of_coef_eq N l k hN
      intro n
      rw [hh1, hh2, _root_.GlobalTheory.Hk.coef_heckeT N l q k σ hN hq hqN hσ gr, _root_.GlobalTheory.Hk.coef_heckeT N l r k τ hN hr hrN hτ gq,
        dσ, dτ, _root_.GlobalTheory.Hk.coef_heckeT N l r k τ hN hr hrN hτ fσ, _root_.GlobalTheory.Hk.coef_heckeT N l q k σ hN hq hqN hσ fτ,
        hgr, hgq, _root_.GlobalTheory.Hk.coef_heckeT N l r k τ hN hr hrN hτ f, _root_.GlobalTheory.Hk.coef_heckeT N l q k σ hN hq hqN hσ f,
        dd, hfσ, hfτ]
      exact heckeT_coeff_formula_comm_distinct_primes hq hr hqr _ _ _ _ _ _ n
    rw [← hgr, ← hgq, ← hh1, ← hh2, key]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSqSubMemOldformsGamma1
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem GlobalTheory.HeckeFamilyMatrices.ulSq_old : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  intro N l k hN hl hlN hk χ f hf
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨u, v, huv⟩ : IsCoprime (l : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have h : (l : ℤ) * u - N * (-v) = 1 := by linear_combination huv
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero l := ⟨hl0.ne'⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  set W := wOld N l (-v) u with hW
  set D := dg (l : ℤ) 1 with hD
  have hWdet : 0 < W.det := by
    rw [hW, wOld, Matrix.det_fin_two_of]; nlinarith
  have hDdet : 0 < D.det := by
    rw [hD, dg, Matrix.det_fin_two_of]; simpa using hl0
  set F : ℍ → ℂ := ⇑f with hFdef
  have hF : ChiInv (k : ℤ) N (N * l) χ F := hf
  have cF : CuspAll (k : ℤ) F := _root_.GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll (Lev N l) k f
  set G := F ∣[(k : ℤ)] toGL W with hGdef
  have hG : ChiInv (k : ℤ) N (N * l) χ G := _root_.GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld N l k (-v) u h χ F hl0 hF
  have cG : CuspAll (k : ℤ) G := _root_.GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL k W F hWdet cF
  have cTr : ∀ H, CuspAll (k : ℤ) H → CuspAll (k : ℤ) (trOld k N l (-v) u h H) := by
    intro H hH
    unfold trOld
    refine cuspAll_add hH ?_
    induction (Finset.range l) using Finset.induction_on with
    | empty => simpa using cuspAll_smul 0 hH
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      refine cuspAll_add ?_ ih
      rw [slash_SL_eq]
      exact _root_.GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL k _ H (by simp [mat]) hH
  set A := trOld k N l (-v) u h F with hAdef
  set B := trOld k N l (-v) u h G with hBdef
  have hA : ChiInv (k : ℤ) N N χ A := _root_.GlobalTheory.HeckeFamilyMatrices.chiInv_trOld N l k (-v) u h χ F hN0 hl hF
  have hB : ChiInv (k : ℤ) N N χ B := _root_.GlobalTheory.HeckeFamilyMatrices.chiInv_trOld N l k (-v) u h χ G hN0 hl hG
  have cA : CuspAll (k : ℤ) A := cTr F cF
  have cB : CuspAll (k : ℤ) B := cTr G cG
  set C := B ∣[(k : ℤ)] toGL D with hCdef
  have hC : ChiInv (k : ℤ) N (N * l) χ C := GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise N l k χ B hl0 hB
  have cC : CuspAll (k : ℤ) C := _root_.GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL k D B hDdet cB
  have hTC : ChiInv (k : ℤ) N N χ (trOld k N l (-v) u h C) := _root_.GlobalTheory.HeckeFamilyMatrices.chiInv_trOld N l k (-v) u h χ C hN0 hl hC
  have cTC : CuspAll (k : ℤ) (trOld k N l (-v) u h C) := cTr C cC
  set c₁ : ℂ := χ (l : ZMod N) with hc₁
  set p : ℂ := (l : ℂ) ^ ((k : ℤ) - 2) with hp
  have h₁ : ChiInv (k : ℤ) N N χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) :=
    chiInv_add (chiInv_smul _ hTC) (chiInv_smul _ hA)
  obtain ⟨f₁, hf₁⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv N k χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) hN0
    (cuspAll_add (cuspAll_smul _ cTC) (cuspAll_smul _ cA)) h₁
  obtain ⟨f₂, hf₂⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv N k χ (-(c₁ ^ 2) • B) hN0 (cuspAll_smul _ cB) (chiInv_smul _ hB)
  refine ⟨f₁, f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
  · rw [hf₁]; exact h₁ γ hγ
  · rw [hf₂]; exact chiInv_smul _ hB γ hγ
  rw [hf₁, hf₂]
  have e1 := _root_.GlobalTheory.HeckeFamilyMatrices.trOld_eq N l k (-v) u h F hl0
  have e2 := _root_.GlobalTheory.HeckeFamilyMatrices.trOld_eq N l k (-v) u h G hl0
  have e3 := GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus N l k (-v) u h χ F hl0 hF
  have e4 := _root_.GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld N l k (-v) u h χ B hl0 hB
  rw [← hAdef, ← hGdef] at e1
  rw [← hBdef, e3] at e2
  rw [← hCdef] at e4
  have cb : c₁ * χ (u : ZMod N) = 1 := by
    rw [hc₁, ← map_mul]
    have h2 := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at h2
    rw [ZMod.natCast_self] at h2
    rw [show ((l : ZMod N) * (u : ZMod N)) = 1 by linear_combination h2, map_one]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have pp : p * (l : ℂ) ^ (2 - (k : ℤ)) = 1 := by
    rw [hp, ← zpow_add₀ hl']; simp
  have hUG : UlF k l G = p • (A - F) := by
    rw [e1, add_sub_cancel_left, smul_smul, pp, one_smul]
  have hUF : UlF k l F = c₁ • (B - G) := by
    have key : c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * ((l : ℂ) ^ ((k : ℤ) - 2) * χ (u : ZMod N)) = 1 := by
      rw [← hp]
      calc c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * (p * χ (u : ZMod N))
          = (p * (l : ℂ) ^ (2 - (k : ℤ))) * (c₁ * χ (u : ZMod N)) := by ring
        _ = 1 := by rw [pp, cb, one_mul]
    rw [e2, add_sub_cancel_left, ulF_smul k l hl0, smul_smul, smul_smul, key, one_smul]
  have hpk : (l : ℂ) ^ (k - 2) = p := by
    rw [hp, show ((k : ℤ) - 2) = ((k - 2 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hpk, hUF, ulF_smul k l hl0, ulF_sub k l hl0, e4, hUG, smul_slash_toGL k D hDdet, ← hCdef]
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubstStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ f : X.K,
  X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.exp_sl_upper | exact GlobalTheory.CyclotomicQExpansion.exp_sl_upper | (intros; apply GlobalTheory.CyclotomicQExpansion.exp_sl_upper <;> assumption)
end

