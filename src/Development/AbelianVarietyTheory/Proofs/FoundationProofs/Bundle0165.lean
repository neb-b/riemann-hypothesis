module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Bundle0001
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ZCalc

variable {G : Type} [Group G] [Fintype G]

theorem character_inv (V : FDRep ℂ G) (t : G) : V.character t⁻¹ = (starRingEnd ℂ) (V.character t) := by
  let b := Module.finBasis ℂ V
  have htr : ∀ s, V.character s = (LinearMap.toMatrix b b (V.ρ s)).trace := fun s =>
    LinearMap.trace_eq_matrix_trace ℂ b _
  rw [htr, htr]
  refine Formalism.L2.DIV.trace_inv_of_pow_eq_one _ _ (N := Fintype.card G) Fintype.card_ne_zero ?_ ?_
  · rw [LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one, map_one, LinearMap.toMatrix_one]
  · rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one, LinearMap.toMatrix_one]

theorem op_zc (V W : FDRep ℂ G) :
    op W.ρ (zc V.character) = PI.CharIdem.act W (PI.CharIdem.charIdem V) := by
  rw [PI.CharIdemW.act_charIdem]
  simp only [op, zc, FDRep.char_one]

theorem conv_zc_of_scalar (χ : G → ℂ) (W : FDRep ℂ G) (c : ℂ) (h : op W.ρ (zc χ) = c • 1) (x : G) :
    conv (zc χ) (zc W.character) x = c * zc W.character x := by
  have h1 : ∑ y, zc χ y * W.character (y * x⁻¹) = c * W.character x⁻¹ := by
    have h2 : LinearMap.trace ℂ W (op W.ρ (zc χ) * W.ρ x⁻¹) = c * W.character x⁻¹ := by
      rw [h, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h2, op, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]; rfl
  have h3 : ∀ y, zc χ y * zc W.character (y⁻¹ * x) =
      W.character 1 / (Fintype.card G : ℂ) * (zc χ y * W.character (y * x⁻¹)) := by
    intro y
    have : W.character (y⁻¹ * x)⁻¹ = W.character (y * x⁻¹) := by
      rw [mul_inv_rev, inv_inv, FDRep.char_mul_comm]
    rw [show zc W.character (y⁻¹ * x) = W.character 1 / (Fintype.card G : ℂ) * W.character (y⁻¹ * x)⁻¹ from rfl, this]
    ring
  rw [conv, Finset.sum_congr rfl fun y _ => h3 y, ← Finset.mul_sum, h1,
    show zc W.character x = W.character 1 / (Fintype.card G : ℂ) * W.character x⁻¹ from rfl]
  ring

theorem op_conv_eq {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a b : G → ℂ) :
    op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul_sum, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_).symm
  simp

theorem rk_eq_trace {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M)
    (e : G → ℂ) (he : conv e e = e) : (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have hi : IsIdempotentElem (op ρ e) := by
    rw [IsIdempotentElem, ← op_conv_eq, he]
  have hp := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rk, ← hp, op, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem zc_calc : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  intro G _ _ V hV
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · funext x
    have h := (PI.CharIdemW.scalar G V V hV hV).1 ⟨CategoryTheory.Iso.refl V⟩
    rw [conv_zc_of_scalar _ V 1 (by rw [op_zc, h, one_smul]), one_mul]
  · intro x
    simp only [zc, map_mul, map_div₀, FDRep.char_one, map_natCast]
    rw [character_inv V x⁻¹]
  · intro a
    funext x
    simp only [conv]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, zc]
    have : V.character ((y⁻¹ * x)⁻¹ * x)⁻¹ = V.character y⁻¹ := by
      rw [← FDRep.char_conj V y⁻¹ x⁻¹]
      congr 1
      group
    rw [this, mul_comm]
  · intro W hW hne
    funext x
    have h := (PI.CharIdemW.scalar G V W hV hW).2 ⟨fun i => hne (FDRep.char_iso i)⟩
    rw [conv_zc_of_scalar _ W 0 (by rw [op_zc, h, zero_smul]), zero_mul]
    rfl
  · intro e he
    rw [rk_eq_trace _ e he, conv, Finset.mul_sum, Finset.sum_div]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun y => ?_
    simp only [Equiv.inv_apply, zc, mul_one, FDRep.char_one]
    rw [show LinearMap.trace ℂ V (V.ρ y⁻¹) = V.character y⁻¹ from rfl]
    ring

end GlobalTheory.BadShare.ZCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero
section
open Polynomial

namespace GlobalTheory

theorem classGroup_ringOfIntegers_divisible : GlobalTheory.NeedB.ClDiv := by
  intro k K _ _ _ _ _ _ _ _ N hN c
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    exact ⟨c, (pow_one c).symm⟩
  set A := FunctionField.ringOfIntegers k K
  have : Algebra.IsSeparable (RatFunc k) K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  have : Module.Free k[X] A := IsIntegralClosure.module_free k[X] (RatFunc k) K _
  have : Module.Finite k[X] A := IsIntegralClosure.finite k[X] (RatFunc k) K _
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K _
  letI : Algebra k A := ((algebraMap k[X] A).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.exists_integral_norm_natDegree_mod_eq_one k K N hN
  have hdim : Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
    rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hf0]
    exact hf
  exact _root_.GlobalTheory.classGroup_nthPower_of_codim_one_mod k A N hN (_root_.GlobalTheory.exists_class_group_mk0_eq_mul_pow k A N h) ⟨f, hf0, hdim⟩ c

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSum
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_add_smul {u v : ℕ → ℂ} (c : ℂ) (hu : PolyB u) (hv : PolyB v) :
    PolyB (fun n => u n + c * v n) := by
  obtain ⟨C₁, A₁, h₁⟩ := hu
  obtain ⟨C₂, A₂, h₂⟩ := hv
  have hC₁ : 0 ≤ C₁ := by
    have := h₁ 0; simp at this; exact le_trans (norm_nonneg _) this
  have hC₂ : 0 ≤ C₂ := by
    have := h₂ 0; simp at this; exact le_trans (norm_nonneg _) this
  refine ⟨C₁ + ‖c‖ * C₂, A₁ + A₂, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have e1 : ((n : ℝ) + 1) ^ A₁ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  have e2 : ((n : ℝ) + 1) ^ A₂ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  calc ‖u n + c * v n‖ ≤ ‖u n‖ + ‖c‖ * ‖v n‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ A₁ + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ A₂) := by
        gcongr; exacts [h₁ n, h₂ n]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ (A₁ + A₂) + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ (A₁ + A₂)) := by
        gcongr
    _ = (C₁ + ‖c‖ * C₂) * ((n : ℝ) + 1) ^ (A₁ + A₂) := by ring

theorem qs_To_hsum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a →
    PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  intro k q ε a hk hq hε ha
  obtain ⟨hU, hUq⟩ := _root_.GlobalTheory.EisM.Uo_qs_sum_slz k q a hk hq ha
  obtain ⟨hV, hVq⟩ := _root_.GlobalTheory.EisM.Vo_polyB_qs q a hq ha
  have hTo : To k (ε q) q a = fun n => Uo q a n + (ε q * (q : ℂ) ^ (k - 1)) * Vo q a n := by
    funext n; simp only [To, Uo]
  refine ⟨by rw [hTo]; exact polyB_add_smul _ hU hV, ?_⟩
  funext τ
  have sU : Summable fun n : ℕ => Uo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((_root_.GlobalTheory.EisM.qs_summable_continuous _ hU).1 τ).of_norm
  have sV : Summable fun n : ℕ => Vo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((_root_.GlobalTheory.EisM.qs_summable_continuous _ hV).1 τ).of_norm
  have hsplit : qs (To k (ε q) q a) τ = qs (Uo q a) τ + (ε q * (q : ℂ) ^ (k - 1)) * qs (Vo q a) τ := by
    rw [hTo]; simp only [qs]
    rw [← tsum_mul_left, ← sU.tsum_add (sV.mul_left _)]
    congr 1; funext n; ring
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hq) τ.im_pos
  have hσ : qs (Vo q a) τ = qs a ⟨(q : ℂ) * τ, him⟩ := hVq τ ⟨(q : ℂ) * τ, him⟩ rfl
  rw [hsplit, hUq τ, hσ, hsum, Fintype.sum_option]
  have hnone : ε (repT q none 0 0) * slz k (repT q none) (qs a) τ
      = (ε q * (q : ℂ) ^ (k - 1)) * qs a ⟨(q : ℂ) * τ, him⟩ := by
    have : ofComplex ((((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ))) = ⟨(q : ℂ) * τ, him⟩ := by
      rw [show (((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ)) = (q : ℂ) * τ by
        push_cast; ring]
      exact ofComplex_apply_of_im_pos him
    simp only [repT, slz, Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    rw [this]
    push_cast
    simp
    ring
  have hsome : ∀ j : Fin q, ε (repT q (some j) 0 0) * slz k (repT q (some j)) (qs a) τ
      = slz k (repU q j) (qs a) τ := by
    intro j
    simp only [repT, repU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hε, one_mul]
  rw [hnone, Finset.sum_congr rfl (fun j _ => hsome j)]
  ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevel
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.LevelLower

def idx (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) : Fin l :=
  ⟨(((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩

lemma idx_cast (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) :
    ((idx l b d j : ℕ) : ZMod l) = (((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l) := by
  simp [idx, ZMod.natCast_zmod_val]

lemma idx_inj (l : ℕ) [NeZero l] (a b d : ℤ) (had : ((a * d : ℤ) : ZMod l) = 1) :
    Function.Injective (idx l b d) := by
  intro j₁ j₂ h
  have h' := congrArg (fun x : Fin l => ((x : ℕ) : ZMod l)) h
  simp only [idx_cast] at h'
  push_cast at h' had
  have e : ((j₁ : ℕ) : ZMod l) = ((j₂ : ℕ) : ZMod l) := by
    linear_combination (a : ZMod l) ^ 2 * h' -
      (((j₁ : ℕ) : ZMod l) - ((j₂ : ℕ) : ZMod l)) * (1 + (a : ZMod l) * d) * had
  apply Fin.ext
  rw [ZMod.natCast_eq_natCast_iff'] at e
  simpa [Nat.mod_eq_of_lt j₁.2, Nat.mod_eq_of_lt j₂.2] using e

lemma coset (L l : ℕ) [NeZero l] (hlL : l ∣ L) (γ : SL(2, ℤ)) (hc : (L : ℤ) ∣ γ 1 0) (j : Fin l) :
    ∃ γ' : SL(2, ℤ), ((L * l : ℕ) : ℤ) ∣ γ' 1 0 ∧
      γ' 1 1 = γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) ∧
      repU l j * (γ : M2) = (γ' : M2) * repU l (idx l (γ 0 1) (γ 1 1) j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
  have hdiv : (l : ℤ) ∣ γ 0 1 + ((j : ℕ) : ℤ) * γ 1 1 -
      (γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0) * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have hj' := idx_cast l (γ 0 1) (γ 1 1) j
    have hd1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at hj' hd1 ⊢
    rw [hj']
    linear_combination (-((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l))) * hd1 -
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) *
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) * hc0
  obtain ⟨B, hB⟩ := hdiv
  obtain ⟨m, hm⟩ := hc
  refine ⟨⟨!![γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0, B; (l : ℤ) * γ 1 0,
      γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + γ 1 0 * hB
  · refine ⟨m, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [hm]; push_cast; ring
  · simp
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [repU, Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination hB | linear_combination -hB

end GlobalTheory.LevelLower

namespace GlobalTheory.LevelLower

lemma slz_sum (k : ℕ) (δ : M2) {ι : Type} [Fintype ι] (F : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => ∑ i, F i τ) τ = ∑ i, slz k δ (F i) τ := by
  simp only [slz, Finset.mul_sum]

lemma slz_smul (k : ℕ) (δ : M2) (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => c * f τ) τ = c * slz k δ f τ := by
  simp only [slz]; ring

lemma per (L : ℕ) (χ : ℤ → ℂ) (hχ : ∀ d, χ (d + L) = χ d) (m : ℤ) : ∀ d : ℤ, χ (d + m * L) = χ d := by
  refine Int.induction_on m ?_ ?_ ?_
  · intro d; simp
  · intro i ih d
    rw [show d + ((i : ℤ) + 1) * (L : ℤ) = (d + (i : ℤ) * L) + L by ring, hχ, ih]
  · intro i ih d
    have := hχ (d + (-(i : ℤ) - 1) * L)
    rw [show d + (-(i : ℤ) - 1) * (L : ℤ) + L = d + -(i : ℤ) * L by ring, ih] at this
    exact this.symm

end GlobalTheory.LevelLower

theorem GlobalTheory.Uo_lowers_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L →
    (∀ d, χ (d + L) = χ d) → MF k (L * l) χ a → MF k L χ (Uo l a) := by
  intro k L l χ a hk hl hlL hχ hMF
  obtain ⟨hP, hI⟩ := hMF
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨hPU, hqs⟩ := _root_.GlobalTheory.EisM.Uo_qs_sum_slz k l a hk hl.pos hP
  obtain ⟨hcoc, -, hinv, -, -⟩ := _root_.GlobalTheory.EisM.slz_props k (qs a) hk
  have hI' := (hinv (L * l) χ).mp hI
  refine ⟨hPU, ?_⟩
  rw [(_root_.GlobalTheory.EisM.slz_props k (qs (Uo l a)) hk).2.2.1]
  intro γ hc
  have hg : qs (Uo l a) = fun τ => ∑ j : Fin l, slz k (repU l j) (qs a) τ := funext hqs
  have hdU : ∀ j : Fin l, 0 < (repU l j).det := by
    intro j; simp [repU, Matrix.det_fin_two_of]; exact hl.pos
  have hdγ : ∀ γ : SL(2, ℤ), 0 < (γ : M2).det := by
    intro γ; rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos

  have had : ((γ 0 0 * γ 1 1 : ℤ) : ZMod l) = 1 := by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2
      rw [Matrix.det_fin_two] at this
      exact this
    have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at h1 hc0 ⊢
    rw [hc0, mul_zero, sub_zero] at h1
    exact h1
  let e : Fin l ≃ Fin l := Equiv.ofBijective (GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1))
    (Finite.injective_iff_bijective.mp (GlobalTheory.LevelLower.idx_inj l _ _ _ had))
  have key : ∀ (τ : ℍ) (j : Fin l), slz k (γ : M2) (slz k (repU l j) (qs a)) τ =
      χ (γ 1 1) * slz k (repU l (e j)) (qs a) τ := by
    intro τ j
    obtain ⟨γ', h1, h2, h3⟩ := GlobalTheory.LevelLower.coset L l hlL γ hc j
    rw [← hcoc _ _ (hdU j) (hdγ γ), h3, hcoc _ _ (hdγ γ') (hdU _), hI' γ' h1,
      GlobalTheory.LevelLower.slz_smul, h2]
    obtain ⟨m, hm⟩ := hc
    have : χ (γ 1 1 - γ 1 0 * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)) = χ (γ 1 1) := by
      rw [hm, show γ 1 1 - (L : ℤ) * m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) =
        γ 1 1 + (-(m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ))) * L by ring,
        GlobalTheory.LevelLower.per L χ hχ]
    rw [this]
    rfl
  rw [hg]
  funext τ
  rw [GlobalTheory.LevelLower.slz_sum]
  simp_rw [key τ]
  rw [← Finset.mul_sum, Equiv.sum_comp e (fun j => slz k (repU l j) (qs a) τ)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletFourierMixedTwistMultiple
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

noncomputable section

namespace GlobalTheory.EisM

theorem hat_mix_twist : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (ω : DirichletCharacter ℂ l) (φ : ZMod l → ℂ) (a c : ℤ),
    0 < N → 0 < l → N.Coprime l → (∀ x : ℤ, hat φ x = ch ω x) →
    (∀ d u : ZMod l, IsUnit d → φ u = ω d * φ (d * u)) → IsUnit (c : ZMod N) → IsUnit (a : ZMod l) →
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x : ℤ, hat (fun z : ZMod (N * l) => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) x = C * (ch ω x * hat ν x)) ∧
    ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y : ZMod (N * l),
      ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) y) * φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) y) =
      ch ω d * ch ν⁻¹ d * (ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) (y * d)) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) (y * d))) := by
  intro N l ν ω φ a c hN hl hc hφ htw hcu hau
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩
  have hlu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l hc.symm).isUnit
  have hNu : IsUnit (N : ZMod l) := (ZMod.unitOfCoprime N hc).isUnit
  refine ⟨?_, ?_⟩
  · have haN : IsUnit ((a : ZMod l) * N) := hau.mul hNu
    have hωaN : ω ((a : ZMod l) * N) ≠ 0 := (haN.map ω).ne_zero
    have hνcl : ν (-(c : ZMod N) * l) ≠ 0 := ((hcu.neg.mul hlu).map ν).ne_zero
    refine ⟨ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹, mul_ne_zero hνcl (inv_ne_zero hωaN), fun x => ?_⟩
    rw [← hφ x, mul_comm (hat φ x)]
    let f : ZMod N × ZMod l → ZMod (N * l) := fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))
    have hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N) :=
      fun k => map_natCast _ k
    have hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l) :=
      fun k => map_natCast _ k
    have hinj : Function.Injective f := by
      intro p q hpq
      have h1 := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq
      have h2 := congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq
      simp only [f, hcN, hcl] at h1 h2
      push_cast at h1 h2
      simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2
      exact Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hinj, by simp [ZMod.card]⟩
    rw [hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl),
      Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun p => ?_)
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun q => ?_)
    have hN1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q)) = p * l := by
      simp only [f, hcN]; push_cast; simp [ZMod.natCast_self]
    have hl1 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)) = q * N := by
      simp only [f, hcl]; push_cast; simp [ZMod.natCast_self]
    have htq := htw ((a : ZMod l) * N) q haN
    have hval : ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q))) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)))
        = ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹ * (ν p * φ q) := by
      rw [hN1, hl1, htq]
      have e1 : -(c : ZMod N) * (p * l) = (-(c : ZMod N) * l) * p := by ring
      have e2 : (a : ZMod l) * (q * N) = (a : ZMod l) * N * q := by ring
      rw [e1, e2, map_mul]
      field_simp
    have he : (ZMod.stdAddChar (f (p, q) * (x : ZMod (N * l))) : ℂ)
        = ZMod.stdAddChar (p * (x : ZMod N)) * ZMod.stdAddChar (q * (x : ZMod l)) := by
      have : f (p, q) * (x : ZMod (N * l)) = ((((p.val * l + q.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l)) := by
        simp only [f]; push_cast; rfl
      rw [this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int p x, stdAddChar_nat_mul_int q x, ← Complex.exp_add]
      congr 1
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
      push_cast
      field_simp
    rw [hval, he]
    ring
  · intro d hd y
    have hdN : IsUnit (d : ZMod N) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_left)
    have hdl : IsUnit (d : ZMod l) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_right)
    have h1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (y * d)
        = ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y * (d : ZMod N) := by
      rw [map_mul, map_intCast]
    have h2 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (y * d)
        = ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y * (d : ZMod l) := by
      rw [map_mul, map_intCast]
    rw [h1, h2]
    set u := ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y
    set v := ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y
    have hν0 : ν (d : ZMod N) ≠ 0 := (hdN.map ν).ne_zero
    have htv := htw (d : ZMod l) ((a : ZMod l) * v) hdl
    have e1 : -(c : ZMod N) * (u * d) = (-(c : ZMod N) * u) * d := by ring
    have e2 : (a : ZMod l) * (v * d) = (d : ZMod l) * ((a : ZMod l) * v) := by ring
    rw [e1, e2, map_mul ν (-(c : ZMod N) * u) (d : ZMod N)]
    unfold ch
    rw [MulChar.inv_apply_eq_inv', htv]
    field_simp

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralTraceEqZetaSubOneTopStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (S : Finset Ω), (∀ s ∈ S, IsInt (p := p) s) → ∀ j : ℕ, 1 ≤ j →
  ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ ⨅ n, Gn T n) ∧
    (∀ h ∈ ⨅ n, Gn T n, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
    ∑ g ∈ E, g y = T.ζ j - 1 := by
  first | exact @GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top | exact GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top | (intros; apply GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top <;> assumption)
end

