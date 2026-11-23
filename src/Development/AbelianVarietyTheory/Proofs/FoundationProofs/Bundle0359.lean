module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0356

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

def tau (c : Coef l) : c.O →ₗ[ℤ_[l]] ℤ_[l] := Classical.choose (coef_dual_free_rank_one l c)

theorem tau_spec (c : Coef l) : ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = tau c (a * x) :=
  Classical.choose_spec (coef_dual_free_rank_one l c)

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : Qbar l)‖ = 1 := by
  have h1 := CupCob.norm_le_one_of_mem c (u : c.O).2
  have h2 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : ((u : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg ((u : c.O) : Qbar l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : Qbar l)]

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem dvd_of_mem_Ik (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) : ∃ y : c.O, x = (l : c.O) ^ n * y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have : ((l : c.O) : Qbar l) = 0 := by rw [h]; rfl
    rw [SubringClass.coe_natCast] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have nl : ‖((l : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ e := by
    rw [hw, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have nx : ‖((x : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ k := by
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlt : ‖((l : c.O) : Qbar l)‖ < 1 := by rw [SubringClass.coe_natCast]; exact norm_l_lt_one
  have hϖ1 : ‖((ϖ : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ϖ.2
  have he : e ≠ 0 := by
    rintro rfl
    rw [nl, pow_zero] at hlt
    exact lt_irrefl _ hlt
  have hϖlt : ‖((ϖ : c.O) : Qbar l)‖ < 1 := by
    rcases hϖ1.lt_or_eq with h | h
    · exact h
    · rw [nl, h, one_pow] at hlt; exact absurd hlt (lt_irrefl _)
  have hϖ0 : 0 < ‖((ϖ : c.O) : Qbar l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hle : e * n ≤ k := by
    have h := (mem_Ik.1 hx)
    have e2 : ‖((l : ℕ) : Qbar l) ^ n‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ (e * n) := by
      rw [norm_pow, ← SubringClass.coe_natCast c.O, nl, pow_mul]
    rw [nx, e2] at h
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 h
  refine ⟨(u : c.O) * ϖ ^ (k - e * n) * ((w⁻¹ : c.Oˣ) : c.O) ^ n, ?_⟩
  rw [hu, hw]
  have hk : k = e * n + (k - e * n) := by omega
  conv_lhs => rw [hk]
  calc (u : c.O) * ϖ ^ (e * n + (k - e * n))
      = (u : c.O) * ϖ ^ (k - e * n) * (((w : c.O) * ((w⁻¹ : c.Oˣ) : c.O)) ^ n * ϖ ^ (e * n)) := by
        rw [Units.mul_inv, one_pow, one_mul, pow_add]; ring
    _ = _ := by ring

theorem tau_red_zero (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) :
    PadicInt.toZModPow n (tau c x) = 0 := by
  obtain ⟨y, rfl⟩ := dvd_of_mem_Ik c n hx
  have e : (l : c.O) ^ n * y = ((l : ℤ_[l]) ^ n) • y := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, map_smul, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

def lft (c : Coef l) (n : ℕ) : Qn c n → c.O := Function.surjInv (red_surjective c n)

theorem red_lft (c : Coef l) (n : ℕ) (b : Qn c n) : red c n (lft c n b) = b :=
  Function.surjInv_eq (red_surjective c n) b

theorem tau_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : red c n x = red c n y) :
    PadicInt.toZModPow n (tau c x) = PadicInt.toZModPow n (tau c y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine tau_red_zero c n ?_
  rw [← red_eq_zero_iff_mem, map_sub, h, sub_self]

def tbA (c : Coef l) (n : ℕ) : Qn c n →+ ZMod (l ^ n) where
  toFun b := PadicInt.toZModPow n (tau c (lft c n b))
  map_zero' := by
    rw [← map_zero (red c n), tau_congr c n (red_lft c n _), map_zero, map_zero]
  map_add' a b := by
    obtain ⟨x, rfl⟩ := red_surjective c n a
    obtain ⟨y, rfl⟩ := red_surjective c n b
    rw [← map_add (f := _), tau_congr c n (red_lft c n _), tau_congr c n (red_lft c n _),
      tau_congr c n (red_lft c n _), map_add, map_add]

theorem tbA_red (c : Coef l) (n : ℕ) (x : c.O) : tbA c n (red c n x) = PadicInt.toZModPow n (tau c x) :=
  tau_congr c n (red_lft c n _)

def pairA (c : Coef l) (n : ℕ) (y : Mn c n) : Mn c n →+ ZMod (l ^ n) where
  toFun x := tbA c n (x 0 * y 1 - x 1 * y 0)
  map_zero' := by simp
  map_add' a b := by
    rw [← map_add (f := _)]; congr 1; simp only [Pi.add_apply]; ring

def Phi (c : Coef l) (n : ℕ) : Mn c n →ₗ[ZMod (l ^ n)] TDual (ZMod (l ^ n)) (Mn c n) :=
  (AddMonoidHom.mk' (fun y => TDual.mk ((pairA c n y).toZModLinearMap (l ^ n))) (fun a b => by
    refine DFunLike.ext _ _ fun x => ?_
    show tbA c n _ = tbA c n _ + tbA c n _
    rw [← map_add (f := _)]; congr 1; simp only [Pi.add_apply]; ring)).toZModLinearMap (l ^ n)

theorem Phi_apply (c : Coef l) (n : ℕ) (y x : Mn c n) : Phi c n y x = tbA c n (x 0 * y 1 - x 1 * y 0) := rfl

theorem red_mulVec (c : Coef l) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (hM : ∀ i j, M i j ∈ c.O)
    (v : Fin 2 → Qbar l) (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    red c n ⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ =
      ((Matrix.of fun i j => red c n ⟨M i j, hM i j⟩) *ᵥ fun j => red c n ⟨v j, hv j⟩) i := by
  have e : (⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ : c.O) =
      (⟨M i 0, hM i 0⟩ : c.O) * ⟨v 0, hv 0⟩ + (⟨M i 1, hM i 1⟩ : c.O) * ⟨v 1, hv 1⟩ := by
    apply Subtype.ext
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subalgebra.coe_add, Subalgebra.coe_mul]
  rw [e, map_add (f := _), map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]

def lftV (c : Coef l) (n : ℕ) (y : Mn c n) : Fin 2 → Qbar l := fun i => (lft c n (y i) : Qbar l)

theorem lftV_mem (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : lftV c n y i ∈ c.O := (lft c n (y i)).2

theorem red_lftV (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : red c n ⟨lftV c n y i, lftV_mem c n y i⟩ = y i :=
  red_lft c n (y i)

theorem cg_of_red {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩) : Cg n a b := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).1 h

theorem red_of_cg {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : Cg n a b) : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩ := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).2 h

end GlobalTheory.Ord2.SelPerp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditions
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.Unbounded

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | (apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem ..)

theorem mulVec_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {x : Fin 2 → Qbar l}
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ j, x j ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM i 0) (hx 0)) (c.O.mul_mem (hM i 1) (hx 1))

theorem lpow_ne_zero (n : ℕ) : ((l : ℕ) : Qbar l) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem inv_mul_sub_mem (c : Coef l) (n : ℕ) {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O) (h : Cg n a b) :
    (((l : ℕ) : Qbar l) ^ n)⁻¹ * (a - b) ∈ c.O := by
  refine _root_.GlobalTheory.Ord2.mem_coefO_of_memE_norm_le_one l c _ ⟨n, ?_⟩ ?_
  · rw [← mul_assoc, mul_inv_cancel₀ (lpow_ne_zero n), one_mul]
    exact c.O.sub_mem ha hb
  · rw [norm_mul, norm_inv]
    have hp : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (lpow_ne_zero n)
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact h

end GlobalTheory.Ord2.Unbounded

namespace GlobalTheory.Ord2.Unbounded

theorem divSel_unbounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) →
    (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n W ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
      (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n W (Ine (F := ℚ) B) z) ∧
      (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat W s 1 1 * x - x)) ∧
      ¬ Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) →
    ∀ m : ℕ, ∃ x : DivSel c W S A, l ^ m • x ≠ 0 := by
  intro l _ Ω _ _ _ S A W c hW hg H m
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.Ord2.exists_pow_smul_cob1_of_cv_mod_pow l Ω W c hW hg
  obtain ⟨n, z, hcoc, hker, hine, hdec, hnot⟩ := H (m + r)
  have hz : ∀ s i, z s i ∈ c.O := hcoc.2.1
  have hL0 : ((l : ℕ) : Qbar l) ^ n ≠ 0 := lpow_ne_zero n
  set L : Qbar l := ((l : ℕ) : Qbar l) ^ n with hL
  have hLO : L ∈ c.O := natPow_mem c n
  let ζ : G ℚ Ω → Fin 2 → Qbar l := fun s => L⁻¹ • z s
  have hζ : ∀ s i, ζ s i = L⁻¹ * z s i := fun s i => rfl
  have hmem : ζ ∈ divSelCoc c W S A := by
    refine ⟨⟨n, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B' hB' => ?_, ?_⟩
    · rw [hζ, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hz s i
    · have e : ζ (s * t) i - ζ s i - (mat W s *ᵥ ζ t) i = L⁻¹ * (z (s * t) i - (z s + mat W s *ᵥ z t) i) := by
        simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
      rw [e]
      exact inv_mul_sub_mem c n (hz _ _) (c.O.add_mem (hz s i) (mulVec_mem c (hW s) (hz t) i))
        (hcoc.2.2 s trivial t trivial i)
    · have hc : Continuous z := by
        have := hcoc.1
        rw [Subgroup.coe_top, continuousOn_univ] at this
        exact this
      have hp : 0 < ‖L‖ := norm_pos_iff.2 hL0
      filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto s) _ hp] with t ht i
      have e : ζ t i - ζ s i = L⁻¹ * (z t i - z s i) := by
        simp only [ζ, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine inv_mul_sub_mem c n (hz t i) (hz s i) ?_
      unfold Cg
      rw [dist_eq_norm] at ht
      exact le_trans (norm_le_pi_norm (z t - z s) i) ht.le
    · have e : ζ a i = L⁻¹ * (z a i - 0) := by rw [sub_zero, hζ]
      rw [e]
      exact inv_mul_sub_mem c n (hz a i) c.O.zero_mem (hker a ha i)
    · obtain ⟨B, hB, hcob⟩ := hine q hq hl
      obtain ⟨x, hx, hxs⟩ := GlobalTheory.T.coboundary_inertia_independent l Ω W c n z q B B' hW hcoc hB hB' hcob
      refine ⟨L⁻¹ • x, ⟨n, fun i => ?_⟩, fun s hs i => ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx i
      · have e : ζ s i - (mat W s *ᵥ (L⁻¹ • x) - L⁻¹ • x) i = L⁻¹ * (z s i - (mat W s *ᵥ x - x) i) := by
          simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s i) (c.O.sub_mem (mulVec_mem c (hW s) hx i) (hx i)) (hxs s hs i)
    · obtain ⟨x, hx, hxs⟩ := hdec
      refine ⟨L⁻¹ * x, ⟨n, ?_⟩, fun s hs => ?_⟩
      · rw [← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx
      · have e : ζ s 1 - (mat W s 1 1 * (L⁻¹ * x) - L⁻¹ * x) = L⁻¹ * (z s 1 - (mat W s 1 1 * x - x)) := by
          rw [hζ]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s 1) (c.O.sub_mem (c.O.mul_mem (hW s 1 1) hx) hx) (hxs s hs)
  refine ⟨QuotientAddGroup.mk ⟨ζ, hmem⟩, fun h0 => hnot ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
  obtain ⟨y, ⟨k, hk⟩, hy⟩ := h0
  have hy' : ∀ s i, ((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i ∈ c.O := by
    intro s i
    have := hy s i
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have key := hr n (fun s => ((l : ℕ) : Qbar l) ^ m • z s) (L • y)
    (fun s i => by rw [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (natPow_mem c m) (hz s i))
    ⟨k, fun i => by
      rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]; exact c.O.mul_mem hLO (hk i)⟩
    (fun s i => by
      have e : (((l : ℕ) : Qbar l) ^ m • z s) i - (mat W s *ᵥ (L • y) - L • y) i =
          L * (((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i) := by
        rw [hζ]
        simp only [Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_sub L, mul_sub L, mul_left_comm L, mul_inv_cancel_left₀ hL0]
      unfold Cg
      rw [e, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem c (hy' s i)))
  have hf : (fun s => ((l : ℕ) : Qbar l) ^ r • (fun s => ((l : ℕ) : Qbar l) ^ m • z s) s) =
      fun s => ((l : ℕ) : Qbar l) ^ (m + r) • z s := by
    funext s; rw [smul_smul, ← pow_add, add_comm]
  rw [hf] at key
  exact key

end GlobalTheory.Ord2.Unbounded

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumFix

theorem pow_val_add {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (h : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, h, one_pow, mul_one]

theorem isClosed_of_le {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H N U : Subgroup Γ)
    (hH : IsClosed (H : Set Γ)) (hU : IsOpen (U : Set Γ)) (hNH : N ≤ H) (hUN : ∀ s ∈ H, s ∈ U → s ∈ N) :
    IsClosed (N : Set Γ) := by
  have h1 : IsOpen ((U.subgroupOf H : Subgroup H) : Set H) := hU.preimage continuous_subtype_val
  have h2 : IsOpen ((N.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.isOpen_mono (H₁ := U.subgroupOf H) (fun s hs => hUN s s.2 hs) h1
  have h3 : IsClosed ((N.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ h2
  have h4 := hH.isClosedMap_subtype_val _ h3
  convert h4 using 1
  ext s
  constructor
  · intro hs
    exact ⟨⟨s, hNH hs⟩, hs, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

theorem exists_eigen {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} [NeZero n] (H : Subgroup (G ℚ Ω))
    (hH : IsClosed (H : Set (G ℚ Ω))) (ζ : Ω) (hζ : ζ ^ n = 1) (hfix : ∀ s ∈ H, s ζ = ζ) (χ : G ℚ Ω → ZMod n)
    (hχ : ∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) (U : Subgroup (G ℚ Ω)) (hU : IsOpen (U : Set (G ℚ Ω)))
    (hUχ : ∀ s ∈ H, s ∈ U → χ s = 0) : ∃ w : Ω, w ≠ 0 ∧ ∀ s ∈ H, s w = ζ ^ (χ s).val * w := by
  classical
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  have h1 : χ 1 = 0 := by
    have := hχ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ s ∈ H, χ s⁻¹ = -χ s := by
    intro s hs
    have := hχ s⁻¹ (H.inv_mem hs) s hs
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let N : Subgroup (G ℚ Ω) :=
    { carrier := {s | s ∈ H ∧ χ s = 0}
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by rw [hχ a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨H.one_mem, h1⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by rw [hinv a ha.1, ha.2, neg_zero]⟩ }
  have hNc : IsClosed (N : Set (G ℚ Ω)) :=
    isClosed_of_le H N U hH hU (fun s hs => hs.1) (fun s hs hsU => ⟨hs, hUχ s hs hsU⟩)
  have hNfix : (IntermediateField.fixedField N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hNc⟩
  let E := IntermediateField.fixedField N
  let ι := {k : ZMod n // ∃ g ∈ H, χ g = k}
  choose r hrH hrχ using fun k : ι => k.2
  let f : ι → (E →* Ω) := fun k =>
    { toFun := fun x => r k (x : Ω)
      map_one' := by simp
      map_mul' := fun x y => by simp }
  have hf : Function.Injective f := by
    intro j k hjk
    have hm : (r j)⁻¹ * r k ∈ N := by
      rw [← hNfix, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e : r j x = r k x := DFunLike.congr_fun hjk ⟨x, hx⟩
      rw [AlgEquiv.mul_apply, ← e]
      exact (r j).symm_apply_apply x
    have h2 := hm.2
    rw [hχ _ (H.inv_mem (hrH j)) _ (hrH k), hinv _ (hrH j), hrχ, hrχ] at h2
    exact Subtype.ext (neg_add_eq_zero.mp h2)
  have hli := (linearIndependent_monoidHom E Ω).comp f hf
  have hex : ∃ x : E, ∑ k : ι, ζ ^ (-(k : ZMod n)).val * r k (x : Ω) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Fintype.linearIndependent_iff.mp hli (fun k => ζ ^ (-(k : ZMod n)).val) (by
      funext x
      rw [Finset.sum_apply]
      exact hcon x) ⟨0, 1, H.one_mem, h1⟩
    exact pow_ne_zero _ hζ0 this
  obtain ⟨x, hx⟩ := hex
  refine ⟨_, hx, fun s hs => ?_⟩
  let e : ι ≃ ι :=
    { toFun := fun k => ⟨χ s + k, s * r k, H.mul_mem hs (hrH k), by rw [hχ _ hs _ (hrH k), hrχ]⟩
      invFun := fun k => ⟨-χ s + k, s⁻¹ * r k, H.mul_mem (H.inv_mem hs) (hrH k), by
        rw [hχ _ (H.inv_mem hs) _ (hrH k), hrχ, hinv s hs]⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, ← Equiv.sum_comp e (fun k : ι => ζ ^ (χ s).val * (ζ ^ (-(k : ZMod n)).val * r k (x : Ω)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hm : (r (e k))⁻¹ * (s * r k) ∈ N := by
    refine ⟨H.mul_mem (H.inv_mem (hrH _)) (H.mul_mem hs (hrH k)), ?_⟩
    rw [hχ _ (H.inv_mem (hrH _)) _ (H.mul_mem hs (hrH k)), hinv _ (hrH _), hχ _ hs _ (hrH k), hrχ, hrχ]
    exact neg_add_cancel _
  have hx1 : ((r (e k))⁻¹ * (s * r k)) (x : Ω) = x := (IntermediateField.mem_fixedField_iff N x).mp x.2 _ hm
  have hx2 : s (r k (x : Ω)) = r (e k) (x : Ω) := by
    have := congrArg (r (e k)) hx1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
    rw [← this]
    exact ((r (e k)).apply_symm_apply _).symm
  rw [map_mul, map_pow, hfix s hs, hx2, ← mul_assoc, ← pow_val_add hζ]
  congr 3
  change -(k : ZMod n) = χ s + -(χ s + k)
  ring

theorem exists_kumVal : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (H : Subgroup (G ℚ Ω)), IsClosed (H : Set (G ℚ Ω)) → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → (∀ s ∈ H, s ζ = ζ) → ∀ χ : G ℚ Ω → ZMod (l ^ m), (∀ s ∈ H, ∀ t ∈ H, χ (s * t) = χ s + χ t) → ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → (∀ s ∈ H, s ∈ U → χ s = 0) → ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧ ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (χ s) := by
  intro l _ Ω _ _ _ m H hH ζ hζ hfix χ hχ U hU hUχ
  haveI : NeZero (l ^ m) := ⟨(pow_pos (Fact.out : l.Prime).pos m).ne'⟩
  obtain ⟨w, hw0, hw⟩ := exists_eigen H hH ζ hζ.pow_eq_one hfix χ hχ U hU hUχ
  refine ⟨w ^ (l ^ m), pow_ne_zero _ hw0, fun s hs => ?_, fun s hs => ⟨w, rfl, hw s hs⟩⟩
  rw [map_pow, hw s hs, mul_pow, ← pow_mul, mul_comm (χ s).val, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.KumFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfEx

theorem up2 {k : Type} [Field k] (X Y Z : Matrix (Fin 2) (Fin 2) k) (hX : X 1 0 = 0) (hY : Y 1 0 = 0) (hZ : Z 1 0 = 0) :
    (X * Y * Z) 1 0 = 0 ∧ (X * Y * Z) 0 0 = X 0 0 * Y 0 0 * Z 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hX, hY, hZ]

theorem inv_up {k : Type} [Field k] (B : GL (Fin 2) k) (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧
    (B : Matrix (Fin 2) (Fin 2) k) 0 0 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
  have key : ∀ i j, ∑ x, (B : Matrix (Fin 2) (Fin 2) k) i x * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) x j =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => by
    rw [← Matrix.mul_apply, B.mul_inv]
  have e10 := key 1 0
  have e11 := key 1 1
  have e00 := key 0 0
  rw [Fin.sum_univ_two, hB, zero_mul, zero_add] at e10 e11
  rw [Fin.sum_univ_two] at e00
  rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
  rw [Matrix.one_apply_eq] at e11 e00
  have hN : ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rcases mul_eq_zero.1 e10 with h | h
    · rw [h, zero_mul] at e11
      exact absurd e11 zero_ne_one
    · exact h
  refine ⟨hN, ?_⟩
  rw [hN, mul_zero, add_zero] at e00
  exact e00

end GlobalTheory.NfEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperRep
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem sum_act_upper_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (N l : ℕ) [Fact l.Prime] (q M : ℕ), 0 < q → Nat.Coprime q M → ∀ b : X.Fn l,
    (∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b) →
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] b =
      ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b := by
  intro Ω _ _ _ ε X N l _ q M hq hqM b hb
  have hT : ∀ t : ℤ, X.act l !![1, t; 0, 1] b = b := by
    intro t
    let T : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hmem : T ∈ Gam N l := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [CongruenceSubgroup.Gamma1_mem]
        refine ⟨?_, ?_, ?_⟩ <;> simp [T]
      · rw [CongruenceSubgroup.Gamma0_mem]
        simp [T]
    exact hb T hmem
  have he : IsCoprime (M : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd_natCast_natCast] using hqM.symm
  exact (Tower.sum_act_upper_mul_unit X l b hT q (M : ℤ) hq he).symm

end GlobalTheory.KZ.ES
end

