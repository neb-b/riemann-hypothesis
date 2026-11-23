module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0201
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulDescentPhiMemLatticeOfOrbitBound
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPowKillsLatticeCokernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisEqZeroOfForallDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

def InJ (w : Per.Ainf l) : Prop := ∃ c : Per.OC l, Per.θ l w = (l : Per.OC l) * c

def IsLogJ (w : Per.Ainf l) (y : Per.Acris l) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ s : Per.Acris0 l,
    ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) w) ^ (k + 1) ∧
    ∃ z : Per.Acris l, y - algebraMap (Per.Acris0 l) (Per.Acris l) s = ((l : ℕ) : Per.Acris l) ^ r * z

theorem isLogJ_zero : IsLogJ (0 : Per.Ainf l) 0 := fun _ => ⟨0, fun _ _ => ⟨0, by simp, 0, by simp⟩⟩

private theorem acris_eq_zero_of_forall_dvd (x : Per.Acris l)
    (h : ∀ r : ℕ, ∃ z : Per.Acris l, x = ((l : ℕ) : Per.Acris l) ^ r * z) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.Acris l)})
    (GlobalTheory.MemLoc.acris_basic l).1.toIsHausdorff x fun r => ?_
  obtain ⟨z, hz⟩ := h r
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem isLogJ_unique {w : Per.Ainf l} {y y' : Per.Acris l} (h : IsLogJ w y) (h' : IsLogJ w y') :
    y = y' := by
  rw [← sub_eq_zero]
  refine acris_eq_zero_of_forall_dvd (y - y') fun r => ?_
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  obtain ⟨s, hs, z, hz⟩ := hN (max N N') (le_max_left _ _)
  obtain ⟨s', hs', z', hz'⟩ := hN' (max N N') (le_max_right _ _)
  have : s = s' := Subtype.ext
    ((GlobalTheory.RingBasics.isUnit_nat l _ (Nat.factorial_ne_zero _)).mul_left_cancel (hs.trans hs'.symm))
  subst this
  have key : y - y' = ((l : ℕ) : Per.Acris l) ^ r * (z - z') := by linear_combination hz - hz'
  exact ⟨z - z', key⟩

theorem isLogJ_extends {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) {w : Per.Ainf l} {y : Per.Acris l}
    (hy : IsLogJ w y) : IsLogJ (f w) (F y) := by
  intro r
  obtain ⟨N, hN⟩ := hy r
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, z, hz⟩ := hN n hn
  refine ⟨⟨Per.extP f s, hf.mem _ s.2⟩, ?_, F z, ?_⟩
  · have := congrArg (Per.extP f) hs
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, GlobalTheory.RingBasics.awayMap_algebraMap₂] using this
  · have := congrArg F hz
    rw [map_sub, map_mul, map_pow, map_natCast, hf.env] at this
    exact this

theorem inJ_mu {e : Per.Fl l} (he : e.untilt = 1) : InJ (mu e) :=
  ⟨0, by rw [Model.theta_mu, he, sub_self, mul_zero]⟩

theorem inJ_pow {e : Per.Fl l} (h : InJ (Per.tm e - 1)) (m : ℕ) : InJ (Per.tm (e ^ m) - 1) := by
  obtain ⟨c, hc⟩ := h
  have hθ : Per.θ l (Per.tm e) - 1 = (l : Per.OC l) * c := by rw [← hc, map_sub, map_one]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (Per.θ l (Per.tm e)) 1 m
  refine ⟨c * d, ?_⟩
  have e1 : Per.tm (e ^ m) = Per.tm e ^ m := map_pow (WittVector.teichmuller l) e m
  rw [e1, map_sub, map_one, map_pow, ← one_pow m, hd, hθ, mul_assoc]

end GlobalTheory.LogU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentMonodromyImageValuation
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.LcImage

open GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem eval_zero_polyR (l e : ℕ) (U : Finset ℤ) (η : ℕ) :
    (polyR l e U η).eval 0 = ∏ n ∈ (shifts U η).erase 0, (-(n * e * l)) := by
  simp [polyR, Polynomial.eval_prod]

theorem abs_lt_of_mem_shifts {l : ℕ} {U : Finset ℤ} {η H : ℕ} (hU : U ⊆ Finset.Icc (-(η : ℤ)) H)
    (hl : H + η < l) {n : ℤ} (hn : n ∈ shifts U η) : |n| < l := by
  obtain ⟨i, hi, k, ⟨hk1, hk2⟩, rfl⟩ := mem_shifts.1 hn
  have := Finset.mem_Icc.1 (hU hi)
  rw [abs_lt]; constructor <;> omega

theorem not_dvd_of_abs_lt {l : ℕ} {n : ℤ} (hn : n ≠ 0) (h : |n| < l) : ¬ (l : ℤ) ∣ n := by
  intro hd
  have h1 := Nat.le_of_dvd (Int.natAbs_pos.2 hn) (Int.ofNat_dvd_left.1 hd)
  have h2 : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
  omega

theorem padicValInt_prod {p : ℕ} [Fact p.Prime] (S : Finset ℤ) (f : ℤ → ℤ)
    (hf : ∀ n ∈ S, f n ≠ 0 ∧ padicValInt p (f n) = 1) :
    (∏ n ∈ S, f n) ≠ 0 ∧ padicValInt p (∏ n ∈ S, f n) = S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    have ih' := ih fun n hn => hf n (Finset.mem_insert_of_mem hn)
    have hx' := hf x (Finset.mem_insert_self x S)
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    refine ⟨mul_ne_zero hx'.1 ih'.1, ?_⟩
    rw [padicValInt.mul hx'.1 ih'.1, hx'.2, ih'.2]; ring

theorem valuation {l e a : ℕ} [Fact l.Prime] (hsucc : e + 1 = l ^ a) (ha : a ≠ 0) (he : e ≠ 0)
    (U : Finset ℤ) (η H N : ℕ) (hU : U ⊆ Finset.Icc (-(η : ℤ)) H) (hN : U.card ≤ N + 1)
    (hl : H + η < l) : Valuation l e U η N := by
  have hp : l.Prime := Fact.out
  have hle : ¬ (l : ℤ) ∣ (e : ℤ) := by
    intro hd
    have hd' : l ∣ e := Int.natCast_dvd_natCast.1 hd
    have h1 : l ∣ l ^ a := dvd_pow_self l ha
    rw [← hsucc] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd').1 h1))
  have key : ∀ n ∈ (shifts U η).erase 0, (-(n * e * l) : ℤ) ≠ 0 ∧ padicValInt l (-(n * e * l)) = 1 := by
    intro n hn
    obtain ⟨hn0, hnS⟩ := Finset.mem_erase.1 hn
    have hnl := not_dvd_of_abs_lt hn0 (abs_lt_of_mem_shifts hU hl hnS)
    have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast he
    have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine ⟨neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hn0 he0) hl0), ?_⟩
    have hneg : padicValInt l (-(n * e * l)) = padicValInt l (n * e * l) := by simp [padicValInt]
    rw [hneg, padicValInt.mul (mul_ne_zero hn0 he0) hl0, padicValInt.mul hn0 he0,
      padicValInt.eq_zero_of_not_dvd hnl, padicValInt.eq_zero_of_not_dvd hle, padicValInt.self hp.one_lt]
  obtain ⟨h1, h2⟩ := padicValInt_prod _ _ key
  refine ⟨fun n hn => abs_lt_of_mem_shifts hU hl hn, ?_, ?_, ?_, Nat.mul_le_mul_right _ hN⟩
  · rw [eval_zero_polyR]; exact h1
  · rw [eval_zero_polyR]; exact h2
  · calc ((shifts U η).erase 0).card ≤ (shifts U η).card := Finset.card_erase_le
      _ ≤ U.card * (Finset.Icc (1 : ℤ) η).card := Finset.card_image₂_le _ _ _
      _ = U.card * η := by rw [Int.card_Icc]; simp

end GlobalTheory.LcImage

namespace GlobalTheory.LcImage

open GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

section Lin

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem aeval_map_intCast {V : Type} [AddCommGroup V] [Module K V] (T : Module.End K V) (q : Polynomial ℤ) :
    Polynomial.aeval T (q.map (Int.castRingHom K)) = Polynomial.aeval T q := by
  rw [← Polynomial.aeval_map_algebraMap K T q]; rfl

theorem eval_polyRK_root {U : Finset ℤ} {n : ℤ} (hn : n ∈ shifts U η) (hn0 : n ≠ 0) :
    ((polyR l e U η).map (Int.castRingHom K)).eval (((n * e * l : ℤ) : K)) = 0 := by
  rw [polyR, Polynomial.map_prod, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hn0, hn⟩) ?_
  simp

theorem polyRK_mul_eq_zero (U : Finset ℤ) (hS : D.jumps ⊆ U) :
    Polynomial.aeval D.LcZ ((polyR l e U η).map (Int.castRingHom K)) * D.LcZ = 0 := by
  obtain ⟨-, -, htop⟩ := _root_.GlobalTheory.LcSemisimple.lc_semisimple O K l e a ι η H D U hS
  have hle : ⨆ n ∈ shifts U η, D.LcZ.eigenspace ((n * e * l : ℤ) : K) ≤
      LinearMap.ker (Polynomial.aeval D.LcZ ((polyR l e U η).map (Int.castRingHom K)) * D.LcZ) := by
    refine iSup₂_le fun n hn x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [LinearMap.mem_ker, Module.End.mul_apply, hx, map_smul]
    by_cases hn0 : n = 0
    · simp [hn0]
    by_cases hx0 : x = 0
    · simp [hx0]
    rw [Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩,
      eval_polyRK_root hn hn0, zero_smul, smul_zero]
  ext x
  have : x ∈ LinearMap.ker (Polynomial.aeval D.LcZ ((polyR l e U η).map (Int.castRingHom K)) * D.LcZ) := hle (htop ▸ Submodule.mem_top)
  simpa using this

end Lin

end GlobalTheory.LcImage

namespace GlobalTheory.LcImage

open GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem eval_zero_polyR_ne_zero {l e : ℕ} (hl : l ≠ 0) (he : e ≠ 0) (U : Finset ℤ) (η : ℕ) :
    (polyR l e U η).eval 0 ≠ 0 := by
  rw [eval_zero_polyR, Finset.prod_ne_zero_iff]
  intro n hn
  have hn0 := (Finset.mem_erase.1 hn).1
  have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast he
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hn0 he0) hl0)

section Lin2

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem LcZ_aeval_polyR₁ (U : Finset ℤ) (w : D.Zl) :
    D.LcZ (Polynomial.aeval D.LcZ (polyR₁ l e U η) w) =
      Polynomial.aeval D.LcZ (polyR l e U η) w - (((polyR l e U η).eval 0 : ℤ) : K) • w := by
  have := congrArg (fun q => Polynomial.aeval D.LcZ q w) (X_mul_polyR₁ l e U η)
  simpa [Module.End.mul_apply, Int.cast_smul_eq_zsmul] using this

theorem castK_ne_zero (U : Finset ℤ) : ((((polyR l e U η).eval 0 : ℤ)) : K) ≠ 0 := by
  have hr := eval_zero_polyR_ne_zero (Fact.out : l.Prime).ne_zero (NeZero.ne e) U η
  rw [← map_intCast (algebraMap ℚ_[l] K)]
  exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hr)

theorem image (U : Finset ℤ) (hS : D.jumps ⊆ U) : Image D U := by
  have h0 := polyRK_mul_eq_zero D U hS
  rw [aeval_map_intCast] at h0
  refine ⟨fun w hw => ?_, fun W hW => ?_⟩
  · have hR : Polynomial.aeval D.LcZ (polyR l e U η) w = 0 := by
      obtain ⟨u, rfl⟩ := hw
      rw [← Module.End.mul_apply, h0, LinearMap.zero_apply]
    refine ⟨hR, ?_⟩
    rw [LcZ_aeval_polyR₁, hR, zero_sub, neg_neg]
  · apply le_antisymm
    · intro w hw
      obtain ⟨hwR, hwW⟩ := Submodule.mem_inf.1 hw
      have h := GlobalTheory.coeff_zero_smul_mem_map_of_aeval_mul_eq_zero D.LcZ ((polyR l e U η).map (Int.castRingHom K))
        (polyRK_mul_eq_zero D U hS) W (fun z hz => hW hz) w hwW hwR
      rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero] at h
      have hne := castK_ne_zero (K := K) (l := l) (e := e) (η := η) U
      have : w = ((((polyR l e U η).eval 0 : ℤ)) : K)⁻¹ • ((Int.castRingHom K) ((polyR l e U η).eval 0) • w) := by
        rw [eq_intCast, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h
    · rintro _ ⟨x, hx, rfl⟩
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ _, hW hx⟩

theorem mem_Z_aeval (hI : Integral D) (q : Polynomial ℤ) (x : D.Zl) (hx : (x : D.Pol) ∈ D.Z) :
    ((Polynomial.aeval D.LcZ q x : D.Zl) : D.Pol) ∈ D.Z := by
  have hpow : ∀ (n : ℕ) (y : D.Zl), (y : D.Pol) ∈ D.Z → (((D.LcZ ^ n) y : D.Zl) : D.Pol) ∈ D.Z := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hI _ (ih y hy)
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply, Submodule.coe_add]; exact D.Z.add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    have := hpow n x hx
    simpa using zsmul_mem this c

theorem integralImage (U : Finset ℤ) (hS : D.jumps ⊆ U) (hI : Integral D) : IntegralImage D U := by
  intro c w hw hcw
  refine ⟨-(Polynomial.aeval D.LcZ (polyR₁ l e U η) w), ?_, ?_⟩
  · have := mem_Z_aeval D hI (polyR₁ l e U η) ((l : K) ^ c • w) (by simpa using hcw)
    rw [map_smul] at this
    rw [Submodule.coe_neg, smul_neg]
    exact D.Z.neg_mem (by simpa using this)
  · rw [map_neg]; exact ((image D U hS).1 w hw).2

end Lin2

end GlobalTheory.LcImage

theorem GlobalTheory.LcImage.image_valuation_integralImage : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D U ∧ (H + η < l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Valuation l e U η N) ∧ (10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralImage D U) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hS hU hN hηH
  refine ⟨GlobalTheory.LcImage.image D U hS, fun hl => ?_, fun hl => ?_⟩
  · exact GlobalTheory.LcImage.valuation (TameDescentExponentData.succ_eq (K := K)) (NeZero.ne a) (NeZero.ne e) U η H N hU hN hl
  · exact GlobalTheory.LcImage.integralImage D U hS (_root_.GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral O K l e a ι η H D hηH hl)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentPowSmulMonodromyAddPhiMem
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK.MonIntegral

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

omit [CompleteSpace K] in
theorem pow_smul_mem (W : Submodule O D.Pol) (n : ℕ) {w : D.Pol} (hw : w ∈ W) : (l : K) ^ n • w ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hw _


omit [CompleteSpace K] [NeZero e] in
theorem E_smul_mem_EM {p : Vec K a ι} (hp : p ∈ D.L) : E K l e • p ∈ D.EM η := by
  rw [mem_divE, smul_comm]
  exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)


omit [CompleteSpace K] in
theorem cls_E_smul_eq_zero {f : Vec K a ι} (hf : Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man) :
    D.cls (E K l e • f) = 0 := by
  have h := D.smul_mem_Man (pow_mem (E_mem l e (Rpi O K l e)) (2 * H + 1)) hf
  have h1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
  rw [smul_smul, pow_succ', mul_assoc, h1, mul_one] at h
  exact D.cls_eq_zero_iff.2 h

end GlobalTheory.BK.MonIntegral


open GlobalTheory.BK.MonIntegral in
theorem GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ r : ℕ, 1 ≤ r → (∀ τ, ∀ c ∈ D.desc.chars τ, frobPeriod l c ≤ r) → (r + 2) * η < l + 1 → l ≠ 2 → ∀ y ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ (η * (r + 1)) • D.Mon (y + D.phi m) ∈ D.Z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hH h14 h10 r hr hc hrl hl y hy m hm
  obtain ⟨hsplit, hfil, -⟩ := _root_.GlobalTheory.IntegralityComp.integralityComputation O K l e a ι η H D hH h10
  have hint := _root_.GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral O K l e a ι η H D hH h10
  have hyY : y ∈ D.Y := D.desc.Y'_le_Y η hy
  set W : Submodule O D.Pol :=
    ((D.EM η).restrictScalars O).map (D.cls.restrictScalars O) with hW
  have hL : ∀ p ∈ D.L, D.cls (E K l e • p) ∈ W := fun p hp => ⟨_, E_smul_mem_EM D hp, rfl⟩
  have hMM : ∀ μ ∈ D.MM, D.cls (E K l e • μ) ∈ W := fun μ hμ => by
    obtain ⟨p, hp, f, hf, rfl⟩ := hsplit μ hμ
    rw [smul_add, map_add (f := _), cls_E_smul_eq_zero D (hfil f hf), add_zero]
    exact hL p hp
  have h1 : D.Mon y ∈ W := by
    rw [D.Mon_eq]
    refine sub_mem (hint _ (D.desc.cls_mem_Z hyY)).1 ?_
    obtain ⟨p, hp, f, hf, h⟩ := _root_.GlobalTheory.BK.zeta_Y'_fine_bound O K l e a ι η H D hη hH h14 y hy
    rw [h, smul_add, map_add (f := _), smul_comm (E K l e) _ p, smul_comm (E K l e) _ f,
      D.cls.map_smul ((l : K) ^ _), D.cls.map_smul (_⁻¹ : K), cls_E_smul_eq_zero D (hfil f hf), smul_zero, add_zero]
    exact pow_smul_mem D W _ (hL p hp)
  have h2 : (l : K) ^ (η * (r + 1)) • D.Mon (D.phi m) ∈ W := by
    rw [D.Mon_eq, smul_sub, BKDat.Lc_cls, PhiMod.EN_apply]
    refine sub_mem (pow_smul_mem D W _ (hMM _ (D.conn_mem_MM
      (D.ext_mono (A_le_S l e) (D.phi_mem_L hm.1))))) ?_
    rw [← map_smul, ← smul_comm (E K l e)]
    exact hMM _ (_root_.GlobalTheory.BK.l_pow_smul_zeta_phi_mem_MM O K l e a ι η H D r hr hc hrl hl m hm)
  refine ⟨?_, ?_⟩
  · rw [map_add (f := _), smul_add]
    exact add_mem (pow_smul_mem D W _ h1) h2
  · refine D.desc.actPol.invariants.smul_mem _ (D.desc.Mon_mem_invariants (add_mem hyY.2 fun g => ?_))
    rw [D.desc.act_phi, hm.2 g]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLpowEisensteinPowTwistedDecomp
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

section Helpers

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {a : ℕ} {ι : Type}

theorem Epow_smul_mem_of_hasU (l e : ℕ) {B : Subalgebra O K⟦X⟧} [HasU B]
    (W : Submodule B (Vec K a ι)) (k : ℕ) {x : Vec K a ι} (hx : x ∈ W) : E K l e ^ k • x ∈ W := by
  have := W.smul_mem (EIn l e B ^ k) hx
  rwa [Subalgebra.smul_def, SubmonoidClass.coe_pow, coe_EIn] at this

theorem natPow_smul_mem {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] [Module K M]
    (W : Submodule R M) (l n : ℕ) {x : M} (hx : x ∈ W) : (l : K) ^ n • x ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact W.nsmul_mem hx _

end Helpers

theorem lpow_Epow_twistedMon_decomp : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (c : ℕ), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ c • D.zeta (D.phi m) ∈ D.MM → ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man ∧ (l : K) ^ c • (E K l e ^ (2 * H) • (E K l e • D.zeta (y' + D.phi m) - D.EN (y' + D.phi m))) = p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D c h1 h2 h3 h4 y' hy' m hm hc
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hr : ((l : K) ^ (3 * H)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have IC := _root_.GlobalTheory.IntegralityComp.integralityComputation O K l e a ι η H D h2 h4
  obtain ⟨p₁, hp₁, f₁, hf₁, h₁⟩ := _root_.GlobalTheory.BK.zeta_Y'_fine_bound O K l e a ι η H D h1 h2 h3 y' hy'
  obtain ⟨p', hp', f', hf', h'⟩ := IC.1 _ hc
  have hy : y' + D.phi m ∈ D.EM η := by
    refine add_mem ((D.desc.Y'_le_Y η hy').1 : y' ∈ D.EM η) ?_
    rw [mem_divE]
    exact D.upper _ (D.phi_mem_L hm.1)
  obtain ⟨p'', hp'', f'', hf'', h''⟩ := IC.2.2 _ hy
  set r : K := (l : K)
  set u : K⟦X⟧ := E K l e
  have hF : (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) ∈ D.FilMM (10 * H) :=
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ hf₁))
      (natPow_smul_mem _ _ _ (Epow_smul_mem_of_hasU l e _ _ hf')))
      (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hf''))
  refine ⟨u ^ (2 * H + 1) • (r ^ c • r ^ (l - 14 * H) • p₁) + u ^ (2 * H + 1) • p' - r ^ c • p'',
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hp₁)))
      (Epow_smul_mem_of_hasU l e _ _ hp')) (natPow_smul_mem _ _ _ hp''), _, hF, IC.2.1 _ hF, ?_⟩
  have hinv : (r ^ (3 * H))⁻¹ • (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) =
      u ^ (2 * H + 1) • (r ^ c • ((r ^ (3 * H))⁻¹ • f₁)) + u ^ (2 * H + 1) • f' - r ^ c • f'' := by
    rw [smul_sub, smul_add, inv_smul_smul₀ hr, inv_smul_smul₀ hr, smul_comm (r ^ (3 * H))⁻¹ (u ^ (2 * H + 1)),
      smul_comm (r ^ (3 * H))⁻¹ (r ^ c)]
  rw [hinv, map_add D.zeta, h₁, smul_sub, smul_smul (u ^ (2 * H)) u, ← pow_succ, smul_sub,
    smul_comm (r ^ c) (u ^ (2 * H + 1)), smul_add (r ^ c) _ (D.zeta (D.phi m)), h', h'']
  simp only [smul_add]
  abel

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDualZmodLeCard
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_dual_zmod_le_card :
    ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card A := by
  intro n _ A _ _ _
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let Φ : Module.Dual (ZMod n) A → AddChar A ℂ := fun f =>
    (ZMod.stdAddChar (N := n)).compAddMonoidHom f.toAddMonoidHom
  have hinj : Function.Injective Φ := by
    intro f g h
    ext a
    have h1 := congrArg (fun χ : AddChar A ℂ => χ a) h
    simp only [Φ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h1
    exact ZMod.injective_stdAddChar h1
  calc Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card (AddChar A ℂ) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card A := by
        rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  intro O K _ _ _ _ _ l e a _ _ _ _ hT ι κ _ _ _ _ Sig U N η H hB D₁ D₂ hD₁ hD₂ F hF
  haveI : FiniteDimensional ℚ_[l] K := hT.finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  exact _root_.GlobalTheory.CokerLift.killsAll_of_killsCoker_L O K l e a ι κ η H D₁ D₂ F _
    (_root_.GlobalTheory.CokerL.kills_cokerL O K l e a ι κ η H D₁ D₂ F Sig U N hB hD₁.chars_subset hD₂ hF)

end GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow
end

