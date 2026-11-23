module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionHypothesesOfConditions
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.EqZeroOfPowEqOne

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.AtVariableArtinHasseEqOneLog
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus oneLog thetaOne)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)

namespace SingleLetterLog

section Lin

variable {K : Type} [NormedField K] {τ : Type}

theorem iter_one (σ : K →+* K) (k : ℕ) : σ^[k] 1 = 1 :=
  Function.iterate_fixed (map_one σ) k

theorem univ_two : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

theorem linEL_two (σ : K →+* K) (L : ZMod 2 → MvPowerSeries τ K) : linEL σ 1 L = L 0 := by
  unfold linEL
  rw [univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1]

theorem linOL_two (σ : K →+* K) (L : ZMod 2 → MvPowerSeries τ K) : linOL σ 1 L = L 1 := by
  unfold linOL
  rw [univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1]

theorem trDual_two (σ : K →+* K) : TrDual 2 σ (fun _ : Unit => (1 : K)) (fun _ => 1) := by
  refine ⟨by simp, fun r r' => ?_⟩
  rw [univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1]

theorem owOK_two (σ : K →+* K) : OwOK 2 σ (fun _ : Unit => (1 : K)) (fun _ => 1) :=
  ⟨fun _ => ⟨by simp, by simp⟩, fun _ => ⟨iter_one σ 2, iter_one σ 2⟩⟩

end Lin

section Log

theorem at_variable_artin_hasse_eq_one_log {K τ : Type} [Field K] [DecidableEq τ] (l : ℕ) (x : τ) :
    at1 x (lgF K l) = oneLog l x := by
  ext n
  unfold at1
  rw [PowerSeries.coeff_subst_single]
  change _ = oneLog (K := K) l x n
  unfold oneLog lgF
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · have hd : n.degree = n x := by
      conv_lhs => rw [h]
      simp
    rw [hd]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h3 : (n = Finsupp.single x ((l ^ 2) ^ e)) ↔ n x = (l ^ 2) ^ e :=
      ⟨fun h' => by rw [h']; simp, fun h' => by rw [h, h']⟩
    simp only [h3]
  · symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp

end Log

end SingleLetterLog

open SingleLetterLog Pair

theorem OneLetterHalf_of : MeanSimeqL → OneLetterHalf := by
  intro hM K0 _ _ _ l σ hU F hF be0 hF1 hF2 ζ hζ ph hph
  have hp : l.Prime := hU.1
  have hl : 2 ≤ l := hp.two_le
  have hlK : (l : K0) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hrefl, hsymm, htrans, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules K0 Unit
  have hST : ShiftType l σ (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0)) :=
    fun _ => FormalExponential.ip_lgF l σ hl hlK
  have h1 := hM K0 l 2 σ hU le_rfl (by decide) F hF be0 hF1 hF2 Unit _ _ (owOK_two σ)
    (trDual_two σ) ζ hζ Unit _ hST
  have hX : constantCoeff (PowerSeries.X : MvPowerSeries Unit K0) = 0 :=
    PowerSeries.constantCoeff_X
  have hlog : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K0) (lgF K0 l) = lgF K0 l :=
    PowerSeries.X_subst _
  have h2 : subst (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0))
      (beTil (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1)) =
      subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0 := by
    rw [subst_tilde K0 l 2 σ hl be0 Unit _ _ Unit _ (fun _ => cc_lgF hl)]
    rw [Finset.univ_unique, Finset.sum_singleton, linEL_two, linOL_two]
    have h3 := addC_log exponential_specification hl hX hX be0
    rw [hlog] at h3
    rw [h3]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [h2] at h1
  have h4 := B4.simeq_sub_zero (htrans _ _ _ hph (hsymm _ _ h1))
  have h5 := Formalism.InvariantFactorPaths.G7.Top.lamModule K0 Unit l σ hp hU.2.2.1 hU.2.2.2.2 _ 2
    (by
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      have := hU.2.1
      omega) h4
  unfold Simeq at h5 ⊢
  have h2K : (2 : K0) ≠ 0 := two_ne_zero
  have e : ∀ B : MvPowerSeries Unit K0, (ph : MvPowerSeries Unit K0) - MvPowerSeries.C ((2 : K0)⁻¹) * B =
      MvPowerSeries.C (((2 : ℕ) : K0)⁻¹) * (MvPowerSeries.C (2 : K0) * ph - B) - 0 := by
    intro B
    rw [sub_zero, mul_sub, ← mul_assoc, ← map_mul]
    simp [h2K]
  rw [e]
  exact h5

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionPointsOfExpSpec
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Pair

namespace BiextensionSums

theorem simeq_sum {K ι α : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    (s : Finset α) (f g : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Simeq (f a) (g a)) :
    Simeq (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.2.2.1 _ _ _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem subst_sumE {K ι κ : Type} [Field K] [Fintype ι] {N0 N1 : ℕ}
    {Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries κ K}
    (h0 : ∀ x, constantCoeff (Xt x) = 0) (be : MvPowerSeries (Fin 2) K) :
    subst Xt (sumE be) = ∑ e : ι × Fin N0 × Fin N1, subst ![Xt (false, e), Xt (true, e)] be := by
  have hX : HasSubst Xt := hasSubst_of_constantCoeff_zero h0
  unfold sumE
  rw [subst_sum hX]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (by intro a; simp)) hX]
  congr 1
  funext a
  rw [subst_X hX]
  fin_cases a <;> rfl

end BiextensionSums

open BiextensionSums

theorem biextension_points_of_exp_spec (hE : ExpSpec) (hM : MeanSimeqL) : BiextensionPointsIntegral := by
  intro K _ _ _ l d N0 N1 _ σ hU h2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
  have hl : 2 ≤ l := hU.1.two_le
  have hLS := fun a b => (letter_shift K l d σ hU.1).2.2 N0 N1 a b
  have hSI := ShiftIP_of_frobSq frobenius_square K l d σ hU hd (Formalism.DworkPowerSeriesWeights.ZV d N0 N1)
  have hIP : ∀ x : Bool × ι × Fin N0 × Fin N1, IP l σ
      (if x.1 = false then
        linEL (d := d) σ (oms x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))
      else linOL (d := d) σ (om x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))) := by
    intro x
    split_ifs
    · exact (hSI _ (hLS x.2.2.1 x.2.2.2) (oms x.2.1) (hOw.1 x.2.1).2 (hOw.2 x.2.1).2).1
    · exact (hSI _ (hLS x.2.2.1 x.2.2.2) (om x.2.1) (hOw.1 x.2.1).1 (hOw.2 x.2.1).1).2
  choose Xt h0 hi hlog using fun x => integral_part_lemma K l σ hU _ _ (hIP x)
  refine ⟨Xt, fun x => ⟨h0 x, hi x⟩, hlog, ?_⟩
  have hsum : (∑ e : ι × Fin N0 × Fin N1, subst ![Xt (false, e), Xt (true, e)] be0) =
      ∑ ab : Fin N0 × Fin N1, ∑ r : ι, subst ![Xt (false, r, ab), Xt (true, r, ab)] be0 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [subst_sumE h0, hsum]
  refine simeq_sum (K := K) _ _ _ fun ab _ => ?_
  have key := hM K l d σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ _
    (fun s => entLog (K := K) l (s, ab.1, ab.2)) (hLS ab.1 ab.2)
  rw [subst_tilde K l d σ hl be0 ι om oms _ _ (fun s => (hLS ab.1 ab.2 s).1)] at key
  have e : ∀ r : ι, subst ![Xt (false, r, ab), Xt (true, r, ab)] be0 =
      subst ![linEL (d := d) σ (oms r) (fun s => entLog (K := K) l (s, ab.1, ab.2)),
        linOL (d := d) σ (om r) (fun s => entLog (K := K) l (s, ab.1, ab.2))] (addC l be0) := by
    intro r
    rw [← addC_log hE hl (h0 _) (h0 _), hlog, hlog]
    simp
  simp only [e]
  exact key

end Formalism.L2.Th1.D
end
end

