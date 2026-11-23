module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0011
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerPrin
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0021
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0019
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0013
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgPhInt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem phNorm_int {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hF : C.Frame R l linv ph) (h1 : C.F1 R l linv ph) (hneg : C.PhNormAt R l linv ph (-1) (-1))
    (h2 : (2 : K)⁻¹ ∈ R) (n : ℤ) : C.PhNormAt R l linv ph (n : K) (n : K) := by
  have hl : C.IsLogPair l linv := hF.1
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hXpt : C.IsPt R (PowerSeries.X : MvPowerSeries Unit K) := C.Pts.isPt_X

  set q : K → MvPowerSeries Unit K :=
    fun a => PowerSeries.subst (C.fmul l linv a (PowerSeries.X : MvPowerSeries Unit K)) ph with hq
  set B : MvPowerSeries Unit K :=
    C.be0 l linv ph (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.X : MvPowerSeries Unit K)
    with hB
  have hphX : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph

  have hE : ∀ m : ℤ, C.LG R (q (1 + (m : K)) - ph - q (m : K) - (m : K) • B) := by
    intro m
    have h := C.zLinInt K R l linv ph hF h1 m Unit _ _ hXpt hXpt
    unfold C.Cong at h
    rw [C.be0] at h
    have e : C.fadd l linv (PowerSeries.X : MvPowerSeries Unit K)
        (C.fmul l linv (m : K) (PowerSeries.X : MvPowerSeries Unit K)) =
        C.fmul l linv (1 + (m : K)) (PowerSeries.X : MvPowerSeries Unit K) := by
      rw [C.Pts.fmul_add hl 1 (m : K) hX, C.Pts.fmul_one hl hX]
    rw [e, hphX] at h
    exact h
  have hq0 : q 0 = 0 := by
    simp only [hq]
    rw [C.Pts.fmul_zero_left hl, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2]
  have hN : C.LG R (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) := by
    have h := hneg
    unfold C.PhNormAt C.Cong at h
    rw [C.Pts.mulBy_eq_fmul] at h
    exact h

  have hG : C.LG R (B - (2 : K) • (ph : MvPowerSeries Unit K)) := by
    have h := C.Calc.lg_add (hE (-1)) hN
    have e : (q (1 + ((-1 : ℤ) : K)) - ph - q ((-1 : ℤ) : K) - ((-1 : ℤ) : K) • B) +
        (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) =
        B - (2 : K) • (ph : MvPowerSeries Unit K) := by
      have e0 : (1 : K) + ((-1 : ℤ) : K) = 0 := by push_cast; ring
      have e1 : (((-1 : ℤ) : K)) = -1 := by push_cast; ring
      rw [e0, hq0, e1]
      module
    rwa [e] at h
  have hstep : ∀ m : ℤ, C.LG R ((q (((m + 1 : ℤ)) : K) -
      ((((m + 1 : ℤ)) : K) * (((m + 1 : ℤ)) : K)) • (ph : MvPowerSeries Unit K)) -
      (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K))) := by
    intro m
    have h := C.Calc.lg_add (hE m) (C.lGBinom K R Unit (m : K) (C.intBinomScalar K R m) _ hG)
    have e1 : (((m + 1 : ℤ)) : K) = 1 + (m : K) := by push_cast; ring
    rw [e1]
    convert h using 1
    module
  have main : ∀ m : ℤ, C.LG R (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K)) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      have : q ((0 : ℤ) : K) - (((0 : ℤ) : K) * ((0 : ℤ) : K)) • (ph : MvPowerSeries Unit K) = 0 := by
        rw [Int.cast_zero, hq0]; simp
      rw [this]; exact C.Calc.lg_zero
    | succ i ih =>
      have h := C.Calc.lg_add (hstep i) ih
      rwa [sub_add_cancel] at h
    | pred i ih =>
      have h := C.Calc.lg_add (C.Calc.lg_neg (hstep (-(i : ℤ) - 1))) ih
      rw [sub_add_cancel] at h
      convert h using 1
      abel
  have h := main n
  unfold C.PhNormAt C.Cong
  rw [C.Pts.mulBy_eq_fmul]
  exact h

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerIdeal
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem xsOf_filter (L : PeriodPair) (α β : ℂ) (hα : MulStable L α) (hβ : MulStable L β) (T T' : Finset ℂ)
    (hT : IsHalfReps L α T) (hT' : IsHalfReps L β T') :
    xsOf L (T.filter (fun P => β * P ∈ L.lattice)) = xsOf L T ∩ xsOf L T' := by
  ext x
  simp only [xsOf, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨P, ⟨hP, hβP⟩, rfl⟩
    refine ⟨⟨P, hP, rfl⟩, ?_⟩
    have := (hT'.mem_xsOf hβ (hT.notMem hP)).2 hβP
    simpa only [xsOf, Finset.mem_image] using this
  · rintro ⟨⟨P, hP, rfl⟩, h2⟩
    refine ⟨P, ⟨hP, ?_⟩, rfl⟩
    refine (hT'.mem_xsOf hβ (hT.notMem hP)).1 ?_
    simpa only [xsOf, Finset.mem_image] using h2

theorem natCast_mulStable (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by
  intro ω hω
  have := L.lattice.nsmul_mem hω n
  simpa [nsmul_eq_mul] using this

theorem kerProd_ideal (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L)
    (l : ℕ) (hl : l.Prime) (h3 : 3 ∣ d) (hd3 : d ≠ 3) : KerProdAt d L l 3 := by
  obtain ⟨p, r, hp, hb, -, hp3, hr, hdiv, hndiv⟩ := prime_choice d (l + 3) hsq hd4 h3 hd3
  obtain ⟨M, hM⟩ := hdiv
  have hpM : ¬ p ∣ M := by
    rintro ⟨c, rfl⟩
    exact hndiv ⟨c, by rw [hM]; ring⟩
  have hp2 : p ≠ 2 := by omega
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set β : ℂ := (r : ℂ) + redSqD d with hβdef
  have hβs : MulStable L β := sqD_mulStable d L hCM r
  have hβN : Complex.normSq β = ((p * M : ℕ) : ℝ) := by rw [← hM]; exact sqD_normSq d r
  have hβN' : Complex.normSq β = ((r ^ 2 + d : ℕ) : ℝ) := sqD_normSq d r
  have hps : MulStable L (p : ℂ) := natCast_mulStable L p
  have hpN : Complex.normSq (p : ℂ) = ((p * p : ℕ) : ℝ) := by
    rw [Complex.normSq_natCast]; push_cast; ring
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hdodd : Odd d := by rw [Nat.odd_iff]; omega
  have hNodd : Odd (r ^ 2 + d) := (hr.pow_of_ne_zero two_ne_zero).add_odd hdodd
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hβN'
    have : (r ^ 2 + d : ℕ) = 0 := by exact_mod_cast hβN'.symm
    omega
  obtain ⟨T, hT⟩ := halfReps_exist L (p : ℂ) hp0 hps (p * p) hpN (hpodd.mul hpodd)
  obtain ⟨T', hT'⟩ := halfReps_exist L β hβ0 hβs (r ^ 2 + d) hβN' hNodd
  have hcard := card_G L β hβs p M hp hp2 hβN hpM T hT
  refine ⟨p, T.filter (fun P => β * P ∈ L.lattice), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.dvd_prime hp).1 h with h1 | h1
    · exact hl.one_lt.ne' h1
    · omega
  · omega
  · omega
  · intro z hz
    have hz' := (Finset.mem_filter.1 hz).1
    exact ⟨hT.notMem hz', (hT.1 z hz').1⟩
  · intro k h2 h3' hω
    have hpk : (p : ℂ) ∈ k := natCast_mem k p
    have hβk : β ∈ k := by
      rw [hβdef, redSqD]
      exact k.add_mem (natCast_mem k r)
        (k.sub_mem (k.mul_mem (by simp) hω) k.one_mem)
    have h1 := kerPoly_mem L (p : ℂ) T hp0 hps hT k h2 h3' hpk
    have h1' := kerPoly_mem L β T' hβ0 hβs hT' k h2 h3' hβk
    have h4 := prod_mem_of_rootPoly k _ (rootPoly_inter_mem k _ _ h1 h1')
    rw [← xsOf_filter L (p : ℂ) β hps hβs T T' hT hT', xsOf, Finset.prod_image] at h4
    · exact h4
    · intro a ha b hb hab
      exact hT.injOn (Finset.mem_coe.2 (Finset.mem_filter.1 ha).1)
        (Finset.mem_coe.2 (Finset.mem_filter.1 hb).1) hab

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ShortWIntModel
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem lgS_eq_logSer {K : Type} [Field K] [CharZero K] (g2 g3 : K) :
    lgS g2 g3 = Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3) := by
  obtain ⟨h0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec K (Formalism.L2.Th1.A.shortW g2 g3)
  obtain ⟨-, -, -, h4, -⟩ := Formalism.L2.Th1.A.expSpec K (Formalism.L2.Th1.A.shortW g2 g3)
  refine (lgS_unique g2 g3 _ h0 ?_).symm
  rw [Formalism.L2.Th1.A.uSerEq K g2 g3]
  exact h4

theorem shortW_intModel {K : Type} [NormedField K] (g2 g3 : K)
    (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1) (h : ‖(2 : K)‖ = 1) :
    Formalism.L2.Th1.A.IntModel (Formalism.L2.Th1.A.shortW g2 g3) := by
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Formalism.L2.Th1.A.shortW, h4, h2, h3]

theorem curve_law {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K)
    (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1) (h : ‖(2 : K)‖ = 1) :
    LawD (lgS g2 g3) (Formalism.L2.Th1.A.fgl (Formalism.L2.Th1.A.shortW g2 g3)) := by
  rw [lgS_eq_logSer]
  obtain ⟨⟨hF0, hFi, hl0, hl1, -⟩, -, -⟩ :=
    Formalism.L2.Th1.A.bridgeLaw K (Formalism.L2.Th1.A.shortW g2 g3) (shortW_intModel g2 g3 h2 h3 h)
  exact ⟨hl0, hl1, hF0, hFi, (Formalism.L2.Th1.A.fglLog K (Formalism.L2.Th1.A.shortW g2 g3)).1⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

