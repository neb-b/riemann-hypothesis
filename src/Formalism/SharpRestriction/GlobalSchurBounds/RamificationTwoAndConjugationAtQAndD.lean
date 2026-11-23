module

public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0005
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
public import Development.AutomorphicArithmetic.ConductorsKronecker.Bundle0001
public import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
public import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
public import Development.AutomorphicArithmetic.ConductorsKronecker.InertiaD
public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.ConductorsKronecker.IsInertIff
public import Development.AutomorphicArithmetic.PrimitiveCosets.Bundle0002
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open DirichletCharacter Filter

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset
open scoped Pointwise ComplexConjugate

open Classical

abbrev MM (D : D7) : Type := D5.E0 × D.R.A

def AD (D : D7) : characterSumData.ArithData D.R.A := UpperTheory.Comparison₂.arith D.host.toHostRaw

def tE (D : D7) : D.R.GG ≃ MM D :=
  Equiv.ofBijective (fun g => (UpperTheory.Comparison₂.toE D.R.toFrame g).toAdd)
    (Multiplicative.toAdd.bijective.comp (UpperTheory.Comparison₂.toE_bij D.R.toFrame).1)

variable (D : D7)

theorem tE_mul (g g' : D.R.GG) : tE D (g * g') = tE D g + tE D g' := by
  show (UpperTheory.Comparison₂.toE D.R.toFrame (g * g')).toAdd = (UpperTheory.Comparison₂.toE D.R.toFrame g).toAdd + (UpperTheory.Comparison₂.toE D.R.toFrame g').toAdd
  rw [map_mul, toAdd_mul]
theorem tE_one : tE D 1 = 0 := by
  show (UpperTheory.Comparison₂.toE D.R.toFrame 1).toAdd = 0
  rw [map_one, toAdd_one]
theorem tE_pow (g : D.R.GG) (i : ℕ) : tE D (g ^ i) = i • tE D g := by
  show (UpperTheory.Comparison₂.toE D.R.toFrame (g ^ i)).toAdd = i • (UpperTheory.Comparison₂.toE D.R.toFrame g).toAdd
  rw [map_pow, toAdd_pow]

def cOf (φ : AddChar (MM D) ℂ) : Chr D :=
  MonoidHom.toHomUnits
    { toFun := fun g => φ (tE D g)
      map_one' := by simp [tE_one]
      map_mul' := fun g g' => by simp [tE_mul, AddChar.map_add_eq_mul] }

theorem exists_prime_over (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 D.host.E), P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI hp' : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 D.host.E)
    (Ideal.span {(p : ℤ)}) ⊥ (Ideal.comap_bot_le_of_injective _ (RingHom.injective_int _))
  exact ⟨Q, hQ, ⟨hc.symm⟩⟩

theorem fieldFacts (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
    (hL : P.LiesOver (Ideal.span {(p : ℤ)})) (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    ((∀ x : 𝓞 D.host.E, σ • x - x ∈ P) ↔
      tE D (D.host.galE σ) ∈ (AD D).inertia p) ∧
    (IsArithFrobAt ℤ σ P ↔
      tE D (D.host.galE σ) - (AD D).frob p ∈ (AD D).inertia p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hL
  exact Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.fld D p P σ

theorem frob_spec (p : ℕ) (hp : p.Prime) :
    tE D (frob D p) - (AD D).frob p ∈ (AD D).inertia p := by
  obtain ⟨P, hP, hL⟩ := exists_prime_over D p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hL
  exact Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.frob_mem D p P

theorem unram_iff (p : ℕ) :
    Unram D p ↔ p.Prime ∧ ¬ p ∣ D.host.condN :=
  ⟨fun h => ⟨h.1, Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.not_dvd_condN_of_unram' D p h⟩,
    fun h => Formalism.MainNotions.GlobalTheoryTheory.ConductorDivisibility.jnt_unram D p h.1 h.2⟩

theorem inertia_unram {p : ℕ} (h : Unram D p) : (AD D).inertia p = ⊥ := by
  have hu := (LHost.unramified_spec D.host.condN p (Formalism.MainNotions.GlobalTheoryTheory.ConductorLiftingHypotheses.hostN_ne D) h.1
    ((unram_iff D p).mp h).2).1
  show Subgroup.toAddSubgroup' ((LHost.localUnits D.host.condN p).map (UpperTheory.Comparison₂.recH D.host.toHostRaw)) = ⊥
  rw [hu, Subgroup.map_bot]
  rfl

theorem frob_unram {p : ℕ} (h : Unram D p) : tE D (frob D p) = (AD D).frob p := by
  have h1 := frob_spec D p h.1
  rw [inertia_unram D h, AddSubgroup.mem_bot, sub_eq_zero] at h1
  exact h1

def ell (φ : AddChar (MM D) ℂ) : ℂ := Lp D (cOf D φ)

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset
open scoped Pointwise ComplexConjugate

open Classical

variable (D : D7)

def tH (t : HH D) : D.R.A := t

theorem inPhi_iff (g : D.R.GG) : D5.InPhi (tE D g) ↔ g ∈ D.R.Psi :=
  LHost.sgn2_toAdd_eq_zero_iff g.1.2

theorem inPhi_symm_iff (x : MM D) : (tE D).symm x ∈ D.R.Psi ↔ D5.InPhi x := by
  rw [← inPhi_iff, Equiv.apply_symm_apply]

theorem tE_cc : tE D (D.R.cc) = D5.cconj := rfl
theorem top_place_of_first_tau (t : HH D) : tE D (D.R.tau1 t) = D5.topPl (tH D t) := rfl
theorem tE_iner : tE D (iner D) = characterSumData.sgc0 := rfl

theorem tE_rho (t : HH D) (g : D.R.GG) :
    tE D (rho D (D.R.tau1 t) g) = characterSumData.partner (tH D t) (tE D g) := by
  unfold rho characterSumData.partner
  rw [tE_mul, tE_mul, tE_cc, top_place_of_first_tau]

def wM (w : D.R.GG → ℝ) : MM D → ℝ := fun x => w ((tE D).symm x)

theorem wM_partner (w : D.R.GG → ℝ) (t : HH D) (g : D.R.GG) :
    wM D w (characterSumData.partner (tH D t) (tE D g)) = w (rho D (D.R.tau1 t) g) := by
  unfold wM
  rw [← tE_rho, Equiv.symm_apply_apply]

theorem rho_mem (t : HH D) {g : D.R.GG} (hg : g ∉ D.R.Psi) :
    rho D (D.R.tau1 t) g ∈ D.R.Psi := by
  rw [← inPhi_iff, tE_rho]
  exact characterSumData.partner_inPhi _ (fun h => hg ((inPhi_iff D g).1 h))

theorem isInert_iff (p : ℕ) : characterSumData.IsInert (AD D) p ↔ InertK D p := by
  refine (UpperTheory.GL.isInert_iff D.host.toHostAx p).trans ?_
  unfold InertK Host.cls
  refine and_congr_right fun hp => ?_
  rw [primeClass_eq_signal_iff' hp, primeClass_eq_inert_iff_symbols hp]
  constructor
  · rintro ⟨hN, hJ⟩
    rcases D.host.psAt_eq_one_or (hp.coprime_iff_not_dvd.2 hN) with h | h
    · exact Or.inl ⟨hN, hJ, h⟩
    · exact Or.inr ⟨hN, hJ, h⟩
  · rintro (⟨hN, hJ, -⟩ | ⟨hN, hJ, -⟩) <;> exact ⟨hN, hJ⟩

theorem inertK_unram {p : ℕ} (h : InertK D p) : Unram D p := by
  obtain ⟨hp, hN, -⟩ := (UpperTheory.GL.isInert_iff D.host.toHostAx p).1 ((isInert_iff D p).2 h)
  exact (unram_iff D p).2 ⟨hp, hN⟩

theorem term_zero {a W : ℝ} {N M : ℕ} (hW : 0 < W) (hN : a / W ≤ N) (hM : N < M) :
    max (a / (M : ℝ) - W) 0 = 0 := by
  have h2 : (N : ℝ) < M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hM0 : (0 : ℝ) < M := lt_of_le_of_lt hN0 h2
  have h1 : a ≤ N * W := (div_le_iff₀ hW).mp hN
  have h3 : a / M ≤ W := by
    rw [div_le_iff₀ hM0]
    nlinarith
  exact max_eq_right (by linarith)

theorem gD_spec (i : ℕ) :
    tE D (gD D i) - i • (AD D).frob (AD D).d ∈ (AD D).inertia (AD D).d ∧ ¬ D5.InPhi (tE D (gD D i)) := by
  have h0 : tE D (frob D D.host.d ^ i) - i • (AD D).frob (AD D).d ∈ (AD D).inertia (AD D).d := by
    rw [tE_pow, ← smul_sub]
    exact AddSubgroup.nsmul_mem _ (frob_spec D D.host.d D.host.hyp.2.1) i
  have hs : characterSumData.sgc0 ∈ (AD D).inertia (AD D).d :=
    ((UpperTheory.GL.inertia_d D.host.toHostAx).1 _).2 (Or.inr rfl)
  have hin : iner D ∉ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff]; show (sgc0).2 ≠ 1; decide
  unfold gD
  by_cases hm : frob D D.host.d ^ i ∈ D.R.Psi
  · rw [if_neg (by tauto)]
    constructor
    · rw [tE_mul, tE_iner, add_sub_right_comm]
      exact AddSubgroup.add_mem _ h0 hs
    · rw [inPhi_iff, Subgroup.mul_mem_cancel_left _ hm]
      exact hin
  · rw [if_pos hm]
    exact ⟨h0, by rw [inPhi_iff]; exact hm⟩

section vonMangoldtClassSum
variable (a : ℝ) (w : D.R.GG → ℝ) (hw : ∀ ρ ∈ D.R.Psi, 0 < w ρ) (N : ℕ)
  (hN : ∀ ρ ∈ D.R.Psi, a / w ρ ≤ N) (t : HH D)
include hw hN

theorem primePowerSum_eq_local {p : ℕ} (hp : InertK D p) :
    askP D a w (D.R.tau1 t) p = characterSumData.askP (AD D) N a (tH D t) (wM D w) p := by
  have hU := inertK_unram D hp
  have hfr := frob_unram D hU
  unfold askP characterSumData.askP
  rw [tsum_eq_sum (s := Icc 1 N), Finset.sum_filter]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi1 := (Finset.mem_Icc.1 hi).1
    have e1 : i • (AD D).frob p = tE D (frob D p ^ i) := by rw [tE_pow, hfr]
    rw [e1, wM_partner]
    by_cases hm : frob D p ^ i ∈ D.R.Psi
    · rw [if_neg (by tauto), if_neg (by rw [inPhi_iff]; tauto)]
    · rw [if_pos ⟨hi1, hm⟩, if_pos (by rw [inPhi_iff]; exact hm)]
  · intro i hi
    by_cases hc : 1 ≤ i ∧ frob D p ^ i ∉ D.R.Psi
    · rw [if_pos hc]
      have hiN : N < i := by
        by_contra hcon
        exact hi (Finset.mem_Icc.2 ⟨hc.1, by omega⟩)
      have hpi : N < p ^ i := hiN.trans (Nat.lt_pow_self hp.1.one_lt)
      have := term_zero (a := a) (hw _ (rho_mem D t hc.2)) (hN _ (rho_mem D t hc.2)) hpi
      rwa [Nat.cast_pow] at this
    · rw [if_neg hc]

theorem primePowerSum_eq_zero_of_cutoff_lt {p : ℕ} (hpN : N < p) :
    characterSumData.askP (AD D) N a (tH D t) (wM D w) p = 0 := by
  unfold characterSumData.askP
  refine Finset.sum_eq_zero (fun i hi => ?_)
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  have hi1' := (Finset.mem_Icc.1 hi1).1
  have hpi : N < p ^ i := lt_of_lt_of_le hpN (Nat.le_self_pow (by omega) p)
  have hρ : (tE D).symm (characterSumData.partner (tH D t) (i • (AD D).frob p)) ∈ D.R.Psi := by
    rw [inPhi_symm_iff]; exact characterSumData.partner_inPhi _ hi2
  have := term_zero (a := a) (hw _ hρ) (hN _ hρ) hpi
  rwa [Nat.cast_pow] at this

theorem askD_eq :
    askD D a w (D.R.tau1 t) = characterSumData.askD (AD D) N a (tH D t) (wM D w) := by
  unfold askD characterSumData.askD
  rw [tsum_eq_sum (s := Icc 1 N)]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi1 := (Finset.mem_Icc.1 hi).1
    rw [if_pos hi1]
    obtain ⟨g0, -, huniq⟩ := (UpperTheory.GL.inertia_d D.host.toHostAx).2.2 i
    have hg := gD_spec D i
    rw [Finset.sum_eq_single_of_mem (tE D (gD D i)) (by simp only [mem_filter, mem_univ, true_and]; exact hg)]
    · rw [wM_partner]; rfl
    · intro b hb hne
      simp only [mem_filter, mem_univ, true_and] at hb
      exact absurd ((huniq b hb).trans (huniq _ hg).symm) hne
  · intro i hi
    by_cases hc : 1 ≤ i
    · rw [if_pos hc]
      have hiN : N < i := by
        by_contra hcon
        exact hi (Finset.mem_Icc.2 ⟨hc, by omega⟩)
      have hpi : N < D.host.d ^ i := hiN.trans (Nat.lt_pow_self D.host.hyp.2.1.one_lt)
      have hg : gD D i ∉ D.R.Psi := fun h => (gD_spec D i).2 ((inPhi_iff D _).2 h)
      have := term_zero (a := a) (hw _ (rho_mem D t hg)) (hN _ (rho_mem D t hg)) hpi
      rwa [Nat.cast_pow] at this
    · rw [if_neg hc]

theorem ASK_eq :
    ASKjt D a w (D.R.tau1 t) = characterSumData.ASK (AD D) N a (tH D t) (wM D w) := by
  unfold ASKjt characterSumData.ASK
  rw [askD_eq D a w hw N hN t]
  congr 1
  rw [tsum_eq_sum (s := range (N + 1)), Finset.sum_filter]
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : InertK D p
    · rw [if_pos hp, if_pos ((isInert_iff D p).2 hp), primePowerSum_eq_local D a w hw N hN t hp]
    · rw [if_neg hp, if_neg (fun h => hp ((isInert_iff D p).1 h))]
  · intro p hp
    by_cases hI : InertK D p
    · rw [if_pos hI, primePowerSum_eq_local D a w hw N hN t hI, primePowerSum_eq_zero_of_cutoff_lt D a w hw N hN t (by
        simpa using hp), mul_zero]
    · rw [if_neg hI]

end vonMangoldtClassSum

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset

variable (D : D7) (s : Scale)

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion.Br

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters Finset
open scoped Pointwise ComplexConjugate

open Classical

variable (D : D7)

def tHe : HH D ≃ D.R.A :=
  Equiv.ofBijective (tH D) Function.bijective_id

theorem tHe_apply (t : HH D) : tHe D t = tH D t := rfl

def TTm : Finset D.R.A := D.host.TT.map (tHe D).toEmbedding

theorem sum_lifts (m : ℕ) (f : ℕ → ℝ) : ∑ j : Fin m, f (j + 1) = ∑ j ∈ Icc 1 m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [Finset.sum_Icc_succ_top (by omega), ih]

end Formalism.MainNotions.ZetaZeroFreeRegion.Br

end

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Formalism.LFunctionChainParameters

end Formalism.MainNotions.ZetaZeroFreeRegion

end
