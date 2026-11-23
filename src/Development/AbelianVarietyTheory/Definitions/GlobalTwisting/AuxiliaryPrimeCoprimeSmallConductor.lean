module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109

@[expose] public section

noncomputable section

namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem auxiliaryPrime_coprime_smallConductor {R : Ranks} (H : Host R) : Nat.Coprime (q0H H) H.QS := by
  have h1 : Nat.Coprime (q0H H) (H.QS * H.q * H.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, mod_cond H, Nat.gcd_one_left]
  exact h1.coprime_dvd_right ⟨H.q * H.d, by ring⟩

def relevel {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (q0 : ℕ)
    (hq : Nat.Coprime q0 H.QS := by exact GlobalTheory.EX.DC.auxiliaryPrime_coprime_smallConductor _) : Host R :=
  { H with
    levelPrimes := {H.g 0, H.g 1, H.pde, H.pde', q0}
    g_level := by intro i; fin_cases i <;> simp
    pde_level := by simp
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h | h <;> rw [h]
      · exact H.level_coprimeS _ (H.g_level 0)
      · exact H.level_coprimeS _ (H.g_level 1)
      · exact H.level_coprimeS _ H.pde_level.1
      · exact H.level_coprimeS _ H.pde_level.2
      · exact hq }

theorem firstTypePrime_lt_rowPrime (D : D7) (u : D.what₂.Word) : D.host.g 0 < (D.mem u).A.T := by
  have h := (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd D.host.d _ _ (by have := D.host.hyp.2.2.2.1; omega)
    ((GlobalTheory.Mem.An.normOne_iff_host D.R D.host _ _).2 (D.T_norm u))).1
  have h' : (D.mem u).A.T ≡ 1 [MOD D.host.g 0] := Nat.ModEq.of_dvd (Dvd.dvd.mul_left ⟨D.host.g 0 * D.host.g 1 ^ 2, by ring⟩ _) h
  have h1 := (D.mem u).A.T_prime.one_lt
  have := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' h1.le).1 h'.symm)
  omega

end GlobalTheory.EX.DC

end
