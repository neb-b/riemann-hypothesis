module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CycZConjGal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base

namespace UpperTheory.V.Kum

section Lim

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

omit [IsAlgClosure F Ω] in
theorem levU_anti (U : Subgroup (G F Ω)) {m n : ℕ} (h : m ≤ n) : levU l U n ≤ levU l U m := by
  intro g hg
  simp only [levU, Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.mem_princ] at hg ⊢
  exact ⟨hg.1, (pow_dvd_pow _ h).trans hg.2⟩


theorem galOf_Fn (n : ℕ) : galOf F (Fn F Ω l n) Ω = Un F Ω l n := by
  have := (fnCyc F Ω l n).1
  rw [galOfCyc F Ω l n F (Fn F Ω l n), galOf_self]


private theorem princ_smul_eq_self_of_pow_smul_eq_zero {k : ℕ} {x : QZ l} (hx : l ^ k • x = 0) {w : ℤ_[l]ˣ}
    (hw : w ∈ KStar.TotallyRealRoots.princ l k) : (w : ℤ_[l]) • x = x := by
  rw [KStar.TotallyRealRoots.mem_princ] at hw
  obtain ⟨c, hc⟩ := hw
  have h1 : ((w : ℤ_[l]) - 1) • x = 0 := by
    rw [hc, mul_comm ((l : ℤ_[l]) ^ k) c, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem locConst_qzG (e : ℤ) (m : QZ l) : IsLocallyConstant fun g => qzG F Ω l e g m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 m
  have hc : Continuous fun g => cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ :=
    (continuous_cycZ F Ω l).mul continuous_const
  have hmem : ∀ᶠ g in nhds g0, cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ ∈ KStar.TotallyRealRoots.princ l k := by
    apply hc.continuousAt.preimage_mem_nhds
    apply (KStar.TotallyRealRoots.isOpen_princ k).mem_nhds
    simp only [mul_inv_cancel]
    exact (KStar.TotallyRealRoots.princ l k).one_mem
  filter_upwards [hmem] with g hg
  show ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m = ((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m
  have hw : (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) ∈ KStar.TotallyRealRoots.princ l k := zpow_mem hg _
  have hx : l ^ k • (((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m) = 0 := by
    rw [smul_comm, hk, smul_zero]
  have key : cycZ F Ω l g ^ (-e) =
      (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) * cycZ F Ω l g0 ^ (-e) := by
    rw [← mul_zpow, inv_mul_cancel_right]
  rw [key, Units.val_mul, mul_smul, princ_smul_eq_self_of_pow_smul_eq_zero hx hw]

variable [IsCMField F]

end Lim

end UpperTheory.V.Kum

end
