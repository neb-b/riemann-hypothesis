module

public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem t2 : InjectivityOnLayerOfPower := by
  intro R _ Xm _ _ g k z α h hz
  have e1 : (g - 1) * (∑ j ∈ Finset.range k, g ^ j) = g ^ k - 1 := mul_geom_sum g k
  have e2 : (∑ j ∈ Finset.range k, g ^ j) * (g - 1) = g ^ k - 1 := geom_sum_mul g k
  constructor
  · intro x hx
    have h1 : (g ^ k - 1) x = 0 := by
      rw [← e2, Module.End.mul_apply]
      simp [hx]
    have h2 : z • α x = 0 := by
      rw [← h x]; simpa using h1
    exact α.map_eq_zero_iff.1 (hz _ h2)
  · intro x
    refine ⟨(∑ j ∈ Finset.range k, g ^ j) (α.symm x), ?_⟩
    have h1 : (g ^ k - 1) (α.symm x) = z • x := by
      have := h (α.symm x)
      simpa using this
    rw [← h1, ← e1, Module.End.mul_apply]
    simp

section padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma tf_pow {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    (htf : ∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) (k : ℕ) (x : V)
    (h : ((ℓ : ℤ_[ℓ]) ^ k) • x = 0) : x = 0 := by
  induction k with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply htf
    rw [smul_smul, ← pow_succ']
    exact h

lemma poly_split (R : Polynomial ℤ_[ℓ]) : ∃ R' : Polynomial ℤ_[ℓ], R = C (R.eval 1) + (X - 1) * R' := by
  obtain ⟨R', hR'⟩ : (X - C (1 : ℤ_[ℓ])) ∣ R - C (R.eval 1) := X_sub_C_dvd_sub_C_eval
  refine ⟨R', ?_⟩
  rw [map_one] at hR'
  rw [← hR']; ring

lemma aeval_split {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V)
    (R R' : Polynomial ℤ_[ℓ]) (h : R = C (R.eval 1) + (X - 1) * R') (x : V) :
    aeval g R x = (R.eval 1) • x + (g (aeval g R' x) - aeval g R' x) := by
  conv_lhs => rw [h]
  simp [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one]

lemma aeval_split' {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V)
    (R R' : Polynomial ℤ_[ℓ]) (h : R = C (R.eval 1) + (X - 1) * R') (x : V) :
    aeval g R x = (R.eval 1) • x + aeval g R' (g x - x) := by
  conv_lhs => rw [h, mul_comm]
  simp [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one]

end padic

theorem eigen : StatEigen := by
  intro ℓ _ w m hm h2 hw U i V _ _ g htf hkill k x x' hx
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  have h1 : aeval g (Rpoly ℓ w U i) (g x' - x') = 0 := by
    have h0 : aeval g ((X - 1) * Rpoly ℓ w U i) x' = 0 := by rw [hkill]; rfl
    rw [mul_comm, map_mul, Module.End.mul_apply] at h0
    simpa using h0
  have h3 : aeval g (Rpoly ℓ w U i) x = 0 := by
    apply tf_pow htf k
    rw [← map_smul, hx, h1]
  obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
  have h4 := aeval_split g _ R' hR' x
  rw [h3] at h4
  have hu := PadicInt.unitCoeff_spec hne
  rw [hval] at hu
  set c := PadicInt.unitCoeff hne with hc
  refine ⟨-(((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • aeval g R' x), ?_⟩
  have h5 : ((Rpoly ℓ w U i).eval 1) • x = -(g (aeval g R' x) - aeval g R' x) :=
    eq_neg_of_add_eq_zero_left h4.symm
  have h6 : ((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x
      = ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((Rpoly ℓ w U i).eval 1) • x) := by
    rw [smul_smul]
    conv_rhs => rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [h6, h5]
  simp only [map_neg, map_smul, smul_neg, smul_sub]
  abel

theorem htpoly : StatHTpoly := by
  intro ℓ _ w U i
  by_cases hi : i ∈ U
  · refine ⟨?_, fun h => absurd hi h⟩
    have : HTpoly ℓ w U i = (X - 1) * Rpoly ℓ w U i := by
      unfold HTpoly Rpoly
      rw [← Finset.mul_prod_erase U _ hi]
      simp
    rw [this]
  · have : HTpoly ℓ w U i = Rpoly ℓ w U i := by
      unfold HTpoly Rpoly
      rw [Finset.erase_eq_of_notMem hi]
    exact ⟨this ▸ dvd_mul_left _ _, fun _ => this⟩

theorem eigenInj : StatEigenInj := by
  intro ℓ _ w m hm h2 hw U i hi V _ _ g htf hkill x hx
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  rw [(htpoly ℓ w U i).2 hi] at hkill
  obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
  have h4 := aeval_split' g _ R' hR' x
  rw [hkill, hx, sub_self, map_zero, add_zero] at h4
  have hu := PadicInt.unitCoeff_spec hne
  rw [hval] at hu
  apply tf_pow htf (rI ℓ m U i)
  have h5 : ((PadicInt.unitCoeff hne : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x) = 0 := by
    rw [smul_smul, ← hu]; exact h4.symm
  have h6 := congrArg (fun y => (((PadicInt.unitCoeff hne)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • y) h5
  simpa [smul_smul] using h6

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
