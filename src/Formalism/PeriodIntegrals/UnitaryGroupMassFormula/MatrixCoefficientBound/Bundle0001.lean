module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GamOneReal
section
open Finset

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

theorem gam_one_real {F : Type} [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) = (((Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) : ℝ) : ℂ) := by
  rw [gam_one]; push_cast; rfl

theorem eigBound_of (hP : PlaceBound) (hJ : JointEig) (hF : ProdFormula) : EigBound := by
  intro hC hR ι _ Fq _ _ k ψ hψ hq V _ _ _ π w μ hw he
  obtain ⟨W, hW0, hWinv, hWeig, hv⟩ := hJ ι Fq k ψ V π w μ hw he
  choose μv hμv using hv
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hpl : ∀ v, ∃ c : ℝ, μv v = gam (ψ v) (1 : GL (Fin k) (Fq v)) * (c : ℂ) ∧ 0 ≤ c ∧
      c ≤ 1 + 3 / (Fintype.card (Fq v) : ℝ) := by
    intro v
    refine hP hC hR (Fq v) k (ψ v) (hψ v) (hq v) V
      (π.comp (MonoidHom.mulSingle (fun v => GL (Fin k) (Fq v)) v)) W (μv v) hW0 ?_ ?_
    · intro g y hy; exact hWinv _ y hy
    · intro y hy
      rw [← hμv v y hy]
      simp [repGam, placeOp, LinearMap.sum_apply]
  choose c hc using hpl
  have h1 : totOp ψ π x = (∏ v, μv v) • x := hF ι Fq k ψ V π μv x (fun v => hμv v x hxW)
  have h2 : μ = ∏ v, μv v := by
    have h3 := hWeig x hxW
    rw [h1] at h3
    exact (smul_left_injective ℂ hx0 h3).symm
  set g : ι → ℝ := fun v => (Fintype.card (GL (Fin k) (Fq v)) : ℝ) / (cardU (Fq v) k : ℝ) with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hG1 : gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v)) = ((∏ v, g v : ℝ) : ℂ) := by
    unfold gamProd
    push_cast
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Pi.one_apply, gam_one_real]
  refine ⟨(∏ v, g v) * ∏ v, c v, ?_, ?_, ?_⟩
  · rw [h2]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hc v).1, gam_one_real]
  · exact mul_nonneg (Finset.prod_nonneg fun v _ => hg0 v) (Finset.prod_nonneg fun v _ => (hc v).2.1)
  · rw [hG1, Complex.ofReal_re, mul_comm (∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ)))]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun v _ => (hc v).2.1) (fun v _ => (hc v).2.2))
      (Finset.prod_nonneg fun v _ => hg0 v)

end PI.GGMatBoundW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GammaMatrixInverse
section
open Finset

open scoped ComplexConjugate

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic PI.GGConvScalarW

theorem addChar_inv_eq_conj {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (a : F) :
    (ψ₀ a)⁻¹ = conj (ψ₀ a) := by
  rw [← AddChar.map_neg_eq_inv, AddChar.map_neg_eq_conj]

theorem psiNat_inv {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiNat ψ₀ u⁻¹ = conj (psiNat ψ₀ u) := by
  unfold psiNat
  by_cases hu : IsUni k u
  · rw [if_pos (isUni_inv hu), if_pos hu]
    rw [eq_inv_of_mul_eq_one_left (psiU_inv_mul ψ₀ hu)]
    unfold psiU
    exact addChar_inv_eq_conj ψ₀ _
  · have hu' : ¬ IsUni k u⁻¹ := fun h => hu (by simpa using isUni_inv h)
    rw [if_neg hu', if_neg hu, map_zero]

end PI.GGMatBoundW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GgMatrixBoundOfLitOf
section
open Finset Matrix

open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

theorem ggMatrixBound_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hC : ConvScalar) (hR : GenericRatio) : GGMatrixBound := by
  intro ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd
  obtain ⟨hA, hAt⟩ := hM ι Fq k ψ X hfree d hd
  set A := LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) with hAdef
  have hherm : A.IsHermitian := hH ι Fq k ψ X
  have hspec := hS X A _ hherm (fun w μ hw hAw =>
    hE hC hR ι Fq k ψ hψ hq (X → ℂ) (permRep (∀ v, GL (Fin k) (Fq v)) X) w μ hw
      (by rw [← hAw, hAdef, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']))
  rw [hAt, hA]
  exact ⟨hspec.1.transpose, hspec.2⟩

theorem ggMatrixBoundOfLit_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hCL : ConvScalarOfLit) (hRB : GenericRatioOfBound) (hCU : CardUni) : GGMatrixBoundOfLit :=
  fun hGG hMB => ggMatrixBound_of hM hH hE hS (hCL hGG) (hRB hMB hCU)

end PI.GGMatBoundW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.ProdFormula
section
open Finset

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

section Prod

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

def beta (ψ : ∀ v, AddChar (Fq v) ℂ) (s : Finset ι) (x : ∀ v, GL (Fin k) (Fq v)) : ℂ :=
  if ∀ w, w ∉ s → x w = 1 then ∏ v ∈ s, gam (ψ v) (x v) else 0

theorem beta_insert (ψ : ∀ v, AddChar (Fq v) ℂ) {a : ι} {s : Finset ι} (ha : a ∉ s)
    (z : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ (insert a s) z =
      ∑ y : GL (Fin k) (Fq a), gam (ψ a) y * beta ψ s ((Pi.mulSingle a y)⁻¹ * z) := by
  have hz : ∀ w, ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = if w = a then 1 else z w := by
    intro w
    by_cases hw : w = a
    · subst hw
      simp
    · simp [hw, Pi.mulSingle_eq_of_ne hw]
  rw [Finset.sum_eq_single (z a)]
  · unfold beta
    have hcond : (∀ w, w ∉ insert a s → z w = 1) ↔
        (∀ w, w ∉ s → ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = 1) := by
      constructor
      · intro h w hw
        rw [hz]
        by_cases hwa : w = a
        · rw [if_pos hwa]
        · rw [if_neg hwa]
          exact h w (by simp [hwa, hw])
      · intro h w hw
        simp only [Finset.mem_insert, not_or] at hw
        have := h w hw.2
        rwa [hz, if_neg hw.1] at this
    have hprod : ∏ v ∈ s, gam (ψ v) (((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) v) =
        ∏ v ∈ s, gam (ψ v) (z v) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [hz, if_neg (fun (h : v = a) => ha (h ▸ hv))]
    by_cases h : ∀ w, w ∉ insert a s → z w = 1
    · rw [if_pos h, if_pos (hcond.mp h), hprod, Finset.prod_insert ha]
    · rw [if_neg h, if_neg (fun h' => h (hcond.mpr h')), mul_zero]
  · intro y _ hy
    unfold beta
    rw [if_neg, mul_zero]
    intro h
    apply hy
    have := h a ha
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at this
    exact inv_mul_eq_one.mp this
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem beta_univ (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ Finset.univ x = gamProd ψ x := by
  unfold beta gamProd
  rw [if_pos (fun w hw => absurd (Finset.mem_univ w) hw)]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem placeOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (v : ι) (w : V) : placeOp ψ π v w = ∑ y, gam (ψ v) y • π (Pi.mulSingle v y) w := by
  simp only [placeOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem totOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (w : V) : totOp ψ π w = ∑ x, gamProd ψ x • π x w := by
  simp only [totOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem sum_beta_empty (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (w : V) : ∑ x, beta ψ ∅ x • π x w = w := by
  rw [Finset.sum_eq_single 1]
  · unfold beta
    simp
  · intro b _ hb
    unfold beta
    rw [if_neg, zero_smul]
    intro h
    exact hb (funext fun v => h v (by simp))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_beta_insert (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    {a : ι} {s : Finset ι} (ha : a ∉ s) (w : V) :
    ∑ x, beta ψ (insert a s) x • π x w = placeOp ψ π a (∑ x, beta ψ s x • π x w) := by
  rw [placeOp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [beta_insert ψ ha, Finset.sum_smul, map_sum, map_smul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle a y)⁻¹) _ _ fun z => ?_
  simp only [Equiv.coe_mulLeft]
  have hπ : π (Pi.mulSingle a y) (π ((Pi.mulSingle a y)⁻¹ * z) w) = π z w := by
    have h2 := congrArg (fun f => f w) (map_mul π (Pi.mulSingle a y) ((Pi.mulSingle a y)⁻¹ * z))
    simp only [mul_inv_cancel_left] at h2
    exact h2.symm
  rw [hπ, mul_smul]

end Prod

theorem prod_formula' : ProdFormula := by
  intro ι _ Fq _ _ k ψ V _ _ π μ w hμ
  have key : ∀ s : Finset ι, ∑ x, beta ψ s x • π x w = (∏ v ∈ s, μ v) • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [sum_beta_empty, Finset.prod_empty, one_smul]
    | @insert a s ha ih =>
      rw [sum_beta_insert ψ π ha w, ih, map_smul, hμ, smul_smul, Finset.prod_insert ha, mul_comm]
  rw [totOp_apply, ← key Finset.univ]
  simp_rw [beta_univ]

end PI.GGMatBoundW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.SpectrumPositiveSemidefinite
section
open Matrix

open scoped ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

theorem spectrum_positive_semidefinite : SpecPSD := by
  intro X _ M c hM hev
  have gen : ∀ (A : Matrix X X ℂ) (hA : A.IsHermitian) (b : ℝ),
      (∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → A *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ b ≤ r) →
      ∀ j, b ≤ hA.eigenvalues j := by
    intro A hA b h j
    have hv := hA.mulVec_eigenvectorBasis j
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero j
    have key : ∀ v : X → ℂ, v ≠ 0 → A *ᵥ v = hA.eigenvalues j • v → b ≤ hA.eigenvalues j := by
      intro v hv0 hAv
      obtain ⟨r, hr, hbr⟩ := h v (hA.eigenvalues j : ℂ) hv0 (by rw [hAv]; ext i; simp)
      have hre : hA.eigenvalues j = r := by exact_mod_cast hr
      rw [hre]
      exact hbr
    exact key _ (fun h0 => hne (by ext i; simpa using congrFun h0 i)) hv
  have h1 : ((c : ℂ) • (1 : Matrix X X ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hN : ((c : ℂ) • (1 : Matrix X X ℂ) - M).IsHermitian := h1.sub hM
  have hNev : ∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → ((c : ℂ) • (1 : Matrix X X ℂ) - M) *ᵥ w = μ • w →
      ∃ r : ℝ, μ = r ∧ 0 ≤ r := by
    intro w μ hw h
    have hMw : M *ᵥ w = ((c : ℂ) - μ) • w := by
      rw [Matrix.sub_mulVec] at h
      first
        | rw [Matrix.smul_mulVec] at h
        | rw [Matrix.smul_mulVec_assoc] at h
        | simp only [Matrix.smul_mulVec_assoc] at h
      rw [Matrix.one_mulVec] at h
      rw [sub_smul, ← h]
      abel
    obtain ⟨r, hr, _, hrc⟩ := hev w ((c : ℂ) - μ) hw hMw
    refine ⟨c - r, ?_, by linarith⟩
    push_cast
    linear_combination -hr
  constructor
  · refine hM.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen M hM 0 ?_ j
    intro w μ hw h
    obtain ⟨r, hr, h0, _⟩ := hev w μ hw h
    exact ⟨r, hr, h0⟩
  · exact hN.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen _ hN 0 hNev j

end PI.GGMatBoundW
end
end

