module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdjQuot

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

noncomputable section

namespace UpperTheory.V.Lit.KT

open UpperHalfPlane ModularForm
open scoped Manifold

private structure Good (H : Subgroup SL(2, ℤ)) (k : ℤ) (F : ℍ → ℂ) : Prop where
  hol : MDiff F
  bd : ∃ C : ℝ, ∀ z, ‖petersson k F F z‖ ≤ C
  inv : ∀ γ ∈ H, F ∣[k] γ = F

variable {H : Subgroup SL(2, ℤ)} {k : ℤ} {F G : ℍ → ℂ}

private theorem Good.cont (hF : Good H k F) (hG : Good H k G) : Continuous (petersson k F G) :=
  petersson_continuous k hF.hol.continuous hG.hol.continuous

private theorem Good.pbd (hF : Good H k F) (hG : Good H k G) : ∃ C : ℝ, ∀ z, ‖petersson k F G z‖ ≤ C := by
  obtain ⟨A, hA⟩ := hF.bd
  obtain ⟨B, hB⟩ := hG.bd
  refine ⟨A + B, fun z => le_trans ?_ (add_le_add (hA z) (hB z))⟩
  simp only [petersson, norm_mul, Complex.norm_conj]
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  nlinarith [sq_nonneg (‖F z‖ - ‖G z‖), norm_nonneg (F z), norm_nonneg (G z)]

private theorem Good.pinv (hF : Good H k F) (hG : Good H k G) : ∀ γ ∈ H, ∀ z, petersson k F G (γ • z) = petersson k F G z :=
  fun γ hγ z => by rw [← petersson_slash_SL, hF.inv γ hγ, hG.inv γ hγ]

private theorem Good.slash {K : Subgroup SL(2, ℤ)} (hF : Good K k F) (α : GL (Fin 2) ℝ) (h : H ≤ conjGL K α) :
    Good H k (F ∣[k] α) := by
  obtain ⟨A, hA⟩ := hF.bd
  refine ⟨hF.hol.slash k α, ⟨‖((|α.det.val| : ℝ) : ℂ) ^ (k - 2)‖ * A, fun z => ?_⟩, fun γ hγ => ?_⟩
  · rw [petersson_slash, norm_mul, norm_σ]
    exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)
  · obtain ⟨y, hy, e⟩ := mem_conjGL.1 (h hγ)
    have e' : α * (γ : GL (Fin 2) ℝ) = (y : GL (Fin 2) ℝ) * α := by rw [e]; group
    rw [SL_slash, ← SlashAction.slash_mul, e', SlashAction.slash_mul, ← SL_slash, hF.inv y hy]

private theorem le_conj [hN : H.Normal] (γ : SL(2, ℤ)) : H ≤ conjGL H (γ : GL (Fin 2) ℝ) := fun x hx =>
  mem_conjGL.2 ⟨_, hN.conj_mem x hx γ, by simp⟩

private theorem Good.slashSL [H.Normal] (hF : Good H k F) (γ : SL(2, ℤ)) : Good H k (F ∣[k] γ) :=
  hF.slash _ (le_conj γ)

private theorem B_slash [H.FiniteIndex] {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val) (h1 : (conjGL H α).FiniteIndex)
    (h2 : (conjGL H α⁻¹).FiniteIndex) (hF : Good H k F) (hG : Good H k G) (hF' : Good H k (F ∣[k] α))
    (hG' : Good H k (G ∣[k] α)) :
    quotInt H (petersson k (F ∣[k] α) (G ∣[k] α)) = (α.det.val : ℂ) ^ (k - 2) * quotInt H (petersson k F G) := by
  have e : ∀ z, petersson k (F ∣[k] α) (G ∣[k] α) z = (α.det.val : ℂ) ^ (k - 2) * petersson k F G (α • z) := fun z => by
    rw [petersson_slash, σ, if_pos hα, abs_of_pos hα]; rfl
  have h0 : (α.det.val : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hα.ne')
  obtain ⟨C, hC⟩ := hF.pbd hG
  rw [funext e, quotInt_mul, quotInt_conj H α h1 h2 (hF.cont hG) hC (hF.pinv hG) fun γ hγ z => ?_]
  refine mul_left_cancel₀ h0 ?_
  rw [← e, ← e, hF'.pinv hG' γ hγ]

private theorem B_slashSL [H.FiniteIndex] [H.Normal] (γ : SL(2, ℤ)) (hF : Good H k F) (hG : Good H k G) :
    quotInt H (petersson k (F ∣[k] γ) (G ∣[k] γ)) = quotInt H (petersson k F G) := by
  have hd : (γ : GL (Fin 2) ℝ).det.val = 1 := by simp
  have h2 : (conjGL H (γ : GL (Fin 2) ℝ)⁻¹).FiniteIndex := by
    have := Subgroup.finiteIndex_of_le (le_conj (H := H) γ⁻¹)
    rwa [map_inv, map_inv] at this
  have := B_slash (α := (γ : GL (Fin 2) ℝ)) (by rw [hd]; exact one_pos) (Subgroup.finiteIndex_of_le (le_conj γ)) h2 hF hG
    (hF.slashSL γ) (hG.slashSL γ)
  rw [hd, Complex.ofReal_one, one_zpow, one_mul] at this
  exact this

private theorem B_smul_left [H.FiniteIndex] (c : ℂ) :
    quotInt H (petersson k (c • F) G) = conj c * quotInt H (petersson k F G) := by
  rw [← quotInt_mul]; congr 1; funext z; simp [petersson]; ring

private theorem B_smul_right [H.FiniteIndex] (c : ℂ) :
    quotInt H (petersson k F (c • G)) = c * quotInt H (petersson k F G) := by
  rw [← quotInt_mul]; congr 1; funext z; simp [petersson]; ring

private theorem Good.smul (hF : Good H k F) (c : ℂ) : Good H k (c • F) := by
  obtain ⟨A, hA⟩ := hF.bd
  refine ⟨hF.hol.const_smul c, ⟨‖c‖ ^ 2 * A, fun z => ?_⟩, fun γ hγ => by rw [SL_smul_slash, hF.inv γ hγ]⟩
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hA z) (by positivity))
  simp [petersson]; ring

private theorem B_adj [H.FiniteIndex] {α β : GL (Fin 2) ℝ} {p : ℕ} (hp : 0 < p) (hβ : β.det.val = p)
    (h1 : (conjGL H β).FiniteIndex) (h2 : (conjGL H β⁻¹).FiniteIndex) (hF : Good H k F) (hG : Good H k G)
    (hF' : Good H k (F ∣[k] α)) (hG' : Good H k (G ∣[k] β)) (e : (F ∣[k] α) ∣[k] β = (p : ℂ) ^ (k - 2) • F) :
    quotInt H (petersson k F (G ∣[k] β)) = quotInt H (petersson k (F ∣[k] α) G) := by
  have h := B_slash (by rw [hβ]; exact_mod_cast hp) h1 h2 hF' hG (e ▸ hF.smul _) hG'
  rw [e, B_smul_left, hβ, map_zpow₀, map_natCast, Complex.ofReal_natCast] at h
  exact mul_left_cancel₀ (zpow_ne_zero _ (by exact_mod_cast hp.ne')) h

private def dg (m n : ℕ) (h : m * n ≠ 0) : GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℚ), 0; 0, (n : ℚ)]
    (by rw [Matrix.det_fin_two_of, mul_zero, sub_zero]; exact_mod_cast h)).map (Rat.castHom ℝ)

private theorem dg_val (m n : ℕ) (h : m * n ≠ 0) : (dg m n h).1 = !![(m : ℝ), 0; 0, (n : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

private theorem dg_det (m n : ℕ) (h : m * n ≠ 0) : (dg m n h).det.val = (m * n : ℕ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, dg_val]; simp

private theorem dg_fin (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (m n : ℕ) (h : m * n ≠ 0) :
    (conjGL H (dg m n h)).FiniteIndex := finiteIndex_conjGL_rat H _

private theorem dg_fin' (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (m n : ℕ) (h : m * n ≠ 0) :
    (conjGL H (dg m n h)⁻¹).FiniteIndex := by
  rw [dg, ← map_inv]; exact finiteIndex_conjGL_rat H _

private theorem dg_slash (m n : ℕ) (h : m * n ≠ 0) (k : ℤ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[k] dg m n h) z = ((m * n : ℕ) : ℂ) ^ (k - 1) * (n : ℂ) ^ (-k) * F (ofComplex (m * (z : ℂ) / n)) := by
  have hpos : 0 < (dg m n h).det.val := by rw [dg_det]; exact_mod_cast Nat.pos_of_ne_zero h
  rw [slash_apply, σ, if_pos hpos, dg_det, ← ofComplex_apply (dg m n h • z), coe_smul_of_det_pos hpos]
  simp [num, denom, dg_val]
  ring

private theorem dg_mul (m n : ℕ) (h : m * n ≠ 0) (h' : n * m ≠ 0) (k : ℤ) (F : ℍ → ℂ) :
    (F ∣[k] dg m n h) ∣[k] dg n m h' = ((m * n : ℕ) : ℂ) ^ (k - 2) • F := by
  have e : dg m n h * dg n m h' = dg (m * n) (m * n) (mul_ne_zero h h) := by
    apply Units.ext
    simp [dg_val, mul_comm]
  have h0 : ((m * n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h
  funext z
  rw [← SlashAction.slash_mul, e, dg_slash, mul_div_cancel_left₀ _ h0, ofComplex_apply, Nat.cast_mul (m * n), mul_zpow,
    ← zpow_add₀ h0, ← zpow_add₀ h0, Pi.smul_apply, smul_eq_mul]
  congr 2
  ring

private theorem B_symm [H.FiniteIndex] : quotInt H (petersson k G F) = conj (quotInt H (petersson k F G)) := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [quotInt, finsum_eq_sum_of_fintype, map_sum, ← integral_conj, ← petersson_symm]

private theorem quotInt_petersson_eq_add_of_hecke_sum [H.FiniteIndex] [H.Normal] {p : ℕ} {c : ℂ} {A B TF : ℍ → ℂ} (hF : Good H k F) (hA : Good H k A)
    (hB : Good H k B) (hT : ∀ u : ℤ, F ∣[k] (ModularGroup.T ^ u) = F)
    (e : ∀ z, TF z = c * A z + ∑ u ∈ Finset.range p, (B ∣[k] (ModularGroup.T ^ (u : ℤ))) z) :
    quotInt H (petersson k F TF) = c * quotInt H (petersson k F A) + p * quotInt H (petersson k F B) := by
  have e1 : petersson k F TF = fun z => petersson k F (c • A) z +
      ∑ u ∈ Finset.range p, petersson k F (B ∣[k] (ModularGroup.T ^ (u : ℤ))) z := by
    funext z
    simp only [petersson, e, Pi.smul_apply, smul_eq_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  have hc := fun u : ℕ => hF.cont (hB.slashSL (ModularGroup.T ^ (u : ℤ)))
  have hb := fun u : ℕ => hF.pbd (hB.slashSL (ModularGroup.T ^ (u : ℤ)))
  choose C hC using hb
  obtain ⟨D, hD⟩ := hF.pbd (hA.smul c)
  rw [e1, quotInt_add H (hF.cont (hA.smul c)) hD (continuous_finsetSum _ fun u _ => hc u)
    (C' := ∑ u ∈ Finset.range p, C u) fun z => (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => hC u z),
    quotInt_sum H _ hc fun u => ⟨_, hC u⟩, B_smul_right]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => quotInt H (petersson k F B)) fun u _ => ?_]
  · simp
  · rw [← B_slashSL (ModularGroup.T ^ (u : ℤ)) hF hB, hT]

private theorem good_cusp {M k : ℕ} [NeZero M] (f : CuspForm (Gamma1 M) (k : ℤ)) (h : H ≤ Gamma1 M) : Good H k f :=
  ⟨f.holo', CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f,
    fun γ hγ => f.slash_action_eq' _ ⟨γ, h hγ, rfl⟩⟩

end UpperTheory.V.Lit.KT

