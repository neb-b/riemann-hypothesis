module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
public import GroundTheory.AutomorphicForms.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

private theorem barW_coe (z : (A E)ˣ) : ((Units.map (D.bar : A E →* A E) z : (A E)ˣ) : A E) = D.bar z := rfl

private theorem bar_mul_barInv (z : (A E)ˣ) :
    D.bar (z : A E) * (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = 1 := by
  rw [← barW_coe, Units.mul_inv]

private theorem sZ_val (z : (A E)ˣ) :
    (sZ D z).val = !![(z : A E), 0; 0, (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E)] := by
  simp only [sZ, Units.val_mul, aE_val, dM_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem em_val (h : GL (Fin 2) (A ℚ)) (i j : Fin 2) : (em E h).val i j = am E (h.val i j) := rfl

private theorem am_norm_mul (z : (A E)ˣ) :
    (z : A E) * D.bar z * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
  rw [← D.am_ideleNorm z, ← map_mul, Units.mul_inv, map_one]

private theorem barInv_eq (z : (A E)ˣ) :
    (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) * z := by
  have h2 := am_norm_mul D z
  have h3 := bar_mul_barInv D z
  linear_combination ((z : A E) * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ)) * h3 - (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) * h2

private theorem sZ_mul (z z' : (A E)ˣ) : sZ D (z * z') = sZ D z * sZ D z' := by
  simp only [sZ, map_mul, mul_inv, aE_mul, dM_mul]
  rw [mul_assoc, mul_assoc, ← mul_assoc (dM _) (aE z'), dM_mul_aE, ← mul_assoc (aE z')]

private theorem sZ_cont : Continuous (sZ D) := by
  have h : Continuous (Units.map (D.bar : A E →* A E)) := Continuous.units_map _ D.continuous_bar
  exact continuous_aE.mul (continuous_dM.comp h.inv)

private theorem nu_sZ (z : (A E)ˣ) : nu ℚ (sZ D z) = 1 := by
  have h : ideleNorm ℚ E (Units.map (D.bar : A E →* A E) z) = ideleNorm ℚ E z := D.ideleNorm_barU z
  rw [sZ, nu_mul, nu_aE, nu_dM, map_inv, h, mul_inv_cancel]

private theorem hermitian_standardVector : D.herm (rp X0) = !![0, rt D.θ; -rt D.θ, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE_def, X0, rp]

private theorem action_fixes_standardVector {h : GL (Fin 2) (A E)}
    (h1 : h.val * !![0, rt D.θ; -rt D.θ, 0] * D.star2 h.val = !![0, rt D.θ; -rt D.θ, 0]) :
    D.act h (rp X0) = rp X0 := by
  apply D.herm_injective
  rw [D.herm_act, hermitian_standardVector, h1]

private theorem act_sZ (z : (A E)ˣ) : D.act (sZ D z) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have h3 : (z : A E) * ((z⁻¹ : (A E)ˣ) : A E) = 1 := Units.mul_inv z
  have h4 : D.bar ((z⁻¹ : (A E)ˣ) : A E) * D.bar (z : A E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [sZ_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply]
  · linear_combination (rt D.θ) * h3
  · linear_combination (rt D.θ) * h4

private theorem act_em (g : G1 ℚ) : D.act (em E (gl g)) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have hd : am E (g 0 0) * am E (g 1 1) - am E (g 0 1) * am E (g 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, specialLinear_det_entries, map_one]
  have e : (em E (gl g)).val = !![am E (g 0 0), am E (g 0 1); am E (g 1 0), am E (g 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [e]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, D.bar_am]
  · ring
  · linear_combination (rt D.θ) * hd
  · linear_combination (-rt D.θ) * hd
  · ring

private theorem sZ_diag (e : Eˣ) : ∃ γ, sZ D (IdeleGroup.diagonal E e) = ratGL E 2 γ := by
  obtain ⟨γ₁, h₁⟩ := exists_ratGL_aE (F := E) e
  obtain ⟨γ₂, h₂⟩ := exists_ratGL_dM (F := E) (Units.map (D.σ : E →* E) e)⁻¹
  refine ⟨γ₁ * γ₂, ?_⟩
  have h : (Units.map (D.bar : A E →* A E) (IdeleGroup.diagonal E e))⁻¹ =
      IdeleGroup.diagonal E (Units.map (D.σ : E →* E) e)⁻¹ := by
    rw [map_inv]
    congr 1
    apply Units.ext
    rw [barW_coe, coe_diagonal, coe_diagonal, D.bar_rt]
    rfl
  rw [sZ, h, map_mul, h₁, h₂]

private theorem sZ_conj (z : (A E)ˣ) (g : G1 ℚ) :
    sZ D z * em E (gl g) = em E (gl (cD (ideleNorm ℚ E z)⁻¹ g)) * sZ D z := by
  have hn := am_norm_mul D z
  have hb := barInv_eq D z
  have hN := D.am_ideleNorm z
  have hc : ∀ i j, (em E (gl (cD (ideleNorm ℚ E z)⁻¹ g))).val i j = am E ((cD (ideleNorm ℚ E z)⁻¹ g).1 i j) := fun _ _ => rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hc, em_val, gl_val, cD_val]
  fin_cases i <;> fin_cases j <;> simp [inv_inv, map_mul, hN]
  · ring
  · rw [GroundTheory.Global.coe_ideleNorm] at hN
    rw [hN]
    linear_combination (-(am E (g 0 1)) * (z : A E)) * hn
  · ring
  · ring

private theorem sZ_scalar (z : (A E)ˣ) :
    sZ D z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * em E (dM (ideleNorm ℚ E z)⁻¹) := by
  have hb := barInv_eq D z
  apply Units.ext
  rw [Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, em_val, dM_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · ring

private theorem quadraticForm_rational_points (δ : ℚ) (ξ : Fin 4 → ℚ) : q4 δ (rp ξ) = rt (qr δ ξ) := by
  simp [q4, qr, rp, map_sub, map_mul, map_pow]

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws :
    SzLaws := by
  intro E _ _ _ D
  refine ⟨sZ_mul D, sZ_cont D, nu_sZ D, nu_gl, act_sZ D, act_em D, sZ_diag D, sZ_conj D, sZ_scalar D, ?_, quadraticForm_rational_points D.δ⟩
  intro x hx v
  rw [D.quadForm_act, hx]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private theorem vn (q : A F) : (nU q).val = !![1, q; 0, 1] := rfl

private theorem vm (a : (A F)ˣ) : (mD a).val = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl

private theorem gmul (x y : G1 F) : gl (x * y) = gl x * gl y := map_mul _ _ _

private theorem cont_n : Continuous fun q : A F => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q => inv_eq_of_mul_eq_one_right (Units.ext (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two]))
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

private theorem tri (Y : GL (Fin 2) (A F)) (t₀ t₁ : (A F)ˣ) (h0 : Y.val 0 0 = t₀) (h1 : Y.val 1 1 = t₁) (h : Y.val 1 0 = 0) :
    Y = gl (nU (Y.val 0 1 * ((t₁⁻¹ : (A F)ˣ) : A F))) * diagUnits 2 ![t₀, t₁] := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, h0, h1, h]

private theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem rat_m (c : Fˣ) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (mD (IdeleGroup.diagonal F c)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] i j) = _
  fin_cases i <;> fin_cases j
  · rfl
  · simp [vm]
  · simp [vm]
  · rfl

private theorem units_cpt {C : Set (GL (Fin 2) (A F))} (hC : IsCompact C) :
    ∃ U : Set (A F)ˣ, IsCompact U ∧ ∀ β ∈ C, β ∈ adelicBorel (K := F) (n := 2) → ∀ i, ∃ u ∈ U, (u : A F) = β.val i i := by
  let Q : Set (A F) := ⋃ i : Fin 2, ((fun β : GL (Fin 2) (A F) => β.val i i) '' C ∪ (fun β : GL (Fin 2) (A F) => (β⁻¹).val i i) '' C)
  have hQ : IsCompact Q := isCompact_iUnion fun i =>
    (hC.image (Units.continuous_val.matrix_elem i i)).union
      (hC.image (Units.continuous_coe_inv.matrix_elem i i))
  refine ⟨Units.embedProduct _ ⁻¹' (Q ×ˢ (MulOpposite.op '' Q)), Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hQ.prod (hQ.image MulOpposite.continuous_op)), fun β hβ hb i => ?_⟩
  have h1 : β.val 1 0 = 0 := hb (by decide : (0 : Fin 2) < 1)
  have h2 : (β⁻¹).val 1 0 = 0 := (adelicBorel.inv_mem hb) (by decide : (0 : Fin 2) < 1)
  have h3 : β.val i i * (β⁻¹).val i i = 1 := by
    have := congrFun (congrFun β.mul_inv i) i
    rw [Matrix.mul_apply, Fin.sum_univ_two] at this
    fin_cases i
    · simpa [-Matrix.coe_units_inv, h2] using this
    · simpa [-Matrix.coe_units_inv, h1] using this
  exact ⟨⟨β.val i i, (β⁻¹).val i i, h3, by rw [mul_comm]; exact h3⟩,
    ⟨Set.mem_iUnion.2 ⟨i, Or.inl ⟨β, hβ, rfl⟩⟩, _, Set.mem_iUnion.2 ⟨i, Or.inr ⟨β, hβ, rfl⟩⟩, rfl⟩, rfl⟩

private theorem siegel {C : Set (GL (Fin 2) (A F))} (hC : IsCompact C) :
    ∃ ω : Set (GL (Fin 2) (A F)), IsCompact ω ∧ ω ⊆ (adelicBorel (K := F) (n := 2) : Subgroup _) ∧
      ∀ (b : A F) (a : (A F)ˣ), ∀ k ∈ C, ∀ (s : ℝ) (hs : 0 < s), s ^ Module.finrank ℚ F = ab a →
        ∃ γ γ' : GL (Fin 2) F, ∃ y ∈ ω, ∃ kk ∈ maxCompact (K := F) (n := 2), gl (nU b * mD a) * k =
          ratGL F 2 γ' * (ratGL F 2 γ * (y * diagUnits 2 ![posIdele s hs, (posIdele s hs)⁻¹] * kk)) := by
  obtain ⟨U, hU, hUm⟩ := units_cpt (hC.mul (isCompact_maxCompact (K := F) (n := 2)))
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  obtain ⟨Q₀, hQ₀, hQ⟩ := exists_isCompact_forall_exists_sub_mem F
  have hQc := hQ₀.prod (isCompact_integralFiniteAdeles F)
  let P : A F × (A F)ˣ × (A F)ˣ × (A F)ˣ → GL (Fin 2) (A F) := fun p =>
    gl (nU p.1) * diagUnits 2 ![p.2.1 * p.2.2.1, p.2.1⁻¹ * p.2.2.2]
  have hP : Continuous P := (cont_n.comp continuous_fst).mul ((continuous_diagUnits (K := F) 2).comp
    (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop))
  refine ⟨P '' _, (hQc.prod (hS.prod (hU.prod hU))).image hP, ?_, fun b a k hk s hs hsa => ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    refine mul_mem ?_ (diagUnits_mem_adelicBorel _ _)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vn]
  obtain ⟨β, hβ, kk, hkk, rfl⟩ := exists_adelicBorel_mul_maxCompact (K := F) (n := 2) k
  have hβC := (mul_inv_cancel_right β kk) ▸ Set.mul_mem_mul hk (show kk⁻¹ ∈ ((maxCompact (K := F) (n := 2) : Subgroup _) : Set (GL (Fin 2) (A F))) from inv_mem hkk)
  obtain ⟨u₀, hu₀, e₀⟩ := hUm β hβC hβ 0
  obtain ⟨u₁, hu₁, e₁⟩ := hUm β hβC hβ 1
  have h1 : β.val 1 0 = 0 := hβ (by decide : (0 : Fin 2) < 1)
  set p : (A F)ˣ := posIdele s hs with hp
  have hm : (IdeleGroup.ideleModule F (a * p⁻¹) : ℝ) = 1 := by
    have : IdeleGroup.ideleModule F a = IdeleGroup.ideleModule F p :=
      Subtype.ext (by rw [hp, ideleModule_posIdele, hsa]; rfl)
    rw [map_mul, map_inv, this, mul_inv_cancel]; rfl
  obtain ⟨c, hc⟩ := hSm (a * p⁻¹) hm.ge hm.le
  set g : (A F)ˣ := IdeleGroup.diagonal F c with hg
  set Y := gl (mD g) * (gl (nU b * mD a) * β) with hY
  have hY' := tri Y (g * a * u₀) ((g * a)⁻¹ * u₁)
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1, ← e₀, mul_assoc])
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, ← e₁, mul_assoc, mul_left_comm])
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1])
  set e := Y.val 0 1 * ((((g * a)⁻¹ * u₁)⁻¹ : (A F)ˣ) : A F)
  obtain ⟨ξ, hξ⟩ := hQ e
  obtain ⟨γ, hγ⟩ := rat_n ξ
  obtain ⟨γ', hγ'⟩ := rat_m c
  refine ⟨γ, γ'⁻¹, _, ⟨(e - rt ξ, g * (a * p⁻¹), u₀, u₁), ⟨hξ, hc, hu₀, hu₁⟩, rfl⟩, kk, hkk, ?_⟩
  have hd : diagUnits 2 ![g * a * u₀, (g * a)⁻¹ * u₁] =
      diagUnits 2 ![g * (a * p⁻¹) * u₀, (g * (a * p⁻¹))⁻¹ * u₁] * diagUnits 2 ![p, p⁻¹] := by
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_assoc, mul_comm, mul_left_comm]
  rw [map_inv, eq_inv_mul_iff_mul_eq, hγ, hγ', ← hg, ← mul_assoc _ β, ← mul_assoc, ← hY, hY', hd]
  have : gl (nU e) = gl (nU (rt ξ)) * gl (nU (e - rt ξ)) := by rw [← n_add]; congr 2; ring
  rw [this]
  simp only [P, mul_assoc]

private theorem pos_inv {s : ℝ} (hs : 0 < s) : (posIdele (K := F) s hs)⁻¹ = posIdele s⁻¹ (inv_pos.2 hs) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← posIdeleHom_apply (K := F) ⟨s, hs⟩, ← posIdeleHom_apply (K := F) ⟨s⁻¹, inv_pos.2 hs⟩, ← map_mul, ← map_one (posIdeleHom F)]
  exact congrArg _ (Subtype.ext (mul_inv_cancel₀ hs.ne'))

private theorem arith {C H M τ s s₀ h : ℝ} {e N d r : ℕ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hh : 0 ≤ h)
    (h1 : h ≤ H * (H * M * (τ * s) ^ e)) :
    C * (s⁻¹ / s) ^ (e * N + d * r) * h ^ N ≤ |C| * (H * (H * M * τ ^ e)) ^ N * s₀⁻¹ ^ (e * N + d * r) * (s ^ d)⁻¹ ^ r := by
  have hp : 0 < s := hs₀.trans_le hs
  have h2 : h ^ N ≤ (H * (H * M * τ ^ e)) ^ N * s ^ (e * N) := by
    refine (pow_le_pow_left₀ hh h1 N).trans_eq ?_
    rw [pow_mul, ← mul_pow, mul_pow τ]; ring_nf
  have h3 : s⁻¹ ^ (e * N + d * r) ≤ s₀⁻¹ ^ (e * N + d * r) := pow_le_pow_left₀ (by positivity) (inv_anti₀ hs₀ hs) _
  have h4 : 0 ≤ (H * (H * M * τ ^ e)) ^ N := by
    by_contra hn
    exact absurd (h2.trans_lt (mul_neg_of_neg_of_pos (not_le.1 hn) (by positivity))) (not_lt.2 (by positivity))
  calc C * (s⁻¹ / s) ^ (e * N + d * r) * h ^ N
      ≤ |C| * (s⁻¹ / s) ^ (e * N + d * r) * ((H * (H * M * τ ^ e)) ^ N * s ^ (e * N)) := by
        gcongr
        exact le_abs_self C
    _ = |C| * (H * (H * M * τ ^ e)) ^ N * s⁻¹ ^ (e * N + d * r) * (s ^ d)⁻¹ ^ r := by
        rw [div_eq_mul_inv, mul_pow, pow_add s⁻¹ (e * N), inv_pow (s ^ d), ← pow_mul, inv_pow s (e * N), inv_pow s (d * r)]
        field_simp
    _ ≤ _ := by gcongr

end SlopeTestRemainingChoices

set_option maxHeartbeats 800000 in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.decE :
    DecE := by
  intro F _ _ _ π f hf
  obtain ⟨ψ, rfl⟩ := UpperTheory.V.Cm.mem_range_ofCusp.2 (π.cusp f hf)
  refine ⟨⟨ψ.2.1.continuous, (π.cusp _ hf).1.left⟩, fun g => ?_, fun C hC c hc r => ?_⟩
  · letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
    rw [← Pp.int_one (ι := UPos 2 1), ← ψ.2.2 1 one_pos one_lt_two g]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : gl (nU (x default)) = unipGL x := by
      refine Units.ext ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Pp.vn, unipMatrix, blockEntry_apply]
      rfl
    simp only [this]
    rfl
  obtain ⟨ω, hω, hωB, hs⟩ := siegel hC
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hω
  set d := Module.finrank ℚ F
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  set s₀ := c ^ (d : ℝ)⁻¹
  have hs₀ : 0 < s₀ := Real.rpow_pos_of_pos hc _
  obtain ⟨N, hN⟩ := CuspidalSpectrum.exists_norm_le_siegel_root ψ.2 hω hωB (pow_pos hs₀ 2) one_pos one_lt_two
  set e := 2 * Fintype.card (InfinitePlace F)
  obtain ⟨B, hB⟩ := hN (e * N + d * r)
  set τ := 1 + s₀⁻¹ + s₀⁻¹ ^ 2
  set H := heightConst F 2
  refine ⟨|B| * (H * (H * M * τ ^ e)) ^ N * s₀⁻¹ ^ (e * N + d * r), fun b a k hk ha => ?_⟩
  set s := ab a ^ (d : ℝ)⁻¹
  have h0 : s₀ ≤ s := Real.rpow_le_rpow hc.le ha (by positivity)
  have hp : 0 < s := hs₀.trans_le h0
  have hsa : s ^ d = ab a := Real.rpow_inv_natCast_pow (hc.le.trans ha) hd
  obtain ⟨γ, γ', y, hy, kk, hkk, e1⟩ := hs b a k hk s hp hsa
  rw [e1, (π.cusp _ hf).1.left, (π.cusp _ hf).1.left, ← hsa]
  have hρ : ∀ i, 0 < (![s, s⁻¹] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> simp [hp]
  have e2 : (![posIdele s hp, (posIdele s hp)⁻¹] : Fin 2 → IdeleGroup F) = fun i => posIdele (![s, s⁻¹] i) (hρ i) := by
    funext i
    fin_cases i
    · rfl
    · exact pos_inv hp
  have hi : s⁻¹ ≤ s₀⁻¹ := inv_anti₀ hs₀ h0
  have h1 : 1 ≤ s₀⁻¹ * s := by rw [inv_mul_eq_div, one_le_div hs₀]; exact h0
  have hi0 : 0 < s₀⁻¹ := inv_pos.2 hs₀
  have h2 : s₀⁻¹ ≤ s₀⁻¹ ^ 2 * s := by nlinarith
  have hL : 1 ≤ τ * s ∧ s ≤ τ * s ∧ s⁻¹ ≤ τ * s := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [τ] <;> nlinarith
  have h3 := hB y hy _ hρ (fun i j hij => by
    obtain rfl : i = 0 := Fin.ext (by have := j.2; simp; omega)
    obtain rfl : j = 1 := Fin.ext (by simpa using hij)
    change s₀ ^ 2 * s⁻¹ ≤ s
    rw [← div_eq_mul_inv, div_le_iff₀ hp]; nlinarith) kk hkk _ rfl
  rw [e2]
  refine h3.trans (arith hs₀ h0 (height_pos _).le ?_)
  have hH : 0 ≤ H := zero_le_one.trans one_le_heightConst
  refine (height_mul_le _ _).trans ?_
  rw [height_eq_one_of_mem_maxCompact hkk, mul_one]
  refine mul_le_mul_of_nonneg_left ((height_mul_le _ _).trans ?_) hH
  have h5 := CuspidalSpectrum.height_diagUnits_posIdele_le (K := F) hρ hL.1 (fun i => by
    fin_cases i
    · exact ⟨hL.2.1, hL.2.2⟩
    · exact ⟨hL.2.2, by simpa using hL.2.1⟩)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hM y hy) hH) h5 (height_pos _).le
    (mul_nonneg hH ((height_pos _).le.trans (hM y hy)))
end

