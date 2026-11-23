module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacB

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInst
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

open MvPolynomial

def toRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
    else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def ofRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
    else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem ofRe_toRe {m n : ℕ} (P : PX m n) : ofRe m n (toRe m n P) = P := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hC : (C Complex.I : PX m n) * C (1 / (2 * Complex.I)) = C (1 / 2) := by
    rw [← C_mul]; congr 1; field_simp
  have hC2 : (C (1 / 2) : PX m n) + C (1 / 2) = 1 := by
    rw [← C_add, ← C_1]; congr 1; norm_num
  have : (ofRe m n).comp (toRe m n) = AlgHom.id ℂ (PX m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_add (f := _), map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination (X (a, i, false) - X (a, i, true)) * hC + X (a, i, false) * hC2
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_sub, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hC + X (a, i, true) * hC2
  exact congrArg (fun f => f P) this

theorem evX_eq_eval_toRe {m n : ℕ} (P : PX m n) (y : Fin m × Fin n × Bool → ℝ) :
    evX P (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ)) =
      eval (fun k => (y k : ℂ)) (toRe m n P) := by
  have key : (aeval fun k : Fin m × Fin n × Bool => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ))
      else (y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ)) = (aeval fun k => (y k : ℂ)).comp (toRe m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp [toRe]
    · simp [toRe, Complex.conj_ofReal, sub_eq_add_neg]
  unfold evX
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact congrArg (fun f => f P) key

theorem evX_injective {m n : ℕ} {P Q : PX m n} (h : ∀ u, evX P u = evX Q u) : P = Q := by
  have h0 : toRe m n (P - Q) = 0 := by
    apply eq_zero_of_eval_real
    intro y
    rw [← evX_eq_eval_toRe]
    have := h (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ))
    unfold evX at this ⊢
    rw [map_sub, this, sub_self]
  rw [← sub_eq_zero, ← ofRe_toRe (P - Q), h0, map_zero]

theorem fP_injective {m n : ℕ} {c : ℝ} {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  apply evX_injective
  intro u
  have := congrFun h u
  simp only [fP] at this
  have hg : gs c u ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hg this

theorem fP_smul_add {m n : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add (f := _), smul_eq_C_mul, map_mul, eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.LocInstH

namespace PositivityTheory.Rg.Sw.Glob

open LocInstH

theorem locInst_of (hT : TensMem) (hl : LIl) (hlin : LIlin) (hlaw : LIlaw) (hcell : LIcell) (hcont : LIcont)
    (hrho : LIrho) (hk : LIkact) (hvac : LIvac) (hkv : LIkvac) : LocInst := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  have hl0 := hl D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨hlinL, hid⟩ := hlin D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨e, he⟩ := hlaw D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨C0, hC0, hCc⟩ := hcell D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨ρ, hρ, hfin⟩ := hrho D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  have hzero : ∀ y : GR n, L y (fP (cLoc l τ) (0 : PX V.rank n)) = 0 := by
    intro y
    have h2 := hlinL y 1 0 0
    simp only [one_smul, add_zero] at h2
    have : L y (fP (cLoc l τ) (0 : PX V.rank n)) + L y (fP (cLoc l τ) (0 : PX V.rank n)) =
        L y (fP (cLoc l τ) (0 : PX V.rank n)) + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel this
  let sL : PX V.rank n →ₗ[ℂ] (GR n → ℂ) :=
    { toFun := fun P => sLd L (cLoc l τ) P
      map_add' := fun P Q => by
        funext y
        have h2 := hlinL y 1 P Q
        rw [one_smul, one_smul] at h2
        simp only [sLd, Pi.add_apply, h2]
      map_smul' := fun a P => by
        funext y
        have h2 := hlinL y a P 0
        rw [add_zero, hzero y, add_zero] at h2
        simp only [sLd, Pi.smul_apply, RingHom.id_apply, h2, smul_eq_mul] }
  have hsign : ((tLoc l τ = cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε true ∧ (pqOf ε l τ).2 = cnt ε false) ∨
      (tLoc l τ = -cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε false ∧ (pqOf ε l τ).2 = cnt ε true)) := by
    unfold tLoc cLoc pqOf
    split_ifs with h
    · exact Or.inl ⟨by rw [abs_of_pos h], rfl, rfl⟩
    · have hneg : l τ < 0 := lt_of_le_of_ne (not_lt.mp h) hl0
      exact Or.inr ⟨by rw [abs_of_neg hneg]; ring, rfl, rfl⟩
  have hcpos : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.mpr hl0
    positivity
  have h11 : sLd L (cLoc l τ) 1 1 = 1 := by
    simp [sLd, hid, fP, evX, gs]
  have hvac' : ∀ g, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g :=
    hvac V.rank n ε (cLoc l τ) (tLoc l τ) (pqOf ε l τ).1 (pqOf ε l τ).2 e hcpos hsign (sLd L (cLoc l τ) 1) C0
      (hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL 1) h11 (fun y g hy => he 1 y g hy) (fun g b hb hg => hCc 1 g b hb hg)
  refine ⟨sL, ρ, (pqOf ε l τ).1, (pqOf ε l τ).2, e, ?_, ?_, fun P y => rfl, hρ⟩
  · have hs := hC.hsig
    unfold pqOf GoodSig at *
    split_ifs <;> omega
  · refine ⟨hcpos, hsign, fun P => hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P, hvac', fun P y g hy => he P y g hy,
      ⟨C0, hC0, fun P g b hb hg => hCc P g b hb hg⟩,
      fun P g k hk' => hk D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk', ?_, hfin⟩
    intro k hkK
    have h1 := hkv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac' k hkK
    rw [hρ k 1 hkK] at h1
    apply fP_injective (c := cLoc l τ)
    rw [h1]
    have := fP_smul_add (cLoc l τ) (F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k) (1 : PX V.rank n) 0
    simp only [add_zero] at this
    rw [this]
    funext u
    simp [fP, evX]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacC
section
noncomputable section

open Matrix Filter Topology Polynomial
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem inG_JJ : InG (JJ n) := by
  unfold InG
  rw [JJ_conjTranspose, Matrix.mul_assoc, JJ_sq, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem nU_mul (b c : Matrix (Fin n) (Fin n) ℂ) : nU b * nU c = nU (b + c) := by
  simp [nU, fromBlocks_multiply, add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, fromBlocks_one]

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG; simp [nU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, hb.eq]

def jjE : GR n := ⟨⟨JJ n, -JJ n, by rw [Matrix.mul_neg, JJ_sq, neg_neg], by rw [Matrix.neg_mul, JJ_sq, neg_neg]⟩, inG_JJ⟩

def nuE (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : GR n :=
  ⟨⟨nU b, nU (-b), by rw [nU_mul, add_neg_cancel, nU_zero], by rw [nU_mul, neg_add_cancel, nU_zero]⟩, inG_nU hb⟩

def nbar (s : ℝ) : M2 n := fromBlocks 1 0 ((s : ℂ) • 1) 1

theorem nbar_mul (s t : ℝ) : nbar (n := n) s * nbar t = nbar (s + t) := by
  simp [nbar, fromBlocks_multiply, add_smul, add_comm]

theorem nbar_zero : nbar (n := n) 0 = 1 := by simp [nbar, fromBlocks_one]

theorem inG_nbar (s : ℝ) : InG (nbar (n := n) s) := by
  unfold InG
  simp [nbar, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_smul, Complex.conj_ofReal]

def nbE (s : ℝ) : GR n :=
  ⟨⟨nbar s, nbar (-s), by rw [nbar_mul, add_neg_cancel, nbar_zero], by rw [nbar_mul, neg_add_cancel, nbar_zero]⟩, inG_nbar s⟩

theorem nbE_zero : nbE (n := n) 0 = 1 := Subtype.ext (Units.ext nbar_zero)

theorem cont_nbar : Continuous (nbar (n := n)) := by
  unfold nbar
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

theorem cont_nbE : Continuous (nbE (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨cont_nbar, ?_⟩
  exact cont_nbar.comp continuous_neg

theorem lower_left_block_mul_lowering (g : GR n) (s : ℝ) :
    (mR (g * nbE s)).toBlocks₂₁ = (mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂ := by
  rw [mR_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
  show (fromBlocks _ _ _ _ * nbar s).toBlocks₂₁ = _
  simp [nbar, fromBlocks_multiply]

theorem finite_bad (g : GR n) :
    {s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0}.Finite := by
  set C := (mR g).toBlocks₂₁
  set D := (mR g).toBlocks₂₂
  set P : Polynomial ℂ := det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C) with hP
  have hev : ∀ z : ℂ, P.eval z = (C + z • D).det := by
    intro z
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP0 : P ≠ 0 := by
    intro h0
    have hz := hev Complex.I
    rw [h0, Polynomial.eval_zero] at hz
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz.symm
    apply hv
    apply vec_zero g (-Complex.I) (by simp) v
    have hm : (-Complex.I) • C + D = (-Complex.I) • (C + Complex.I • D) := by
      rw [smul_add, smul_smul]
      simp
    rw [hm, Matrix.vecMul_smul, hv0, smul_zero]
  apply ((P.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot, hev]
  exact hs

theorem dense_cell : Dense {g : GR n | ((mR g).toBlocks₂₁).det ≠ 0} := by
  intro g
  have hT : Tendsto (fun s : ℝ => g * nbE s) (𝓝[≠] 0) (𝓝 g) := by
    have hc : Continuous fun s : ℝ => g * nbE s := continuous_const.mul cont_nbE
    have h := hc.tendsto 0
    rw [nbE_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hfin := finite_bad g
  have hZ : IsClosed ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  have h0 : (0 : ℝ) ∉ ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) := by simp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hZ.isOpen_compl.mem_nhds h0), self_mem_nhdsWithin] with s hs hs0
  show ((mR (g * nbE s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_mul_lowering]
  intro hdet
  exact hs ⟨hdet, hs0⟩

theorem bigcell (g : GR n) (hγ : ((mR g).toBlocks₂₁).det ≠ 0) :
    ∃ (y h : GR n) (b : Matrix (Fin n) (Fin n) ℂ), (mR y).toBlocks₂₁ = 0 ∧ b.IsHermitian ∧ mR h = JJ n * nU b ∧
      g = y * h := by
  set C := (mR g).toBlocks₂₁ with hC
  set D := (mR g).toBlocks₂₂ with hD
  have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hγ
  have huH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hγ)
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * Cᴴ⁻¹ = C⁻¹ * (C * Dᴴ) * Cᴴ⁻¹ := by rw [nonsing_inv_mul_cancel_left C _ hu]
      _ = C⁻¹ * (D * Cᴴ) * Cᴴ⁻¹ := by rw [hC, hD, lagr g]
      _ = C⁻¹ * D := by rw [← Matrix.mul_assoc, mul_nonsing_inv_cancel_right Cᴴ _ huH]
  refine ⟨g * (jjE * nuE (C⁻¹ * D) hb)⁻¹, jjE * nuE (C⁻¹ * D) hb, C⁻¹ * D, ?_, hb, ?_, by group⟩
  · have hinv : mR (jjE * nuE (C⁻¹ * D) hb)⁻¹ = nU (-(C⁻¹ * D)) * (-JJ n) := by
      rw [_root_.mul_inv_rev, mR_mul]
      rfl
    rw [mR_mul, hinv]
    conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
    simp [nU, JJ, fromBlocks_multiply, fromBlocks_neg, ← hC, ← hD]
    rw [mul_nonsing_inv_cancel_left C D hu, neg_add_cancel]
  · rw [mR_mul]
    rfl

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ZReAddZImStar
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

def xyC (Z : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (Z a c) * MvPolynomial.X (c, i, b)

def vfC (c : ℝ) (Zh Za : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyC Zh a i false * pderiv (a, i, false) P + xyC Za a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyC Zh a i false * MvPolynomial.X (a, i, true) + xyC Za a i true * MvPolynomial.X (a, i, false)) * P)

theorem vfX_eq (c : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : vfX c Z P = vfC c Z (Z.map star) P := by
  have h1 : ∀ a (i : Fin n), xyP Z a i false = xyC Z a i false := fun a i => by simp [xyP, xyC]
  have h2 : ∀ a (i : Fin n), xyP Z a i true = xyC (Z.map star) a i true := fun a i => by simp [xyP, xyC, Matrix.map_apply]
  simp only [vfX, vfC, h1, h2]

theorem xyC_add_smul (Z Z' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    xyC (Z + r • Z') a i b = xyC Z a i b + C r * xyC Z' a i b := by
  simp only [xyC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem vfC_lin (c : ℝ) (Zh Za Zh' Za' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (P : PX m n) :
    vfC c Zh Za P + r • vfC c Zh' Za' P = vfC c (Zh + r • Zh') (Za + r • Za') P := by
  simp only [vfC, xyC_add_smul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem xyC_single (a b a' : Fin m) (r : ℂ) (i : Fin n) (β : Bool) :
    xyC (r • Matrix.single a b (1 : ℂ)) a' i β = if a' = a then C r * MvPolynomial.X (b, i, β) else 0 := by
  by_cases h : a' = a
  · subst h
    simp only [xyC, Matrix.smul_apply, Matrix.single_apply, true_and, smul_eq_mul, mul_ite, mul_one,
      mul_zero, if_true]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [xyC, Matrix.single_apply, h, Ne.symm h]

theorem sgn_star (ε : Fin m → Bool) (a : Fin m) : star (sgn ε a) = sgn ε a := by
  unfold sgn; split_ifs <;> simp

theorem zRe_add_zIm (ε : Fin m → Bool) (a b : Fin m) :
    zRe ε a b + Complex.I • zIm ε a b = (1 : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zRe_add_zIm_star (ε : Fin m → Bool) (a b : Fin m) :
    (zRe ε a b).map star + Complex.I • (zIm ε a b).map star = (-(sgn ε a * sgn ε b)) • Matrix.single b a (1 : ℂ) := by
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := sgn_star ε a
  have ht : (starRingEnd ℂ) (sgn ε b) = sgn ε b := sgn_star ε b
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, Matrix.neg_apply, Matrix.single_apply, Complex.star_def]
  split_ifs <;> simp [map_add (f := _), map_mul, map_neg, map_sub, hs, ht, h2, Complex.conj_I] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem hOp_eq (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) :
    hOp ε c a b P = vfX c (zRe ε a b) P + Complex.I • vfX c (zIm ε a b) P := by
  rw [vfX_eq, vfX_eq, vfC_lin, zRe_add_zIm, zRe_add_zIm_star]
  unfold vfC hOp
  simp only [xyC_single]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, add_mul, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [map_neg, map_one, map_mul, map_sub]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH
end
end

