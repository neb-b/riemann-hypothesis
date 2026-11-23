module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmul
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem cwA_add (w : InfinitePlace F) (X Y : Mx F E d.m d.n) : d.cw w (X + Y) = d.cw w X + d.cw w Y := by
  ext i j
  simp [SD.cw]

theorem cwA_realAd (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    d.cw w (realAd F t • X) = (t : ℂ) • d.cw w X := by
  ext i j
  simp [SD.cw, GlobalTheory.RealScalar.piInf_realAd_smul]

theorem locA_add (R : RD d) (w : InfinitePlace F) (X Y : Mx F E d.m d.n) :
    R.loc w (X + Y) = R.loc w X + R.loc w Y := by
  simp only [RD.loc, cwA_add, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _

theorem locA_realAd (R : RD d) (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    R.loc w (realAd F t • X) = (t : ℂ) • R.loc w X := by
  simp only [RD.loc, cwA_realAd, Matrix.mul_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  rfl

def arcAF (R : RD d) (X : Mx F E d.m d.n) : Iw d → ℝ :=
  fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im

theorem arcA_eq (R : RD d) (X : Mx F E d.m d.n) : arc R X = (EuclideanSpace.equiv (Iw d) ℝ).symm (arcAF R X) := rfl

theorem arc_add' (R : RD d) (X Y : Mx F E d.m d.n) : arc R (X + Y) = arc R X + arc R Y := by
  have : arcAF R (X + Y) = arcAF R X + arcAF R Y := by
    funext i
    simp only [arcAF, locA_add, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [arcA_eq, arcA_eq, arcA_eq, this, map_add (f := _)]

theorem arc_realAd' (R : RD d) (t : ℝ) (X : Mx F E d.m d.n) : arc R (realAd F t • X) = t • arc R X := by
  have : arcAF R (realAd F t • X) = t • arcAF R X := by
    funext i
    simp only [arcAF, locA_realAd, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [arcA_eq, arcA_eq, this, map_smul]

theorem crdA_add (X Y : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Y) k = d.crd X k + d.crd Y k := by
  simp [SD.crd]

theorem sndA_crd_of (Z : Mx F E d.m d.n) (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have h1 : finOne F • Z k.1 k.2.1 = 0 := by
    have := congrFun (congrFun hZ k.1) k.2.1
    simpa using this
  have h2 : finOne F * (Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2 = 0 := by
    have := congrArg (fun z => (Algebra.TensorProduct.basis (AF F) d.bs).repr z k.2.2) h1
    simpa only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] using this
  have h3 : (1 : FiniteAdeleRing (𝓞 F) F) * ((Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2).2 = 0 :=
    congrArg Prod.snd h2
  rw [one_mul] at h3
  exact h3

theorem fin_add_of' (R : RD d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    fin d (X + Z) = fin d X := by
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [crdA_add]
  show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  rw [sndA_crd_of Z hZ k, add_zero]

theorem fin_realAd_smul' {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  rw [smul_comm, hZ, smul_zero]

theorem gau_eq' (R : RD d) (X : Mx F E d.m d.n) : gau R X = (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) := by
  have hn : ‖arc R X‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, arc, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.equiv, if_true, if_false]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  simp only [gau, fP, evX, map_one, one_mul, gs]
  rw [hn, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

end PositivityTheory.SiegelWeilFormula.KFP

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Imports
section

end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.RotVac
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open Matrix

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sb (n : ℕ) (a b c e : ℂ) : M2 n := fromBlocks (a • 1) (b • 1) (c • 1) (e • 1)

theorem sb_mul (n : ℕ) (a b c e a' b' c' e' : ℂ) :
    sb n a b c e * sb n a' b' c' e' = sb n (a * a' + b * c') (a * b' + b * e') (c * a' + e * c') (c * b' + e * e') := by
  simp only [sb, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 1 <;> congr 1 <;> ring

theorem sb_ct (n : ℕ) (a b c e : ℂ) : (sb n a b c e)ᴴ = sb n (star a) (star c) (star b) (star e) := by
  simp only [sb, fromBlocks_conjTranspose, conjTranspose_smul, conjTranspose_one]

theorem sb_congr (n : ℕ) {a b c e a' b' c' e' : ℂ} (h1 : a = a') (h2 : b = b') (h3 : c = c') (h4 : e = e') :
    sb n a b c e = sb n a' b' c' e' := by
  subst h1 h2 h3 h4; rfl

theorem sb_one (n : ℕ) : (1 : M2 n) = sb n 1 0 0 1 := by
  simp [sb, fromBlocks_one]

theorem sb_JJ (n : ℕ) : JJ n = sb n 0 1 (-1) 0 := by
  simp [sb, JJ]

theorem yrotM_sb (n : ℕ) (s : ℤˣ) (t : ℝ) :
    yrotM n s t = sb n (Real.cos t) (((s : ℤ) : ℂ) * Real.sin t) (-(((s : ℤ) : ℂ) * Real.sin t)) (Real.cos t) := rfl

theorem cs1 (t : ℝ) : (Real.cos t : ℂ) * Real.cos t + (Real.sin t : ℂ) * Real.sin t = 1 := by
  have := Real.cos_sq_add_sin_sq t
  exact_mod_cast (by nlinarith [this] : Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1)

theorem yrotM_mul' (n : ℕ) (s : ℤˣ) (t t' : ℝ) : yrotM n s t * yrotM n s t' = yrotM n s (t + t') := by
  rw [yrotM_sb, yrotM_sb, yrotM_sb, sb_mul]
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    apply sb_congr <;> push_cast [Real.cos_add, Real.sin_add] <;> ring

theorem yrotM_zero' (n : ℕ) (s : ℤˣ) : yrotM n s 0 = 1 := by
  rw [yrotM_sb, sb_one]
  apply sb_congr <;> simp

theorem inK_yrotM' (n : ℕ) (s : ℤˣ) (t : ℝ) : InK (yrotM n s t) := by
  have h1 := cs1 t
  have e1 : star (Real.cos t : ℂ) = Real.cos t := Complex.conj_ofReal _
  have e2 : star (Real.sin t : ℂ) = Real.sin t := Complex.conj_ofReal _
  have hs : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or s with h | h <;> simp [h]
  have es : star ((s : ℤ) : ℂ) = ((s : ℤ) : ℂ) := by simp
  rw [yrotM_sb]
  generalize (Real.cos t : ℂ) = c at h1 e1 e2 ⊢
  generalize (Real.sin t : ℂ) = sn at h1 e1 e2 ⊢
  generalize ((s : ℤ) : ℂ) = z at hs es ⊢
  refine ⟨?_, ?_⟩
  · simp only [InG]
    rw [sb_ct, sb_JJ, sb_mul, sb_mul]
    apply sb_congr <;> simp only [star_mul', star_neg, e1, e2, es] <;>
      first | ring1 | linear_combination h1 + sn * sn * hs | linear_combination -(h1 + sn * sn * hs)
  · rw [sb_ct, sb_mul, sb_one]
    apply sb_congr <;> simp only [star_mul', star_neg, e1, e2, es] <;>
      first | ring1 | linear_combination h1 + sn * sn * hs | linear_combination -(h1 + sn * sn * hs)

theorem sgn_sq (s : ℤˣ) : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or s with h | h <;> simp [h]

theorem det_yrotM_ne (n : ℕ) (s : ℤˣ) (t : ℝ) : (yrotM n s t).det ≠ 0 := by
  have h := congrArg Matrix.det (yrotM_mul' n s t (-t))
  rw [add_neg_cancel, yrotM_zero', det_mul, det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem rot_unit (s : ℤˣ) (t : ℝ) (a : ℂ) (ha : a = 1 ∨ a = -1) :
    ((Real.cos t : ℂ) + a * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) ≠ 0 := by
  intro h0
  have h1 := cs1 t
  have hs := sgn_sq s
  have ha2 : a * a = 1 := by rcases ha with rfl | rfl <;> ring
  have hp : ((Real.cos t : ℂ) + a * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) *
      ((Real.cos t : ℂ) - a * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) = 1 := by
    linear_combination h1 + (Real.sin t : ℂ) * Real.sin t * hs -
      ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) * (Real.sin t : ℂ) * Real.sin t * Complex.I_mul_I +
      ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) * (Real.sin t : ℂ) * Real.sin t * Complex.I * Complex.I * ha2 * (-1)
  rw [h0, zero_mul] at hp
  exact zero_ne_one hp

theorem weight_factor_rotation_ne_zero (p q : ℕ) (e : ℤ) (n : ℕ) (s : ℤˣ) (t : ℝ) : F0 p q e (yrot n s t) ≠ 0 := by
  have hu1 : u1 (yrotM n s t) = ((Real.cos t : ℂ) + (-1) * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) • 1 := by
    rw [u1, yrotM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_smul, ← add_smul]
    congr 1
    ring
  have hu2 : u2 (yrotM n s t) = ((Real.cos t : ℂ) + 1 * Complex.I * (((s : ℤ) : ℂ) * Real.sin t)) • 1 := by
    rw [u2, yrotM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_smul, ← neg_smul, ← add_smul]
    congr 1
    ring
  simp only [F0, f0, mR_yrot]
  refine mul_ne_zero (zpow_ne_zero _ (det_yrotM_ne n s t)) (mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_))
  · rw [hu1, det_smul, det_one, mul_one]
    exact pow_ne_zero _ (rot_unit s t _ (Or.inr rfl))
  · rw [hu2, det_smul, det_one, mul_one]
    exact pow_ne_zero _ (rot_unit s t _ (Or.inl rfl))

variable {d : SD σ}

theorem om_place (hT : TAll) (hLO : LocOpEx) (hLI : LocInst) (R : RD d) (w : InfinitePlace F) :
    ∃ (p q : ℕ) (e : ℤ), ∀ y : GR d.n, InK (mR y) → ∀ g ∈ SB (Yf d), ∀ Ω ∈ d.sch, d.T Ω = vac R g →
      d.om (R.ι w y) Ω = F0 p q e y • Ω := by
  obtain ⟨L, hL⟩ := hLO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, -, hLk⟩ := hLI F E σ d R w L hL
  refine ⟨p, q, e, fun y hy g hg Ω hΩ hTΩ => ?_⟩
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g (fun k => (d.crd X k).2)
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have hvt : d.T Ω = R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    rw [hTΩ]
    funext X
    simp only [vac, gau, RD.tens, fin, Ψ]
    rw [← Finset.mul_prod_erase Finset.univ (fun w' => fP (1 : PX d.m d.n) (R.loc w' X)) (Finset.mem_univ w), mul_assoc]
    rfl
  have h1 := (hL y (fP (1 : PX d.m d.n)) (KFock.isSw_fP 1)).2 Ψ (KFock.away_inv R w Ψ hΨ) Ω hΩ hvt
  rw [hLk y 1 hy, hLD.kvac y hy] at h1
  have hfP : fP (F0 p q e y • (1 : PX d.m d.n)) = F0 p q e y • fP (1 : PX d.m d.n) := by
    funext u
    simp only [fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring
  have htens : R.tens w (F0 p q e y • fP (1 : PX d.m d.n)) Ψ = F0 p q e y • R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    funext X
    simp only [RD.tens, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfP, htens, ← hvt, ← KFock.T_smul] at h1
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  exact KFock.T_inj hT.1 d (hS.pres _ Ω hΩ) (d.sch.smul_mem _ hΩ) h1

theorem om_rot_vac' (hT : TAll) (hLO : LocOpEx) (hLI : LocInst) (R : RD d) (t : ℝ) :
    ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (Yf d), ∀ Ω ∈ d.sch, d.T Ω = vac R g → d.om (rot R t) Ω = χ • Ω := by
  have key : ∀ l : List (InfinitePlace F), ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (Yf d), ∀ Ω ∈ d.sch, d.T Ω = vac R g →
      d.om ((l.map fun w => R.ι w (yrot d.n (R.sg w) t)).prod) Ω = χ • Ω := by
    intro l
    induction l with
    | nil => exact ⟨1, one_ne_zero, fun g _ Ω _ _ => by simp⟩
    | cons w l ih =>
      obtain ⟨χ, hχ, h⟩ := ih
      obtain ⟨p, q, e, hw⟩ := om_place hT hLO hLI R w
      refine ⟨F0 p q e (yrot d.n (R.sg w) t) * χ, mul_ne_zero (weight_factor_rotation_ne_zero p q e d.n (R.sg w) t) hχ,
        fun g hg Ω hΩ hTΩ => ?_⟩
      have hK : InK (mR (yrot d.n (R.sg w) t)) := by rw [mR_yrot]; exact inK_yrotM' _ _ _
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, h g hg Ω hΩ hTΩ, map_smul,
        hw _ hK g hg Ω hΩ hTΩ, smul_smul, mul_comm]
  exact key _

end PositivityTheory.SiegelWeilFormula.KFP

end
end

