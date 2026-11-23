module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitary
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FdDom

open ReciprocityTheory.ChartRestriction.G.FD

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [IsCMField E] in
theorem gram_neg_transpose (τ : E →+* ℂ) (H : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ (-Hᵀ) x = (-(xᴴ * H.map τ * x))ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem lminor_transpose (A : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) : lminor Aᵀ i = lminor A i := by
  unfold lminor
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]

theorem map_mem_UH (τ : E →+* ℂ) (H g : Matrix (Fin r) (Fin r) E)
    (hg : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) (g.mulVec x) (g.mulVec y) = ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) x y) :
    g.map τ ∈ Formalism.QuantumDeterminants.UH (H.map τ) := by
  change (g.map τ)ᴴ * H.map τ * g.map τ = H.map τ
  ext b a
  have h := congrArg τ (hg (Pi.single a 1) (Pi.single b 1))
  have hc : ∀ z : E, τ (ReciprocityTheory.ChartRestriction.G.FD.cc z) = starRingEnd ℂ (τ z) := fun z =>
    IsCMField.complexEmbedding_complexConj E τ z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul, hc, Matrix.neg_apply,
    Matrix.transpose_apply, map_neg, Pi.single_apply, apply_ite τ, apply_ite (starRingEnd ℂ), map_one, map_zero,
    ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, RCLike.star_def]
  have h2 : (∑ x, ∑ y, if x = a then if y = b then -τ (H y x) else 0 else 0) = -τ (H b a) := by
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [← neg_inj, ← h2, ← h]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := by
  intro s t h
  apply D.eTau.injective
  apply Subtype.ext
  apply (D.host.gal).symm.injective
  exact AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)

theorem dom_iff_frDoms : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ k, ∃ e : D.what₂.Tau ≃ (X k).Ψ, (∀ ρ, (e ρ).1 = tauE D ρ) ∧ (∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r, x ∈ (X k).dom ↔ (fun ρ a b => x (e ρ) (Fin.cast hr a) (Fin.cast hr b)) ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ))) ∧ ∀ γ ∈ (X k).Γ, ∀ ρ, Matrix.reindex (finCongr hr.symm) (finCongr hr.symm) ((γ : Matrix (Fin r) (Fin r) D.host.E).map (tauE D ρ)) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  intro D θ V S M w r hr Comp X la dict mu c Kf _ hG k
  subst hr
  have hΨ := hG.base.1 k
  have hp := hG.base.2.1 k
  have hGm : (X k).Gm = -V.gramᵀ := (hG.model k).1
  let f : D.what₂.Tau → (X k).Ψ := fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t h => tauE_injective D (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := (hΨ τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext hρ.symm⟩
  refine ⟨Equiv.ofBijective f hf, fun _ => rfl, fun x => ?_, fun γ hγ ρ => ?_⟩
  · change (∀ τ : (X k).Ψ, _) ↔ ∀ ρ, _
    rw [← (Equiv.ofBijective f hf).forall_congr_right]
    refine forall_congr' fun ρ => ?_
    simp only [dmin, hGm, gram_neg_transpose, lminor_transpose, hp ρ]
    rfl
  · have h := ((X k).Γ_stab γ hγ).1
    rw [hGm] at h
    exact map_mem_UH (tauE D ρ) V.gram _ h

end GlobalTheory.HolDict.FdDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.HeisTwist

theorem jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  rw [Jm, Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal]
  simp [Matrix.diagonal_neg]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

theorem jm_mul_mul_jm_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (l : Ln P Q R S) :
    (Complex.I * lineSign l.1 l.2 * c l.1 l.2) • raiB l (1 : Pol P Q R S)
      - (lineSign l.1 l.2 * star (Complex.I * lineSign l.1 l.2 * c l.1 l.2)) • lowB l 1
      = Complex.I • (c l.1 l.2 • raiB l (1 : Pol P Q R S) - (lineSign l.1 l.2 * star (c l.1 l.2)) • lowB l 1) := by
  rcases l with ⟨a | a, b | b⟩ <;>
    simp [raiB, lowB, linePos, lineSign, smul_sub, smul_smul] <;> ring_nf <;> simp [Complex.conj_I] <;> module

end GlobalTheory.HeisTwist

namespace GlobalTheory.RealLift

theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm Complex.I]
  congr 1
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Matrix.smul_apply,
    GlobalTheory.HeisTwist.jm_mul_mul_jm_apply, smul_eq_mul]
  rw [← GlobalTheory.HeisTwist.term_one c l, mul_assoc]

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.RealLift.QuadFock

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPlLin (w : ι) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun _ => LinearMap.id) w

theorem atPlLin_apply (w : ι) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := by
  simp only [atPlLin, MultilinearMap.toLinearMap_apply, PiTensorProduct.mapMultilinear_apply, atPl]

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  rw [← atPlLin_apply, map_zero]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]
    rfl

end Tensor

variable {P Q R S : ℕ}

theorem heisOp_smul (r : ℝ) (c : Matrix (Ix P Q) (Ix R S) ℂ) : heisOp (r • c) = (r : ℂ) • heisOp c := by
  unfold heisOp
  rw [smul_comm (r : ℂ) ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.smul_apply, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, smul_sub, smul_smul]
  congr 2 <;> ring

theorem heisOp_zero : heisOp (0 : Matrix (Ix P Q) (Ix R S) ℂ) = 0 := by
  simpa using heisOp_smul (P := P) (Q := Q) (R := R) (S := S) 0 0

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι) (M : Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w' => heisOp ((Pi.single w M : ι → Matrix (Ix P Q) (Ix R S) ℂ) w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ}

def sgn (a : Ix P Q) (b : Ix R S) : ℝ := (lineSign a b).re

theorem lineSign_eq_sgn (a : Ix P Q) (b : Ix R S) : lineSign a b = ((sgn a b : ℝ) : ℂ) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

theorem sgn_mul_self (a : Ix P Q) (b : Ix R S) : sgn a b * sgn a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single w (Matrix.single a b x)

theorem eS_apply (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (w' : ι) (a' : Ix P Q) (b' : Ix R S) :
    eS w a b x w' a' b' = if w' = w ∧ a' = a ∧ b' = b then x else 0 := by
  by_cases hw : w' = w
  · subst hw
    simp only [eS, Pi.single_eq_same, Matrix.single_apply, true_and]
    by_cases h : a' = a ∧ b' = b
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
  · simp [eS, hw]

theorem sum_eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [eS_apply]
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

theorem decomp (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [eS_apply, and_self, if_true, Complex.real_smul, mul_one]
    exact (Complex.re_add_im _).symm
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def cu (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem dual {l : Type} [Fintype l] (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

theorem cu_true_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, true) w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, false) w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, true) = (Pi.single w (Matrix.single a b Complex.I) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, false) = (Pi.single w (Matrix.single a b (1 : ℂ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem atPlLin_mul {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) (L L' : Module.End ℂ (V w)) :
    atPlLin w (L * L') = atPlLin w L * atPlLin w L' := by
  simp only [atPlLin_apply, atPl_mul]

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

theorem quad_fock : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  intro H1 H2 ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := H1 l (ι × Ix P Q × Ix R S × Bool) Z (fun i => φ (cu i)) (fun i => φ (cv i)) (dual φ hφ)
  have hop : sumPl (V := fun _ : ι => Pol P Q R S) (fun w => fockAct2 P Q R S (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
        (sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) +
          sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ))) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu_true_mul, cu_false_mul, cv_true, cv_false, sumPl_single,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [H2 P Q R S (Y w) (hY w)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add (f := _), atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear H1 H2 hq hop hφ hY
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.RealLift.QuadFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVariableMultiplicationMemSpanHeisenbergOpera
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.MulVarSpan

variable {P Q R S : ℕ}

theorem heisOp_single (l : Ln P Q R S) (a : ℂ) :
    heisOp (Matrix.single l.1 l.2 a) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (a • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star a) • lowB l) := by
  unfold heisOp
  congr 1
  rw [Finset.sum_eq_single l]
  · simp [Matrix.single_apply]
  · intro l' _ hne
    have h : ¬ (l.1 = l'.1 ∧ l.2 = l'.2) := by
      rintro ⟨h1, h2⟩; exact hne (Prod.ext h1.symm h2.symm)
    simp [Matrix.single_apply, h]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem sq_ne (l : Ln P Q R S) : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast this.ne'

theorem lineSign_sq (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  cases a <;> cases b <;> simp [lineSign]

theorem raiB_mem (l : Ln P Q R S) :
    raiB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  have key : (2 * s) • raiB l = heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    generalize lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 = σ
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (2 * s) ≠ 0 := mul_ne_zero two_ne_zero (sq_ne l)
  have : raiB l = (2 * s)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem lowB_mem (l : Ln P Q R S) :
    lowB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  set σ := lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 with hσ
  have hσσ : σ * σ = 1 := lineSign_sq l.1 l.2
  have key : (-2 * s * σ) • lowB l = heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single, ← hσ]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (-2 * s * σ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) (sq_ne l)) ?_
    intro h; rw [h, zero_mul] at hσσ; exact zero_ne_one hσσ
  have : lowB l = (-2 * s * σ)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (add_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem mulX_mem_span : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
    Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  intro P Q R S l
  cases h : linePos l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = lowB l := by simp [lowB, h]
    rw [e]; exact lowB_mem l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = raiB l := by simp [raiB, h]
    rw [e]; exact raiB_mem l

end GlobalTheory.MulVarSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermFormPulledBackCombinationsExpandMonomialsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_form_pulledBack_combinations_expand_monomials : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  first | (exact @GlobalTheory.FormsLocus.germ_eval_comb) | (exact GlobalTheory.FormsLocus.germ_eval_comb) | (intros; apply GlobalTheory.FormsLocus.germ_eval_comb  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIff
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem good_iff_labE_and_lab_conj :
    ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (GoodEmb T.Q.c (res T σ) ↔ labE σ (lab σ ρ) = tauE D ρ) ∧ lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ :=
  fun _ T _ hl ha σ ρ => ⟨GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ, GlobalTheory.ConjReading.lab_conj σ ρ⟩

end GlobalTheory.HolRead
end

