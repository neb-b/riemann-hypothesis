module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisLineDiffF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAEF : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAEF : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_AF (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add (f := _), LinearMap.map_add (f := _), ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem map_trace_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (p : R →ₐ[F] R')
    (y : R ⊗[F] E) :
    p (Algebra.trace R (R ⊗[F] E) y) =
      Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) y) := by
  have h1 : ∀ (S : Type) [CommRing S] [Algebra F S] (r : S) (x : E),
      Algebra.trace S (S ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F S (Algebra.trace F E x) := by
    intro S _ _ r x
    have h1 : Algebra.trace S (S ⊗[F] E) ((1 : S) ⊗ₜ[F] x) = algebraMap F S (Algebra.trace F E x) := by
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    have h2 : r ⊗ₜ[F] x = r • ((1 : S) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2, LinearMap.map_smul, h1, smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h1, h1, map_mul, AlgHom.commutes]
  | add y y' hy hy' => simp only [map_add (f := _), hy, hy']

theorem finPartF_sigR (σ : E →ₐ[F] E) (z : AEF F E) :
    finPartF F E (sigR (AF F) σ z) = sigR (Af F) σ (finPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

theorem sndA_symplOHF (ξ₀ : E) (w y : WOF F E nS nT) (hy : y.map (finPartF F E) = 0) :
    sndA F (symplOHF σ JS JT ξ₀ w y) = 0 := by
  have hk : ∀ a b c d, finPartF F E (incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * w d a) = 0 := by
    intro a b c d
    have h0 : finPartF F E (y c b) = 0 := congrFun (congrFun hy c) b
    rw [map_mul, map_mul, map_mul, finPartF_sigR, h0, map_zero, mul_zero, zero_mul, zero_mul]
  have hh : finPartF F E (hOF σ JS JT w y) = 0 := by
    unfold hOF
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hk, Finset.sum_const_zero]
  unfold symplOHF symplOF
  rw [map_mul, map_trace_tens]
  have e : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (incAF F E ξ₀ * hOF σ JS JT w y) =
      finPartF F E (incAF F E ξ₀ * hOF σ JS JT w y) := rfl
  rw [e, map_mul, hh, mul_zero, map_zero, mul_zero]

theorem symplOHF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOHF_zero_right (ξ₀ : E) (x : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x 0 = 0 := by
  have := symplOHF_add_right σ JS JT ξ₀ x 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem continuous_symplOHF (ξ₀ : E) (w : WOF F E nS nT) {X : Type} [TopologicalSpace X] {y : X → WOF F E nS nT}
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ₀ w (y t) := by
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    (continuous_sigR_AF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hh : Continuous fun t => hOF σ JS JT w (y t) :=
    continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul continuous_const
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

theorem exists_log {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStdCharF tauE ψ (-1)) :
    ∃ lam : AF F →+ ℂ, Continuous lam ∧ ∀ a, sndA F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (fstA F a ⊗ₜ[F] (1 : E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finsetSum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA F a)
    have e : pairA F (fstA F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

end GlobalTheory.HeisLineDiffF


open Formalism.IndefR.DatumF in
theorem GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, DifferentiableAt ℝ (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log hψ
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun x y => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)
  let L' : (Fin 1 → ℝ) →+ WOF F E nS nT := L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
  have hL' : Continuous L' := hL.comp (continuous_apply 0)
  have hsm := hf.smooth 1 L' hL' (fun x => hL0 (x 0)) w
  have hg : ContDiff ℝ ∞ fun t : ℝ => f (w + L' (fun _ => t)) :=
    hsm.comp (contDiff_pi.2 fun _ => contDiff_id)
  have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f w) =
      fun t : ℝ => Complex.exp (φ t) * f (w + L' (fun _ => t)) := by
    funext t
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w (L t) (hL0 t))]
    rfl
  rw [e]
  have hd1 : DifferentiableAt ℝ (fun t : ℝ => Complex.exp (φ t)) 0 :=
    ((φ.toRealLinearMap hφ).differentiableAt).cexp
  exact hd1.mul ((hg.differentiable (by simp)) 0)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DblSchr

open Matrix GlobalTheory.Doubling

theorem dblGram_xi : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ξ • incM D.host.F (GlobalTheory.DblSchr.JBd S JB) = incM D.host.F (D.host.xi0 • (GlobalTheory.Doubling.dblSp S).gram⁻¹) := by
  intro D S JB ξ h
  have hinv : (dblSp S).gram⁻¹ = blkMat finSumFinEquiv S.gram⁻¹ (-S.gram⁻¹) :=
    Matrix.inv_eq_left_inv (by
      rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram S).2.isUnit, blkMat_one])
  rw [hinv, incM_JBd]
  ext i j
  have hij : ∀ a b, ξ * incM D.host.F JB a b = incM D.host.F (D.host.xi0 • S.gram⁻¹) a b := fun a b => by
    rw [← h]; rfl
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [blkMat, GlobalTheory.WeilM.dbl, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, Matrix.smul_apply, Matrix.submatrix_apply, h1, h2,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, map_zero, smul_neg, map_neg, smul_eq_mul, mul_zero, mul_neg] at hij ⊢
  · exact hij i' j'
  · exact congrArg Neg.neg (hij i' j')

end GlobalTheory.DblSchr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceSplittingConstantHalfRealPlaces
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.DConst

theorem Jm_diag' (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem Jm_mul_self' (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_diag', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases a <;> simp

theorem card_eq_of_isFrame {β : Type} [Fintype β] [DecidableEq β] {r s : ℕ} {M : Matrix β β ℂ}
    {C : Matrix β (Ix r s) ℂ} (h : IsFrame M C) : Fintype.card β = r + s := by
  obtain ⟨h1, C', h2⟩ := h
  apply le_antisymm
  · have := Matrix.rank_mul_le_left C C'
    rw [h2, Matrix.rank_one] at this
    have h3 := Matrix.rank_le_card_width C
    simp only [Fintype.card_sum, Fintype.card_fin] at h3
    simpa using this.trans h3
  · have e : (Jm r s * Cᵀ * M) * C.map star = 1 := by
      rw [Matrix.mul_assoc (Jm r s * Cᵀ), Matrix.mul_assoc, ← Matrix.mul_assoc Cᵀ, h1, Jm_mul_self']
    have := Matrix.rank_mul_le_right (Jm r s * Cᵀ * M) (C.map star)
    rw [e, Matrix.rank_one] at this
    have h3 := Matrix.rank_le_card_height (C.map star)
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    exact this.trans h3

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (w : ι)
    (L : Module.End ℂ V) (f : ι → V) :
    atPl (V := fun _ => V) w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem cd_eq_half_exp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ)
    (cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) JA (dbl JB) dd χ (diagCols β) omd → HasExp τ χ m →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x)) →
    (∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 →
    0 < R + S → ∀ w, cd w = m w / 2 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB dd a b A C Φd omd χ m cd hCM hψ hFr hWS hχ hAct hl hne hpos w₀
  obtain ⟨l, hladm, hlinv, g, hg, hlint⟩ := hl
  obtain ⟨z, γ, hγ, hgen, hγz, hzat, hzpi⟩ :=
    GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace F E σ (β ⊕ β) (R + S) (S + R) τ (dbl JB) (fun w => dblM (C w)) w₀ hCM
  have hcard : Fintype.card β = R + S := card_eq_of_isFrame (hFr.2.2 w₀)
  have hzz : ∀ t, (z t : AE F E) * cA σ (z t : AE F E) = 1 := by
    intro t
    have h0 := GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero F E σ hCM τ
      ((z t : AE F E) * cA σ (z t : AE F E) - 1) ?_ ?_
    · exact sub_eq_zero.mp h0
    · intro u hu
      have h1 := hzat t u hu
      have e : (z t : AE F E) * cA σ (z t : AE F E) - 1 =
          ((z t : AE F E) - 1) * cA σ (z t : AE F E) + cA σ ((z t : AE F E) - 1) := by
        rw [map_sub, map_one]; ring
      rw [e, smul_add, ← smul_mul_assoc, h1, zero_mul, ← map_smul, h1, map_zero, add_zero]
    · intro w
      rw [map_sub, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, hzpi, map_one]
      split_ifs
      · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
      · simp
  have hχz : ∀ t : ℝ, (χ (z t) : ℂ) = Complex.exp (((m w₀ : ℂ) * Complex.I) * t) := by
    intro t
    rw [hχ (z t) (hzat t), Finset.prod_eq_single w₀]
    · rw [hzpi, if_pos rfl, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
      congr 1; ring
    · intro w _ hw
      rw [hzpi, if_neg hw]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  let tt : ℝ → GL β (AE F E) := fun t =>
    Units.map (Matrix.scalar β : AE F E →+* Matrix β β (AE F E)).toMonoidHom (z t)
  have htt : ∀ t, ((tt t : GL β (AE F E)) : Matrix β β (AE F E)) = (z t : AE F E) • 1 := by
    intro t; simp [tt, Matrix.smul_one_eq_diagonal]
  have hdet : ∀ t, Matrix.GeneralLinearGroup.det (tt t) = z t ^ Fintype.card β := by
    intro t; ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, htt, Matrix.det_smul, Matrix.det_one, mul_one,
      Units.val_pow_eq_pow_val]
  set φ : (κ ⊕ κ → AF F) → ℂ := pureA F (Φd (PiTensorProduct.tprod ℂ fun _ => 1)) g with hφdef
  have hφ : φ ∈ (adeleClass F).sp (κ ⊕ κ) := Submodule.subset_span ⟨_, g, hg, rfl⟩
  set L := ∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x) with hL
  have hlφ : l φ = L := hlint _
  set c₀ : ℂ := ((m w₀ : ℂ) * ((R + S : ℕ) : ℂ)) * Complex.I with hc₀
  have hval : ∀ t : ℝ, l (omd (γ (Multiplicative.ofAdd t)) φ) = L * Complex.exp (c₀ * t) := by
    intro t
    have hp : (((γ (Multiplicative.ofAdd t) : UG (cA σ) (dbl JB)) : GL (β ⊕ β) (AE F E)) :
        Matrix (β ⊕ β) (β ⊕ β) (AE F E)) * (diagCols β : Matrix (β ⊕ β) β (AE F E)) =
        (diagCols β : Matrix (β ⊕ β) β (AE F E)) * ((tt t : GL β (AE F E)) : Matrix β β (AE F E)) := by
      erw [hγz t]
      rw [htt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    have hmod : Units.map (Algebra.norm (AF F) : AE F E →* AF F) (z t ^ Fintype.card β) = 1 := by
      ext; simp [GlobalTheory.T.norm_extensionAdeles_eq_one_of_mul_conj_eq_one F E σ hCM _ (hzz t)]
    rw [hWS.2.2 l hladm hlinv _ (tt t) hp φ hφ, hdet, hmod, map_one, map_pow, hlφ]
    simp only [NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one]
    rw [show ((χ (z t) ^ Fintype.card β : Circle) : ℂ) = (χ (z t) : ℂ) ^ Fintype.card β from by simp, hχz, ← Complex.exp_nat_mul, hcard, mul_comm]
    congr 1; rw [hc₀]; push_cast; ring_nf
  have hder1 : HasDerivAt (fun t : ℝ => l (omd (γ (Multiplicative.ofAdd t)) φ)) (L * c₀) 0 := by
    have h1 : HasDerivAt (fun y : ℂ => L * Complex.exp (c₀ * y)) (L * (Complex.exp (c₀ * ((0 : ℝ) : ℂ)) * (c₀ * 1)))
        ((0 : ℝ) : ℂ) := (((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul c₀).cexp).const_mul L
    have h2 := h1.comp_ofReal
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)
  have hd := hAct γ hγ _ hgen (PiTensorProduct.tprod ℂ fun _ => 1) g hg l hladm
  have huniq := hd.unique hder1
  have hsum : ∑ c : Ix (R + S) (S + R), Complex.I * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c = 0 := by
    simp [Fintype.sum_sum_type]; ring
  have hT : sumPl (fun w => fockAct2 P Q (R + S) (S + R)
        ((fun w => if w = w₀ then Complex.I • (1 : Mat (R + S) (S + R)) else 0) w) +
        (cd w * ((fun w => if w = w₀ then Complex.I • (1 : Mat (R + S) (S + R)) else 0) w).trace) • 1)
        (PiTensorProduct.tprod ℂ fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R))) =
      (cd w₀ * (Complex.I * (((R + S : ℕ) : ℂ) + ((S + R : ℕ) : ℂ)))) •
        PiTensorProduct.tprod ℂ fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) := by
    unfold sumPl
    rw [LinearMap.sum_apply, Finset.sum_eq_single w₀]
    · rw [atPl_tprod]
      simp only [↓reduceIte]
      have hf : (fockAct2 P Q (R + S) (S + R) (Complex.I • (1 : Mat (R + S) (S + R))) +
          (cd w₀ * (Complex.I • (1 : Mat (R + S) (S + R))).trace) • 1) (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) =
          (cd w₀ * (Complex.I * (((R + S : ℕ) : ℂ) + ((S + R : ℕ) : ℂ)))) • (1 : Formalism.BasicNotions.TH.Pol P Q (R + S) (S + R)) := by
        rw [LinearMap.add_apply, Matrix.smul_one_eq_diagonal, GlobalTheory.VacuumWeight.fockAct2_diagonal_one, hsum, mul_zero,
          zero_smul, zero_add, ← Matrix.smul_one_eq_diagonal, Matrix.trace_smul, Matrix.trace_one]
        simp [Fintype.card_sum, Fintype.card_fin]
      rw [hf, MultilinearMap.map_update_smul, Function.update_eq_self]
      rfl
    · intro w _ hw
      rw [atPl_tprod]
      simp only [if_neg hw, map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero, LinearMap.zero_apply]
      exact (PiTensorProduct.tprod ℂ).map_update_zero _ _
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hT, map_smul, hlint] at huniq
  simp only [SchwartzMap.smul_apply, smul_eq_mul] at huniq
  rw [MeasureTheory.integral_const_mul, ← hL] at huniq
  have hRS : ((R + S : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hfin : (cd w₀ - (m w₀ : ℂ) / 2) * (2 * Complex.I * ((R + S : ℕ) : ℂ) * L) = 0 := by
    rw [hc₀] at huniq
    push_cast at huniq hRS ⊢
    linear_combination huniq
  have hne' : 2 * Complex.I * ((R + S : ℕ) : ℂ) * L ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hRS) hne
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfin).resolve_right hne')

end GlobalTheory.RealLift.DConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_X_sub_C' (μ : ℂ) : (X - C μ : ℂ[X]).reverse = 1 - C μ * X := by
  have h1 : (1 : ℂ[X]).reverse = 1 := by simp only [reverse, natDegree_one, reflect_one, pow_zero]
  have hX : (X : ℂ[X]).reverse = 1 := by simpa [h1] using reverse_X_mul (1 : ℂ[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, neg_mul, ← sub_eq_add_neg]

theorem prod_conj_reverse (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    (((s.map fun z => X - C z).prod).map (starRingEnd ℂ)).reverse =
      C (conj (((s.map fun z => X - C z).prod).coeff 0)) * (s.map fun z => X - C z).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    have hs' : ∀ z ∈ s, ‖z‖ = 1 := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have ha : ‖a‖ = 1 := hs a (Multiset.mem_cons_self a s)
    have hca : conj a * a = 1 := by
      rw [Complex.conj_mul', ha]; simp
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, reverse_mul_of_domain, ih hs',
      mul_coeff_zero]
    have hlin : ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse = C (-conj a) * (X - C a) := by
      rw [Polynomial.map_sub, map_X, map_C, reverse_X_sub_C']
      have hw : C (conj a) * C a = (1 : ℂ[X]) := by rw [← C_mul, hca, C_1]
      rw [C_neg]
      linear_combination (-1 : ℂ[X]) * hw
    have hc0 : (X - C a : ℂ[X]).coeff 0 = -a := by simp
    rw [hlin, hc0, map_mul, C_mul]
    simp only [map_neg]
    ring

end GlobalTheory.ConjSelfRecip

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_map_inj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem ell_conj_selfRecip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ C (IsCMField.complexConj E (P.coeff 0)) * P =
      (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  intro E _ _ _ n P hP
  obtain ⟨hm, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := Classical.choice inferInstance
  have hQm : (P.map τ).Monic := hm.map τ
  have hQ : ((P.map τ).roots.map fun z => X - C z).prod = P.map τ :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm IsAlgClosed.card_roots_eq_natDegree
  have hr : ∀ z ∈ (P.map τ).roots, ‖z‖ = 1 := hroots τ
  have key := prod_conj_reverse (P.map τ).roots hr
  rw [hQ] at key
  constructor
  · intro h0
    have h0' : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots hQm.ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hr 0 h0'
    simp at this
  · apply Polynomial.map_injective τ τ.injective
    have hcomp : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ := by
      ext x
      simp [IsCMField.complexEmbedding_complexConj]
    rw [Polynomial.map_mul, map_C, ← reverse_map_inj τ τ.injective, Polynomial.map_map, hcomp,
      ← Polynomial.map_map, key, coeff_map]
    congr 2
    simp [IsCMField.complexEmbedding_complexConj]

end GlobalTheory.ConjSelfRecip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesOrthonormalJStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_orthonormal_J : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (InfinitePlace F → Mat R S), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) ∧ ∀ w (M M' : Mat R S), C w * M = C w * M' → M = M' := by
  first | exact @GlobalTheory.RealLiftComp.exists_comp | exact GlobalTheory.RealLiftComp.exists_comp | (intros; apply GlobalTheory.RealLiftComp.exists_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesPlacewiseSigStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_placewise_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) ∧ ∀ w (M M' : Mat (R w) (S w)), C w * M = C w * M' → M = M' := by
  first | exact @GlobalTheory.RealLiftCompD.exists_compD | exact GlobalTheory.RealLiftCompD.exists_compD | (intros; apply GlobalTheory.RealLiftCompD.exists_compD <;> assumption)
end

