module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGram
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.CartStd

variable {D : D7}

theorem tauE_star_eq (τ : D.what₂.Tau) (x : D.host.E) : tauE D τ (star x) = star (tauE D τ x) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) ℂ) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rfl

theorem stdJ_mul_self (n : ℕ) : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero]
  rw [blk4, show Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℂ) 0 0 (-1) = -1 by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]]
  rw [show ((-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) from rfl,
    Matrix.submatrix_one_equiv]

theorem stdJ_conjTranspose (n : ℕ) :
    (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ)ᴴ = -blk4 0 1 (-1) 0 := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
    show -((Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm) = (-(Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm from rfl, Matrix.fromBlocks_neg]
  simp

theorem map_Jst (τ : D.what₂.Tau) (n : ℕ) : (Jst D n).map (tauE D τ) = blk4 0 1 (-1) 0 := by
  unfold Jst blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  have h1 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
    rw [← RingHom.mapMatrix_apply, map_neg, map_one]
  simp [h1]

end GlobalTheory.CartStd

namespace GlobalTheory.CartStd

theorem isCartanInv_stdInv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ s : RealMat (dblSp A),
    IsStdInv A μ s → ∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (s τ) := by
  intro D A μ hμ s hs τ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  set f := tauE D τ with hf
  set T := (Tm A μ).map f with hT
  set J : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) ℂ := blk4 0 1 (-1) 0 with hJ
  set z := f μ with hz
  have hstar : Function.Semiconj f star star := fun x => tauE_star_eq τ x
  have hTG : Tᴴ * gramAt D (dblSp A) τ * T = z • J := by
    have h := congrArg (fun M => M.map f) hgram
    simp only [Matrix.map_mul] at h
    rw [Matrix.conjTranspose_map f hstar] at h
    rw [show gramAt D (dblSp A) τ = (dblSp A).gram.map f from rfl, h, hJ, ← map_Jst τ A.rank]
    ext i j
    simp [Matrix.smul_apply, hz, hf]
  have hTdet : IsUnit T.det := by
    rw [hT, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map f
  set U := T⁻¹ with hU
  have hTU : T * U = 1 := Matrix.mul_nonsing_inv T hTdet
  have hUT : U * T = 1 := Matrix.nonsing_inv_mul T hTdet
  have hUhTh : Uᴴ * Tᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hTU, Matrix.conjTranspose_one]

  have hz0 : z ≠ 0 := (map_ne_zero f).2 hμ.1
  have hzc : star z = -z := by rw [hz, ← tauE_star_eq, hμ.2, map_neg]
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hzz : z * z = -(((‖z‖ : ℝ) : ℂ) ^ 2) := by
    have h1 := Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, ← Complex.star_def, hzc] at h1
    push_cast at h1
    linear_combination -h1
  set c := z / ((‖z‖ : ℝ) : ℂ) with hc
  have hcc : c * c = -1 := by
    rw [hc]; field_simp; linear_combination hzz
  have hcstar : star c = -c := by
    rw [hc, star_div₀, hzc, Complex.star_def, Complex.conj_ofReal, neg_div]
  have hzc' : z * c = -((‖z‖ : ℝ) : ℂ) := by
    rw [hc]; field_simp; linear_combination hzz

  set S := c • J with hS
  have hJJ : J * J = -1 := stdJ_mul_self _
  have hSS : S * S = 1 := by
    rw [hS, smul_mul_smul_comm, hcc, hJJ, neg_one_smul, neg_neg]
  have hSh : Sᴴ = S := by
    rw [hS, Matrix.conjTranspose_smul, hJ, stdJ_conjTranspose, hcstar, smul_neg, neg_smul, neg_neg]
  have hsS : s τ = T * S * U := by
    have h := hs τ
    rw [show stdInv A.rank μ τ = S from rfl] at h
    calc s τ = s τ * T * U := by rw [Matrix.mul_assoc, hTU, Matrix.mul_one]
      _ = T * S * U := by rw [h]
  have hG : gramAt D (dblSp A) τ = Uᴴ * (z • J) * U := by
    rw [← hTG]
    calc gramAt D (dblSp A) τ = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * U) := by
          rw [hUhTh, hTU, Matrix.one_mul, Matrix.mul_one]
      _ = Uᴴ * (Tᴴ * gramAt D (dblSp A) τ * T) * U := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsS]
    calc T * S * U * (T * S * U) = T * S * (U * T) * S * U := by simp only [Matrix.mul_assoc]
      _ = T * U := by rw [hUT, Matrix.mul_one, Matrix.mul_assoc T S S, hSS, Matrix.mul_one]
      _ = 1 := hTU
  · rw [hsS, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh]
    have hSJS : S * (z • J) * S = z • J := by
      rw [hS, smul_mul_smul_comm, hJJ, smul_mul_smul_comm, Matrix.neg_mul, Matrix.one_mul,
        show c * z * c = -z by linear_combination z * hcc, neg_smul, smul_neg, neg_neg]
    calc Uᴴ * (S * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U)
        = Uᴴ * (S * (Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
      _ = gramAt D (dblSp A) τ := by rw [hTG, hSJS, hG]
  · have hGs : gramAt D (dblSp A) τ * s τ = Uᴴ * (((‖z‖ : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) * U := by
      rw [hsS]
      calc gramAt D (dblSp A) τ * (T * S * U) = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U) := by
            rw [hUhTh, Matrix.one_mul]
        _ = Uᴴ * ((Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hTG, hS, smul_mul_smul_comm, hJJ, hzc', neg_smul, smul_neg, neg_neg]
    rw [hGs]
    have hpos : (0 : ℂ) < ((‖z‖ : ℝ) : ℂ) := Complex.zero_lt_real.2 (norm_pos_iff.2 hz0)
    refine (Matrix.PosDef.one.smul hpos).conjTranspose_mul_mul_same ?_
    intro x y hxy
    have h := congrArg T.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hTU] using h

end GlobalTheory.CartStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrCombAny

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem real_part {S T : HSp D} (x : WO S T) : (GlobalTheory.FinTranslate.eInf D • x : WO S T).map (finPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (x i j)

theorem fin_part {S T : HSp D} (x : WO S T) : ((1 - GlobalTheory.FinTranslate.eInf D) • x : WO S T).map (infPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (x i j)

theorem psi_fin_eq {S T : HSp D} {w : WO S T} (hw : w.map (infPart D) = 0) (x : WO S T) :
    ψ (symplOH S T w x) = ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) := by
  have hx : x = GlobalTheory.FinTranslate.eInf D • x + (1 - GlobalTheory.FinTranslate.eInf D) • x := by
    rw [← add_smul, add_sub_cancel, one_smul]
  conv_lhs => rw [hx]
  rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_fin_real hw (real_part x), zero_add]

theorem exists_orth_any {S T : HSp D} (hψ : IsStdChar D ψ (-1)) (s : Finset (WO S T)) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ w ∈ U, w.map (infPart D) = 0 → ∀ x ∈ s, ψ (symplOH S T w x) = 1 := by
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∀ x ∈ s, ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1}
      zero_mem' := fun x _ => by rw [GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb x hx => by
        rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
      neg_mem' := fun {a} ha x hx => by
        have := AddChar.map_add_eq_mul ψ (symplOH S T a ((1 - GlobalTheory.FinTranslate.eInf D) • x))
          (symplOH S T (-a) ((1 - GlobalTheory.FinTranslate.eInf D) • x))
        rw [← GlobalTheory.FinTranslate.symplOH_add_left, add_neg_cancel, GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one,
          ha x hx, one_mul] at this
        exact this.symm }
  refine ⟨U, ?_, fun w hw hw' x hx => (psi_fin_eq hw' x).trans (hw x hx)⟩
  have e : (U : Set (WO S T)) = ⋂ x ∈ s, {w | ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1} := by
    ext w
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  exact isOpen_biInter_finset fun x _ => GlobalTheory.FrComb.isOpen_ker hψ (fin_part x)

theorem contDiff_psi {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {n : ℕ} {L : (Fin n → ℝ) →+ WO S T} (hL : Continuous L)
    (hLf : ∀ t, (L t).map (finPart D) = 0) (x : WO S T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => ψ (symplOH S T (L t) x) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  let φ : (Fin n → ℝ) →+ ℂ :=
    { toFun := fun t => lam (symplOH S T (L t) x)
      map_zero' := by rw [map_zero L, GlobalTheory.FinTranslate.symplOH_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L, GlobalTheory.FinTranslate.symplOH_add_left, map_add (f := _)] }
  have hφ := GlobalTheory.WeilVacMove.contDiff_additive φ (hl.comp ((GlobalTheory.FinTranslate.continuous_symplOH S T x).comp hL))
  have e : (fun t => ψ (symplOH S T (L t) x)) = fun t => Complex.exp (φ t) :=
    funext fun t => hlam _ (GlobalTheory.WeilVacMove.snd_symplOH S T (L t) x (Or.inl (hLf t)))
  rw [e]
  exact hφ.cexp

theorem biTheta_combL {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => K u' v) u) := by
  have e : (fun u v => comb ψ A S c (fun u' => K u' v) u) =
      fun u v => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * K (u + x) v) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ u
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH A S x).comp continuous_fst)).mul
        (hK.cont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S (u + L t) x) * K (u + L t + x) (v + L' t))) =
        fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * (ψ (symplOH A S (L t) x) * K (u + x + L t) (v + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL hLf x).mul (hK.smooth n L L' hL hL' hLf hL'f (u + x) v)))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, hK.quasiL, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH A S (ratW S A γ) x + symplOH A S u x) * ψ (-(symplOH A S (ratW S A γ) u + symplOH A S (ratW S A γ) x)) =
        ψ (-(symplOH A S (ratW S A γ) u)) * ψ (symplOH A S u x) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c x * K (u + x) v) * key
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hK.quasiR]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' v)
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    refine ⟨U, hU, fun a ha ha' u => ?_⟩
    funext v
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e3 := congrFun (hUf a ha ha' (u + x)) v
    simp only [heisO] at e3
    rw [← e3]
    ring

theorem biTheta_combR {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (K u) v) := by
  have e : (fun u v => comb ψ S A' c (K u) v) =
      fun u v => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * K u (v + y)) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ v
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finsetSum _ fun y _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH S A' y).comp continuous_snd)).mul
        (hK.cont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' (v + L' t) y) * K (u + L t) (v + L' t + y))) =
        fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * (ψ (symplOH S A' (L' t) y) * K (u + L t) (v + y + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm v, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun y _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL' hL'f y).mul (hK.smooth n L L' hL hL' hLf hL'f u (v + y))))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hK.quasiL]
    ring
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [add_assoc, hK.quasiR, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH S A' (ratW A' S γ) y + symplOH S A' v y) * ψ (-(symplOH S A' (ratW A' S γ) v + symplOH S A' (ratW A' S γ) y)) =
        ψ (-(symplOH S A' (ratW A' S γ) v)) * ψ (symplOH S A' v y) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c y * K u (v + y)) * key
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    refine ⟨U, hU, fun a ha ha' v => ?_⟩
    funext u
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e3 := congrFun (hUf a ha ha' (v + y)) u
    simp only [heisO] at e3
    rw [← e3]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' u)

theorem biTheta_biComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (C : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' C → ∀ (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ), IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) := by
  intro D ψ hψ A S A' C hC c c'
  exact biTheta_combL hψ (biTheta_combR hψ hC c') c

end GlobalTheory.FrCombAny

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRealSSmulTwoSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Scale

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T →₀ ℂ) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T a (c • f) = c • comb ψ S T a f := by
  simp only [comb, heisO_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S →₀ ℂ) (a' : WO S A' →₀ ℂ) (c : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' a a' (c • C) = c • biComb ψ A S A' a a' C := by
  funext u v
  simp only [biComb]
  have h1 : (fun u' => comb ψ S A' a' ((c • C) u') v) = c • fun u' => comb ψ S A' a' (C u') v := by
    funext u'
    show comb ψ S A' a' (c • C u') v = c * comb ψ S A' a' (C u') v
    rw [comb_smul]; rfl
  rw [h1, comb_smul]; rfl

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul, hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem isLatVac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) : IsLatVac (heisO ψ S T) Λ (c • f) :=
  ⟨fun u hu => by rw [heisO_smul, hf.1 u hu], fun e' he u hu hh => by rw [heisO_smul, hf.2 e' he u hu hh]⟩

theorem isBiVac_smul {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {LA : Set (Fin A.rank → D.host.E)}
    {LS : Set (Fin S.rank → D.host.E)} {LA' : Set (Fin A'.rank → D.host.E)} (c : ℂ) {C : WO A S → WO S A' → ℂ}
    (h : IsBiVac ψ A S A' LA LS LA' C) : IsBiVac ψ A S A' LA LS LA' (c • C) := by
  refine ⟨continuous_const.mul h.cont, ?_, ?_⟩
  · intro v
    have e : (fun u => (c • C) u v) = c • fun u => C u v := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.left v).1, isLatVac_smul c (h.left v).2⟩
  · intro u
    have e : (c • C) u = c • C u := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.right u).1, isLatVac_smul c (h.right u).2⟩

theorem isBiSmooth_smul {A S A' : HSp D} (c : ℂ) {C : WO A S → WO S A' → ℂ} (h : IsBiSmooth C) :
    IsBiSmooth (c • C) :=
  fun n L L' hL hL' h0 h0' u v => by
    show ContDiff ℝ _ fun t => c * C (u + L t) (v + L' t)
    exact ContDiff.mul contDiff_const (h n L L' hL hL' h0 h0' u v)

end GlobalTheory.SeeSaw.Scale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KeepLatticeHyperbolicEmbedding
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.EmbLevel

open Formalism.UG

section Ring

variable {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {φ : A →+* B}

theorem cT_map (hφ : ∀ x, φ (σ x) = τ (φ x)) {m p : Type} (M : Matrix m p A) :
    (cT σ M).map φ = cT τ (M.map φ) := by
  funext i j
  exact hφ (M j i)

theorem conj_mem_iff {n : ℕ} (b g : GL (Fin n) B) :
    b⁻¹ * g * b ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = cT τ (b⁻¹).1 * (b⁻¹).1 := by
  have h1 : b.1 * (b⁻¹).1 = 1 := b.mul_inv
  have h2 : (b⁻¹).1 * b.1 = 1 := b.inv_mul
  have h3 : cT τ (b⁻¹).1 * cT τ b.1 = 1 := by rw [← cT_mul, h1, cT_one]
  have h4 : cT τ b.1 * cT τ (b⁻¹).1 = 1 := by rw [← cT_mul, h2, cT_one]
  change cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = 1 ↔ _
  have e : cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) =
      cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
    simp only [cT_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e]
  generalize cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = X
  constructor
  · intro h
    calc X = (cT τ (b⁻¹).1 * cT τ b.1) * X * (b.1 * (b⁻¹).1) := by rw [h1, h3, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ (b⁻¹).1 * (cT τ b.1 * X * b.1) * (b⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  · rintro rfl
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul, h2]

theorem conj_bc_mem_iff (hφ : ∀ x, φ (σ x) = τ (φ x)) {n : ℕ} (c g : GL (Fin n) A) :
    (bc φ c)⁻¹ * bc φ g * bc φ c ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      (cT σ g.1 * (cT σ (c⁻¹).1 * (c⁻¹).1) * g.1).map φ = (cT σ (c⁻¹).1 * (c⁻¹).1).map φ := by
  rw [conj_mem_iff, ← map_inv]
  simp only [Matrix.map_mul, cT_map hφ]
  rfl

end Ring

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

omit [NumberField E] in
theorem mem_levelAll_iff (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (c : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) : g ∈ levelAll σ J L c ↔
    (∀ v y, y ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1.map (compFin F E v) *ᵥ y ∈ latLoc F L v) ∧
      ∀ w, (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (GlobalTheory.AdelicU.matHom _ σ J g).1 *
          (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * (GlobalTheory.AdelicU.matHom _ σ J g).1).map (compInf F E w) =
        (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1).map (compInf F E w) := by
  refine mem_levelAll.trans (and_congr Iff.rfl (forall_congr' fun w => ?_))
  rw [mem_stabArch, matHom_projArch]
  exact conj_bc_mem_iff (compInf_sigR σ w) c _

end Lattice

variable {D : D7}

end GlobalTheory.RegSch.EmbLevel

end
end

