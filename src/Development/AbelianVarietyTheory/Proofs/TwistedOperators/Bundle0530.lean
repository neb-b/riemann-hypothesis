module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarmonicColumnOperatorEndMemOfUnitaryStable
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumSmulMemOfSumZpowSmulMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledLatticeCompletionSupportedInvIdealSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LatMulAt

variable {D : D7}

theorem exists_int_of_mem_inv {I : GlobalTheory.SeeSaw.FI D} {a t : D.host.E} (ha : a ∈ I) (ht : t ∈ I⁻¹) :
    ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = t * a := by
  have h1 : t * a ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul ht ha
  rw [FractionalIdeal.inv_eq, mul_comm] at h1
  exact (FractionalIdeal.mem_one_iff _).1 (FractionalIdeal.mul_one_div_le_one h1)

theorem gen_mul (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F)
    (hαv : ∀ w, ¬ w = v → evalV D.host.F w α = 0) (hβv : ∀ w, w ≠ v → evalV D.host.F w β = 0)
    {a t : D.host.E} (ha : a ∈ I) (ht : t ∈ I⁻¹) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    (pairA D.host.F 0 β ⊗ₜ[D.host.F] t) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) ∈
      latV S L (· = v) := by
  obtain ⟨r, hr⟩ := exists_int_of_mem_inv ha ht
  refine AddSubgroup.subset_closure ⟨β * α, ?_, ?_, 1, rfl, r • x, L.smul_mem r hx, ?_⟩
  · intro w
    rw [map_mul]
    exact mul_mem (hβ w) (hα w)
  · intro w hw
    rw [map_mul, hβv w hw, zero_mul]
  · funext i
    rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, Pi.smul_apply,
      Algebra.smul_def, hr, one_mul, mul_assoc]

theorem latMul_inv_smul : ∀ {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (y : Fin S.rank → AE D), y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ I} L (· = v) → (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ GlobalTheory.SeeSaw.idV I⁻¹ v, s • y ∈ latV S L (· = v) := by
  intro D S L I v y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
    refine ⟨fun i => GlobalTheory.FinPlLoc.pair_mem_idAt _ α hαv _, fun s hs => ?_⟩
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ, hβv, t, ht, rfl⟩ := hs
      exact gen_mul S L I v hα hβ hαv hβv ha ht hx
    | zero => rw [zero_smul]; exact zero_mem _
    | add s s' _ _ h h' => rw [add_smul]; exact add_mem h h'
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    exact ⟨fun i => add_mem (hy.1 i) (hz.1 i), fun s hs => by rw [smul_add]; exact add_mem (hy.2 s hs) (hz.2 s hs)⟩
  | neg y _ hy =>
    exact ⟨fun i => neg_mem (hy.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (hy.2 s hs)⟩

end GlobalTheory.LatMulAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOriented
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ) (T.gram.map (incA D)))
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a
      = ∑ b, ∑ d, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem trace_mul_submatrix {A : Type} [CommRing A] {m d : ℕ} (e : Fin m ≃ Fin d) (P : Matrix (Fin d) (Fin d) A)
    (K : Matrix (Fin m) (Fin m) A) : (P * K.submatrix e.symm e.symm).trace = (P.submatrix e e * K).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  simp

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun _ _ => S.herm.eq _ _

theorem gram_map_herm (S : HSp D) : ((S.gram.map (incA D)).map (cA D))ᵀ = S.gram.map (incA D) := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem gram_inv_mul (T : HSp D) : T.gram⁻¹.map (incA D) * T.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne _))]; simp

theorem hTens_eq_trace' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (c' : A →+* A)
    (hc : ∀ a, c a = c' a) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) : GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c' * JBᵀ).trace := by
  rw [hTens_eq_trace]
  congr 3
  ext i j
  exact hc _

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sgn_gram (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]


set_option maxHeartbeats 1000000 in
theorem symp_eq (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (JV : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (JW : Matrix (Fin d) (Fin d) D.host.E)
    (hJ : JV = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : JW = D.host.xi0 • reindex e e X.gramᵀ)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) → WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (u w : Matrix (Fin S.rank) (Fin d) (AE D)) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW) u w = symplO (sgn ε S) X (cS u) (cS w) := by
  have hGs : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = (sgn ε S).gram.map (incA D) := by
    rw [← sgn_gram]; rfl
  have hJA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV = -(sgn ε S).gram.map (incA D) := by
    rw [hJ, sgn_gram]
    cases ε <;> ext i j <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hJB : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW)ᵀ =
      incA D D.host.xi0 • (X.gram.map (incA D)).submatrix e.symm e.symm := by
    rw [hJW]; ext i j; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  unfold GlobalTheory.WeilM.symp symplO
  rw [hTens_eq_trace' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (cA D) (fun _ => rfl), hO_eq_trace, hcS, hcS, hGs, hJA, hJB]
  have hinv := gram_inv_mul (sgn ε S)
  have hh := gram_map_herm (sgn ε S)
  have hW : ((wᵀ.submatrix e id).map (cA D))ᵀ = (w.map (cA D)).submatrix id e := rfl
  congr 1
  rw [Matrix.map_mul, Matrix.transpose_mul, hh, ← Matrix.mul_assoc _ _ (((wᵀ.submatrix e id).map (cA D))ᵀ), hinv,
    Matrix.one_mul, hW]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.trace_neg,
    smul_eq_mul, trace_mul_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  rw [Matrix.mul_assoc (uᵀ.submatrix e id * _), Matrix.trace_mul_comm (uᵀ.submatrix e id * _)]
  ring

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem invOf_two' {D : D7} : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem isDatum_rho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ), IsDatum M ψ cS Φ f →
        ∀ w : Matrix (Fin S.rank) (Fin d) (AE D), IsDatum M ψ cS (M.co.rho ψ w Φ) (heisO ψ (sgn ε S) X (cS w) f) := by
  intro D ψ θ _ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW _ _ _ M _ cS hcS Φ f hD w
  refine ⟨?_, fun u => ?_⟩
  · have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
    exact GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd w Φ hD.1
  · rw [GlobalTheory.BigDat.rho_rho M.co ψ u w Φ, GlobalTheory.WeilM.thetaSum_smul, hD.2 (u + w)]
    unfold heisO symplOH
    rw [symp_eq ε S X e Vs.J Ws.J hJ hJW cS hcS u w, map_add (f := _), invOf_two']

end GlobalTheory.SquareAgree.HeisCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddings
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CMNorm

theorem sqrt_absNorm_le_prod_tauE : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  intro D 𝔪 u hu hu0
  have hnorm : ∏ τ, ‖tauE D τ (u : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (GlobalTheory.LevelSeries.mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (GlobalTheory.LevelSeries.mk_tauE_complex D τ)]
    rfl
  have hspan : Ideal.span {u} ≤ 𝔪 := (Ideal.span_singleton_le_iff_mem _).2 hu
  have hne : Ideal.absNorm (Ideal.span {u}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hu0
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  have hle : Ideal.absNorm 𝔪 ≤ Ideal.absNorm (Ideal.span {u}) := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have habs : ((Ideal.absNorm (Ideal.span {u}) : ℕ) : ℝ) = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton]
    rw [← Algebra.coe_norm_int]
    push_cast
    simp
  have hle' : ((Ideal.absNorm 𝔪 : ℕ) : ℝ) ≤ (∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2 := by
    rw [← Finset.prod_pow, hnorm, ← habs]; exact_mod_cast hle
  calc Real.sqrt (Ideal.absNorm 𝔪) ≤ Real.sqrt ((∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2) := Real.sqrt_le_sqrt hle'
    _ = ∏ τ, ‖tauE D τ (u : D.host.E)‖ := Real.sqrt_sq (Finset.prod_nonneg fun τ _ => norm_nonneg _)

end GlobalTheory.CMNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StableFockSpanContainsRowHighestPolynomials
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.StableFock

theorem revB_isB : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B₀ : C.Bas), C.IsB B₀ → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ := by
  intro D S T C B₀ hB₀
  let σ : Equiv.Perm (Fin T.rank) := Function.Involutive.toPerm (revPos C.X.p0) (revPos_revPos C.X.p0)
  have hσ : ∀ τ, revB C.X.p0 B₀ τ = (B₀ τ).submatrix id σ := fun τ => rfl
  have hsg : ∀ a : Fin T.rank, sgn C.X.p0 ((σ a : Fin T.rank) : ℕ) = sgn C.X.p0 (a : ℕ) := by
    intro a
    show sgn C.X.p0 ((revPos C.X.p0 a : Fin T.rank) : ℕ) = _
    unfold revPos
    split_ifs with h
    · simp only [sgn, if_pos h.1, if_pos (show C.X.p0 - 1 - (a : ℕ) < C.X.p0 by omega)]
    · rfl
  have hD : (sgnM C.X).submatrix σ σ = sgnM C.X := by
    unfold sgnM
    rw [Matrix.submatrix_diagonal _ _ σ.injective]
    congr 1
    funext a
    simp only [Function.comp_apply, hsg]
  have hD' : ∀ M : Matrix (Fin T.rank) (Fin T.rank) ℂ, M.submatrix id σ * sgnM C.X = (M * sgnM C.X).submatrix id σ := by
    intro M
    ext i j
    simp only [sgnM, Matrix.mul_diagonal, Matrix.submatrix_apply, id, hsg]
  refine ⟨fun τ => ?_, funext fun τ => ?_⟩
  · rw [hσ, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_id_id (gramAt D T τ),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hB₀ τ, hD]
  · show (revB C.X.p0 B₀ τ) * sgnM C.X * (revB C.X.p0 B₀ τ)⁻¹ = B₀ τ * sgnM C.X * (B₀ τ)⁻¹
    rw [hσ, hD', show (B₀ τ).submatrix id σ = (B₀ τ).submatrix (Equiv.refl _) σ from rfl,
      Matrix.inv_submatrix_equiv, show (B₀ τ * sgnM C.X).submatrix id σ = (B₀ τ * sgnM C.X).submatrix (Equiv.refl _) σ from rfl,
      Matrix.submatrix_mul_equiv]
    rfl

theorem pureTensorO_revB : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B₀ : C.Bas), C.IsB B₀ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), C.IsTh f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS (revB C.X.p0 B₀) f (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P) := by
  intro D S T C B₀ hB₀ BS f hf P
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := by
    intro τ
    have e : gramAt D S τ = 1 := by simp [gramAt, C.m.gS]
    rw [e]
    refine ⟨by simp, by simp, ?_⟩
    simpa using Matrix.PosDef.one
  have hT := fun τ => (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B₀ hB₀).2.2.1 τ).1
  have := GlobalTheory.OneMapRef.IoCmp.pureTensorO_rename C.std C.inf hS hT hf BS B₀ (revB C.X.p0 B₀)
    (fun _ => revPos C.X.p0) (fun τ => rfl) (fun v : FVar D T.rank S.rank => v.1)
    (fun v => revPos C.X.p0 v.2.1) (fun v => v.2.2) P
  simp only [revPos_revPos] at this
  rw [← this]
  have e : (MvPolynomial.rename fun k : FVar D T.rank S.rank => (k.1, k.2.1, k.2.2)) P = P := by
    change MvPolynomial.rename id P = P
    exact MvPolynomial.rename_id_apply P
  rw [e]

theorem pureTensorO_source : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∃ u : C.X.Ψ → GL (Fin S.rank) ℂ, (∀ σ, (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom u (C.toH Q) → ∀ B, C.IsB B → ∀ f, C.IsTh f → pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q = C.fvec B f Q' := by
  intro D S T C BS hBS
  obtain ⟨h, -, hh⟩ := _root_.GlobalTheory.StdRealLift.exists_real_point D S T C BS hBS
  obtain ⟨u, hu, -, hcol⟩ := GlobalTheory.Ker.ColChange.col_change D S T C h
  refine ⟨u, hu, fun Q Q' hQ B hB f hf => ?_⟩
  have := hcol Q Q' hQ B hB f hf
  rwa [show (fun τ => compAt C.θ τ (mt S h)) = BS from funext hh] at this

theorem colU_surjective : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (u : C.X.Ψ → GL (Fin S.rank) ℂ), (∀ σ, (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∃ h ∈ GinfC S, GlobalTheory.Ker.ColChange.colU C h = u := by
  intro D S T C u hu
  have hv : ∀ τ, ((u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj)ᴴ *
      (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj = 1 := by
    intro τ
    have hA := (Matrix.mem_unitaryGroup_iff').1 (hu (C.m.e τ))
    have e : ((u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj)ᴴ *
        (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj =
        (star (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ) *
          (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ)).map conj := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, Matrix.star_eq_conjTranspose]
    rw [e, hA]
    ext i j
    simp [Matrix.one_apply]
  obtain ⟨h, hh, hcomp⟩ := _root_.GlobalTheory.StdRealLift.exists_real_point D S T C _ hv
  refine ⟨h, hh, funext fun σ => Units.ext ?_⟩
  show (compAt C.θ (C.m.e.symm σ) (mt S h)).map conj = (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ)
  rw [hcomp]
  ext i j
  simp

theorem fockSpan_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → T.rank ≤ S.rank → ∀ B₀, C.IsB B₀ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∀ f, C.IsTh f → C.IsFock B₀ f → f ≠ 0 → ∀ (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ = C.X.p0) → (∀ τ, q τ = C.q0) → ∀ (pt : MvPolynomial (FVar D T.rank S.rank) ℂ → WO S T → ℂ) (U : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ)), (∀ P, pt P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P) → Formalism.IndefR.Datum.delta p q ap am ∈ U → (∀ h ∈ GinfC S, ∀ P ∈ U, ∃ P' ∈ U, om (h, 1) (pt P) = pt P') → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ ∧ ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q₀ : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q₀ ∈ Harm.rowHighest ℂ c c' ∧ C.fvec (revB C.X.p0 B₀) f Q₀ = pt (Formalism.IndefR.Datum.delta p q ap am) ∧ pt (Formalism.IndefR.Datum.delta p q ap am) ≠ 0 ∧ ∀ Q, C.toH Q ∈ Harm.rowHighest ℂ c c' → ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
  intro D S T C om hom hrk B₀ hB₀ BS hBS f hf hF hf0 p q ap am hp hq pt U hpt hΔ hU
  obtain ⟨hB, hsB⟩ := revB_isB D S T C B₀ hB₀
  refine ⟨hB, hsB, ?_⟩
  have hFB : C.IsFock (revB C.X.p0 B₀) f := by
    intro τ
    rw [hsB]
    exact hF τ
  obtain ⟨u₀, -, hcol⟩ := pureTensorO_source D S T C BS hBS
  have hinj := C.toH_bijective.1
  have hsurj := C.toH_bijective.2
  have hpt' : ∀ P, ∃ Q, C.toH Q = Harm.colActHom u₀ (C.toH (MvPolynomial.rename
      (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P)) ∧
      C.fvec (revB C.X.p0 B₀) f Q = pt P := by
    intro P
    obtain ⟨Q, hQ⟩ := hsurj (Harm.colActHom u₀ (C.toH (MvPolynomial.rename
      (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P)))
    refine ⟨Q, hQ, ?_⟩
    rw [hpt, pureTensorO_revB D S T C B₀ hB₀ BS f hf P]
    have := hcol _ _ hQ (revB C.X.p0 B₀) hB f hf
    rw [hsB] at this
    exact this.symm
  obtain rfl : p = fun _ => C.X.p0 := funext hp
  obtain rfl : q = fun _ => C.q0 := funext hq
  obtain ⟨c, c', hc, hc0⟩ := GlobalTheory.T.reversedMinorProduct_mem_harmonicRowHighest D S T C hrk ap am
  obtain ⟨Q₀, hQ₀, hQ₀pt⟩ := hpt' (Formalism.IndefR.Datum.delta (fun _ => C.X.p0) (fun _ => C.q0) ap am)
  have hQ₀mem : C.toH Q₀ ∈ Harm.rowHighest ℂ c c' := by
    rw [hQ₀]
    exact Harm.colAct_mem_rowHighest u₀ hc
  have hQ₀ne : C.toH Q₀ ≠ 0 := by
    rw [hQ₀]
    intro h
    apply hc0
    apply (Harm.colAct ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) u₀).injective
    rw [map_zero]
    exact h
  have hfv0 : C.fvec (revB C.X.p0 B₀) f 0 = 0 := by
    unfold Ctx.fvec
    exact map_zero _
  have hptne : pt (Formalism.IndefR.Datum.delta (fun _ => C.X.p0) (fun _ => C.q0) ap am) ≠ 0 := by
    rw [← hQ₀pt]
    intro h
    have := _root_.GlobalTheory.FockPolyInj.fvec_injective D S T C _ hB f hf hFB hf0 (h.trans hfv0.symm)
    exact hQ₀ne (by rw [this, map_zero])
  refine ⟨c, c', Q₀, hQ₀mem, hQ₀pt, hptne, ?_⟩

  set L₁ := pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (revB C.X.p0 B₀)) (fun _ => 1) (revB C.X.p0 B₀) f
    with hL₁
  set L₂ := pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f with hL₂
  have hfv : ∀ Q, C.fvec (revB C.X.p0 B₀) f Q = L₁ Q := fun Q => rfl
  let V : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ) := (U.map L₂).comap L₁
  have hV : ∀ Q, Q ∈ V ↔ ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
    intro Q
    simp only [V, Submodule.mem_comap, Submodule.mem_map, hfv, hpt]
    exact ⟨fun ⟨P, hP, e⟩ => ⟨P, hP, e.symm⟩, fun ⟨P, hP, e⟩ => ⟨P, hP, e.symm⟩⟩
  let W : Submodule ℂ (Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) :=
    V.map C.toH.toLinearMap ⊓ Harm.rowHighest ℂ c c'
  have hW : ∀ w, w ∈ W ↔ (∃ Q ∈ V, C.toH Q = w) ∧ w ∈ Harm.rowHighest ℂ c c' := by
    intro w
    simp [W, Submodule.mem_inf, Submodule.mem_map]
  have hWst : ∀ g : C.X.Ψ → GL (Fin S.rank) ℂ,
      (∀ t, (g t : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) →
      ∀ w ∈ W, Harm.colActHom g w ∈ W := by
    intro g hg w hw
    obtain ⟨⟨Q, hQV, rfl⟩, hwR⟩ := (hW w).1 hw
    refine (hW _).2 ⟨?_, Harm.colAct_mem_rowHighest g hwR⟩
    obtain ⟨Q', hQ'⟩ := hsurj (Harm.colActHom g (C.toH Q))
    refine ⟨Q', ?_, hQ'⟩
    obtain ⟨h, hh, rfl⟩ := colU_surjective D S T C g hg
    obtain ⟨a, ha, hact⟩ := _root_.GlobalTheory.Ker.RealColAct.om_real_fvec D S T C om hom _ hB f hf hFB h hh
    obtain ⟨P, hPU, hP⟩ := (hV Q).1 hQV
    obtain ⟨P', hP'U, hP'⟩ := hU h hh P hPU
    refine (hV Q').2 ⟨a⁻¹ • P', U.smul_mem _ hP'U, ?_⟩
    have e1 := hact Q Q' hQ'
    rw [hP, hP'] at e1
    rw [hpt, map_smul, ← hpt, e1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hle : W ≤ Harm.rowHighest ℂ c c' := inf_le_right
  have hLie := _root_.GlobalTheory.Harm.colLie_mem_of_unitary_stable W hWst
  have hWne : W ≠ ⊥ := by
    intro h
    have : C.toH Q₀ ∈ W := (hW _).2 ⟨⟨Q₀, (hV Q₀).2 ⟨_, hΔ, hQ₀pt⟩, rfl⟩, hQ₀mem⟩
    rw [h, Submodule.mem_bot] at this
    exact hQ₀ne this
  have hn : C.q0 + C.X.p0 ≤ S.rank := by have := C.hr; omega
  have hbase := Harm.basePoly_mem_of_colLie_stable hn c c' W hle hLie hWne
  have hword : ∀ w, Harm.colWord ℂ hn c c' w ∈ W := by
    intro w
    induction w with
    | nil => exact hbase
    | cons i w ih => exact hLie i.1 i.2.1 i.2.2 _ ih
  have hall : Harm.rowHighest ℂ c c' ≤ W :=
    (Harm.rowHighest_le_span_colWord_complex hn c c').trans
      (Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact hword w))
  intro Q hQ
  obtain ⟨⟨Q₁, hQ₁, e⟩, -⟩ := (hW _).1 (hall hQ)
  obtain rfl := hinj e
  exact (hV Q₁).1 hQ₁

end GlobalTheory.AdSpan.StableFock

end
end

