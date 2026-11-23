module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KapXLineDec

variable {D : D7}

theorem pre_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1 ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have h0 : (u.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (u.1.1).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := u.2
  show ((reindex e.symm e.symm u.1.1).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram * reindex e.symm e.symm u.1.1 =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize u.1.1 = M at h0 ⊢
  clear u
  subst hJ
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h0
  have h1 := congrArg (fun A => incA D D.host.xi0⁻¹ • A) h0
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at h1
  have h2 := congrArg (fun A => Aᵀ.submatrix e e) h1
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e.symm e.symm := rfl
  simp only [transpose_mul, transpose_transpose, e1] at h2
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e.symm e.symm).submatrix e e := by simp
  have e3 : ((reindex e.symm e.symm M).map (cA D))ᵀ = ((M.map (cA D))ᵀ).submatrix e e := rfl
  rw [e2, e3, reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
  exact h2

def pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GA D X :=
  ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1, pre_mem X e hJ u⟩

theorem kapX_pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : kapX X e hJ (pre X e hJ u) = u := by
  apply Subtype.ext
  apply Units.ext
  show reindex e e (reindex e.symm e.symm u.1.1) = u.1.1
  simp

theorem pre_mul (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u v : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    pre X e hJ (u * v) = pre X e hJ u * pre X e hJ v := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom (u.1 * v.1) =
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1 *
      Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom v.1
  exact map_mul _ _ _

theorem continuous_pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : Continuous (pre X e hJ) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_reindex e.symm e.symm
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_reindex e.symm e.symm

theorem pre_mem_GinfC (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) {u : UA D.sp.cm.sig Wd.J}
    (hu : u ∈ UAt D.sp.cm.sig Wd (evI D.host.F)) : pre X e hJ u ∈ GinfC X := by
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  show (Formalism.L2.Theta.mt X (pre X e hJ u)).map (finPart D) = 1
  ext i j
  have h1 : At (evI D.host.F) (mat u (e i) (e j) - (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j)) :=
    fun w hw => congrFun (congrFun (hu w hw) (e i)) (e j)
  have h2 := GlobalTheory.ConjInfExp.finPart_eq_one (mat u (e i) (e j) - (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) + 1)
    (by rwa [add_sub_cancel_right])
  rw [RingHom.map_add (f := _), RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at h2
  show finPart D (mat u (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
  rw [h2]
  by_cases c : i = j
  · subst c; simp
  · have c' : e i ≠ e j := fun k => c (e.injective k)
    simp [Matrix.one_apply_ne c, Matrix.one_apply_ne c']

theorem lie_of {n : Type} [Fintype n] [DecidableEq n] (G Y : Matrix n n ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * G * NormedSpace.exp (t • Y) = G) : Yᴴ * G + G * Y = 0 := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have e1 : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ = NormedSpace.exp (t • Yᴴ) := fun t => by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have h1 := ((hasDerivAt_exp_smul_const (Yᴴ) (0:ℝ)).mul_const G).mul (hasDerivAt_exp_smul_const Y (0:ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  have hc : ((fun y : ℝ => NormedSpace.exp (y • Yᴴ) * G) * fun u : ℝ => NormedSpace.exp (u • Y)) = fun _ => G :=
    funext fun t => by
      show NormedSpace.exp (t • Yᴴ) * G * NormedSpace.exp (t • Y) = G
      rw [← e1]; exact h t
  have h2 : HasDerivAt (fun _ : ℝ => G) (Yᴴ * G * 1 + G * Y) 0 :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun hc t).symm)
  have h3 := h2.unique (hasDerivAt_const (0:ℝ) G)
  simpa only [mul_one] using h3

end GlobalTheory.KapXLineDec


open GlobalTheory.KapXLineDec in
theorem GlobalTheory.KapXLineDec.line_dec : ∀ (D : D7) (θ : InfFam D) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ), IsInfFam θ →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod) := by
  intro D θ X d e Wd hJ hθ γ hγ
  classical
  let h : ℝ → GA D X := fun t => pre X e hJ (γ (Multiplicative.ofAdd t))
  have hc : Continuous h := (continuous_pre X e hJ).comp (hγ.1.comp continuous_ofAdd)
  have hadd : ∀ s t, h (s + t) = h s * h t := fun s t => by
    show pre X e hJ (γ (Multiplicative.ofAdd (s + t))) = _
    rw [ofAdd_add, map_mul, pre_mul]
  have h0 : h 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hfin : ∀ t, h t ∈ GinfC X := fun t => pre_mem_GinfC X e Wd hJ (hγ.2 _)
  let N : D.what₂.Tau → ℝ → Matrix (Fin X.rank) (Fin X.rank) ℂ := fun τ t => infMat D.sp.cm.sig X.gram (θ τ) (h t)
  have hNc : ∀ τ, Continuous (N τ) := fun τ => (GlobalTheory.Mem.VolExists.continuous_infMat X.gram (hθ τ)).comp hc
  have hN0 : ∀ τ, N τ 0 = 1 := fun τ => by
    show infMat D.sp.cm.sig X.gram (θ τ) (h 0) = 1
    rw [h0]; exact GlobalTheory.PointAtPlaceHom.infMat_one X _
  have hNm : ∀ τ s t, N τ (s + t) = N τ s * N τ t := fun τ s t => by
    show infMat D.sp.cm.sig X.gram (θ τ) (h (s + t)) = _
    rw [hadd]; exact GlobalTheory.PointAtPlaceHom.infMat_mul X _ _ _
  choose Y hY using fun τ => GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous (N τ) (hNc τ) (hN0 τ) (hNm τ)
  have hYl : ∀ τ, Y τ ∈ lieAt X τ := fun τ =>
    lie_of _ _ fun t => (hY τ t) ▸ GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ X (h t) τ
  let L : List D.what₂.Tau := (Finset.univ : Finset D.what₂.Tau).toList
  refine ⟨L.map fun τ => (τ, Y τ), ?_, fun t => ?_⟩
  · intro q hq
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hq
    exact hYl τ
  · have hP : ((L.map fun τ => (τ, Y τ)).map fun q => oneP θ X q.1 q.2 t).prod = h t := by
      refine GlobalTheory.RowReal.IsRealAll.unique hθ (M := fun τ => N τ t) ⟨?_, fun σ => ?_⟩ ⟨hfin t, fun σ => rfl⟩
      · refine Subgroup.list_prod_mem (GinfC X) fun x hx => ?_
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hq
        exact (GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hYl τ) t).1
      · have e1 : GlobalTheory.RowReal.infMatHom X (θ σ) ((L.map fun τ => (τ, Y τ)).map fun q => oneP θ X q.1 q.2 t).prod =
            (L.map fun ρ => if ρ = σ then N σ t else 1).prod := by
          rw [map_list_prod, List.map_map, List.map_map]
          congr 1
          refine List.map_congr_left fun ρ _ => ?_
          show infMat D.sp.cm.sig X.gram (θ σ) (oneP θ X ρ (Y ρ) t) = _
          have hs := GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hYl ρ) t
          by_cases hρ : ρ = σ
          · subst hρ
            rw [if_pos rfl]
            exact hs.2.1.trans (hY ρ t).symm
          · rw [if_neg hρ]
            exact hs.2.2 σ (Ne.symm hρ)
        exact e1.trans (GlobalTheory.RowReal.list_prod_map_ite _ _ L (Finset.nodup_toList _)
          (Finset.mem_toList.2 (Finset.mem_univ _)))
    rw [hP]
    exact (kapX_pre X e hJ _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section RatPart

variable {L ι : Type} [Field L] (σ : L →+* ℂ)

def ratPart (φ : ℂ → L) (w : ℂ) (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ k ∈ P.support, σ (φ (w * P.coeff k)) • MvPolynomial.monomial k 1

variable {σ}

theorem ratPart_rat {ℓ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ} {Ω : ℂ} (h : ∀ k, ∃ z : L, ℓ (MvPolynomial.monomial k 1) = Ω * σ z)
    (φ : ℂ → L) (w : ℂ) (P : MvPolynomial ι ℂ) : ∃ z : L, ℓ (ratPart σ φ w P) = Ω * σ z := by
  choose z hz using h
  refine ⟨∑ k ∈ P.support, φ (w * P.coeff k) * z k, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ratPart, map_sum, map_smul, hz, map_mul, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratPart_eq {ℓ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ} {Ω : ℂ} (h : ∀ k, ∃ z : L, ℓ (MvPolynomial.monomial k 1) = Ω * σ z)
    (φ : ℂ →+ L) (hφ : ∀ x y, φ (x * σ y) = φ x * y) (w : ℂ) (P : MvPolynomial ι ℂ) :
    ℓ (ratPart σ φ (w * Ω) P) = Ω * σ (φ (w * ℓ P)) := by
  choose z hz using h
  have e : ℓ P = ∑ k ∈ P.support, P.coeff k * (Ω * σ (z k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [P.as_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hz, ← smul_eq_mul, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ratPart, map_sum, map_smul, hz, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show w * (P.coeff k * (Ω * σ (z k))) = (w * Ω * P.coeff k) * σ (z k) by ring, hφ, σ.map_mul]
  ring

theorem exists_dual {x : ℂ} (hx : x ≠ 0) : ∃ φ : ℂ →+ L, (∀ a y, φ (a * σ y) = φ a * y) ∧ φ x ≠ 0 := by
  letI : Algebra L ℂ := σ.toAlgebra
  obtain ⟨φ, hφ⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff L x).1 hx)
  refine ⟨φ.toAddMonoidHom, fun a y => ?_, hφ⟩
  have : a * σ y = y • a := by rw [Algebra.smul_def, mul_comm]; rfl
  show φ (a * σ y) = φ a * y
  rw [this, map_smul, smul_eq_mul, mul_comm]

end RatPart

variable {D : D7}

section Bottom

variable {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem Factor.ratIn {L : Type} [Field L] {σ : L →+* ℂ} {lam : T → ℂ} (h : Factor X ψ θ lam) (hr : X.RationalSums ψ θ σ)
    (hi' : ∀ t P g, IntegrableOn (X.ker' ψ θ t P g) X.fd' X.m')
    (hz : ∀ t P P' (a b : ℂ), (∀ g ∈ GfC WW, a * X.I ψ θ t P g - b * X.I' ψ θ t P' g = 0) →
      ∀ g, a * X.I ψ θ t P g - b * X.I' ψ θ t P' g = 0) (t₀ : T) : RatIn σ t₀ lam := by
  obtain ⟨h0, Pi, p, p', J, hs, hJ, -, hI, hI', P', hP', -⟩ := h
  obtain ⟨Ω, Ω', hΩ, hΩ', H⟩ := hr
  obtain ⟨P, hP⟩ := hs (p' P')
  have hI'' : ∀ t Q, X.I' ψ θ t Q = J t (p' Q) := fun t Q => hI' t Q (hi' t Q)
  let ℓ : T → GA D WW → (PolF D WW.rank A.rank →ₗ[ℂ] ℂ) := fun t g => lam t • (LinearMap.proj g ∘ₗ J t ∘ₗ p)
  let ℓ' : T → GA D WW → (PolF D WW.rank A'.rank →ₗ[ℂ] ℂ) := fun t g => LinearMap.proj g ∘ₗ J t ∘ₗ p'
  have hℓ : ∀ t g Q, ℓ t g Q = X.I ψ θ t Q g := fun t g Q => by rw [hI]; rfl
  have hℓ' : ∀ t g Q, ℓ' t g Q = X.I' ψ θ t Q g := fun t g Q => by rw [hI'']; rfl
  have r : ∀ t, ∀ g ∈ GfC WW, ∀ k, ∃ z : L, ℓ t g (MvPolynomial.monomial k 1) = Ω * σ z := fun t g hg k => by
    rw [hℓ]; exact ((H t g hg).1 k).2
  have r' : ∀ t, ∀ g ∈ GfC WW, ∀ k, ∃ z : L, ℓ' t g (MvPolynomial.monomial k 1) = Ω' * σ z := fun t g hg k => by
    rw [hℓ']; exact ((H t g hg).2 k).2
  have sep : ∀ t Q Q' (a b : ℂ), (∀ g ∈ GfC WW, a * ℓ t g Q - b * ℓ' t g Q' = 0) → (a * lam t) • p Q = b • p' Q' :=
    fun t Q Q' a b hh => hJ t (funext fun g => by
      have := hz t Q Q' a b (fun g hg => by rw [← hℓ, ← hℓ']; exact hh g hg) g
      rw [hI, hI''] at this
      simp only [map_smul, _root_.Pi.smul_apply, smul_eq_mul] at this ⊢
      linear_combination this)
  have nz : ∀ t Q', p' Q' ≠ 0 → ∃ g ∈ GfC WW, ℓ' t g Q' ≠ 0 := fun t Q' hQ => by
    by_contra hc
    push Not at hc
    have := sep t P Q' 0 1 fun g hg => by rw [hc g hg]; simp
    exact hQ (by simpa using this.symm)
  obtain ⟨g₀, hg₀, hn₀⟩ := nz t₀ P' hP'
  obtain ⟨φ, hφ, hφ0⟩ := exists_dual (σ := σ) hn₀
  have e0 : ∀ g, (lam t₀)⁻¹ * ℓ t₀ g P = 1 * ℓ' t₀ g P' := fun g => by
    show (lam t₀)⁻¹ * (lam t₀ * J t₀ (p P) g) = 1 * J t₀ (p' P') g
    rw [hP, inv_mul_cancel_left₀ (h0 _), one_mul]
  set Q := ratPart σ φ ((lam t₀)⁻¹ * Ω) P
  set Q' := ratPart σ φ (1 * Ω') P'
  have e1 : (Ω' * lam t₀) • p Q = Ω • p' Q' := sep t₀ Q Q' Ω' Ω fun g hg => by
    rw [ratPart_eq (r t₀ g hg) φ hφ, ratPart_eq (r' t₀ g hg) φ hφ, e0]; ring
  have hQ' : p' Q' ≠ 0 := fun hh => by
    have h1 : ℓ' t₀ g₀ Q' = 0 := by
      show J t₀ (p' Q') g₀ = 0
      rw [hh, map_zero]; rfl
    rw [ratPart_eq (r' t₀ g₀ hg₀) φ hφ, one_mul] at h1
    exact mul_ne_zero hΩ' ((map_ne_zero σ).2 hφ0) h1
  intro t
  refine ⟨h0 t, ?_⟩
  obtain ⟨g, hg, hn⟩ := nz t Q' hQ'
  obtain ⟨z, hz1⟩ := ratPart_rat (r t g hg) φ ((lam t₀)⁻¹ * Ω) P
  obtain ⟨z', hz2⟩ := ratPart_rat (r' t g hg) φ (1 * Ω') P'
  have e2 : Ω' * lam t₀ * ℓ t g Q = lam t * Ω * ℓ' t g Q' := by
    have := congrArg (fun x => J t x g) e1
    simp only [map_smul, _root_.Pi.smul_apply, smul_eq_mul] at this
    show Ω' * lam t₀ * (lam t * J t (p Q) g) = lam t * Ω * J t (p' Q') g
    linear_combination lam t * this
  have hz' : σ z' ≠ 0 := fun hh => hn (hz2.trans (by rw [hh, mul_zero]))
  have e3 : σ (z / z') = lam t / lam t₀ := by
    rw [show ℓ t g Q = _ from hz1, show ℓ' t g Q' = _ from hz2] at e2
    have := h0 t₀
    rw [map_div₀]
    field_simp
    have e4 : Ω * Ω' * (σ z * lam t₀ - lam t * σ z') = 0 := by linear_combination e2
    have := (mul_eq_zero.1 e4).resolve_left (mul_ne_zero hΩ hΩ')
    linear_combination this
  have hne : z / z' ≠ 0 := fun hh => div_ne_zero (h0 t) (h0 t₀) (by rw [← e3, hh, map_zero])
  exact ⟨Units.mk0 _ hne, e3⟩

theorem ideal_ne_bot (X : Tri T A A' WW) (S : T → Finset (Pl D.host.E)) (t : T) : X.ideal S t ≠ ⊥ :=
  Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

variable {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}

theorem theta_f (h : X.Is ψ θ α β νH S) (t : T) : IsThetaFunO ψ (neg A) WW (X.f t) ∧ IsThetaFunO ψ A' WW (X.f' t) := by
  have hν : IsHeckeChar D (α t / β t) := (h.weil' t).hecT
  obtain ⟨f, h1, h2⟩ := _root_.GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW _ _ _ _ _ h.rigA h.rigW hν (h.idem t) (ideal_ne_bot X S t) h.isVac
  obtain ⟨f', h1', h2'⟩ := _root_.GlobalTheory.CompanionTheory.StdSndTheta.exists_theta D ψ θ A' WW X.rA' X.rW _ _ _ _ A.rank _ h.rigA' h.rigW hν (h.idem t) (ideal_ne_bot X S t) h.isVac'
  obtain ⟨Tm, hT⟩ := h1.1
  obtain ⟨Tm', hT'⟩ := h1'.1
  exact ⟨((h.fst t).2 Tm hT).trans (h1.2 Tm hT).symm ▸ h2, ((h.snd t).2 Tm' hT').trans (h1'.2 Tm' hT').symm ▸ h2'⟩

theorem ratIn_of_definite {L : Type} [Field L] {σ : L →+* ℂ} {lam : T → ℂ} (h : X.Is ψ θ α β νH S)
    (hA : ∀ τ, (gramAt D A τ).PosDef) (hA' : ∀ τ, (gramAt D A' τ).PosDef) (hW : ∀ τ, (gramAt D WW τ).PosDef)
    (hF : Factor X ψ θ lam) (hr : X.RationalSums ψ θ σ) (t₀ : T) : RatIn σ t₀ lam := by
  have c := fun t P => _root_.GlobalTheory.DefSourceInt.theta_integral_source_definite D ψ true A WW _ _ (X.ω t) X.m X.fd _ (h.weil t) hA h.meas.1 h.meas.2
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B (theta_f h t).1 P)
  have c' := fun t P => _root_.GlobalTheory.DefSourceInt.theta_integral_source_definite D ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (h.weil' t) hA' h.meas'.1 h.meas'.2
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO h.isVac.1 h.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B (theta_f h t).2 P)
  refine hF.ratIn hr (fun t P g => (c' t P).1 g) (fun t P P' a b => ?_) t₀
  refine _root_.GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic D WW (fun g => a * X.I ψ θ t P g - b * X.I' ψ θ t P' g) hW
    ((continuous_const.mul (c t P).2.1).sub (continuous_const.mul (c' t P').2.1)) fun γ hγ g => ?_
  exact congrArg₂ (fun u v => a * u - b * v) ((c t P).2.2 γ hγ g) ((c' t P').2.2 γ hγ g)

theorem posDef_of_std {V : HSp D} {r : Rig V} (h : r.IsStd) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]; exact Matrix.PosDef.one

end Bottom

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks} {F : Face D Fam} {G : GridPre R}

theorem exists_expAt (χ : Formalism.L2.Host.HChar D.host.E) (w : Pl D.host.E) : ∃ n, GlobalTheory.CMVal.ExpAt χ w n := by
  classical
  have h := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  refine ⟨Nat.find h, fun m => ⟨fun hm => Nat.find_min' h hm, fun hm x hx hx' => Nat.find_spec h x hx (hx'.trans ?_)⟩⟩
  rw [WithZero.exp_le_exp]
  omega

theorem exists_meas (V : HSp D) : ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓕, inferInstance, h⟩

theorem exists_isWeil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) (ε : Bool)
    (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW) (h3 : ResEta D χS S.rank)
    (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := _root_.GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (sgn ε S) W χS χW hη h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩

end GlobalTheory.ConstRatio

end
end

