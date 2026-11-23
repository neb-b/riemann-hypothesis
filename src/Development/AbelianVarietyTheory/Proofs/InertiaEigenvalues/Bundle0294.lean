module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocks
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem exists_cols_isUnit {F : Type} [CommRing F] (hF : IsField F) {b n : Type} [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] (X : Matrix b n F) (Z : Matrix n b F) (h : X * Z = 1) :
    ∃ e : b → n, IsUnit (X.submatrix id e) := by
  letI : Field F := hF.toField
  have h1 : X.rank = Fintype.card b := by
    apply le_antisymm (Matrix.rank_le_card_height X)
    have := Matrix.rank_mul_le_left X Z
    rw [h, Matrix.rank_one] at this
    exact this
  have h2 : Module.finrank F (Submodule.span F (Set.range X.col)) = Fintype.card b := by
    rw [← Matrix.rank_eq_finrank_span_cols, h1]
  obtain ⟨κ, e, he, hspan, hli⟩ := exists_linearIndependent' F X.col
  haveI : Finite κ := Finite.of_injective e he
  letI : Fintype κ := Fintype.ofFinite κ
  have h3 : Fintype.card κ = Fintype.card b := by
    rw [← finrank_span_eq_card hli, hspan, h2]
  let τ : b ≃ κ := Fintype.equivOfCardEq h3.symm
  refine ⟨e ∘ τ, ?_⟩
  have h4 : LinearIndependent F (X.submatrix id (e ∘ τ)).col := hli.comp τ τ.injective
  exact Matrix.linearIndependent_cols_iff_isUnit.mp h4

end GlobalTheory.PMon.SubquotientAlgEquiv

end

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem map_mul_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p q s : Type}
    [Fintype q] (M : Matrix p q R) (N : Matrix q s R) : (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : R →+* R))

theorem map_one_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p : Type}
    [DecidableEq p] : (1 : Matrix p p R).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

end GlobalTheory.PMon.SubquotientAlgEquiv

namespace GlobalTheory.PMon

open scoped Matrix


open SubquotientAlgEquiv in
theorem subQuot : SubQuot := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c _ hblk hdr
  have hF := (_root_.GlobalTheory.PMon.bdR_tied l P AI T).1
  have e11 : ∀ m g (i j : a), matD P ρ m g (Sum.inl i) (Sum.inl j) = matD P ρ₁ m g i j := by
    intro m g i j; simp [matD, hblk g]
  have e21 : ∀ m g (i : b) (j : a), matD P ρ m g (Sum.inr i) (Sum.inl j) = 0 := by
    intro m g i j; simp [matD, hblk g]
  have e22 : ∀ m g (i j : b), matD P ρ m g (Sum.inr i) (Sum.inr j) = matD P ρ₂ m g i j := by
    intro m g i j; simp [matD, hblk g]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    have hQiQ : ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.inv_mul Q
    have hinv : ∀ g : ↥(GK K), ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) =
        ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g := by
      intro g
      have hs : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
        rw [← map_mul_algEquiv, hQQi, map_one_algEquiv]
      calc ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))
          = (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQiQ, Matrix.one_mul]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
              (matD P ρ m g * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQ g]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g *
              ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hs, Matrix.mul_one]
    let Y : Matrix (a ⊕ b) a P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inl
    let W : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
    have hWY : W * Y = 1 := by
      rw [show W * Y = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inl Sum.inl from
        (Matrix.submatrix_mul _ _ Sum.inl id Sum.inl Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inl_injective
    have hYW : Yᵀ * Wᵀ = 1 := by rw [← Matrix.transpose_mul, hWY, Matrix.transpose_one]
    obtain ⟨e, he⟩ := exists_cols_isUnit hF Yᵀ Wᵀ hYW
    have hY' : IsUnit (Y.submatrix e id) := by
      have := (Matrix.isUnit_transpose _).2 he
      simpa [Matrix.transpose_submatrix] using this
    have hσY : ∀ g : ↥(GK K), (Y.submatrix e id).map (P.actQdR (g : GQ l)) = Y.submatrix e id * matD P ρ₁ m g := by
      intro g; ext i j
      have := congrFun (congrFun (hinv g) (e i)) (Sum.inl j)
      simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e11, e21, mul_zero,
        Finset.sum_const_zero, add_zero] at this
      simpa [Y, Matrix.mul_apply] using this
    refine ⟨hY'.unit⁻¹, fun g => ?_⟩
    have hu : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) = Y.submatrix e id := hY'.unit_spec
    have hs : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
        ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
      rw [← map_mul_algEquiv, Units.mul_inv, map_one_algEquiv]
    calc matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l))
        = (((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) * ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR)) *
            matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [Units.inv_mul, Matrix.one_mul]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            (((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) * matD P ρ₁ m g) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          simp only [Matrix.mul_assoc]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [hu, hσY g]
      _ = _ := by rw [Matrix.mul_assoc, hs, Matrix.mul_one]
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    let X : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
    let Z : Matrix (a ⊕ b) b P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr
    have hXZ : X * Z = 1 := by
      rw [show X * Z = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inr Sum.inr from
        (Matrix.submatrix_mul _ _ Sum.inr id Sum.inr Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inr_injective
    obtain ⟨e, he⟩ := exists_cols_isUnit hF X Z hXZ
    refine ⟨he.unit, fun g => ?_⟩
    rw [he.unit_spec]
    ext i j
    have := congrFun (congrFun (hQ g) (Sum.inr i)) (e j)
    simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e21, e22, zero_mul,
      Finset.sum_const_zero, zero_add] at this
    simpa [X, Matrix.mul_apply] using this

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamTrivialRationalCocycleRestrictionScalars
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

open Matrix

namespace GlobalTheory.PMon.DRvec

theorem blockDiag_mulVec {R : Type*} [CommRing R] {n o : Type} [Fintype n] [Fintype o] [DecidableEq o]
    (M : o → Matrix n n R) (v : n × o → R) (i : n) (m : o) :
    (Matrix.blockDiagonal M *ᵥ v) (i, m) = (M m *ᵥ fun j => v (j, m)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

theorem kd_q {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  show algebraMap (Om l) P.R.BdR (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)) = _
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem ratCocycle_trivial : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) =
      (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) →
    ∃ β : n × Fin r → P.R.BdR, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
        (fun x => P.actQdR (g : GQ l) (β x)) - β := by
  intro l _ P n _ _ K r σ ρ₀ p c c₀ hp hconj hpc hdr
  choose b hb using hdr
  let pG : GL (n × Fin r) P.R.BdR := Matrix.GeneralLinearGroup.map (kd P) p
  let β' : n × Fin r → P.R.BdR := fun x => b x.2 x.1
  have hinvmul : ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.inv_mul
  have hmulinv : (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.mul_inv
  have hpG : ∀ i j, (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j =
      kd P ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) := fun i j => rfl
  refine ⟨((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ β', fun g => ?_⟩
  set pinv := ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpinv
  set pM := (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpM
  set BD := Matrix.blockDiagonal (fun m : Fin r => matD P σ m g) with hBD
  set R0 := (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR) with hR0

  have hfix : ∀ i j, P.actQdR (g : GQ l) (pinv i j) = pinv i j := by
    let φ : P.R.BdR →+* P.R.BdR := (P.actQdR (g : GQ l)).toAlgHom.toRingHom
    have h1 : Matrix.GeneralLinearGroup.map φ pG = pG := by
      ext i j
      show φ (kd P _) = kd P _
      exact act_kd P g (hp i j)
    have h2 : Matrix.GeneralLinearGroup.map φ pG⁻¹ = pG⁻¹ := by rw [map_inv, h1]
    intro i j
    exact congrArg (fun A : GL (n × Fin r) P.R.BdR => (A : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j) h2
  have hactv : (fun x => P.actQdR (g : GQ l) ((pinv *ᵥ β') x)) = pinv *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) := by
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hfix]

  have hd : pM * R0 = BD * pM := by
    have h1 : pM = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map (kd P) := rfl
    have h2 : R0 = ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).map (kd P) := by
      ext i j; simp [hR0, kd_q]
    have h3 : BD = (Matrix.blockDiagonal fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (kd P) := by
      rw [hBD, Matrix.blockDiagonal_map _ _ (map_zero (kd P))]
      rfl
    rw [h1, h2, h3, ← Matrix.map_mul, ← Matrix.map_mul, hconj g]
  have hR : R0 * pinv = pinv * BD := by
    calc R0 * pinv = pinv * (pM * R0) * pinv := by rw [← Matrix.mul_assoc, hinvmul, Matrix.one_mul]
    _ = pinv * (BD * pM) * pinv := by rw [hd]
    _ = pinv * BD := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hmulinv, Matrix.mul_one]
  have hvec : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = pM *ᵥ fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x) := by
    funext x
    have h := congrArg (fun v => kd P (v x)) (hpc g)
    simp only [Matrix.mulVec, dotProduct] at h ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, kd_q, hpG]
  have hbt : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = BD *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) - β' := by
    funext ⟨i, m⟩
    rw [Pi.sub_apply, hBD, blockDiag_mulVec]
    exact congrFun (hb m g) i
  rw [hactv, Matrix.mulVec_mulVec, hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, ← hbt, hvec, Matrix.mulVec_mulVec,
    hinvmul, Matrix.one_mulVec]

end GlobalTheory.PMon.DRvec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecWOfMatrix
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplRed

open GlobalTheory.WachTensor

private theorem tensorProduct_map_algHom_smul {O A M N : Type} [CommRing O] [CommRing A] [Algebra O A]
    [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : A →ₐ[O] A) (g : M →ₗ[O] N) (r : A) (x : A ⊗[O] M) :
    TensorProduct.map f.toLinearMap g (r • x) = f r • TensorProduct.map f.toLinearMap g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

private theorem coeffs_eq_of_sum_smul_eq_of_span_eq {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (B : Module.Basis (Fin n) R M) (c : Fin n → M) (hc : Submodule.span R (Set.range c) = ⊤)
    {v w : Fin n → R} (hvw : ∑ i, v i • c i = ∑ i, w i • c i) : v = w := by
  have hs : Function.Surjective (Fintype.linearCombination R c) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hc]
  have hi : Function.Injective (B.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R c) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (B.equivFun.surjective.comp hs)
  apply hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Fintype.linearCombination_apply, hvw]

theorem decW_of_matrix (S : Sit) (E : S.Comparison₂)
    (h : ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE),
      (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) →
        ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧
          ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧
      (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) →
        (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) →
          ∀ i, ∃ e, z i = E.ioE e)) : DecW S E := by
  unfold DecW
  intro T
  have memH : ∀ x, x ∈ Htl S T ↔ ∀ g ∈ Hker S, TWact (S.gR g) T g x = x := fun x => Iff.rfl
  have hH : ∀ g ∈ Hker S, S.W.resΓ g = 1 := fun g hg => MonoidHom.mem_ker.1 hg

  by_cases hsub : Subsingleton (TW S.RW T)
  · have key : ∀ x : TW S.RW T, x ∈ LinearMap.range (E.jD T) := fun x => ⟨0, Subsingleton.elim _ _⟩
    exact ⟨fun y _ => ⟨0, (Htl S T).zero_mem, key _⟩, fun z _ _ => key z⟩
  have : Nontrivial (TW S.RW T) := not_subsingleton_iff_nontrivial.1 hsub
  have : Nontrivial S.RW := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact hsub (Module.subsingleton S.RW _)
  have : Nontrivial S.O := RingHom.domain_nontrivial (algebraMap S.O S.RW)
  have : Nontrivial S.W.EE := RingHom.domain_nontrivial E.ioE.toRingHom
  have : Module.Free S.O ↥T.L.T := T.L.free
  have : Module.Finite S.O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg

  have bW : Module.Basis (Fin (Module.finrank S.O ↥T.L.T)) S.RW (TW S.RW T) :=
    (Module.finBasis S.O ↥T.L.T).baseChange S.RW
  have hr : 0 < Module.finrank S.O ↥T.L.T := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (TW S.RW T)
    exact hxy (bW.repr.injective (Finsupp.ext fun i => absurd i.isLt (by omega)))
  have hdr := (S.W.DD_free T).2
  have : Module.Free S.W.EE (S.W.DD T) := (S.W.DD_free T).1
  have : Module.Finite S.W.EE (S.W.DD T) := Module.finite_of_finrank_pos (by rw [hdr]; exact hr)
  obtain ⟨d, ⟨bD⟩, ⟨bW'⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) S.W.EE (S.W.DD T)) ∧
      Nonempty (Module.Basis (Fin d) S.RW (TW S.RW T)) :=
    ⟨_, ⟨Module.finBasis _ _⟩, ⟨bW.reindex (finCongr hdr.symm)⟩⟩

  have hexp : ∀ x : S.W.DD T, E.jD T x = ∑ i, E.ioE (bD.repr x i) • E.jD T (bD i) := by
    intro x
    conv_lhs => rw [← bD.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => E.jD_smul T _ _
  have hspan : Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hexp x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : ∀ v w : Fin d → S.RW, ∑ i, v i • E.jD T (bD i) = ∑ i, w i • E.jD T (bD i) → v = w :=
    fun v w hvw => coeffs_eq_of_sum_smul_eq_of_span_eq bW' _ hspan hvw
  have hsurj : ∀ y : TW S.RW T, ∃ v : Fin d → S.RW, y = ∑ i, v i • E.jD T (bD i) := by
    intro y
    have hy : y ∈ Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun S.RW).1 hy
    exact ⟨v, hv.symm⟩

  have actS : ∀ g (r : S.RW) (x : TW S.RW T),
      TWact (S.gR g) T g (r • x) = S.gR g r • TWact (S.gR g) T g x :=
    fun g r x => tensorProduct_map_algHom_smul (S.gR g) (T.actT g) r x
  have mapS : ∀ (r : S.RW) (x : TW S.RW T), TWmap S.φR T (r • x) = S.φR r • TWmap S.φR T x :=
    fun r x => tensorProduct_map_algHom_smul S.φR LinearMap.id r x
  have hfix : ∀ g ∈ Hker S, ∀ x, TWact (S.gR g) T g (E.jD T x) = E.jD T x := by
    intro g hg x
    rw [← E.jD_act, hH g hg, S.W.γD_one]
  have hact : ∀ g ∈ Hker S, ∀ v : Fin d → S.RW,
      TWact (S.gR g) T g (∑ i, v i • E.jD T (bD i)) = ∑ i, S.gR g (v i) • E.jD T (bD i) := by
    intro g hg v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [actS, hfix g hg]
  have hinv : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ Htl S T ↔ ∀ i, ∀ g ∈ Hker S, S.gR g (v i) = v i := by
    intro v
    rw [memH]
    constructor
    · intro hv i g hg
      exact congrFun (hinj _ _ ((hact g hg v).symm.trans (hv g hg))) i
    · intro hv g hg
      rw [hact g hg v]
      exact Finset.sum_congr rfl fun i _ => by rw [hv i g hg]
  have hk : ∀ k, TWmap S.φR T (E.jD T (bD k)) =
      ∑ i, E.ioE (bD.repr (S.W.φD T (bD k)) i) • E.jD T (bD i) := fun k => by
    rw [← E.jD_φ]
    exact hexp _
  have hφ : ∀ z : Fin d → S.RW, TWmap S.φR T (∑ k, z k • E.jD T (bD k)) =
      ∑ i, (∑ k, E.ioE (bD.repr (S.W.φD T (bD k)) i) * S.φR (z k)) • E.jD T (bD i) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [mapS, hk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  have hrng : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ LinearMap.range (E.jD T) ↔ ∀ i, ∃ e, v i = E.ioE e := by
    intro v
    constructor
    · rintro ⟨x, hx⟩
      rw [hexp] at hx
      have hv := hinj _ _ hx
      exact fun i => ⟨bD.repr x i, (congrFun hv i).symm⟩
    · intro hv
      choose e he using hv
      refine ⟨∑ i, e i • bD i, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, he i]

  obtain ⟨h1, h2⟩ := h d (Matrix.of fun i k => bD.repr (S.W.φD T (bD k)) i)
  simp only [Matrix.of_apply] at h1 h2
  refine ⟨fun y hy => ?_, fun z hz hφz => ?_⟩
  · obtain ⟨v, rfl⟩ := hsurj y
    obtain ⟨z, hzH, hz⟩ := h1 v ((hinv v).1 hy)
    refine ⟨∑ i, z i • E.jD T (bD i), (hinv z).2 hzH, ?_⟩
    rw [hφ z, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    exact (hrng _).2 hz
  · obtain ⟨u, rfl⟩ := hsurj z
    have hu := (hinv u).1 hz
    rw [hφ u, ← Finset.sum_sub_distrib] at hφz
    simp only [← sub_smul] at hφz
    exact (hrng u).2 (h2 u hu ((hrng _).1 hφz))

end GlobalTheory.DecomplRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoublingArithStep
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem doublingArith_step (V : ℕ → ℕ → ℕ) (E k : ℕ) (hE : 0 < E)
    (h1 : ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1))
    (h2 : V k (k + 8) ≤ 6 * E)
    (h3 : V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) :
    V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) := by
  have e1 := h1 1 le_rfl (by norm_num)
  have e2 := h1 2 (by norm_num) (by norm_num)
  have e3 := h1 3 (by norm_num) (by norm_num)
  have e4 := h1 4 (by norm_num) (by norm_num)
  have e5 := h1 5 (by norm_num) (by norm_num)
  have e6 := h1 6 (by norm_num) (by norm_num)
  have e7 := h1 7 (by norm_num) (by norm_num)
  rw [show k + 1 + 1 = k + 2 by ring] at e1
  rw [show k + 2 + 1 = k + 3 by ring] at e2
  rw [show k + 3 + 1 = k + 4 by ring] at e3
  rw [show k + 4 + 1 = k + 5 by ring] at e4
  rw [show k + 5 + 1 = k + 6 by ring] at e5
  rw [show k + 6 + 1 = k + 7 by ring] at e6
  rw [show k + 7 + 1 = k + 8 by ring] at e7
  rw [min_le_iff] at e1 e2 e3 e4 e5 e6 e7
  omega

theorem doublingArith : ∀ (V : ℕ → ℕ → ℕ) (E T g : ℕ), 0 < E →
    (∀ k ≤ 2 * T, ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1)) →
    (∀ k ≤ 2 * T, V k (k + 8) ≤ 6 * E) →
    (∀ k, V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) → g ≤ V 0 1 → 2 ^ T * g < E := by
  intro V E T g hE h1 h2 h3 hg
  have step : ∀ k, k ≤ 2 * T → V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) :=
    fun k hk => doublingArith_step V E k hE (h1 k hk) (h2 k hk) (h3 k)
  have ind : ∀ i, i ≤ T → 2 ^ i * g ≤ V (2 * i) (2 * i + 1) := by
    intro i
    induction i with
    | zero => intro _; simpa using hg
    | succ n ih =>
      intro hn
      have hs := (step (2 * n) (by omega)).2
      have ih' := ih (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring, pow_succ]
      calc 2 ^ n * 2 * g = 2 * (2 ^ n * g) := by ring
        _ ≤ 2 * V (2 * n) (2 * n + 1) := Nat.mul_le_mul_left 2 ih'
        _ ≤ V (2 * n + 2) (2 * n + 3) := hs
  exact lt_of_le_of_lt (ind T le_rfl) (step (2 * T) le_rfl).1

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gammaLayer_padic_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ Γ : GamS P K s LL, (∃ lam : ↥Γ.GKs →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ (g : ↥(GK K)) = 1) ∧ (∀ g, lam g = Multiplicative.ofAdd 1 ↔ Γ.resΓ (g : ↥(GK K)) = Γ.gam) ∧ (∃ g, lam g = Multiplicative.ofAdd 1) ∧ IsClosed (Γ.GKs : Set ↥(GK K))) ∧ ∃ lam : ↥(GK K) →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ g ∈ Γ.DelF) ∧ (∀ g, Γ.resΓ g = Γ.gamK → lam g = Multiplicative.ofAdd 1) := by
  first | exact @GlobalTheory.HWL.Coord.exists_gamma_coordinates | exact GlobalTheory.HWL.Coord.exists_gamma_coordinates | (intros; apply GlobalTheory.HWL.Coord.exists_gamma_coordinates <;> assumption)
end

