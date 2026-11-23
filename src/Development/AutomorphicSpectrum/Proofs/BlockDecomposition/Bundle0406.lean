module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRecurrencePolynomial
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquiv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhiTw

variable {k : Type} [Field k]

theorem twKer_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ)
    (h : ∀ n : N, χ (n : G) = 1) : twKer (twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, twist_apply, h, Units.val_one, one_smul]

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  have h0 : ∀ i : Fin n, glEmbMat k n A (Fin.last n) (Fin.castSucc i) = 0 := fun i => by
    simp [glEmbMat]
  have h1 : glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by simp [glEmbMat]
  have h2 : (glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [glEmbMat]
  simp only [h0, h1, h2]
  simp [← two_mul, pow_mul]

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have e : ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + colMat k n v.toAdd := rfl
  rw [e, Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    induction i using Fin.lastCases with
    | last => simp [colMat]
    | cast i => simp [colMat, Fin.castSucc_ne_last]
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := (ne_of_lt hij').symm
    have hj : j ≠ Fin.last n := (lt_of_lt_of_le hij' (Fin.le_last i)).ne
    simp [colMat, hj, hne]

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpowM_unip (n : ℕ) (t : ℝ) (u : MirUin k n) : dpowM n t (u : Mir k n) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hd : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
    ext1
    rw [hv']
    exact det_unip n v
  show dpow (n + 1) t ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [dpow, detChar_apply, hd, map_one]

theorem dpowM_levi (n : ℕ) (t : ℝ) (p : Mir k n) :
    dpowM (n + 1) t ((levi k (n + 1)).comp (Mir k n).subtype p) = dpowM n t p := by
  have hd : Matrix.GeneralLinearGroup.det (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) =
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) := by
    ext1
    exact det_glEmbMat (n + 1) _
  show dpow (n + 2) t (glEmb k (n + 1) (p : GL (Fin (n + 1)) k)) = dpow (n + 1) t (p : GL (Fin (n + 1)) k)
  rw [dpow, dpow, detChar_apply, detChar_apply, hd]

theorem phiMinus_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (j + 1)) W) (t : ℝ),
    Nonempty ((phiMinus k ψ (twist τ (dpowM (j + 1) t))).Equiv (twist (phiMinus k ψ τ) (dpowM j t))) := by
  intro k _ _ _ _ ψ j W _ _ τ t
  have hK := twKer_twist τ (MirUin k (j + 1)) (mirChar k ψ j) (dpowM (j + 1) t) (dpowM_unip (j + 1) t)
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq _ _ hK) fun p => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  show Submodule.Quotient.mk ((twist τ (dpowM (j + 1) t)) ((levi k (j + 1)).comp (Mir k j).subtype p) v) =
    twist (phiMinus k ψ τ) (dpowM j t) p (Submodule.Quotient.mk v)
  rw [twist_apply, twist_apply, dpowM_levi]
  rfl

end Local

end GlobalTheory.CompanionTheory.LeibPhiTw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactor
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Emb

open GlobalTheory.CompanionTheory.BZPhiPhi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirProj_iotaM (n : ℕ) (y : Mir k n) :
    mirabolicProjection k (n + 1) (embedding₂ k n y) = (y : GL (Fin (n + 1)) k) := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k (n + 1) (GlobalTheory.BZMir.glEmbMat k (n + 1) ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) i j = _
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem iotaM_mem_Q (n : ℕ) (y : Mir k n) : embedding₂ k n y ∈ Q k n := by
  show mirabolicProjection k (n + 1) (embedding₂ k n y) ∈ Mir k n
  rw [mirProj_iotaM]
  exact y.2

theorem mem_mirabolicParabolic_of_iotaM_mem (m j : ℕ) (p : Mir k (m + j))
    (h : embedding₂ k (m + j) p ∈ MirabolicParabolic k m (j + 1)) : p ∈ MirabolicParabolic k m j := by
  have h1 := (GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic k m (j + 1) (embedding₂ k (m + j) p)).1 h
  have e : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) p) = (p : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) p
  rw [e] at h1
  exact h1

theorem mem_mirabolicParabolic_of_mirabolicProj_eq_one (m j : ℕ) (w : Mir k (m + j)) (h : mirabolicProjection k (m + j) w = 1) :
    w ∈ MirabolicParabolic k m j := by
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic, h]
  exact one_mem _

theorem rowQ_eq_zero_of_mem_HGP (m j : ℕ) (h : Mir k (m + (j + 1))) (hh : h ∈ MirabolicParabolic k m (j + 1))
    (i : Fin (m + j + 1)) (hi : (i : ℕ) < m) : rowQ k (m + j) h i = 0 := by
  have h1 := (mem_mirabolicParabolic_iff k m (j + 1) h).1 hh ⟨j, by omega⟩ ⟨i, hi⟩
  have e1 : eGP m (j + 1) ⟨true, ⟨j, by omega⟩⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  have e2 : eGP m (j + 1) ⟨false, ⟨i, hi⟩⟩ = Fin.castSucc i :=
    Fin.ext (by rw [blockIndex_false_val]; simp)
  rw [e1, e2] at h1
  exact h1

theorem rowEl_mem_HGP (m j : ℕ) (r : Fin (m + j + 1) → k) (hr : (rowMat (m + j) r).det ≠ 0)
    (h0 : ∀ i : Fin (m + j + 1), (i : ℕ) < m → r i = 0) :
    (rowEl (m + j) r hr : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  have hb := blockIndex_true_val m (j + 1) b
  have ha := blockIndex_false_val m (j + 1) a
  have hval : (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) = rowMat (m + j) r := rfl
  generalize eGP m (j + 1) ⟨true, b⟩ = p at hb ⊢
  generalize eGP m (j + 1) ⟨false, a⟩ = q at ha ⊢
  show (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) p q = 0
  rw [hval, rowMat]
  by_cases hp : p = Fin.castSucc (Fin.last (m + j))
  · subst hp
    rw [updateRow_self]
    have ham := a.2
    have hq : q = Fin.castSucc (⟨a, by omega⟩ : Fin (m + j + 1)) := Fin.ext (by simpa using ha)
    rw [hq, Fin.lastCases_castSucc]
    exact h0 _ a.2
  · rw [updateRow_ne hp, one_apply_ne]
    intro c
    have := congrArg Fin.val c
    have ham := a.2
    omega

theorem mul_inv_qProj_mem (m j : ℕ) (x : Mir k (m + j)) (h d κ : Mir k (m + (j + 1)))
    (hh : h ∈ MirabolicParabolic k m (j + 1)) (hd : d ∈ MirabolicParabolic k m (j + 1)) (hq : d * κ ∈ Q k (m + j))
    (e : embedding₂ k (m + j) x = h * κ) :
    x * (qProj k (m + j) ⟨d * κ, hq⟩)⁻¹ ∈ MirabolicParabolic k m j := by
  apply mem_mirabolicParabolic_of_iotaM_mem
  set y := qProj k (m + j) ⟨d * κ, hq⟩ with hy
  have e1 : embedding₂ k (m + j) (x * y⁻¹) = (h * d⁻¹) * ((d * κ) * (embedding₂ k (m + j) y)⁻¹) := by
    rw [map_mul, map_inv, e]
    group
  rw [e1]
  refine mul_mem (mul_mem hh (inv_mem hd)) (mem_mirabolicParabolic_of_mirabolicProj_eq_one m (j + 1) _ ?_)
  have e2 : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) y) = (y : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) y
  have e3 : (y : GL (Fin (m + j + 1)) k) = mirabolicProjection k (m + (j + 1)) (d * κ) := rfl
  rw [map_mul, map_inv, e2, e3, mul_inv_cancel]

theorem iotaM_descent (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) :
    ∀ K' ∈ 𝓝 (1 : Mir k (m + j)), ∃ K ∈ 𝓝 (1 : Mir k (m + (j + 1))),
      ∀ x : Mir k (m + j), ∀ h ∈ MirabolicParabolic k m (j + 1), ∀ κ ∈ K, embedding₂ k (m + j) x = h * κ →
        ∃ h' ∈ MirabolicParabolic k m j, ∃ κ' ∈ K', x = h' * κ' := by
  have : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  intro K' hK'
  let r : Mir k (m + j + 1) → Fin (m + j + 1) → k := fun κ => rowQ k (m + j) κ⁻¹
  have hcr : Continuous r := (continuous_rowQ (m + j)).comp continuous_inv
  let O : Set (Mir k (m + j + 1)) := {κ | (rowMat (m + j) (r κ)).det ≠ 0}
  have hO : IsOpen O :=
    isOpen_compl_singleton.preimage ((continuous_rowMat (m + j)).comp hcr).matrix_det
  have hr1 : r 1 = Pi.single (Fin.last (m + j)) 1 := by
    show rowQ k (m + j) 1⁻¹ = _
    rw [inv_one, rowQ_one]
  have hm1 : rowMat (m + j) (r 1) = 1 := by rw [hr1, rowMat_single]
  have h1O : (1 : Mir k (m + j + 1)) ∈ O := by
    show (rowMat (m + j) (r 1)).det ≠ 0
    rw [hm1, det_one]
    exact one_ne_zero
  let d : O → Mir k (m + j + 1) := fun κ => rowEl (m + j) (r κ.1) κ.2
  have hdc : Continuous d :=
    (continuous_rowEl (k := k) (m + j)).comp
      (Continuous.subtype_mk (hcr.comp continuous_subtype_val) fun κ => κ.2)
  have hQ : ∀ κ : O, d κ * κ.1 ∈ Q k (m + j) := fun κ => by
    have := mul_inv_mem_Q_of_rowQ_eq (m + j) (d κ) (κ.1)⁻¹ (rowQ_rowEl (m + j) (r κ.1) κ.2)
    rwa [inv_inv] at this
  let φ : O → Q k (m + j) := fun κ => ⟨d κ * κ.1, hQ κ⟩
  have hφc : Continuous φ := Continuous.subtype_mk (hdc.mul continuous_subtype_val) _
  let ψ : O → Mir k (m + j) := fun κ => qProj k (m + j) (φ κ)
  have hψc : Continuous ψ := (GlobalTheory.CompanionTheory.BZMirOnto.continuous_qProj k (m + j)).comp hφc
  have hd1 : d ⟨1, h1O⟩ = 1 := Subtype.ext (Units.ext hm1)
  have hψ1 : ψ ⟨1, h1O⟩ = 1 := by
    have : φ ⟨1, h1O⟩ = 1 := Subtype.ext (by
      show d ⟨1, h1O⟩ * 1 = 1
      rw [hd1, one_mul])
    show qProj k (m + j) (φ ⟨1, h1O⟩) = 1
    rw [this, map_one]
  have hpre : ψ ⁻¹' K' ∈ 𝓝 (⟨1, h1O⟩ : O) :=
    hψc.continuousAt.preimage_mem_nhds (by rw [hψ1]; exact hK')
  refine ⟨Subtype.val '' (ψ ⁻¹' K'), hO.isOpenMap_subtype_val.image_mem_nhds hpre, ?_⟩
  rintro x h hh _ ⟨κ, hκ, rfl⟩ e
  have hκinv : (κ.1)⁻¹ = embedding₂ k (m + j) x⁻¹ * h := by
    rw [map_inv, e]
    group
  have hrow : r κ.1 = rowQ k (m + j) h := by
    show rowQ k (m + j) (κ.1)⁻¹ = _
    rw [hκinv]
    exact rowQ_mul_of_mem_Q k (m + j) _ h (iotaM_mem_Q (m + j) x⁻¹)
  have hdH : d κ ∈ MirabolicParabolic k m (j + 1) :=
    rowEl_mem_HGP m j (r κ.1) κ.2 fun i hi => by
      rw [hrow]
      exact rowQ_eq_zero_of_mem_HGP m j h hh i hi
  exact ⟨x * (ψ κ)⁻¹, mul_inv_qProj_mem m j x h (d κ) κ.1 hh hdH (hQ κ) e, ψ κ, hκ, by group⟩

end GlobalTheory.CompanionTheory.LeibPhi.Emb

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactIwasawa
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.SiegelAssemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}


variable (F E) in
abbrev phiInf : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)


variable (F E) in
abbrev phiFin : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)


omit [NumberField E] in
theorem tens_ext {z z' : AF F ⊗[F] E} (h₁ : phiInf F E z = phiInf F E z') (h₂ : phiFin F E z = phiFin F E z') :
    z = z' := by
  obtain ⟨y, hy⟩ : ∃ y : AF F ⊗[F] E, y = z - z' + 1 := ⟨_, rfl⟩
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1)
    (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiInf F E y = 1
      rw [hy, map_add (f := _), map_sub, h₁, sub_self, zero_add, map_one])
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiFin F E y = 1
      rw [hy, map_add (f := _), map_sub, h₂, sub_self, zero_add, map_one])
  have h3 : z - z' + 1 = 1 := hy.symm.trans (congrFun (congrFun this 0) 0)
  exact sub_eq_zero.1 (add_right_cancel (h3.trans (zero_add 1).symm))

omit [NumberField E] in
theorem matrix_tens_ext {a b : Type} {P Q : Matrix a b (AF F ⊗[F] E)} (h₁ : P.map (phiInf F E) = Q.map (phiInf F E))
    (h₂ : P.map (phiFin F E) = Q.map (phiFin F E)) : P = Q :=
  Matrix.ext fun i j => tens_ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

omit [NumberField E] in
theorem mat_projInf (g : GAd σ J) : (matHom _ σ J (projInf σ J g)).1 = (matHom _ σ J g).1.map (phiInf F E) := rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = (matHom _ σ J g).1.map (phiFin F E) := rfl

theorem mem_minPar_of_parts {p q : GAd σ J} (hp : p ∈ minPar σ J X) (h₁ : projInf σ J q = projInf σ J p)
    (h₂ : projFin σ J q = 1) : q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  let e₀ : AF F ⊗[F] E := (((1 : Ainf F), (0 : Af F)) : AF F) ⊗ₜ[F] (1 : E)
  have e₁ : phiInf F E e₀ = 1 := rfl
  have e₂ : phiFin F E e₀ = 0 := TensorProduct.zero_tmul _ _
  let B' : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
    Matrix.of fun i j => (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j +
      e₀ * (B i j - (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j)
  have b₁ : B'.map (phiInf F E) = B.map (phiInf F E) := Matrix.ext fun i j => by
    simp [B', e₁]
  have b₂ : B'.map (phiFin F E) = 1 := Matrix.ext fun i j => by
    by_cases hij : i = j
    · subst hij; simp [B', e₂]
    · simp [B', e₂, Matrix.one_apply_ne hij]
  refine ⟨B', fun i j hij => ?_, matrix_tens_ext ?_ ?_⟩
  · have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    simp [B', hB hij, Matrix.one_apply_ne hne]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projInf, h₁, mat_projInf, b₁, ← Matrix.map_mul, e, Matrix.map_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projFin, h₂, b₂]
    simp

theorem commute_of_mem {a b : GAd σ J} (ha : a ∈ infPts σ J) (hb : b ∈ finPts σ J) : Commute a b := by
  have ha' : a ∈ (ofInf σ J).range := by rw [range_ofInf]; exact ha
  have hb' : b ∈ (ofFin σ J).range := by rw [range_ofFin]; exact hb
  obtain ⟨x, rfl⟩ := ha'
  obtain ⟨y, rfl⟩ := hb'
  exact commute_ofInf_ofFin σ J x y

theorem mul_mem_leviMin {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

def prodSub (K₁ K₂ : Subgroup (GAd σ J)) (h₁ : K₁ ≤ infPts σ J) (h₂ : K₂ ≤ finPts σ J) : Subgroup (GAd σ J) where
  carrier := (K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))
  one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
    have c : b * a' = a' * b := ((commute_of_mem (h₁ ha') (h₂ hb)).eq).symm
    change a * a' * (b * b') = a * b * (a' * b')
    rw [mul_assoc a b, ← mul_assoc b, c, mul_assoc a', mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
    change a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact ((commute_of_mem (h₁ (K₁.inv_mem ha)) (h₂ (K₂.inv_mem hb))).eq)

end GlobalTheory.CompanionTheory.SiegelAssemble


open GlobalTheory.CompanionTheory.SiegelAssemble in
theorem GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K₁ K₂ : Subgroup (GAd σ J), K₁ ≤ infPts σ J → K₂ ≤ finPts σ J → IsCompact (K₁ : Set (GAd σ J)) → IsCompact (K₂ : Set (GAd σ J)) → (∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ K₁, g = p * k) → (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K₂, g = p * k) → (∀ p ∈ minPar σ J X, p ∈ K₁ → p ∈ leviMin σ J X Y) → GoodPosition σ J X Y K₂ → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ hlev hgood
  refine ⟨prodSub K₁ K₂ h₁ h₂, (show IsCompact ((K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))) from c₁.mul c₂), fun g => ?_, ?_⟩
  · obtain ⟨p₁, hp₁, hp₁', k₁, hk₁, e₁⟩ := iw₁ (ofInf σ J (projInf σ J g)) (mem_infPts.2 (by simp))
    obtain ⟨p₂, hp₂, hp₂', k₂, hk₂, e₂⟩ := iw₂ (ofFin σ J (projFin σ J g)) (mem_finPts.2 (by simp))
    refine ⟨p₁ * p₂, mul_mem_minimal_parabolic hp₁ hp₂, k₁ * k₂, ⟨k₁, hk₁, k₂, hk₂, rfl⟩, ?_⟩
    have c : k₁ * p₂ = p₂ * k₁ := (commute_of_mem (h₁ hk₁) hp₂').eq
    calc g = ofInf σ J (projInf σ J g) * ofFin σ J (projFin σ J g) := (ofInf_projInf_mul_ofFin_projFin σ J g).symm
      _ = p₁ * (k₁ * p₂) * k₂ := by rw [e₁, e₂]; simp only [mul_assoc]
      _ = p₁ * p₂ * (k₁ * k₂) := by rw [c]; simp only [mul_assoc]
  · rintro _ hp ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have i₁ : projFin σ J k₁ = 1 := mem_infPts.1 (h₁ hk₁)
    have i₂ : projInf σ J k₂ = 1 := mem_finPts.1 (h₂ hk₂)
    have m₁ : k₁ ∈ minPar σ J X := mem_minPar_of_parts hp (by simp [i₂]) i₁
    have m₂ : k₂ ∈ minPar σ J X := by
      have := mul_mem_minimal_parabolic (inv_mem_minimal_parabolic h hJ hW m₁) hp
      simpa using this
    obtain ⟨m, hm, hmK, u, hu, huK, rfl⟩ := hgood k₂ m₂ hk₂
    exact ⟨k₁ * m, mul_mem_leviMin (hlev k₁ m₁ hk₁) hm, ⟨k₁, hk₁, m, hmK, rfl⟩, u, hu,
      ⟨1, K₁.one_mem, u, huK, one_mul u⟩, by simp only [mul_assoc]⟩

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGL
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem exists_isFundamentalDomain_of_isSqInt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (φ : GA E N → ℂ), IsSqInt φ →
      ∃ F : Set (GA E N), IsFundamentalDomain (latticeGL E N) F μ := by
  intro E _ _ _ N _ _ μ _ φ _
  obtain ⟨F, -, hF⟩ := GlobalTheory.CompanionTheory.LatticeFD.exists_measurable_isFundamentalDomain E N
  exact ⟨F, hF μ⟩

end GlobalTheory.CompanionTheory.FinDisc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRecurrencePolynomialStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_recurrence_polynomial : ∀ (G : Type) [Group G] (a : ℝ → G) (F₀ : G → ℂ) (S : Submodule ℂ (ℝ → ℂ)), (∀ s t, a (s + t) = a s * a t) →
  (∀ g, Continuous fun t => F₀ (a t * g)) → FiniteDimensional ℂ S → (∀ g, (fun t => F₀ (a t * g)) ∈ S) →
  ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ Module.finrank ℂ S ∧ (∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F₀ (a j * g) = 0) ∧
    ∀ z, p.IsRoot z → ∃ c : ℂ, z = Complex.exp c ∧
      ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)), F ≠ 0 ∧
        ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g := by
  first | exact @GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le | exact GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le | (intros; apply GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_mirUin_gpProj_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  intro k _ _ _ _ m j n
  obtain ⟨v, hv, e⟩ := GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip k m (j + 1) (n : Mir k (j + 1)) n.2
  exact ⟨⟨v, hv⟩, v.2, e⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjectiveStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_unipotent_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : Mir k j), u ∈ MirUin k j → ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | exact GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip <;> assumption)
end

