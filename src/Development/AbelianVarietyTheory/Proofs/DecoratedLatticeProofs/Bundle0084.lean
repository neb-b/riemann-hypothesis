module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedSubgroupOfIndefiniteUnitaryEqMaximalCompa
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical
open Matrix

namespace GlobalTheory.BoundedUnitary

theorem norm_eigenvalue_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (C : ℝ)
    (hC : ∀ k : ℕ, ∀ i j, ‖(M ^ k) i j‖ ≤ C) (v : Fin n → ℂ) (hv : v ≠ 0) (μ : ℂ)
    (h : M *ᵥ v = μ • v) : ‖μ‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormBound.norm_eigenvalue_le_one ..)


open scoped ComplexOrder in
theorem eq_one_of_posSemidef {n : ℕ} (p q : Matrix (Fin n) (Fin n) ℂ) (hp : p.PosSemidef)
    (hqp : q * p = 1) (C : ℝ) (hC : ∀ k : ℕ, ∀ i j, ‖(p ^ k) i j‖ ≤ C)
    (hC' : ∀ k : ℕ, ∀ i j, ‖(q ^ k) i j‖ ≤ C) : p = 1 := by
  have hH := hp.isHermitian
  have hev : ∀ j, hH.eigenvalues j = 1 := by
    intro j
    set v : Fin n → ℂ := ⇑(hH.eigenvectorBasis j) with hvdef
    have hv : v ≠ 0 := by
      intro h0
      have h1 : hH.eigenvectorBasis j = 0 := by
        ext i
        exact congrFun h0 i
      exact hH.eigenvectorBasis.orthonormal.ne_zero j h1
    have h1 : p *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ) • v := by
      have := hH.mulVec_eigenvectorBasis j
      rw [hvdef, this]
      ext i
      simp
    have h0 : 0 ≤ hH.eigenvalues j := hp.eigenvalues_nonneg j
    have h2 : v = ((hH.eigenvalues j : ℝ) : ℂ) • (q *ᵥ v) := by
      rw [← Matrix.mulVec_smul, ← h1, Matrix.mulVec_mulVec, hqp, Matrix.one_mulVec]
    have hne : ((hH.eigenvalues j : ℝ) : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_smul] at h2
      exact hv h2
    have h3 : q *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ)⁻¹ • v := by
      conv_rhs => rw [h2]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    have a1 := norm_eigenvalue_le_one p C hC v hv _ h1
    have a2 := norm_eigenvalue_le_one q C hC' v hv _ h3
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h0] at a2
    rw [Complex.norm_real, Real.norm_of_nonneg h0] at a1
    have hpos : 0 < hH.eigenvalues j := lt_of_le_of_ne h0 (fun h => hne (by rw [← h]; simp))
    exact le_antisymm a1 ((inv_le_one₀ hpos).mp a2)
  have hbasis : ∀ j, p *ᵥ ⇑(hH.eigenvectorBasis j) = ⇑(hH.eigenvectorBasis j) := by
    intro j
    rw [hH.mulVec_eigenvectorBasis j, hev j, one_smul]
  have hU : p * (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    have := congrFun (hbasis j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hU2 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  calc p = p * ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) := by rw [hU2, mul_one]
    _ = 1 := by rw [← mul_assoc, hU, hU2]


open scoped ComplexOrder in
theorem eq_Kset_of_bounded : ∀ (n : ℕ) (ε : Fin n → Bool) (G' : Set (Matrix (Fin n) (Fin n) ℂ)), G' ⊆ Formalism.MainNotions.S.UJset ε → Formalism.REAL.Kset ε ⊆ G' → (∀ a ∈ G', ∀ b ∈ G', a * b ∈ G') → (∀ a ∈ G', a⁻¹ ∈ G') → (∃ C : ℝ, ∀ a ∈ G', ∀ i j, ‖a i j‖ ≤ C) → G' = Formalism.REAL.Kset ε := by
  intro n ε G' hU hK hmul hinv ⟨C, hC⟩
  refine Set.Subset.antisymm (fun a ha => ?_) hK
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJH := Formalism.REAL.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJ
  have hJG : J ∈ G' := hK ⟨by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hJH, hJJ], rfl⟩
  have h1G : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G' := hJJ ▸ hmul _ hJG _ hJG
  have hpow : ∀ b ∈ G', ∀ k : ℕ, b ^ k ∈ G' := by
    intro b hb k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hb
  have hleft : ∀ b ∈ G', (J * bᴴ * J) * b = 1 := by
    intro b hb
    have hb' : bᴴ * J * b = J := hU hb
    calc (J * bᴴ * J) * b = J * (bᴴ * J * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hb', hJJ]
  have hinv_eq : ∀ b ∈ G', b⁻¹ = J * bᴴ * J := fun b hb => Matrix.inv_eq_left_inv (hleft b hb)
  have haH : aᴴ ∈ G' := by
    have : aᴴ = J * a⁻¹ * J := by
      rw [hinv_eq a ha]
      calc aᴴ = (J * J) * aᴴ * (J * J) := by rw [hJJ, one_mul, mul_one]
        _ = _ := by simp only [mul_assoc]
    rw [this]
    exact hmul _ (hmul _ hJG _ (hinv a ha)) _ hJG
  have hpG : aᴴ * a ∈ G' := hmul _ haH _ ha
  have hp1 : aᴴ * a = 1 := by
    refine eq_one_of_posSemidef (aᴴ * a) (aᴴ * a)⁻¹ (Matrix.posSemidef_conjTranspose_mul_self a) ?_ C
      (fun k => hC _ (hpow _ hpG k)) (fun k => hC _ (hpow _ (hinv _ hpG) k))
    rw [hinv_eq _ hpG]
    exact hleft _ hpG
  have hp2 : a * aᴴ = 1 := mul_eq_one_comm.mp hp1
  refine ⟨by rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hp1], ?_⟩
  have ha' : aᴴ * J * a = J := hU ha
  calc a * J = a * (aᴴ * J * a) := by rw [ha']
    _ = (a * aᴴ) * J * a := by simp only [mul_assoc]
    _ = J * a := by rw [hp2, one_mul]

end GlobalTheory.BoundedUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterTensorProductMemRange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.CenterTensor

open Algebra.TensorProduct

theorem center_tensorProduct_mem_range {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (z : A ⊗[ℂ] B) (hz : z ∈ Subalgebra.center ℂ (A ⊗[ℂ] B)) :
    ∃ u : (Subalgebra.center ℂ A) ⊗[ℂ] (Subalgebra.center ℂ B),
      Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (Subalgebra.center ℂ B).val u = z := by
  have h1 : z ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B).range : Set (A ⊗[ℂ] B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    exact Subalgebra.mem_center_iff.1 hz g
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at h1
  obtain ⟨w, hw⟩ := h1
  set f := Algebra.TensorProduct.map (AlgHom.id ℂ A) (Subalgebra.center ℂ B).val with hf
  have finj : Function.Injective f := by
    have : (f : A ⊗[ℂ] (Subalgebra.center ℂ B) → A ⊗[ℂ] B) =
        LinearMap.lTensor A (Subalgebra.center ℂ B).val.toLinearMap := by
      funext x
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp [hf]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [this]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hw2 : w ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)).range :
        Set (A ⊗[ℂ] (Subalgebra.center ℂ B))) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have hw' : f w = z := hw
    have h3 : f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a) = a ⊗ₜ[ℂ] (1 : B) := by simp [hf]
    apply finj
    show f ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a * w) = f (w * (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] (Subalgebra.center ℂ B)) a)
    rw [map_mul, map_mul, hw', h3]
    exact Subalgebra.mem_center_iff.1 hz _
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at hw2
  obtain ⟨u, hu⟩ := hw2
  refine ⟨u, ?_⟩
  have hw' : f w = z := hw
  have hu' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
      (AlgHom.id ℂ (Subalgebra.center ℂ B)) u = w := hu
  rw [← hw', ← hu']
  clear hw hu hw' hu' hz
  induction u using TensorProduct.inductionOn with
  | tmul a b => simp [hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem center_eq_adjoin : ∀ (A B C : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Ring C] [Algebra ℂ C] (e : (A ⊗[ℂ] B) ≃ₐ[ℂ] C), Subalgebra.center ℂ C = Algebra.adjoin ℂ ((fun a => e (a ⊗ₜ 1)) '' (Subalgebra.center ℂ A : Set A) ∪ (fun b => e (1 ⊗ₜ b)) '' (Subalgebra.center ℂ B : Set B)) := by
  intro A B C _ _ _ _ _ _ e
  apply le_antisymm
  · intro c hc
    have hz : e.symm c ∈ Subalgebra.center ℂ (A ⊗[ℂ] B) := by
      rw [Subalgebra.mem_center_iff] at hc ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hc (e g)
    obtain ⟨u, hu⟩ := center_tensorProduct_mem_range _ hz
    have hc' : c = e (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
        (Subalgebra.center ℂ B).val u) := by rw [hu, e.apply_symm_apply]
    rw [hc']
    clear hu hc'
    induction u using TensorProduct.inductionOn with
    | tmul a b =>
      have : (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val
          (Subalgebra.center ℂ B).val) (a ⊗ₜ b) = ((a : A) ⊗ₜ (1 : B)) * ((1 : A) ⊗ₜ (b : B)) := by
        simp
      rw [this, map_mul]
      refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (Algebra.subset_adjoin ?_)
      · exact Or.inl ⟨a, a.2, rfl⟩
      · exact Or.inr ⟨b, b.2, rfl⟩
    | add x y hx hy =>
      simpa only [map_add] using Subalgebra.add_mem _ hx hy
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      induction y using TensorProduct.inductionOn with
      | tmul x y =>
        simp [Subalgebra.mem_center_iff.1 ha x]
      | add x y hx hy => rw [mul_add, add_mul, hx, hy]
    · rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      induction y using TensorProduct.inductionOn with
      | tmul x y =>
        simp [Subalgebra.mem_center_iff.1 hb y]
      | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end GlobalTheory.CenterTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem elementary_size_bounds_of_size_hypotheses : ∀ M : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ),
    thr ≤ C' → thr ≤ Cl → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1000 ≤ Cl ∧ M ≤ Cl ∧ M ≤ (D.R.m : ℝ) ∧
    M ≤ (D.R.k : ℝ) ∧ D.host.rdE ≤ large₂.sc.b ∧ (D.R.k : ℝ) ^ M ≤ large₂.sc.b ∧ (D.R.r : ℝ) ≤ large₂.sc.b ∧
    (D.R.m : ℝ) ^ 2 ≤ D.R.k ∧ M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
  intro M
  refine ⟨max 1000 (2 * |M|), ?_⟩
  intro D large₂ C' Cl Cg cb Cu cT CT hC' hCl h
  have hMabs : M ≤ |M| := le_abs_self M
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hCl1000 : 1000 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl2M : 2 * |M| ≤ Cl := le_trans (le_max_right _ _) hCl
  have hC'M : M ≤ C' := by linarith [le_trans (le_max_right _ _) hC']
  obtain ⟨-, hk, hmf, hfk, -, -, hm2L, -, -, -, hrd, -, -, -, -, hbj, -, -, -, -, -, -, -, hClm, -⟩ := h
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Formalism.MainNotions.S.log_scb large₂
  have hb2 : 2 ≤ large₂.sc.b := Formalism.MainNotions.S.two_le_scb large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hmkR : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast hmk
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hcard : 0 < Fintype.card D.what₂.Tau := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.card_places D, Formalism.MainNotions.LatticeGluingRadicals.d_card D]; omega
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hcard
  have hb1 := hbj τ 1 le_rfl (by omega)

  have hkb2 : (D.R.k : ℝ) ^ Cl ≤ large₂.sc.b ^ (2 : ℝ) := le_trans (le_trans (le_max_left _ _) hb1.1) hb1.2
  have hb0 : 0 ≤ large₂.sc.b := by linarith

  have hkhalf : (D.R.k : ℝ) ^ (Cl / 2) ≤ large₂.sc.b := by
    have e1 : (D.R.k : ℝ) ^ (Cl / 2) = ((D.R.k : ℝ) ^ Cl) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (by linarith)]; ring_nf
    have e2 : large₂.sc.b = (large₂.sc.b ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hb0]; norm_num
    rw [e1, e2]
    exact Real.rpow_le_rpow (by positivity) hkb2 (by norm_num)
  have hkM : (D.R.k : ℝ) ^ M ≤ large₂.sc.b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) hkhalf
  have hk2 : (D.R.k : ℝ) ^ (2 : ℝ) ≤ large₂.sc.b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) hkhalf
  rw [Real.rpow_two] at hk2
  have hr : (D.R.r : ℝ) ≤ large₂.sc.b := by
    have e : (D.R.r : ℝ) = (D.R.k : ℝ) + D.R.m - 1 := by
      unfold Formalism.BasicNotions.Ranks.r; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring
    rw [e]; nlinarith
  have hmL : (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 2 := by positivity
    have a1 : (D.R.m : ℝ) ^ 2 ≤ Cl * (D.R.m : ℝ) ^ 2 := le_mul_of_one_le_left h0 (by linarith)
    have a2 : Cl * (D.R.m : ℝ) ^ 2 ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := by
      have : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right h0 hL.le
      exact mul_le_mul_of_nonneg_left this (by linarith)
    linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    rcases le_or_gt D.host.rdE 0 with hneg | hpos
    · linarith
    · have hLCl : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
      have hlog : Real.log D.host.rdE ≤ Real.log large₂.sc.b := by rw [hlogb]; linarith
      exact (Real.log_le_log_iff hpos (by linarith)).1 hlog
  have hX0 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
  have hMk : M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
    have a : M * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right hC'M hX0
    have e1 : M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = M * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    have e2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    linarith
  exact ⟨hCl1000, by linarith, by linarith, by linarith, hrdb, hkM, hr, hmL, hMk⟩

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoundLatLoc
section
noncomputable section

namespace GlobalTheory.LocalLatticeBound

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem abs_zero_le (v : HeightOneSpectrum (𝓞 F)) (C : ℝ≥0) : absFin F v (0 : Fv F v ⊗[F] E) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_zero, (absBar_eq_zero F v).2 rfl]; exact zero_le

theorem abs_neg_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {y : Fv F v ⊗[F] E} (h : absFin F v y ≤ C) :
    absFin F v (-y) ≤ C :=
  (absFin_le_iff F v).2 fun τ => by rw [map_neg, absBar_neg]; exact (le_absFin F v τ y).trans h

theorem abs_int_mul_le (v : HeightOneSpectrum (𝓞 F)) {C : ℝ≥0} {c y : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v)
    (h : absFin F v y ≤ C) : absFin F v (c * y) ≤ C :=
  (absFin_mul_le F v c y).trans ((mul_le_mul' (absFin_le_one_of_mem_intLoc hc) h).trans_eq (one_mul C))

theorem exists_bound_rat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ x ∈ L, ∀ i, absFin F v ((1 : Fv F v) ⊗ₜ[F] x i) ≤ C := by
  obtain ⟨S, rfl⟩ := hL
  refine ⟨S.sup fun s => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i), fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem s hs =>
    exact (Finset.le_sup (f := fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun s : Fin n → E => Finset.univ.sup fun i => absFin F v ((1 : Fv F v) ⊗ₜ[F] s i)) hs)
  | zero => rw [Pi.zero_apply, TensorProduct.tmul_zero]; exact abs_zero_le v _
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, TensorProduct.tmul_add]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    have e : (1 : Fv F v) ⊗ₜ[F] (c • x) i = ((1 : Fv F v) ⊗ₜ[F] (c : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc (one_mem _) c) hx

theorem exists_bound_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ C : ℝ≥0, ∀ y ∈ latLoc F L v, ∀ i : Fin n, absFin F v (y i) ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_rat L (Submodule.IsLattice.fg (A := E) L) v
  refine ⟨C, fun y hy i => ?_⟩
  change y ∈ AddSubgroup.closure _ at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have e : a ⊗ₜ[F] x i = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]; simp
    change absFin F v (a ⊗ₜ[F] x i) ≤ C
    rw [e]
    exact abs_int_mul_le v (tmul_mem_intLoc ha 1) (hC x hx i)
  | zero => exact abs_zero_le v C
  | add y z _ _ hy hz => exact (absFin_add_le F v _ _).trans (max_le hy hz)
  | neg y _ hy => exact abs_neg_le v hy

end GlobalTheory.LocalLatticeBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingleMemLatLoc
section
open scoped TensorProduct

namespace GlobalTheory.LocalLatticeIntegral

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (M : E) * e := by
  have h : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨M, hM, hi⟩ := h.exists_integral_multiple
  exact ⟨M, hM, ⟨M • e, hi⟩, by simp [zsmul_eq_mul]⟩

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsFullLattice E L] (x : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [Submodule.IsFullLattice.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, h1⟩ := hx
    obtain ⟨M, hM, h2⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem h1 M
    · rw [mul_smul]; exact L.toAddSubgroup.zsmul_mem h2 N
  | smul e x _ hx =>
    obtain ⟨N, hN, h1⟩ := hx
    obtain ⟨M, hM, r, hr⟩ := exists_int_mul_integral e
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h2 := L.smul_mem r h1
    convert h2 using 1
    funext j
    have : (r • N • x) j = (r : E) * ((N : E) * x j) := by
      simp [Algebra.smul_def, zsmul_eq_mul]
    rw [this, hr]
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_mul]
    ring

theorem exists_single_mem_latLoc : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∃ (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), c ≠ (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧ ∀ (i : Fin n), Pi.single i (c ⊗ₜ[F] (1 : E)) ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ n L _ v
  choose N hN hmem using fun i : Fin n => exists_int_smul_mem L (Pi.single i (1 : E))
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN i
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).injective
  refine ⟨((∏ i, N i : ℤ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), Int.cast_ne_zero.2 hP, fun i => ?_⟩
  obtain ⟨k, hk⟩ : N i ∣ ∏ j, N j := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  have h1 : (∏ j, N j) • (Pi.single i (1 : E) : Fin n → E) ∈ L := by
    rw [hk, mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem (hmem i) k
  generalize (∏ j, N j) = P at h1
  refine AddSubgroup.subset_closure ⟨1, one_mem _, _, h1, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      zsmul_eq_mul, mul_one]
  · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, TensorProduct.tmul_zero]

end GlobalTheory.LocalLatticeIntegral
end

