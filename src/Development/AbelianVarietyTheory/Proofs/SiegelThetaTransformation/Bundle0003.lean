module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FoldrHolDEqIteratedFDeriv
section
open Complex
open scoped ComplexConjugate

namespace GlobalTheory.Ker.CreOp

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable def holD (v : W) (Φ : W → ℂ) (z : W) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))

theorem contDiff_fderiv_apply {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => fderiv ℝ Φ z v := (contDiff_infty_iff_fderiv.1 h).2.clm_apply contDiff_const

theorem contDiff_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) (holD v Φ) := by
  show ContDiff ℝ _ fun z => (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))
  exact contDiff_const.mul
    ((contDiff_fderiv_apply h v).sub (contDiff_const.mul (contDiff_fderiv_apply h (I • v))))

theorem holD_add {Φ Ψ : W → ℂ} (h : Differentiable ℝ Φ) (h' : Differentiable ℝ Ψ) (v : W) :
    holD v (fun z => Φ z + Ψ z) = fun z => holD v Φ z + holD v Ψ z := by
  funext z
  have hs : HasFDerivAt (fun y => Φ y + Ψ y) (fderiv ℝ Φ z + fderiv ℝ Ψ z) z :=
    (h z).hasFDerivAt.add (h' z).hasFDerivAt
  simp only [holD, hs.fderiv, ContinuousLinearMap.add_apply]
  ring

theorem exists_clm_of_antilinear [FiniteDimensional ℂ W] {lam : W → ℂ}
    (h1 : ∀ a b, lam (a + b) = lam a + lam b) (h2 : ∀ (t : ℂ) a, lam (t • a) = conj t * lam a) :
    ∃ T : W →L[ℝ] ℂ, lam = T := by
  have hr : ∀ (r : ℝ) (a : W), lam (r • a) = r • lam a := by
    intro r a
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r a, h2]
    simp [Complex.real_smul]
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  exact ⟨LinearMap.toContinuousLinearMap
    ({ toFun := lam, map_add' := h1, map_smul' := fun r a => by rw [RingHom.id_apply]; exact hr r a }
      : W →ₗ[ℝ] ℂ), rfl⟩

theorem holD_mul (T : W →L[ℝ] ℂ) (h2 : ∀ a, T (I • a) = -I * T a) {Φ : W → ℂ}
    (h : Differentiable ℝ Φ) (v : W) :
    holD v (fun z => T z * Φ z) = fun z => T z * holD v Φ z := by
  funext z
  have hT : HasFDerivAt (fun y => T y * Φ y) (T z • fderiv ℝ Φ z + Φ z • T) z :=
    T.hasFDerivAt.mul (h z).hasFDerivAt
  simp only [holD, hT.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, h2]
  linear_combination (1 / 2 : ℂ) * Φ z * T v * I_sq

theorem holD_of_differentiableAt {Φ : W → ℂ} {z : W} (h : DifferentiableAt ℂ Φ z) (v : W) :
    holD v Φ z = fderiv ℂ Φ z v := by
  have e : fderiv ℝ Φ z = (fderiv ℂ Φ z).restrictScalars ℝ := h.fderiv_restrictScalars ℝ
  simp only [holD, e, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul,
    smul_eq_mul]
  linear_combination (-(1 / 2) : ℂ) * fderiv ℂ Φ z v * I_sq

variable {σ : Type} (u : σ → W)

theorem contDiff_foldr_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (M : List σ) :
    ContDiff ℝ (⊤ : ℕ∞) (M.foldr (fun l => holD (u l)) Φ) := by
  induction M with
  | nil => exact h
  | cons l M ih => exact contDiff_holD ih (u l)

theorem foldr_holD_eq_iteratedFDeriv [FiniteDimensional ℂ W] {θ : W → ℂ}
    (hθ : Differentiable ℂ θ) (M : List σ) :
    M.foldr (fun l => holD (u l)) θ =
      fun z => iteratedFDeriv ℂ M.length θ z fun k => u (M.get k) := by
  have hθ' : ContDiff ℂ ⊤ θ := GlobalTheory.SCV.contDiff_of_differentiable hθ ⊤
  induction M with
  | nil => funext z; simp
  | cons l M ih =>
    have hA : Differentiable ℂ (iteratedFDeriv ℂ M.length θ) :=
      hθ'.differentiable_iteratedFDeriv (WithTop.coe_lt_top _)
    funext z
    simp only [List.foldr_cons]
    rw [ih, holD_of_differentiableAt ((hA z).continuousMultilinear_apply_const _),
      fderiv_continuousMultilinear_apply_const_apply (hA z)]
    rfl

private theorem contDiff_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, ContDiff ℝ (⊤ : ℕ∞) p.2) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => (R.map fun p => p.1 z * p.2 z).sum := by
  induction R with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact contDiff_const
  | cons p R ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (p.1.contDiff.mul (hR p (by simp))).add (ih fun q hq => hR q (by simp [hq]))

private theorem holD_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) (v : W) :
    holD v (fun z => (R.map fun p => p.1 z * p.2 z).sum) =
      fun z => (R.map fun p => p.1 z * holD v p.2 z).sum := by
  induction R with
  | nil => funext z; simp [holD]
  | cons p R ih =>
    have hp := hR p (by simp)
    have hR' : ∀ q ∈ R, (∀ a, q.1 (I • a) = -I * q.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) q.2 :=
      fun q hq => hR q (by simp [hq])
    have hS := contDiff_list_sum_mul R fun q hq => (hR' q hq).2
    have hd : Differentiable ℝ p.2 := (contDiff_infty_iff_fderiv.1 hp.2).1
    simp only [List.map_cons, List.sum_cons]
    rw [holD_add (show Differentiable ℝ fun z => p.1 z * p.2 z from p.1.differentiable.mul hd)
      (contDiff_infty_iff_fderiv.1 hS).1,
      holD_mul p.1 hp.1 hd, ih hR']

theorem foldr_creation_zero : ∀ (σ W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (u : σ → W) (lam : σ → W → ℂ) (θ : W → ℂ),
    (∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a) → Differentiable ℂ θ →
    ∀ Dl : σ → (W → ℂ) → W → ℂ,
      (∀ l Φ z, Dl l Φ z = lam l z * Φ z +
        (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))) →
      ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) ∧
        L.foldr Dl θ 0 = iteratedFDeriv ℂ L.length θ 0 fun k => u (L.get k) := by
  intro σ W _ _ _ u lam θ hlam hθ Dl hDl L
  choose T hT using fun l => exists_clm_of_antilinear (hlam l).1 (hlam l).2
  have hTI : ∀ l a, T l (I • a) = -I * T l a := by
    intro l a
    rw [← hT l, (hlam l).2, Complex.conj_I]
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ :=
    (GlobalTheory.SCV.contDiff_of_differentiable hθ _).restrict_scalars ℝ
  have step : ∀ l Φ, Dl l Φ = fun z => T l z * Φ z + holD (u l) Φ z := by
    intro l Φ
    funext z
    rw [hDl, ← hT l]
    rfl
  have hsm : ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) := by
    intro L
    induction L with
    | nil => exact hθs
    | cons l L ih =>
      simp only [List.foldr_cons]
      rw [step]
      exact ((T l).contDiff.mul ih).add (contDiff_holD ih (u l))
  have key : ∀ L : List σ, ∃ R : List ((W →L[ℝ] ℂ) × (W → ℂ)),
      (∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) ∧
      L.foldr Dl θ = fun z =>
        L.foldr (fun l => holD (u l)) θ z + (R.map fun p => p.1 z * p.2 z).sum := by
    intro L
    induction L with
    | nil => exact ⟨[], by simp, by funext z; simp⟩
    | cons l L ih =>
      obtain ⟨R, hR, hE⟩ := ih
      refine ⟨(T l, L.foldr Dl θ) :: R.map (fun p => (p.1, holD (u l) p.2)), ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · exact ⟨hTI l, hsm L⟩
        · exact ⟨(hR q hq).1, contDiff_holD (hR q hq).2 (u l)⟩
      · have hD := contDiff_foldr_holD u hθs L
        have hS := contDiff_list_sum_mul R fun p hp => (hR p hp).2
        have e : holD (u l) (L.foldr Dl θ) = fun z =>
            holD (u l) (L.foldr (fun l => holD (u l)) θ) z +
              (R.map fun p => p.1 z * holD (u l) p.2 z).sum := by
          rw [hE, holD_add (contDiff_infty_iff_fderiv.1 hD).1 (contDiff_infty_iff_fderiv.1 hS).1,
            holD_list_sum_mul R hR (u l)]
        funext z
        simp only [List.foldr_cons, step, e, List.map_cons, List.map_map, List.sum_cons,
          Function.comp_def]
        ring
  refine ⟨hsm L, ?_⟩
  obtain ⟨R, -, hE⟩ := key L
  have h0 : (R.map fun p => p.1 0 * p.2 0).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      simp
  rw [hE]
  simp only [h0, add_zero]
  rw [foldr_holD_eq_iteratedFDeriv u hθ L]

end GlobalTheory.Ker.CreOp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RelIndexDualSubmoduleInfOfSelfDual
section
open Module

namespace GlobalTheory

section SelfDual

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem dualSubmodule_le_dualSubmodule_of_le (B : LinearMap.BilinForm ℚ V)
    {M N : Submodule ℤ V} (h : M ≤ N) : B.dualSubmodule N ≤ B.dualSubmodule M :=
  fun _ hx y hy => hx y (h hy)

theorem eq_zero_of_forall_rat_smul_mem (L : Submodule ℤ V) (hL : L.FG) {x : V}
    (hx : ∀ q : ℚ, q • x ∈ L) : x = 0 := by
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL
  haveI := Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V
  let b := Module.Free.chooseBasis ℤ L
  have h1 : x ∈ L := by simpa using hx 1
  have h2 : (⟨x, h1⟩ : L) = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    set a := b.repr ⟨x, h1⟩ i with ha
    have hn : (0 : ℤ) < |a| + 1 := by positivity
    have h3 : (⟨x, h1⟩ : L) = (|a| + 1) • (⟨((|a| + 1 : ℤ) : ℚ)⁻¹ • x, hx _⟩ : L) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
        mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
    refine Int.eq_zero_of_abs_lt_dvd (m := |a| + 1) ⟨b.repr ⟨_, hx ((|a| + 1 : ℤ) : ℚ)⁻¹⟩ i, ?_⟩
      (lt_add_one _)
    rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← h3]
  exact congrArg Subtype.val h2

variable [FiniteDimensional ℚ V]

theorem isLattice_of_fg_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) (hL : L.FG) (hd : (B.dualSubmodule L).FG) : L.IsFullLattice ℚ := by
  haveI : L.IsLattice ℚ := Submodule.IsLattice.of_fg ℚ hL
  constructor
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have h0 : (B.toDual hB).symm φ = 0 := by
    refine eq_zero_of_forall_rat_smul_mem _ hd fun q y hy => ?_
    have h1 : B ((B.toDual hB).symm φ) y = 0 := by
      rw [LinearMap.BilinForm.apply_toDual_symm_apply]
      exact hle (Submodule.subset_span hy)
    rw [map_smul, LinearMap.smul_apply, h1, smul_zero]
    exact zero_mem _
  exact hφ (by simpa using h0)

theorem exists_basis_span_eq_of_isLattice (L : Submodule ℤ V) [L.IsFullLattice ℚ] :
    ∃ b : Basis (Fin (finrank ℚ V)) ℚ V, L = Submodule.span ℤ (Set.range b) := by
  have := Submodule.IsLattice.finite ℚ L
  have := Submodule.IsLattice.free ℚ L
  have hr : finrank ℤ L = finrank ℚ V := by
    let b := Module.Free.chooseBasis ℤ L
    rw [finrank_eq_card_basis b, finrank_eq_card_basis (b.extendOfIsFullLattice ℚ)]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  refine ⟨b.extendOfIsFullLattice ℚ, ?_⟩
  have h1 : Set.range (b.extendOfIsFullLattice ℚ) = L.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    exact funext fun i => b.extendOfIsFullLattice_apply ℚ i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

theorem finrank_eq_of_isLattice (L : Submodule ℤ V) [L.IsFullLattice ℚ] :
    finrank ℤ L = finrank ℚ V := by
  have := Submodule.IsLattice.finite ℚ L
  have := Submodule.IsLattice.free ℚ L
  let b := Module.Free.chooseBasis ℤ L
  rw [finrank_eq_card_basis b, finrank_eq_card_basis (b.extendOfIsFullLattice ℚ)]

theorem isLattice_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [L.IsFullLattice ℚ] : (B.dualSubmodule L).IsFullLattice ℚ := by
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_isLattice L
  rw [B.dualSubmodule_span_of_basis hB]
  haveI : (Submodule.span ℤ (Set.range (B.dualBasis hB b))).IsLattice ℚ :=
    Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _))
  constructor
  rw [Submodule.span_span_of_tower]
  exact (B.dualBasis hB b).span_eq


omit [FiniteDimensional ℚ V] in
theorem relIndex_span_basis_eq_abs_det {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ V)
    (h : Submodule.span ℤ (Set.range b₁) ≤ Submodule.span ℤ (Set.range b₂)) :
    (((Submodule.span ℤ (Set.range b₁)).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range b₂)).toAddSubgroup : ℕ) : ℚ) = |b₂.det b₁| :=
  AddSubgroup.relIndex_eq_abs_det _ _ h b₁ b₂ (Submodule.span_int_eq_addSubgroupClosure _)
    (Submodule.span_int_eq_addSubgroupClosure _)

theorem relIndex_ne_zero_of_isLattice {M N : Submodule ℤ V} [M.IsFullLattice ℚ] [N.IsFullLattice ℚ]
    (h : M ≤ N) : M.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
  obtain ⟨b₁, rfl⟩ := exists_basis_span_eq_of_isLattice M
  obtain ⟨b₂, rfl⟩ := exists_basis_span_eq_of_isLattice N
  intro h0
  have h1 := relIndex_span_basis_eq_abs_det b₁ b₂ h
  rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at h1
  exact (b₂.isUnit_det b₁).ne_zero h1

theorem relIndex_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    {M N : Submodule ℤ V} [M.IsFullLattice ℚ] [N.IsFullLattice ℚ] (h : M ≤ N) :
    (B.dualSubmodule N).toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup =
      M.toAddSubgroup.relIndex N.toAddSubgroup := by
  have h' := dualSubmodule_le_dualSubmodule_of_le B h
  obtain ⟨b₁, rfl⟩ := exists_basis_span_eq_of_isLattice M
  obtain ⟨b₂, rfl⟩ := exists_basis_span_eq_of_isLattice N
  rw [B.dualSubmodule_span_of_basis hB, B.dualSubmodule_span_of_basis hB] at h' ⊢
  apply Nat.cast_injective (R := ℚ)
  rw [relIndex_span_basis_eq_abs_det _ _ h, relIndex_span_basis_eq_abs_det _ _ h',
    Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose (b₂.toMatrix b₁)]
  congr 2
  ext i j
  rw [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.toMatrix_apply,
    LinearMap.BilinForm.dualBasis_repr_apply]
  conv_lhs => rw [← b₂.sum_repr (b₁ i)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left]
  simp

theorem relIndex_dualSubmodule_inf_of_selfDual (B : LinearMap.BilinForm ℚ V)
    (hB : B.Nondegenerate) {L L' : Submodule ℤ V} [L.IsFullLattice ℚ] [L'.IsFullLattice ℚ]
    (hL : B.dualSubmodule L = L) (hL' : B.dualSubmodule L' = L') :
    L'.toAddSubgroup.relIndex (B.dualSubmodule (L ⊓ L')).toAddSubgroup =
      (L ⊓ L').toAddSubgroup.relIndex L.toAddSubgroup := by
  have h1 := relIndex_dualSubmodule B hB (inf_le_left : L ⊓ L' ≤ L)
  have h2 := relIndex_dualSubmodule B hB (inf_le_right : L ⊓ L' ≤ L')
  have l1 := dualSubmodule_le_dualSubmodule_of_le B (inf_le_left : L ⊓ L' ≤ L)
  have l2 := dualSubmodule_le_dualSubmodule_of_le B (inf_le_right : L ⊓ L' ≤ L')
  rw [hL] at h1 l1
  rw [hL'] at h2 l2
  have m1 := AddSubgroup.relIndex_mul_relIndex (L ⊓ L').toAddSubgroup L.toAddSubgroup
    (B.dualSubmodule (L ⊓ L')).toAddSubgroup (inf_le_left : L ⊓ L' ≤ L) l1
  have m2 := AddSubgroup.relIndex_mul_relIndex (L ⊓ L').toAddSubgroup L'.toAddSubgroup
    (B.dualSubmodule (L ⊓ L')).toAddSubgroup (inf_le_right : L ⊓ L' ≤ L') l2
  rw [h1] at m1
  rw [h2, ← m1] at m2
  rw [h2]
  exact Nat.mul_self_inj.1 m2

end SelfDual

theorem card_selfDual_le {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hlr : ∀ x y, B x y = B y x ∨ B x y = - B y x) (L : Submodule ℤ V) (hL : L.FG) (hLd : B.dualSubmodule L = L) (m : ℕ) (hm : 1 ≤ m) :
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.Finite ∧
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.ncard ≤ m ^ (2 * Module.finrank ℚ V) ∧
    ∀ L' : Submodule ℤ V, L'.FG → B.dualSubmodule L' = L' → L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 ∧ (L'.toAddSubgroup.relIndex L.toAddSubgroup = 1 → L' = L) := by
  have hm0 : m ≠ 0 := by omega
  haveI : L.IsFullLattice ℚ := isLattice_of_fg_dualSubmodule B hB L hL (hLd.symm ▸ hL)
  have hinf : ∀ L' : Submodule ℤ V, (L ⊓ L').toAddSubgroup.relIndex L.toAddSubgroup =
      L'.toAddSubgroup.relIndex L.toAddSubgroup := fun L' =>
    AddSubgroup.inf_relIndex_left L.toAddSubgroup L'.toAddSubgroup
  have hsub : {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧
      L'.toAddSubgroup.relIndex L.toAddSubgroup = m} ⊆
      ⋃ M ∈ {M : Submodule ℤ V | M.IsFullLattice ℚ ∧ M ≤ L ∧
        M.toAddSubgroup.relIndex L.toAddSubgroup = m},
        {H | H ≤ B.dualSubmodule M ∧
          H.toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup = m} := by
    rintro L' ⟨h1, h2, h3⟩
    haveI : L'.IsFullLattice ℚ := isLattice_of_fg_dualSubmodule B hB L' h1 (h2.symm ▸ h1)
    refine Set.mem_biUnion (x := L ⊓ L') ⟨inferInstance, inf_le_left, (hinf L').trans h3⟩ ⟨?_, ?_⟩
    · exact h2.ge.trans (dualSubmodule_le_dualSubmodule_of_le B inf_le_right)
    · rw [relIndex_dualSubmodule_inf_of_selfDual B hB hLd h2, hinf, h3]
  have hcard : {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧
      L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.encard ≤
      ((m ^ (2 * finrank ℚ V) : ℕ) : ℕ∞) := by
    rw [two_mul, pow_add]
    refine (Set.encard_le_encard hsub).trans (encard_biUnion_le_mul _ _ _ _ ?_ ?_)
    · have := Submodule.IsLattice.free ℚ L
      have := Submodule.IsLattice.finite ℚ L
      rw [← finrank_eq_of_isLattice L]
      exact (Set.encard_le_encard (show {M : Submodule ℤ V | M.IsFullLattice ℚ ∧ M ≤ L ∧ M.toAddSubgroup.relIndex L.toAddSubgroup = m} ⊆ {M : Submodule ℤ V | M ≤ L ∧ M.toAddSubgroup.relIndex L.toAddSubgroup = m} from fun _ hM => hM.2)).trans
        (encard_setOf_submodule_le_relIndex_eq_le L hm0)
    · intro M hM
      haveI := hM.1
      haveI := isLattice_dualSubmodule B hB M
      have := Submodule.IsLattice.free ℚ (B.dualSubmodule M)
      have := Submodule.IsLattice.finite ℚ (B.dualSubmodule M)
      rw [← finrank_eq_of_isLattice (B.dualSubmodule M)]
      exact encard_setOf_submodule_le_relIndex_eq_le _ hm0
  have hf := Set.finite_of_encard_le_coe hcard
  refine ⟨hf, ?_, fun L' h1 h2 => ⟨?_, fun h3 => ?_⟩⟩
  · rw [← hf.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  · haveI : L'.IsFullLattice ℚ := isLattice_of_fg_dualSubmodule B hB L' h1 (h2.symm ▸ h1)
    rw [← hinf]
    exact relIndex_ne_zero_of_isLattice inf_le_left
  · have h4 : L ≤ L' := AddSubgroup.relIndex_eq_one.1 h3
    refine le_antisymm ?_ h4
    have := dualSubmodule_le_dualSubmodule_of_le B h4
    rwa [hLd, h2] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TestFunctionWitness
section
open Matrix Complex
open scoped Classical
namespace GlobalTheory.SW

private theorem intM_add_iff_of_intM_right {K : Type} [Field K] {κ ι : Type} {x y : Matrix κ ι K} (hy : IntM y) :
    IntM (x + y) ↔ IntM x :=
  ⟨fun h k i => by simpa using (h k i).sub (hy k i), fun h k i => (h k i).add (hy k i)⟩


open Classical in
theorem ind_sb {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    HasLevel 1 (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_one, one_smul]
    by_contra h
    exact hx (if_neg h)
  · rw [Nat.cast_one, one_smul]
    exact if_congr (intM_add_iff_of_intM_right hy) rfl rfl


open Classical in
theorem ind_isSB {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    IsSB (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := ⟨1, one_pos, ind_sb⟩


open Classical in
theorem ind_ne_zero {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [if_pos (show IntM (0 : Matrix κ ι K) from fun k i => by simpa using isIntegral_zero)] at h0
  exact one_ne_zero h0

end GlobalTheory.SW
end

