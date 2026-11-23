module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0004
public import GroundTheory.AutomorphicForms.RealGroupsLie

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.LocallyConstantCompact
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology
open scoped Pointwise

section Space

variable (X : Type*) [TopologicalSpace X] (R E : Type*) [Semiring R] [AddCommMonoid E]
  [Module R E]

def locallyConstantCompactSupport : Submodule R (X → E) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' {f g} hf hg := ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨hf.1.comp (c • ·), hf.2.mono fun x hx => by
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])⟩

variable {X R E}

theorem mem_locallyConstantCompactSupport {f : X → E} :
    f ∈ locallyConstantCompactSupport X R E ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

theorem indicator_mem_locallyConstantCompactSupport [T2Space X] {U : Set X} (hc : IsCompact U)
    (ho : IsOpen U) (e : E) :
    U.indicator (fun _ => e) ∈ locallyConstantCompactSupport X R E := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const X e) ⟨hc.isClosed, ho⟩).isLocallyConstant

theorem range_finite_of_mem_locallyConstantCompactSupport {f : X → E}
    (hf : f ∈ locallyConstantCompactSupport X R E) : (range f).Finite := by
  have : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2
  have h1 : (range fun x : tsupport f => f x).Finite :=
    (hf.1.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact mem_insert _ _

theorem isCompact_isOpen_fiber {f : X → E} (hf : f ∈ locallyConstantCompactSupport X R E)
    {v : E} (hv : v ≠ 0) : IsCompact {x | f x = v} ∧ IsOpen {x | f x = v} := by
  refine ⟨hf.2.of_isClosed_subset (hf.1.isClosed_fiber v) fun x hx => ?_, hf.1.isOpen_fiber v⟩
  refine subset_tsupport f ?_
  have hx : f x = v := hx
  simp [Function.mem_support, hx, hv]

end Space

section Group

variable {G : Type*} [Group G] {E : Type*}

theorem mk_eq_iff_mem_out_smul (K : Subgroup G) (x : G ⧸ K) (y : G) :
    (y : G ⧸ K) = x ↔ y ∈ x.out • (K : Set G) := by
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [eq_comm, QuotientGroup.eq, mem_leftCoset_iff, SetLike.mem_coe]

theorem apply_eq_of_mem_smul {K : Subgroup G} {f : G → E}
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {g y : G} (hy : y ∈ g • (K : Set G)) : f y = f g := by
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  exact hK g k hk

variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]

theorem mem_locallyConstantCompactSupport_of_forall_mul_right (K : OpenSubgroup G)
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f ∈ locallyConstantCompactSupport G R E := by
  refine ⟨(IsLocallyConstant.iff_exists_open f).2 fun g => ?_, hf⟩
  refine ⟨g • (K : Set G), K.isOpen.smul g, ?_, fun y hy => apply_eq_of_mem_smul hK hy⟩
  exact Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩

theorem finite_image_mk_tsupport (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f) :
    (QuotientGroup.mk '' tsupport f : Set (G ⧸ (K : Subgroup G))).Finite :=
  (hf.image QuotientGroup.continuous_mk).finite_of_discrete

theorem eq_sum_indicator_coset (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f)
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f = ∑ x ∈ (finite_image_mk_tsupport K hf).toFinset,
      (x.out • (K : Set G)).indicator (fun _ => f x.out) := by
  classical
  funext y
  rw [Finset.sum_apply]
  by_cases hy : (y : G ⧸ (K : Subgroup G)) ∈ (finite_image_mk_tsupport K hf).toFinset
  · rw [Finset.sum_eq_single (y : G ⧸ (K : Subgroup G))]
    · have hmem : y ∈ (y : G ⧸ (K : Subgroup G)).out • (K : Set G) :=
        (mk_eq_iff_mem_out_smul (K : Subgroup G) _ y).1 rfl
      rw [Set.indicator_of_mem hmem]
      exact apply_eq_of_mem_smul hK hmem
    · intro b _ hb
      exact Set.indicator_of_notMem
        (fun h => hb ((mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h).symm) _
    · intro h
      exact absurd hy h
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hy ((Set.Finite.mem_toFinset _).2 ⟨y, subset_tsupport f h, rfl⟩)
    · intro b hb
      refine Set.indicator_of_notMem (fun h => hy ?_) _
      rwa [(mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h]

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem exists_forall_mul_right {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ g, ∀ k ∈ K, f (g * k) = f g := by
  let W : Set (G × G) := {p | f (p.1 * p.2) = f p.1}
  have hW : IsOpen W := by
    have hF : IsLocallyConstant fun p : G × G => (f (p.1 * p.2), f p.1) :=
      (hf.1.comp_continuous continuous_mul).prodMk (hf.1.comp_continuous continuous_fst)
    exact hF {q | q.1 = q.2}
  have hsub : tsupport f ×ˢ ({1} : Set G) ⊆ W := by
    rintro ⟨g, k⟩ ⟨-, hk⟩
    simp only [mem_singleton_iff] at hk
    simp [W, hk]
  obtain ⟨u, v, -, hv, hSu, h1v, huv⟩ := generalized_tube_lemma hf.2 isCompact_singleton hW hsub
  obtain ⟨K, hKc, hKv⟩ := exists_openSubgroup_isCompact_subset (hv.mem_nhds (h1v rfl))
  have key : ∀ s ∈ tsupport f, ∀ k ∈ K, f (s * k) = f s := fun s hs k hk =>
    huv (show (s, k) ∈ u ×ˢ v from ⟨hSu hs, hKv hk⟩)
  refine ⟨K, hKc, fun g k hk => ?_⟩
  by_cases hg : g ∈ tsupport f
  · exact key g hg k hk
  · rw [image_eq_zero_of_notMem_tsupport hg]
    by_contra h
    have := key (g * k) (subset_tsupport f h) k⁻¹ (inv_mem hk)
    rw [mul_inv_cancel_right, image_eq_zero_of_notMem_tsupport hg] at this
    exact h this.symm

theorem exists_forall_mul_left {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, ∀ g, f (k * g) = f g := by
  have hf' : (fun g => f g⁻¹) ∈ locallyConstantCompactSupport G R E :=
    ⟨hf.1.comp_continuous continuous_inv, hf.2.comp_homeomorph (Homeomorph.inv G)⟩
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_right hf'
  refine ⟨K, hKc, fun k hk g => ?_⟩
  have := hK g⁻¹ k⁻¹ (inv_mem hk)
  simpa [mul_inv_rev] using this

theorem exists_forall_mul_left_mul_right {f : G → E}
    (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ k ∈ K, ∀ g, ∀ k' ∈ K, f (k * g * k') = f g := by
  obtain ⟨K₁, h₁, hK₁⟩ := exists_forall_mul_right hf
  obtain ⟨K₂, -, hK₂⟩ := exists_forall_mul_left hf
  refine ⟨K₁ ⊓ K₂, isCompact_inf_left h₁, fun k hk g k' hk' => ?_⟩
  rw [mul_assoc, hK₂ k (OpenSubgroup.mem_inf.1 hk).2, hK₁ g k' (OpenSubgroup.mem_inf.1 hk').1]

end Group

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.RealGroupsPolar
section
namespace GroundTheory.Automorphic

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem continuousOn_matrix_inv :
    ContinuousOn (fun A : Matrix n n 𝕜 => A⁻¹) {A | IsUnit A} := by
  rintro _ ⟨u, rfl⟩
  have h := NormedRing.inverse_continuousAt u
  have he : (fun A : Matrix n n 𝕜 => A⁻¹) = Ring.inverse := funext nonsing_inv_eq_ringInverse
  rw [he]
  exact h.continuousWithinAt

theorem posDef_conjTranspose_mul_self_GL (g : GL n 𝕜) : ((g : Matrix n n 𝕜)ᴴ * g).PosDef :=
  PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)

noncomputable def polarPos (g : GL n 𝕜) : Matrix n n 𝕜 := CFC.sqrt ((g : Matrix n n 𝕜)ᴴ * g)

theorem polarPos_posDef (g : GL n 𝕜) : (polarPos g).PosDef := by
  have h := posDef_conjTranspose_mul_self_GL g
  rw [← isStrictlyPositive_iff_posDef] at h ⊢
  exact IsStrictlyPositive.sqrt _ h

theorem polarPos_mul_self (g : GL n 𝕜) : polarPos g * polarPos g = (g : Matrix n n 𝕜)ᴴ * g :=
  CFC.sqrt_mul_sqrt_self _ ((posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarUnitary (g : GL n 𝕜) : Matrix n n 𝕜 := (g : Matrix n n 𝕜) * (polarPos g)⁻¹

theorem isUnit_det_of_posDef {p : Matrix n n 𝕜} (hp : p.PosDef) : IsUnit p.det :=
  (isUnit_iff_isUnit_det p).1 hp.isUnit

theorem polarUnitary_mem (g : GL n 𝕜) : polarUnitary g ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hP : (polarPos g)ᴴ = polarPos g := (polarPos_posDef g).isHermitian
  have hd := isUnit_det_of_posDef (polarPos_posDef g)
  rw [star_eq_conjTranspose, polarUnitary, conjTranspose_mul, conjTranspose_nonsing_inv, hP]
  calc (polarPos g)⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * (polarPos g)⁻¹)
      = (polarPos g)⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * (polarPos g)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarPos g)⁻¹ * (polarPos g * polarPos g) * (polarPos g)⁻¹ := by rw [polarPos_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hd]

theorem polarUnitary_mul_polarPos (g : GL n 𝕜) : polarUnitary g * polarPos g = g := by
  rw [polarUnitary, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef (polarPos_posDef g)), Matrix.mul_one]

theorem polar_unique {g : GL n 𝕜} {k p : Matrix n n 𝕜} (hk : k ∈ unitaryGroup n 𝕜)
    (hp : p.PosDef) (h : k * p = g) : polarPos g = p ∧ polarUnitary g = k := by
  have hkk : kᴴ * k = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hk
  have hP : pᴴ = p := hp.isHermitian
  have hpp : p * p = (g : Matrix n n 𝕜)ᴴ * g := by
    rw [← h, conjTranspose_mul, hP]
    calc p * p = p * (kᴴ * k) * p := by rw [hkk, Matrix.mul_one]
      _ = p * kᴴ * (k * p) := by simp only [Matrix.mul_assoc]
  have h1 : polarPos g = p := CFC.sqrt_unique hpp hp.posSemidef.nonneg
  refine ⟨h1, ?_⟩
  rw [polarUnitary, h1, ← h, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hp), Matrix.mul_one]

noncomputable def polarMul (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) : GL n 𝕜 :=
    ⟨kp.1 * kp.2, kp.2.1⁻¹ * star (kp.1 : Matrix n n 𝕜), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (kp.2 : Matrix n n 𝕜),
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef kp.2.2), Matrix.one_mul]
      exact mem_unitaryGroup_iff.1 kp.1.2, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star (kp.1 : Matrix n n 𝕜)),
        mem_unitaryGroup_iff'.1 kp.1.2, Matrix.one_mul,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef kp.2.2)]⟩

noncomputable def polarEquiv : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ GL n 𝕜 where
  toFun := polarMul
  invFun g := (⟨polarUnitary g, polarUnitary_mem g⟩, ⟨polarPos g, polarPos_posDef g⟩)
  left_inv kp := by
    obtain ⟨⟨k, hk⟩, ⟨p, hp⟩⟩ := kp
    have := polar_unique (g := polarMul (⟨k, hk⟩, ⟨p, hp⟩)) hk hp rfl
    exact Prod.ext (Subtype.ext this.2) (Subtype.ext this.1)
  right_inv g := Units.ext (polarUnitary_mul_polarPos g)

theorem continuous_polarPos
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    Continuous (polarPos : GL n 𝕜 → Matrix n n 𝕜) :=
  hsqrt.comp_continuous
    ((Units.continuous_val.matrix_conjTranspose).mul Units.continuous_val)
    (fun g => (posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarHomeomorph
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ₜ GL n 𝕜 where
  toEquiv := polarEquiv
  continuous_toFun := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    · exact (continuousOn_matrix_inv.comp_continuous (continuous_subtype_val.comp continuous_snd)
        (fun kp => kp.2.2.isUnit)).mul
        (continuous_star.comp (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    have hP := continuous_polarPos (n := n) (𝕜 := 𝕜) hsqrt
    refine Continuous.prodMk ?_ (hP.subtype_mk _)
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.mul
      (continuousOn_matrix_inv.comp_continuous hP (fun g => (polarPos_posDef g).isUnit))

noncomputable def polarHomeomorphReal :
    unitaryGroup n ℝ × {p : Matrix n n ℝ // p.PosDef} ≃ₜ GL n ℝ :=
  polarHomeomorph CFC.continuousOn_sqrt

noncomputable def polarHomeomorphComplex :
    unitaryGroup n ℂ × {p : Matrix n n ℂ // p.PosDef} ≃ₜ GL n ℂ :=
  polarHomeomorph CFC.continuousOn_sqrt

section ExpHermitianComplex

theorem posDef_exp_of_isHermitian_complex {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)

noncomputable def expHermitianHomeomorphComplex :
    {X : Matrix n n ℂ // X.IsHermitian} ≃ₜ {p : Matrix n n ℂ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_complex X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℂ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _

noncomputable def polarExpHomeomorphComplex :
    unitaryGroup n ℂ × {X : Matrix n n ℂ // X.IsHermitian} ≃ₜ GL n ℂ :=
  ((Homeomorph.refl _).prodCongr expHermitianHomeomorphComplex).trans polarHomeomorphComplex

theorem coe_polarExpHomeomorphComplex_apply
    (kX : unitaryGroup n ℂ × {X : Matrix n n ℂ // X.IsHermitian}) :
    ((polarExpHomeomorphComplex kX : GL n ℂ) : Matrix n n ℂ) = kX.1 * NormedSpace.exp kX.2.1 :=
  rfl

end ExpHermitianComplex

section ExpHermitianReal

theorem posDef_exp_of_isHermitian_real {X : Matrix n n ℝ} (hX : X.IsHermitian) :
    (NormedSpace.exp X).PosDef := by
  have h0 : 0 ≤ NormedSpace.exp X := IsSelfAdjoint.exp_nonneg (hX : IsSelfAdjoint X)
  exact (nonneg_iff_posSemidef.1 h0).posDef_iff_isUnit.2 (Matrix.isUnit_exp X)

noncomputable def expHermitianHomeomorphReal :
    {X : Matrix n n ℝ // X.IsHermitian} ≃ₜ {p : Matrix n n ℝ // p.PosDef} where
  toFun X := ⟨NormedSpace.exp X.1, posDef_exp_of_isHermitian_real X.2⟩
  invFun p := ⟨CFC.log p.1, IsSelfAdjoint.log⟩
  left_inv X := Subtype.ext (CFC.log_exp X.1 (X.2 : IsSelfAdjoint X.1))
  right_inv p := Subtype.ext (CFC.exp_log p.1 (isStrictlyPositive_iff_posDef.2 p.2))
  continuous_toFun :=
    ((contDiff_exp ℝ (Matrix n n ℝ) (n := 0)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (CFC.continuousOn_log.comp_continuous continuous_subtype_val
      (fun p => ⟨(p.2.isHermitian : IsSelfAdjoint p.1), p.2.isUnit⟩)).subtype_mk _

noncomputable def polarExpHomeomorphReal :
    unitaryGroup n ℝ × {X : Matrix n n ℝ // X.IsHermitian} ≃ₜ GL n ℝ :=
  ((Homeomorph.refl _).prodCongr expHermitianHomeomorphReal).trans polarHomeomorphReal

theorem coe_polarExpHomeomorphReal_apply
    (kX : unitaryGroup n ℝ × {X : Matrix n n ℝ // X.IsHermitian}) :
    ((polarExpHomeomorphReal kX : GL n ℝ) : Matrix n n ℝ) = kX.1 * NormedSpace.exp kX.2.1 :=
  rfl

end ExpHermitianReal

end GroundTheory.Automorphic
end

