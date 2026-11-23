module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticeRelativeLengthMapIff
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.LenMap

theorem isTorsionFree_submodule {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M]
    [Module R M] (h : ∀ (c : R) (x : M), c ≠ 0 → c • x = 0 → x = 0) (N : Submodule R M) :
    Module.IsTorsionFree R N := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have h1 : r • ((x : M) - y) = 0 := by
    have := congrArg Subtype.val hxy
    simp only [SetLike.val_smul] at this
    rw [smul_sub, this, sub_self]
  exact Subtype.ext (sub_eq_zero.1 (h r _ hr0 h1))

theorem exists_basis_sum {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') (Z : Submodule R M) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (d : Basis ι R ↥(Z ⊓ LinearMap.ker f)) (e : Basis κ R ↥(Z.map f))
    (σ : κ → M) (hσZ : ∀ j, σ j ∈ Z) (hσf : ∀ j, f (σ j) = e j) :
    ∃ b : Basis (ι ⊕ κ) R Z, ∀ k, (b k : M) = Sum.elim (fun i => (d i : M)) σ k := by
  classical
  let w : ι ⊕ κ → M := Sum.elim (fun i => (d i : M)) σ
  have hwZ : ∀ k, w k ∈ Z := by
    rintro (i | j)
    · exact (Submodule.mem_inf.1 (d i).2).1
    · exact hσZ j
  let u : ι ⊕ κ → Z := fun k => ⟨w k, hwZ k⟩
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  have hdli : LinearIndependent R (fun i => (d i : M)) :=
    d.linearIndependent.map' (Z ⊓ LinearMap.ker f).subtype (Submodule.ker_subtype _)
  have heli : LinearIndependent R (fun j => (e j : M')) :=
    e.linearIndependent.map' (Z.map f).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent R u := by
    apply LinearIndependent.of_comp Z.subtype
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ i, g (Sum.inl i) • (d i : M) + ∑ j, g (Sum.inr j) • σ j = 0 := by
      simpa [Fintype.sum_sum_type, u, w] using hg
    have h2 : ∑ j, g (Sum.inr j) • (e j : M') = 0 := by
      have := congrArg f hg'
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_add (f := _), map_sum, map_smul, hdf, hσf] using this
    have hr : ∀ j, g (Sum.inr j) = 0 := Fintype.linearIndependent_iff.1 heli _ h2
    have h1 : ∑ i, g (Sum.inl i) • (d i : M) = 0 := by simpa [hr] using hg'
    have hl : ∀ i, g (Sum.inl i) = 0 := Fintype.linearIndependent_iff.1 hdli _ h1
    rintro (i | j)
    · exact hl i
    · exact hr j
  have hsp : ⊤ ≤ Submodule.span R (Set.range u) := by
    rintro ⟨z, hz⟩ -
    rw [Submodule.mem_span_range_iff_exists_fun]
    have hfz : f z ∈ Z.map f := Submodule.mem_map_of_mem hz
    let bb := e.repr ⟨f z, hfz⟩
    have hy : (∑ j, bb j • (e j : M')) = f z := by
      have h0 := congrArg Subtype.val (e.sum_repr ⟨f z, hfz⟩)
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul] using h0
    have hk : z - ∑ j, bb j • σ j ∈ Z ⊓ LinearMap.ker f := by
      refine Submodule.mem_inf.2 ⟨Z.sub_mem hz (Z.sum_mem fun j _ => Z.smul_mem _ (hσZ j)), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hσf]
      rw [hy, sub_self]
    have hkk := congrArg Subtype.val (d.sum_repr ⟨_, hk⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hkk
    refine ⟨Sum.elim (d.repr ⟨_, hk⟩) bb, ?_⟩
    apply Subtype.ext
    rw [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]
    simp only [Submodule.coe_smul, Sum.elim_inl, Sum.elim_inr, u, w]
    rw [hkk, sub_add_cancel]
  exact ⟨Basis.mk hli hsp, fun k => by simp [u, w]⟩

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
  [Module (Int0 v) M]

theorem val_det_eq {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b c : Basis ι (Int0 v) X) (b' c' : Basis ι (Int0 v) X')
    (A B : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M))
    (hB : ∀ k, (c' k : M) = ∑ i, B i k • (c i : M)) : v (A.det : C) = v (B.det : C) := by
  have key : ∀ (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
      (A : Matrix ι ι (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
    v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]

theorem relLen_iff_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
    (A : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) (r : ℝ) :
    RelLen v X' X r ↔ v (A.det : C) = r := by
  constructor
  · rintro ⟨n, c, c', B, hB, hr⟩
    let e := b.indexEquiv c
    rw [← hr, ← Matrix.det_reindex_self e.symm B]
    refine val_det_eq v hle b (c.reindex e.symm) b' (c'.reindex e.symm) A _ hA fun k => ?_
    simp only [Basis.reindex_apply, Equiv.symm_symm, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hB]
    exact (Equiv.sum_comp e (fun i => B i (e k) • (c i : M))).symm
  · intro h
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, b.reindex e, b'.reindex e, Matrix.reindex e e A, fun k => ?_, ?_⟩
    · simp only [Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [hA]
      exact (Equiv.sum_comp e.symm (fun i => A i (e.symm k) • (b i : M))).symm
    · rw [Matrix.det_reindex_self]; exact h

theorem card_eq_of_relLen {ι ι' : Type} [Fintype ι] [Fintype ι'] {X' X : Submodule (Int0 v) M}
    {r : ℝ} (h : RelLen v X' X r) (b : Basis ι (Int0 v) X) (b' : Basis ι' (Int0 v) X') :
    Fintype.card ι = Fintype.card ι' := by
  obtain ⟨n, c, c', -, -, -⟩ := h
  rw [Fintype.card_congr (b.indexEquiv c), Fintype.card_congr (b'.indexEquiv c')]

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

theorem relLen_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  intro C _ v M M' _ _ _ _ htM htM' f X' X hle hker hX hX' r
  classical
  haveI := isTorsionFree_submodule htM' (X.map f)
  haveI := isTorsionFree_submodule htM' (X'.map f)
  haveI := isTorsionFree_submodule htM (X ⊓ LinearMap.ker f)
  haveI : Module.Finite (Int0 v) (X.map f) := Module.Finite.map X f
  haveI : Module.Finite (Int0 v) (X'.map f) := Module.Finite.map X' f
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X.map f)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X'.map f)
  let g : X →ₗ[Int0 v] X.map f := f.submoduleMap X
  have hg : Function.Surjective g := f.submoduleMap_surjective X
  haveI : Module.FinitePresentation (Int0 v) (X.map f) := Module.finitePresentation_of_projective _ _
  have hfg : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g hg
  have hK : (LinearMap.ker g).map X.subtype = X ⊓ LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy
      simpa [g] using this
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [g] using hfx), rfl⟩
  haveI : Module.Finite (Int0 v) ↥(X ⊓ LinearMap.ker f) := by
    rw [Module.Finite.iff_fg, ← hK]
    exact hfg.map _
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := ↥(X ⊓ LinearMap.ker f))
  have hK' : X' ⊓ LinearMap.ker f = X ⊓ LinearMap.ker f :=
    le_antisymm (inf_le_inf_right _ hle) (le_inf hker inf_le_right)
  obtain ⟨q, ⟨d⟩⟩ : ∃ q : ℕ, Nonempty (Basis (Fin q) (Int0 v) ↥(X ⊓ LinearMap.ker f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p, ⟨c⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p', ⟨c'⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X'.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  let d' : Basis (Fin q) (Int0 v) ↥(X' ⊓ LinearMap.ker f) := d.map (LinearEquiv.ofEq _ _ hK'.symm)
  have hd' : ∀ i, (d' i : M) = d i := fun i => rfl
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  choose σ hσX hσf using fun j => Submodule.mem_map.1 (c j).2
  choose σ' hσX' hσf' using fun j => Submodule.mem_map.1 (c' j).2
  obtain ⟨b, hb⟩ := exists_basis_sum f X d c σ hσX hσf
  obtain ⟨b', hb'⟩ := exists_basis_sum f X' d' c' σ' hσX' hσf'
  by_cases hp : p = p'
  · subst hp
    let A : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) (Int0 v) :=
      Matrix.of fun i k => b.repr (Submodule.inclusion hle (b' k)) i
    have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
      intro k
      have h0 := congrArg Subtype.val (b.sum_repr (Submodule.inclusion hle (b' k)))
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul, Submodule.coe_inclusion, A, Matrix.of_apply] using h0.symm
    rw [relLen_iff_of_basis v hle b b' A hA]
    let B := A.toBlocks₂₂
    have hB : ∀ k, (c' k : M') = ∑ j, B j k • (c j : M') := by
      intro k
      have h1 := congrArg f (hA (Sum.inr k))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hb', Sum.elim_inr, hσf', map_sum, Fintype.sum_sum_type] at h1
      simpa [hb, hdf, hσf, B, Matrix.toBlocks₂₂] using h1
    rw [relLen_iff_of_basis v (Submodule.map_mono hle) c c' B hB]
    have hinl : ∀ i, Submodule.inclusion hle (b' (Sum.inl i)) = b (Sum.inl i) := by
      intro i
      apply Subtype.ext
      rw [Submodule.coe_inclusion, hb, hb', Sum.elim_inl, Sum.elim_inl, hd']
    have h11 : A.toBlocks₁₁ = 1 := by
      ext i k
      simp [A, Matrix.toBlocks₁₁, hinl, Finsupp.single_apply, Matrix.one_apply, eq_comm]
    have h21 : A.toBlocks₂₁ = 0 := by
      ext i k
      simp [A, Matrix.toBlocks₂₁, hinl, Finsupp.single_apply]
    have hdet : A.det = B.det := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks A, h11, h21]
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    rw [hdet]
  · constructor
    · intro h
      have := card_eq_of_relLen v h b b'
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    · intro h
      have := card_eq_of_relLen v h c c'
      simp only [Fintype.card_fin] at this
      exact absurd this hp

end GlobalTheory.LenMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.HasQ.mdifferentiable {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N)
    (h : _root_.GlobalTheory.QFam.HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  exact ((_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h').mdifferentiable (by exact_mod_cast hN)


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty :
    ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → _root_.GlobalTheory.QFam.HasQ N f a →
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  intro N f a hN h
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  have hq := (_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h'
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨hq.mdifferentiable hpos, hq.isBoundedAtImInfty hpos⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumAbsNormCpowUnitClassesPartialZeta
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.PartialZetaSum

variable {F : Type} [Field F] [NumberField F]

theorem exists_ideal (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ J : Ideal (𝓞 F), (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [← FractionalIdeal.le_one_iff_exists_coeIdeal]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
      ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 b.2.1) _
    _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

def idealOf (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : Ideal (𝓞 F) := (exists_ideal 𝔟 b).choose

theorem idealOf_coe (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
  (exists_ideal 𝔟 b).choose_spec

theorem span_eq (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [idealOf_coe, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem idealOf_mem (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : idealOf 𝔟 b ∈ (Ideal (𝓞 F))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have h1 := span_eq 𝔟 b
  rw [h] at h1
  simp at h1
  exact b.2.2 h1

theorem idealOf_class (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ = (ClassGroup.mk F 𝔟)⁻¹ := by
  rw [← ClassGroup.mk_mk0 F, ← map_inv]
  have hb : (b.1 : F) ≠ 0 := b.2.2
  have h : FractionalIdeal.mk0 F ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ =
      toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb) * 𝔟⁻¹ := by
    apply Units.ext
    rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, idealOf_coe]
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb)) = 1 := by
    rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  rw [h, map_mul, hp, one_mul]

theorem rel_of_idealOf_eq (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : idealOf 𝔟 b = idealOf 𝔟 b') : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b' := by
  have h2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b'.1 := by
    rw [span_eq, span_eq, h]
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h2
  exact ⟨z, by rw [← hz, Units.smul_def, Algebra.smul_def]⟩

theorem idealOf_eq_of_rel (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b') : idealOf 𝔟 b = idealOf 𝔟 b' := by
  obtain ⟨ε, hε⟩ := h
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe, idealOf_coe, hε]
  congr 1
  exact FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, by rw [Units.smul_def, Algebra.smul_def]⟩

theorem exists_of_class (𝔟 : Frac F) (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹) :
    ∃ b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F), idealOf 𝔟 b = J.1 := by
  have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * 𝔟) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hJ, inv_mul_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hx' : ((FractionalIdeal.mk0 F J * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    beta_reduce
    rw [FractionalIdeal.coe_spanSingleton]; exact hx
  rw [Units.val_mul, FractionalIdeal.coe_mk0] at hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx'
    exact (mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero J)) (Units.ne_zero 𝔟)) hx'
  have hxm : x ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
    have : FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [← hx']
      calc ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
          ≤ 1 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
        _ = _ := one_mul _
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 this
  let b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := ⟨x, hxm, hx0⟩
  refine ⟨b, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe]
  show FractionalIdeal.spanSingleton (𝓞 F)⁰ x * _ = _
  rw [← hx', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem norm_eq (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    |((Algebra.norm ℚ b.1 : ℚ) : ℝ)| = (Ideal.absNorm (idealOf 𝔟 b) : ℝ) * nrm 𝔟 := by
  have h2 := congrArg FractionalIdeal.absNorm (span_eq 𝔟 b)
  rw [FractionalIdeal.absNorm_span_singleton, map_mul, FractionalIdeal.coeIdeal_absNorm] at h2
  unfold nrm
  rw [← Rat.cast_abs, h2]; push_cast; ring

theorem nrm_nonneg (𝔟 : Frac F) : 0 ≤ nrm 𝔟 := by
  unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _

theorem hasSum_norm_cpow : ∀ (F : Type) [Field F] [NumberField F] (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ s : ℂ, 1 < s.re → HasSum (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-s)) (((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔟 : ℝ) : ℂ) ^ (-s) * Zb s) := by
  intro F _ _ 𝔟 Zb hZ s hs
  let e : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) →
      {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹} :=
    fun c => ⟨⟨idealOf 𝔟 c.out, idealOf_mem 𝔟 c.out⟩, idealOf_class 𝔟 c.out⟩
  have he : Function.Bijective e := by
    constructor
    · intro c c' h
      have h' : idealOf 𝔟 c.out = idealOf 𝔟 c'.out := congrArg (fun J => (J.1.1 : Ideal (𝓞 F))) h
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact Quotient.sound (rel_of_idealOf_eq 𝔟 h')
    · intro J
      obtain ⟨b, hb⟩ := exists_of_class 𝔟 J.1 J.2
      refine ⟨Quotient.mk _ b, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show idealOf 𝔟 (Quotient.mk _ b).out = J.1.1
      rw [← hb]; exact idealOf_eq_of_rel 𝔟 (Quotient.exact (Quotient.out_eq _))
  have key := (hZ.2 s hs).mul_left (((nrm 𝔟 : ℝ) : ℂ) ^ (-s))
  rw [← (Equiv.ofBijective e he).hasSum_iff] at key
  refine (congrArg (fun f => HasSum f _) ?_).mpr key
  funext c
  simp only [Function.comp_apply, Equiv.ofBijective_apply, e]
  rw [norm_eq 𝔟 c.out, ofReal_mul, mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (nrm_nonneg 𝔟), mul_comm,
    ofReal_natCast]

end GlobalTheory.PartialZetaSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumLambertDoubleSeriesDivisors
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem summable_lambert_prod (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ) (hQ : ‖Q‖ < 1)
    (hc : ∀ d m, ‖c d m‖ ≤ 1) :
    Summable fun x : ℕ+ × ℕ+ =>
      ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ)) := by
  have h := summable_prod_mul_pow (𝕜 := ℝ) e (r := ‖Q‖) (by simpa using hQ)
  refine Summable.of_norm_bounded h fun x => ?_
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  calc ((x.2 : ℕ) : ℝ) ^ e * ‖c x.1 x.2‖ ≤ ((x.2 : ℕ) : ℝ) ^ e * 1 := by
        gcongr; exact hc _ _
    _ = _ := mul_one _

theorem hasSum_lambert : ∀ (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ), ‖Q‖ < 1 → (∀ d m, ‖c d m‖ ≤ 1) → HasSum (fun k : ℕ => (∑ m ∈ k.divisors, (m : ℂ) ^ e * c (k / m) m) * Q ^ k) (∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c d m * Q ^ ((d : ℕ) * (m : ℕ))) := by
  intro e Q c hQ hc
  have hs := summable_lambert_prod e Q c hQ hc
  rw [← hs.tsum_prod]
  have h1 := sigmaAntidiagonalEquivProd.hasSum_iff.mpr hs.hasSum
  have h2 := h1.sigma (fun n => hasSum_fintype _)
  refine (Function.Injective.hasSum_iff (g := PNat.val) PNat.coe_injective ?_).mp ?_
  · intro k hk
    have : k = 0 := by
      by_contra h
      exact hk ⟨⟨k, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [this]
  · refine HasSum.congr_fun h2 fun n => ?_
    symm
    have h3 : ∀ x : Nat.divisorsAntidiagonal (n : ℕ),
        ((fun x : ℕ+ × ℕ+ => ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ))) ∘
          sigmaAntidiagonalEquivProd) ⟨n, x⟩ =
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)) x.1 := fun x => rfl
    rw [Finset.sum_congr rfl (fun x _ => h3 x),
      Finset.sum_coe_sort (Nat.divisorsAntidiagonal (n : ℕ))
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)),
      Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => (b : ℂ) ^ e * c a b * Q ^ (a * b))]
    simp only [Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m hm => by
      rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)]

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumRowsInvCubeDerivWeierstrassP
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem hasSum_prod_derivWeierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3)
      (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  have h := ((tauPair τ).hasSum_derivWeierstrassP z).mul_left (-(1 / 2))
  let e : ℤ × ℤ ≃ (tauPair τ).lattice :=
    (Equiv.neg (ℤ × ℤ)).trans (tauPair τ).latticeEquivProd.symm.toEquiv
  rw [← e.hasSum_iff] at h
  have key : (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3) =
      (fun i : (tauPair τ).lattice => -(1 / 2) * (-2 / (z - (i : ℂ)) ^ 3)) ∘ e := ?_
  · rw [key]; exact h
  funext p
  have he : ((e p : (tauPair τ).lattice) : ℂ) = -(p.1 * (τ : ℂ) + p.2) := by
    change ((tauPair τ).latticeEquivProd.symm (-p)).1 = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [tauPair]
    ring
  simp only [Function.comp, he]
  rw [show z - -(p.1 * (τ : ℂ) + p.2) = z + p.1 * (τ : ℂ) + p.2 by ring]
  ring

theorem hasSum_rows_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  intro τ z
  have h := hasSum_prod_derivWeierstrassP τ z
  exact h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum

end GlobalTheory.WpFam
end

