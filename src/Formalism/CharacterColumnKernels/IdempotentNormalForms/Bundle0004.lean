module

public import Formalism.CharacterColumnKernels.Bundle0002

@[expose] public section

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.IdemNormalForm
section
open Module

noncomputable section

namespace Formalism.NG

theorem burnside : StatBurnside := by
  intro k A V _ _ _ _ _ _ _ _ hS hsc f
  classical
  have := hS
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        simp only [Module.End.smul_def, hc, RingHom.id_apply, f.map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k V))
  refine ⟨a, (Module.finBasis k V).ext fun i => ?_⟩
  have := ha (Module.finBasis k V i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa [F] using this.symm

section RankMod

variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]

private theorem free_of_isCompl [IsLocalRing O] (p q : Submodule O (r → O)) (h : IsCompl p q) :
    Module.Free O p ∧ Module.Finite O p := by
  have hproj : Module.Projective O p :=
    Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  have hfin : Module.Finite O p :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl p q h) (fun x => ⟨x, Submodule.linearProjOfIsCompl_apply_left h x⟩)
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩

private theorem idem_normal_form [IsLocalRing O] (e : Matrix r r O) (he : IsIdempotentElem e) :
    ∃ (P Q : Matrix r r O) (d : r → O), (∀ j, d j = 0 ∨ d j = 1) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      e = P * Matrix.diagonal d * Q := by
  classical
  let f : (r → O) →ₗ[O] (r → O) := Matrix.toLin' e
  have hf : f * f = f := by
    show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e
    rw [← Matrix.toLin'_mul, he.eq]
  have hc : IsCompl (LinearMap.range f) (LinearMap.ker f) :=
    LinearMap.IsIdempotentElem.isCompl hf
  obtain ⟨hpF, hpFin⟩ := free_of_isCompl _ _ hc
  obtain ⟨hqF, hqFin⟩ := free_of_isCompl _ _ hc.symm
  let bp := Module.Free.chooseBasis O (LinearMap.range f)
  let bq := Module.Free.chooseBasis O (LinearMap.ker f)
  let b0 := (bp.prod bq).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let σ := b0.indexEquiv (Pi.basisFun O r)
  let b := b0.reindex σ
  have hfb : ∀ j, f (b j) = (if (σ.symm j).isLeft then (1 : O) else 0) • b j := by
    intro j
    rw [Basis.reindex_apply]
    rcases σ.symm j with k | k
    · have hk : (b0 (Sum.inl k) : r → O) = (bp k : r → O) := by
        simp [b0, Basis.map_apply, Basis.prod_apply]
      simp only [Sum.isLeft_inl, if_true, one_smul, hk]
      obtain ⟨y, hy⟩ := (bp k).2
      rw [← hy]
      show (f * f) y = f y
      rw [hf]
    · have hk : (b0 (Sum.inr k) : r → O) = (bq k : r → O) := by
        simp [b0, Basis.map_apply, Basis.prod_apply]
      simp only [Sum.isLeft_inr, Bool.false_eq_true, if_false, zero_smul, hk]
      exact LinearMap.mem_ker.mp (bq k).2
  have hdiag : LinearMap.toMatrix b b f =
      Matrix.diagonal fun i => if (σ.symm i).isLeft then (1 : O) else 0 := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hfb, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine ⟨(Pi.basisFun O r).toMatrix b, b.toMatrix (Pi.basisFun O r),
    fun i => if (σ.symm i).isLeft then (1 : O) else 0,
    fun j => by by_cases h : (σ.symm j).isLeft <;> simp [h],
    Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  rw [← hdiag, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,
    LinearMap.toMatrix_eq_toMatrix']
  exact (LinearMap.toMatrix'_toLin' e).symm

private theorem rank_map_conj {F : Type*} [Field F] (f : O →+* F) (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ((P * Matrix.diagonal d * Q).map f).rank = Nat.card {j // d j = 1} := by
  classical
  have hm1 : P.map f * Q.map f = 1 := by
    rw [← Matrix.map_mul, hPQ]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have hm2 : Q.map f * P.map f = 1 := by
    rw [← Matrix.map_mul, hQP]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hm2),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hm1),
    Matrix.diagonal_map (map_zero f), Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro j
  constructor
  · intro h
    rcases hd j with h0 | h1
    · exact (h (by rw [h0, map_zero])).elim
    · exact h1
  · intro h1
    rw [h1, map_one]
    exact one_ne_zero

end RankMod

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.MemCcIdealIffForall
section
open Finset

noncomputable section

namespace Formalism.NG

theorem mem_ccIdeal_iff_forall {O : Type*} [CommRing O] {X : Type*} (T : Subalgebra O (X → O))
    (Z : Set X) (c : T) : c ∈ ccIdeal T Z ↔ ∀ x ∉ Z, (c : X → O) x = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa [resOff] using this
  · intro h
    funext x
    simp [resOff, h x.1 x.2]

theorem vccBaseChange : StatVccBaseChange := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X T T' hT' Z x
  classical
  set b := Module.Free.chooseBasis O O' with hb
  set φ : (X → O) → (X → O') := fun f => algebraMap O O' ∘ f with hφ
  have hdec : ∀ f ∈ Submodule.span O' (φ '' (T : Set (X → O))),
      ∃ g : Module.Free.ChooseBasisIndex O O' → (X → O), (∀ j, g j ∈ T) ∧ f = ∑ j, b j • φ (g j) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨t, ht, rfl⟩ := hf
      refine ⟨fun j => b.repr 1 j • t, fun j => T.smul_mem ht _, ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      calc algebraMap O O' (t x') = algebraMap O O' (t x') * ∑ j, b.repr 1 j • b j := by
            rw [b.sum_repr, mul_one]
        _ = ∑ j, b j * algebraMap O O' (b.repr 1 j * t x') := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, map_mul]
            ring
    | zero =>
      refine ⟨0, fun j => T.zero_mem, ?_⟩
      funext x'
      simp [hφ]
    | add f f' _ _ hf hf' =>
      obtain ⟨g, hg, rfl⟩ := hf
      obtain ⟨g', hg', rfl⟩ := hf'
      refine ⟨g + g', fun j => T.add_mem (hg j) (hg' j), ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        map_add, mul_add, Finset.sum_add_distrib]
    | smul o f _ hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      refine ⟨fun k => ∑ j, b.repr (o * b j) k • g j, fun k => T.sum_mem fun j _ => T.smul_mem (hg j) _, ?_⟩
      funext x'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_sum, map_mul]
      calc o * ∑ j, b j * algebraMap O O' (g j x') = ∑ j, (o * b j) * algebraMap O O' (g j x') := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (∑ k, b.repr (o * b j) k • b k) * algebraMap O O' (g j x') := by
            simp_rw [b.sum_repr]
        _ = ∑ k, b k * ∑ j, algebraMap O O' (b.repr (o * b j) k) * algebraMap O O' (g j x') := by
            simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hvan : ∀ (g : Module.Free.ChooseBasisIndex O O' → X → O) (x' : X),
      ∑ j, b j * algebraMap O O' (g j x') = 0 → ∀ j, g j x' = 0 := by
    intro g x' h
    have h2 : ∑ j, g j x' • b j = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ h2
  apply le_antisymm
  · have hne : ((fun c : T => IsDiscreteValuationRing.addVal O ((c : X → O) x)) ''
        (ccIdeal T Z : Set T)).Nonempty := ⟨_, 0, (ccIdeal T Z).zero_mem, rfl⟩
    obtain ⟨c0, hc0, hc0eq⟩ := csInf_mem hne
    have hvcc : vcc T Z x = IsDiscreteValuationRing.addVal O ((c0 : X → O) x) := by
      rw [show IsDiscreteValuationRing.addVal O ((c0 : X → O) x) = _ from hc0eq, sInf_image]
      rfl
    rw [hvcc, ← he]
    have hmem : φ (c0 : X → O) ∈ T' := by
      have h1 : φ (c0 : X → O) ∈ (T' : Set (X → O')) := by
        rw [hT']
        exact Submodule.subset_span ⟨c0, c0.2, rfl⟩
      exact h1
    have hc0' : (⟨φ (c0 : X → O), hmem⟩ : T') ∈ ccIdeal T' Z := by
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T Z c0).mp hc0 x' hx'
      simp [hφ, h0]
    exact iInf₂_le _ hc0'
  · unfold vcc
    refine le_iInf₂ fun c' hc' => ?_
    have hc'span : (c' : X → O') ∈ Submodule.span O' (φ '' (T : Set (X → O))) := by
      have h1 : (c' : X → O') ∈ (T' : Set (X → O')) := c'.2
      rw [hT'] at h1
      exact h1
    obtain ⟨g, hg, hgeq⟩ := hdec _ hc'span
    have hgZ : ∀ j, (⟨g j, hg j⟩ : T) ∈ ccIdeal T Z := by
      intro j
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T' Z c').mp hc' x' hx'
      rw [hgeq] at h0
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at h0
      exact hvan g x' h0 j
    rw [hgeq]
    simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    refine AddValuation.map_le_sum _ fun j _ => ?_
    rw [AddValuation.map_mul, he]
    refine le_trans ?_ le_add_self
    exact mul_le_mul_of_nonneg_left (iInf₂_le (⟨g j, hg j⟩ : T) (hgZ j)) (zero_le)

end Formalism.NG
end
end

