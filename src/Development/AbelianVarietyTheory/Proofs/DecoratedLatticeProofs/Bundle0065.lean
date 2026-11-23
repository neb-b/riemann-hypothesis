module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EquivariantHomMultiplicityFreeIrreducible
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.EquivHomIrr

theorem tensor_eq_of_coord_contract {A B ι : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (b : Module.Basis ι ℂ B) (x y : A ⊗[ℂ] B)
    (h : ∀ i, TensorProduct.rid ℂ A (LinearMap.lTensor A (b.coord i) x)
      = TensorProduct.rid ℂ A (LinearMap.lTensor A (b.coord i) y)) : x = y := by
  classical
  have key : ∀ (z : A ⊗[ℂ] B) (i), TensorProduct.equivFinsuppOfBasisRight b z i
      = TensorProduct.rid ℂ A (LinearMap.lTensor A (b.coord i) z) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, key, h]

theorem contract_map_left {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (l : Module.Dual ℂ B) (f : A →ₗ[ℂ] A) (y : A ⊗[ℂ] B) :
    TensorProduct.rid ℂ A (LinearMap.lTensor A l (TensorProduct.map f LinearMap.id y))
      = f (TensorProduct.rid ℂ A (LinearMap.lTensor A l y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem intertwining_eq_zero_of_isEmpty {G V A : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup A] [Module ℂ A] (ρ : Representation ℂ G V) (α : Representation ℂ G A)
    (hρ : ρ.IsIrreducible) (hα : α.IsIrreducible) (hne : IsEmpty (ρ.Equiv α))
    (f : ρ.IntertwiningMap α) : f = 0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with h | h
  · exact (hne.false (f.ofBijective h)).elim
  · exact h

theorem intertwining_eq_smul {G V A : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup A] [Module ℂ A] (ρ : Representation ℂ G V)
    (α : Representation ℂ G A) (hρ : ρ.IsIrreducible) (ι : ρ.Equiv α)
    (f : ρ.IntertwiningMap α) : ∃ c : ℂ, ∀ v, f v = c • ι v := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (ι.symm.toIntertwiningMap.comp f)
  refine ⟨c, fun v => ?_⟩
  have h1 := congrArg (fun F : ρ.IntertwiningMap ρ => F v) hc
  simp only [Representation.IntertwiningMap.algebraMap_apply] at h1
  calc f v = ι (ι.symm (f v)) := by simp
    _ = ι (c • v) := by
      have h2 : ι.symm (f v) = c • v := h1.symm
      rw [h2]
    _ = c • ι v := map_smul _ _ _

end GlobalTheory.EquivHomIrr

namespace GlobalTheory.EquivHomIrr

theorem equivariantHom_mem_of_stable : ∀ (G H J : Type) [Group G] [Group H] [DecidableEq J] (A B : J → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)] [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, FiniteDimensional ℂ (A j)] [∀ j, FiniteDimensional ℂ (B j)] (α : ∀ j, Representation ℂ G (A j)) (β : ∀ j, Representation ℂ H (B j)), (∀ j, (α j).IsIrreducible) → (∀ j, (β j).IsIrreducible) → (∀ j j', Nonempty ((α j).Equiv (α j')) → j = j') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ω : Representation ℂ (G × H) W), Nonempty ((Representation.directSum fun j => Representation.tprod ((α j).comp (MonoidHom.fst G H)) ((β j).comp (MonoidHom.snd G H))).Equiv ω) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V), ρ.IsIrreducible → ∀ S : Submodule ℂ (V →ₗ[ℂ] W), (∀ T ∈ S, ∀ g v, T (ρ g v) = ω (g, 1) (T v)) → (∀ T ∈ S, ∀ h, ω (1, h) ∘ₗ T ∈ S) → S ≠ ⊥ → ∀ Q : V →ₗ[ℂ] W, (∀ g v, Q (ρ g v) = ω (g, 1) (Q v)) → Q ∈ S := by
  intro G H J _ _ _ A B _ _ _ _ _ _ α β hα hβ hαinj W _ _ ω he V _ _ _ ρ hρ S hSG hSH hS0 Q hQ
  classical
  obtain ⟨e⟩ := he
  set R := Representation.directSum fun j => Representation.tprod ((α j).comp (MonoidHom.fst G H))
    ((β j).comp (MonoidHom.snd G H)) with hR
  have heS : ∀ (x : G × H) (w : W), e.symm (ω x w) = R x (e.symm w) := fun x w =>
    LinearMap.congr_fun (e.symm.isIntertwining' x) w
  have heF : ∀ (x : G × H) y, e (R x y) = ω x (e y) := fun x y =>
    LinearMap.congr_fun (e.isIntertwining' x) y
  let con : ∀ j, Module.Dual ℂ (B j) → (DirectSum J fun j => A j ⊗[ℂ] B j) →ₗ[ℂ] A j := fun j l =>
    (TensorProduct.rid ℂ (A j)).toLinearMap ∘ₗ LinearMap.lTensor (A j) l ∘ₗ
      DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j
  have hcon : ∀ j l (g : G) y, con j l (R (g, 1) y) = α j g (con j l y) := by
    intro j l g y
    have h1 : DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j (R (g, 1) y)
        = TensorProduct.map (α j g) LinearMap.id (DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j y) := by
      rw [hR, Representation.directSum_apply]
      simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
        MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, Module.End.one_eq_id]
      rfl
    simp only [con, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, contract_map_left]
  let cT : ∀ T : V →ₗ[ℂ] W, (∀ g v, T (ρ g v) = ω (g, 1) (T v)) → ∀ j, Module.Dual ℂ (B j) →
      ρ.IntertwiningMap (α j) := fun T hT j l =>
    { toLinearMap := con j l ∘ₗ e.symm.toLinearMap ∘ₗ T
      isIntertwining' := fun g => LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply]
        rw [hT, Representation.Equiv.coe_toLinearMap, heS, hcon] }
  have hcT : ∀ (T : V →ₗ[ℂ] W) hT j l v, cT T hT j l v = con j l (e.symm (T v)) := fun _ _ _ _ _ => rfl
  have hzero : ∀ (T : V →ₗ[ℂ] W) (hT : ∀ g v, T (ρ g v) = ω (g, 1) (T v)) j, IsEmpty (ρ.Equiv (α j)) → ∀ v,
      DirectSum.component ℂ J (fun j => A j ⊗[ℂ] B j) j (e.symm (T v)) = 0 := by
    intro T hT j hj v
    apply tensor_eq_of_coord_contract (Module.Free.chooseBasis ℂ (B j))
    intro i
    have h0 := intertwining_eq_zero_of_isEmpty ρ (α j) hρ (hα j) hj
      (cT T hT j ((Module.Free.chooseBasis ℂ (B j)).coord i))
    have h2 := congrArg (fun F : ρ.IntertwiningMap (α j) => F v) h0
    simp only [hcT, Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at h2
    simpa [con] using h2
  by_cases hex : ∃ j0, Nonempty (ρ.Equiv (α j0))
  swap
  · have hQ0 : Q = 0 := by
      refine LinearMap.ext fun v => (EquivLike.injective e.symm) ?_
      rw [LinearMap.zero_apply, map_zero]
      refine DirectSum.ext_component ℂ fun j => ?_
      rw [map_zero]
      exact hzero Q hQ j (not_nonempty_iff.1 fun h => hex ⟨j, h⟩) v
    rw [hQ0]
    exact S.zero_mem
  obtain ⟨j0, ⟨ι⟩⟩ := hex
  have honly : ∀ j, j ≠ j0 → IsEmpty (ρ.Equiv (α j)) := fun j hj =>
    ⟨fun κ => hj (hαinj j0 j ⟨ι.symm.trans κ⟩).symm⟩
  let Φ : B j0 →ₗ[ℂ] (V →ₗ[ℂ] W) :=
    { toFun := fun b => e.toLinearMap ∘ₗ DirectSum.lof ℂ J (fun j => A j ⊗[ℂ] B j) j0 ∘ₗ
        (TensorProduct.mk ℂ (A j0) (B j0)).flip b ∘ₗ ι.toLinearMap
      map_add' := by intros; ext; simp [TensorProduct.tmul_add]
      map_smul' := by intros; ext; simp }
  have hΦ : ∀ b v, e.symm (Φ b v) = DirectSum.lof ℂ J (fun j => A j ⊗[ℂ] B j) j0 (ι v ⊗ₜ b) := by
    intro b v
    simp [Φ]
  have hrep : ∀ T : V →ₗ[ℂ] W, (∀ g v, T (ρ g v) = ω (g, 1) (T v)) → ∃ b, Φ b = T := by
    intro T hT
    let bs := Module.Free.chooseBasis ℂ (B j0)
    choose c hc using fun i => intertwining_eq_smul ρ (α j0) hρ ι (cT T hT j0 (bs.coord i))
    have hc' : ∀ i v, con j0 (bs.coord i) (e.symm (T v)) = c i • ι v := fun i v => hc i v
    refine ⟨bs.repr.symm (Finsupp.equivFunOnFinite.symm c),
      LinearMap.ext fun v => (EquivLike.injective e.symm) ?_⟩
    rw [hΦ]
    refine DirectSum.ext_component ℂ fun j => ?_
    by_cases hj : j = j0
    · subst hj
      rw [DirectSum.component.lof_self]
      apply tensor_eq_of_coord_contract bs
      intro i
      have h3 := hc' i v
      simp only [con, LinearMap.comp_apply, LinearEquiv.coe_coe] at h3
      rw [h3]
      simp
    · rw [DirectSum.component.of, dite_eq_right (Ne.symm hj), hzero T hT j (honly j hj) v]
  let S' : Subrepresentation (β j0) :=
    { toSubmodule := S.comap Φ
      apply_mem_toSubmodule := by
        intro h b hb
        simp only [Submodule.mem_comap] at hb ⊢
        have hh : Φ (β j0 h b) = (ω (1, h)) ∘ₗ Φ b := by
          refine LinearMap.ext fun v => (EquivLike.injective e.symm) ?_
          rw [hΦ, LinearMap.comp_apply, heS, hΦ, hR, Representation.directSum_apply,
            DirectSum.lmap_lof]
          simp
        rw [hh]
        exact hSH _ hb h }
  haveI := hβ j0
  rcases eq_bot_or_eq_top S' with h | h
  · exfalso
    apply hS0
    rw [eq_bot_iff]
    intro T hT
    obtain ⟨b, rfl⟩ := hrep T (hSG T hT)
    have hb : b ∈ S'.toSubmodule := hT
    rw [h] at hb
    have hb0 : b = 0 := (Submodule.mem_bot ℂ).1 hb
    rw [hb0, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨b, rfl⟩ := hrep Q hQ
    have hb : b ∈ S'.toSubmodule := by rw [h]; exact Submodule.mem_top
    exact hb

end GlobalTheory.EquivHomIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocks
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.BlockPoly

variable (ι σ : Type) [Fintype ι] [DecidableEq ι]

noncomputable def blockMul :
    (ι → MvPolynomial σ ℂ) →ₘₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap)

theorem blockMul_apply (f : ι → MvPolynomial σ ℂ) :
    blockMul ι σ f = ∏ τ, rename (Prod.mk τ) (f τ) := by
  simp [blockMul]

noncomputable def expEquiv : (ι → σ →₀ ℕ) ≃ (ι × σ →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.trans Finsupp.curryEquiv.symm

theorem expEquiv_apply (d : ι → σ →₀ ℕ) (a : ι) (b : σ) : expEquiv ι σ d (a, b) = d a b := by
  simp [expEquiv]

theorem sum_mapDomain_eq (d : ι → σ →₀ ℕ) :
    ∑ τ, (d τ).mapDomain (Prod.mk τ) = expEquiv ι σ d := by
  ext ⟨a, b⟩
  rw [expEquiv_apply, Finset.sum_apply', Finset.sum_eq_single a]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => by simpa using h) _ _
  · intro τ _ hτ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨c, hc⟩
    exact hτ (congrArg Prod.fst hc)
  · intro h; exact absurd (Finset.mem_univ a) h

theorem prod_rename_monomial (d : ι → σ →₀ ℕ) :
    ∏ τ, rename (Prod.mk τ) (monomial (d τ) (1 : ℂ)) = monomial (expEquiv ι σ d) 1 := by
  simp only [rename_monomial]
  rw [← monomial_sum_one, sum_mapDomain_eq]

noncomputable def blockEquiv :
    PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).equiv
    (basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

theorem blockEquiv_toLinearMap :
    (blockEquiv ι σ).toLinearMap = PiTensorProduct.lift (blockMul ι σ) := by
  refine (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).ext (fun p => ?_)
  rw [LinearEquiv.coe_coe, blockEquiv, Module.Basis.equiv_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.lift.tprod, blockMul_apply]
  simp only [coe_basisMonomials]
  rw [prod_rename_monomial]

theorem blockEquiv_tprod (f : ι → MvPolynomial σ ℂ) :
    blockEquiv ι σ (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  rw [← LinearEquiv.coe_coe, blockEquiv_toLinearMap, PiTensorProduct.lift.tprod, blockMul_apply]

theorem map_subtype_injective (U : ι → Submodule ℂ (MvPolynomial σ ℂ)) :
    Function.Injective (PiTensorProduct.map fun τ => (U τ).subtype) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective (U τ).subtype (U τ).ker_subtype
  have h : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) =
      LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  exact Function.LeftInverse.injective (g := PiTensorProduct.map g)
    (fun x => by simpa using LinearMap.congr_fun h x)

theorem exists_blockEquiv :
    ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  intro ι σ _ _
  refine ⟨blockEquiv ι σ, blockEquiv_tprod ι σ, fun U => ⟨?_, ?_⟩⟩
  · exact (blockEquiv ι σ).injective.comp (map_subtype_injective ι σ U)
  · rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨fun τ => (g τ : MvPolynomial σ ℂ), fun τ => (g τ).2, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (fun τ => (⟨f τ, hf τ⟩ : U τ)), ⟨_, rfl⟩, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]

end GlobalTheory.BlockPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentities
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem sum_three_fintype_reverse {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ y, ∑ x, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_fintype_permute {α β γ δ M : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := by
  calc ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ j, ∑ k, ∑ l, f k j i l := sum_three_fintype_reverse _
    _ = ∑ i, ∑ j, ∑ l, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem mvZ_subY_comp (hab : a ≤ b) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (subY hab y') = (subY hab (fun τ => h τ * y' τ)).comp (lft g) := by
  apply MvPolynomial.algHom_ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, AlgHom.comp_apply, subY, lft, aeval_X, aeval_X, map_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, mvZ, subY, aeval_X, algHom_C, algebraMap_eq, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_three_fintype_reverse]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_mvZ_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (mvZ g' h') = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, mvZ, aeval_X, algHom_C, algebraMap_eq, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_fintype_permute]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lft_lft_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) :
    (lft g).comp (lft g') = lft (fun τ => g' τ * g τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, lft, aeval_X, algHom_C, algebraMap_eq, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_one : mvZ (ι := ι) (a := a) (b := b) (fun _ => 1) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [mvZ, Matrix.one_apply, apply_ite C, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem lft_one : lft (ι := ι) (a := a) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [lft, Matrix.one_apply]

def scaleFP (t : ι → ℂ) : FP ι a b →ₐ[ℂ] FP ι a b :=
  aeval fun v => C (t v.1) * X v

theorem subY_smul (hab : a ≤ b) (t : ι → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    subY hab (fun τ => t τ • y' τ) = (scaleFP t).comp (subY hab y') := by
  apply MvPolynomial.algHom_ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [subY, scaleFP, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C,
    Matrix.smul_apply, smul_eq_mul, C_mul, algebraMap_eq]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem scaleVariables_monomial (t : ι → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    scaleFP t (monomial m (1 : ℂ)) = (m.prod fun k n => t k.1 ^ n) • monomial m (1 : ℂ) := by
  rw [scaleFP, aeval_monomial, map_one, one_mul, ← C_mul', ← prod_X_pow_eq_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]

theorem jetL_monomial_one (c : ι → ℂ) (G : VCx ι a b → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    jetL c G (monomial m (1 : ℂ)) = jetC c G m := by
  have e : (monomial m (1 : ℂ) : FP ι a b) = basisMonomials (ι × Fin b × Fin a) ℂ m := by
    rw [coe_basisMonomials]
  rw [e, jetL, Module.Basis.constr_basis]

theorem jetL_comp_scale (c t : ι → ℂ) (G : VCx ι a b → ℂ) :
    (jetL c G).comp (scaleFP (a := a) (b := b) t).toLinearMap = jetL (fun τ => c τ * t τ) G := by
  refine (basisMonomials (ι × Fin b × Fin a) ℂ).ext fun m => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coe_basisMonomials]
  rw [scaleVariables_monomial, map_smul, jetL_monomial_one, jetL_monomial_one, smul_eq_mul, jetC, jetC, ← mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (frDet ℂ a τ : PY ι a) = (y τ).det := by
  rw [evalAt, frDet, RingHom.map_det]
  congr 1
  ext α s
  simp

theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (F * ∏ τ, (frDet ℂ a τ : PY ι a)) = evalAt y F * ∏ τ, (y τ).det := by
  unfold evalAt
  rw [map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => evalAt_frDet y τ

theorem frDet_prod_ne_zero : (∏ τ, (frDet ℂ a τ : PY ι a)) ≠ 0 := by
  intro h
  have h1 : (1 : PY ι a) * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by rw [one_mul, h]
  have h2 := congrArg (evalAt (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ))) h1
  rw [evalAt_mul_prod] at h2
  simp [evalAt] at h2

theorem eq_zero_of_invertible (F : PY ι a) (hF : ∀ y, IsInv y → evalAt y F = 0) : F = 0 := by
  have h0 : F * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by
    apply MvPolynomial.funext
    intro x
    have key : eval x (F * ∏ τ, (frDet ℂ a τ : PY ι a)) =
        evalAt (fun τ => Matrix.of fun α s => x (τ, α, s)) (F * ∏ τ, (frDet ℂ a τ : PY ι a)) := rfl
    rw [map_zero, key, evalAt_mul_prod]
    by_cases hI : IsInv (fun τ => Matrix.of fun α s => x (τ, α, s))
    · rw [hF _ hI, zero_mul]
    · simp only [IsInv, not_forall] at hI
      obtain ⟨τ, hτ⟩ := hI
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by simpa using hτ), mul_zero]
  exact (mul_eq_zero.mp h0).resolve_right frDet_prod_ne_zero

theorem evalAt_lft_eq (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  simp only [evalAt, lft]
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, hp, aeval_X, eval_X, map_sum, eval_C, Matrix.mul_apply]

theorem substIdentities : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), (∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), mvZ g h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) (lft g F)) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b), mvZ g h (mvZ g' h' P) = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) P) ∧ (∀ P : FP ι a b, mvZ (fun _ => 1) (fun _ => 1) P = P) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), lft g (lft g' F) = lft (fun τ => g' τ * g τ) F) ∧ (∀ F : PY ι a, lft (fun _ => 1) F = F) ∧ (∀ (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F) ∧ (∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) ∧ ∀ (c t : ι → ℂ) (G : VCx ι a b → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), jetL c G (subY hab (fun τ => t τ • y' τ) F) = jetL (fun τ => c τ * t τ) G (subY hab y' F) := by
  intro ι _ a b hab
  refine ⟨fun g h y' F => ?_, fun g g' h h' P => ?_, fun P => ?_, fun g g' F => ?_, fun F => ?_,
    fun g y F => evalAt_lft_eq g y F, fun F hF => eq_zero_of_invertible F hF, fun c t G y' F => ?_⟩
  · have := DFunLike.congr_fun (mvZ_subY_comp hab g h y') F
    simpa only [AlgHom.comp_apply] using this
  · have := DFunLike.congr_fun (mvZ_mvZ_comp g g' h h') P
    simpa only [AlgHom.comp_apply] using this
  · rw [mvZ_one, AlgHom.id_apply]
  · have := DFunLike.congr_fun (lft_lft_comp g g') F
    simpa only [AlgHom.comp_apply] using this
  · rw [lft_one, AlgHom.id_apply]
  · rw [subY_smul, AlgHom.comp_apply, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, jetL_comp_scale]

end GlobalTheory.KJInf
end
end

