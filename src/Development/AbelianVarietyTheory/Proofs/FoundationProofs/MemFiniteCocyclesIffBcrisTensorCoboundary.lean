module

public import Mathlib
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

noncomputable section

namespace GlobalTheory.CoeffExt

open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

section Linear

variable {R : Type} [Ring R] {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module R W]
  [Module R W'] {ι : Type}

def subEquiv (E : W' ≃ₗ[R] (ι → W)) (S' : Submodule R W') (S : Submodule R W)
    (h : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) : ↥S' ≃ₗ[R] (ι → ↥S) where
  toFun x i := ⟨E x i, (h x).1 x.2 i⟩
  invFun y := ⟨E.symm fun i => (y i : W), (h _).2 fun i => by simp⟩
  map_add' x y := by funext i; apply Subtype.ext; simp
  map_smul' c x := by funext i; apply Subtype.ext; simp
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by funext i; apply Subtype.ext; simp

end Linear

section Length

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {W W' : Type} [AddCommGroup W]
  [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W'] [IsScalarTower O O' W'] {ι : Type}
  [Fintype ι]

end Length

section Tensor

variable {Qp : Type} [Field Qp] {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
  [Algebra Qp LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  [Module LL' V'] [IsScalarTower Qp LL' V']
  {ι : Type} [Fintype ι] [DecidableEq ι] (E : V' ≃ₗ[LL] (ι → V))

def tensCoord (C : Type) [AddCommGroup C] [Module Qp C] :
    V' ⊗[Qp] C ≃ₗ[LL] (ι → V ⊗[Qp] C) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun i => AlgebraTensorModule.map (LinearMap.proj i ∘ₗ E.toLinearMap) LinearMap.id)
    (∑ i, AlgebraTensorModule.map (E.symm.toLinearMap ∘ₗ LinearMap.single LL (fun _ => V) i)
      LinearMap.id ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.pi_ext' fun j => ?_
      refine AlgebraTensorModule.ext fun v c => ?_
      funext i
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.single_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h])
    (by
      refine AlgebraTensorModule.ext fun v c => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.proj_apply, LinearMap.pi_apply, AlgebraTensorModule.map_tmul,
        LinearMap.single_apply, LinearEquiv.coe_coe]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_tmul, ← map_sum, Finset.univ_sum_single, E.symm_apply_apply])

theorem tensCoord_map {C D : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup D] [Module Qp D]
    (φ' : V' →ₗ[LL'] V') (φ : V →ₗ[LL] V) (h : ∀ x i, E (φ' x) i = φ (E x i)) (ψ : C →ₗ[Qp] D)
    (x : V' ⊗[Qp] C) (i : ι) :
    tensCoord E D (AlgebraTensorModule.map φ' ψ x) i =
      AlgebraTensorModule.map φ ψ (tensCoord E C x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tensCoord, h]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]

end Tensor

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}

omit [Algebra LL LL'] [IsScalarTower LL LL' V'] in
theorem tensCoord_actVB (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (g : G) (x : V' ⊗[Qp] B)
    (i : ι) : tensCoord E B (actVB PD ρ' g x) i = actVB PD ρ g (tensCoord E B x i) := by
  unfold actVB
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i

omit [Algebra LL LL'] [IsScalarTower LL LL' V'] in
theorem tensCoord_actVdR (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (g : G) (x : V' ⊗[Qp] BdR)
    (i : ι) : tensCoord E BdR (actVdR PD ρ' g x) i = actVdR PD ρ g (tensCoord E BdR x i) := by
  unfold actVdR
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i

omit [Algebra LL LL'] [IsScalarTower LL LL' V'] in
theorem mem_Dcris_iff (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (x : V' ⊗[Qp] B) :
    x ∈ Dcris PD ρ' ↔ ∀ i, tensCoord E B x i ∈ Dcris PD ρ := by
  have key : ∀ {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
      (r : Representation LL G W) (y : W ⊗[Qp] B), y ∈ Dcris PD r ↔ ∀ g, actVB PD r g y = y := by
    intro W _ _ _ _ r y
    simp [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
  have key' : x ∈ Dcris PD ρ' ↔ ∀ g, actVB PD ρ' g x = x := by
    simp [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
  rw [key']
  constructor
  · intro hx i
    rw [key]
    intro g
    rw [← tensCoord_actVB PD hE g x i, hx g]
  · intro hx g
    apply (tensCoord E B).injective
    funext i
    rw [tensCoord_actVB PD hE]
    exact (key _ _).1 (hx i) g

theorem finrank_fun' {F M : Type} [Field F] [AddCommGroup M] [Module F M] (ι : Type) [Fintype ι] :
    finrank F (ι → M) = Fintype.card ι * finrank F M := by
  by_cases hM : Module.Finite F M
  · simp [Module.finrank_pi_fintype]
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · rw [Module.finrank_zero_of_subsingleton]
      simp
    ·
      have hnot : ¬ Module.Finite F (ι → M) := fun h =>
        hM (Module.Finite.of_surjective (LinearMap.proj i : (ι → M) →ₗ[F] M)
          (fun m => ⟨fun _ => m, rfl⟩))
      rw [Module.finrank_of_not_finite hnot, Module.finrank_of_not_finite hM, mul_zero]

theorem isCrys_ext (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hι : finrank LL LL' = Fintype.card ι) [Nonempty ι] (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  unfold IsCrys at h ⊢
  have hn : 0 < Fintype.card ι := Fintype.card_pos

  let eD : ↥((Dcris PD ρ').restrictScalars LL) ≃ₗ[LL] (ι → ↥(Dcris PD ρ)) :=
    subEquiv (tensCoord E B) _ _ (fun x => mem_Dcris_iff PD hE x)
  have h1 : finrank LL ↥(Dcris PD ρ') = Fintype.card ι * finrank LL ↥(Dcris PD ρ) := by
    have h0 := eD.finrank_eq
    rw [finrank_fun'] at h0
    exact h0
  have h2 : finrank LL V' = Fintype.card ι * finrank LL V := by
    rw [E.finrank_eq, finrank_fun']
  have t1 := Module.finrank_mul_finrank LL LL' ↥(Dcris PD ρ')
  have t2 := Module.finrank_mul_finrank LL LL' V'
  rw [hι] at t1 t2
  have e1 : finrank LL' ↥(Dcris PD ρ') = finrank Qp K₀ * finrank LL V :=
    Nat.eq_of_mul_eq_mul_left hn (by rw [t1, h1, h])
  have e2 : finrank LL' V' = finrank LL V := Nat.eq_of_mul_eq_mul_left hn (by rw [t2, h2])
  rw [e1, e2]

theorem mem_FildR_iff (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (τ : K →ₐ[Qp] LL)
    (τ' : K →ₐ[Qp] LL') (hτ : ∀ c, τ' c = algebraMap LL LL' (τ c)) (a : ℤ) (x : V' ⊗[Qp] BdR) :
    x ∈ FildR PD ρ' τ' a ↔ ∀ i, tensCoord E BdR x i ∈ FildR PD ρ τ a := by

  have hA : ∀ y : V' ⊗[Qp] BdR, y ∈ DdR PD ρ' ↔ ∀ i, tensCoord E BdR y i ∈ DdR PD ρ := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    constructor
    · intro hy i g
      rw [← tensCoord_actVdR PD hE g y i, hy g]
    · intro hy g
      apply (tensCoord E BdR).injective
      funext i
      rw [tensCoord_actVdR PD hE]
      exact hy i g

  have hmul : ∀ (c : K) (y : V' ⊗[Qp] BdR) i,
      tensCoord E BdR (mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL') c y) i =
        mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (tensCoord E BdR y i) :=
    fun c y i => tensCoord_map E LinearMap.id LinearMap.id (fun _ _ => rfl) _ y i
  have hsm : ∀ (c : K) (y : V' ⊗[Qp] BdR) i,
      tensCoord E BdR (τ' c • y) i = τ c • tensCoord E BdR y i := by
    intro c y i
    rw [hτ, algebraMap_smul, map_smul, Pi.smul_apply]
  have hB : ∀ y : V' ⊗[Qp] BdR, (∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL') c y =
      τ' c • y) ↔ ∀ i, ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
        (tensCoord E BdR y i) = τ c • tensCoord E BdR y i := by
    intro y
    constructor
    · intro hy i c
      rw [← hmul, ← hsm, hy c]
    · intro hy c
      apply (tensCoord E BdR).injective
      funext i
      rw [hmul, hsm]
      exact hy i c

  have hC : ∀ y : V' ⊗[Qp] BdR, y ∈ FilV PD (LL := LL') (V := V') a ↔
      ∀ i, tensCoord E BdR y i ∈ FilV PD (LL := LL) (V := V) a := by
    intro y
    have hmap : ∀ (z : V' ⊗[Qp] ↥((PD.Fil a).restrictScalars Qp)) i,
        tensCoord E BdR (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL'] V')
          ((PD.Fil a).restrictScalars Qp).subtype z) i =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype
          (tensCoord E _ z i) :=
      fun z i => tensCoord_map E LinearMap.id LinearMap.id (fun _ _ => rfl) _ z i
    simp only [FilV, LinearMap.mem_range]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨tensCoord E _ z i, (hmap z i).symm⟩
    · intro hy
      choose z hz using hy
      refine ⟨(tensCoord E _).symm z, ?_⟩
      apply (tensCoord E BdR).injective
      funext i
      rw [hmap, LinearEquiv.apply_symm_apply, hz i]
  simp only [FildR, DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  rw [hA, hB, hC]
  simp only [forall_and]

end Period

section Cochains

variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  {V V' : Type} [AddCommGroup V] [AddCommGroup V'] [Module LL V] [Module LL V'] [Module O V]
  [Module O V'] [IsScalarTower O LL V] [IsScalarTower O LL V'] {ι : Type}

end Cochains

section Lat

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    {O O' : Type} [CommRing O] [CommRing O'] [Algebra O LL] [Algebra O' LL']
    {ι : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace G]

section One

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [Module O V'] [IsScalarTower O LL V']
    [Module O' V'] [IsScalarTower O' LL' V']
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {E : V' ≃ₗ[LL] (ι → V)} {L : Lattice (O := O) ρ} {L' : Lattice (O := O') ρ'}

end One

section Two

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [Module O V₁] [IsScalarTower O LL V₁]
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul LL V₁]
    {V₁' : Type} [AddCommGroup V₁'] [Module LL V₁'] [Module Qp V₁'] [IsScalarTower Qp LL V₁']
    [Module LL' V₁'] [IsScalarTower Qp LL' V₁'] [Module O V₁'] [IsScalarTower O LL V₁']
    [Module O' V₁'] [IsScalarTower O' LL' V₁']
    [TopologicalSpace V₁'] [ContinuousAdd V₁'] [ContinuousConstSMul LL' V₁']
    {ρ₁ : Representation LL G V₁} {ρ₁' : Representation LL' G V₁'}
    {E₁ : V₁' ≃ₗ[LL] (ι → V₁)} {L₁ : Lattice (O := O) ρ₁} {L₁' : Lattice (O := O') ρ₁'}
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [Module O V₂] [IsScalarTower O LL V₂]
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul LL V₂]
    {V₂' : Type} [AddCommGroup V₂'] [Module LL V₂'] [Module Qp V₂'] [IsScalarTower Qp LL V₂']
    [Module LL' V₂'] [IsScalarTower Qp LL' V₂'] [Module O V₂'] [IsScalarTower O LL V₂']
    [Module O' V₂'] [IsScalarTower O' LL' V₂']
    [TopologicalSpace V₂'] [ContinuousAdd V₂'] [ContinuousConstSMul LL' V₂']
    {ρ₂ : Representation LL G V₂} {ρ₂' : Representation LL' G V₂'}
    {E₂ : V₂' ≃ₗ[LL] (ι → V₂)} {L₂ : Lattice (O := O) ρ₂} {L₂' : Lattice (O := O') ρ₂'}
    (F : LatHom L₁ L₂) (F' : LatHom L₁' L₂')

end Two


end Lat

theorem finrank_ext {O O' : Type} [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O']
    {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W']
    [IsScalarTower O O' W'] {ι : Type} [Fintype ι] (b : Basis ι O O') (E : W' ≃ₗ[O] (ι → W))
    (S' : Submodule O' W') (S : Submodule O W) [Module.Free O' ↥S'] [Module.Free O ↥S]
    (hS : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) : finrank O' ↥S' = finrank O ↥S := by
  have : Nontrivial O := (algebraMap O O').domain_nontrivial
  have : Module.Free O O' := Module.Free.of_basis b
  have : Nonempty ι := b.index_nonempty
  have hn : 0 < Fintype.card ι := Fintype.card_pos

  let eS : ↥(S'.restrictScalars O) ≃ₗ[O] (ι → ↥S) := subEquiv E (S'.restrictScalars O) S hS
  have hpi : finrank O (ι → ↥S) = Fintype.card ι * finrank O ↥S :=
    (Finsupp.linearEquivFunOnFinite O ↥S ι).finrank_eq.symm.trans (finrank_finsupp O ↥S)
  have t := Module.finrank_mul_finrank O O' ↥S'
  have t' : finrank O ↥S' = finrank O (ι → ↥S) := eS.finrank_eq
  rw [Module.finrank_eq_card_basis b, t', hpi] at t
  exact Nat.eq_of_mul_eq_mul_left hn t

end GlobalTheory.CoeffExt
