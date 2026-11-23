module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply

@[expose] public section

open TensorProduct

namespace GlobalTheory.Forms

abbrev Bil (Y A : Type*) [AddCommGroup Y] [AddCommGroup A] := Y →ₗ[ℤ] Y →ₗ[ℤ] A

section Symmetric

variable (S : Type*) [Semiring S] (Y : Type*) [AddCommGroup Y] (A : Type*) [AddCommGroup A]
  [Module S A]

def symForms : Submodule S (Bil Y A) where
  carrier := {b | ∀ y y', b y y' = b y' y}
  add_mem' {b c} hb hc y y' := by simp only [LinearMap.add_apply, hb y y', hc y y']
  zero_mem' _ _ := rfl
  smul_mem' s b hb y y' := by simp only [LinearMap.smul_apply, hb y y']

variable {S Y A}

theorem mem_symForms {b : Bil Y A} : b ∈ symForms S Y A ↔ ∀ y y', b y y' = b y' y := Iff.rfl

theorem mem_symForms_iff_flip {b : Bil Y A} : b ∈ symForms S Y A ↔ b.flip = b :=
  ⟨fun h => by ext y y'; exact h y' y, fun h y y' => by
    conv_lhs => rw [← h]
    rfl⟩

variable (Y) in
abbrev SymLattice : Type _ := symForms ℤ Y ℤ

instance [Module.Finite ℤ Y] [Module.Free ℤ Y] (L : Submodule ℤ (Bil Y ℤ)) : Module.Finite ℤ L :=
  Module.Finite.of_injective L.subtype L.injective_subtype

instance [Module.Finite ℤ Y] [Module.Free ℤ Y] (L : Submodule ℤ (Bil Y ℤ)) : Module.Free ℤ L :=
  Module.free_of_finite_type_torsion_free'

end Symmetric

section Pullback

variable (S : Type*) [Semiring S] {Y Y' Y'' : Type*} [AddCommGroup Y] [AddCommGroup Y']
  [AddCommGroup Y''] (A : Type*) [AddCommGroup A] [Module S A]

def pullback (f : Y →ₗ[ℤ] Y') : Bil Y' A →ₗ[S] Bil Y A where
  toFun b := b.compl₁₂ f f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {S A}




end Pullback

section SymSq

variable {S : Type*} [Semiring S] (Y : Type*) [AddCommGroup Y]

def symRel : AddSubgroup (Y ⊗[ℤ] Y) :=
  AddSubgroup.closure {x | ∃ y y' : Y, x = y ⊗ₜ y' - y' ⊗ₜ y}

def SymSq : Type _ := (Y ⊗[ℤ] Y) ⧸ symRel Y

instance : AddCommGroup (SymSq Y) := inferInstanceAs (AddCommGroup ((Y ⊗[ℤ] Y) ⧸ symRel Y))

namespace SymSq

def ofTensor : Y ⊗[ℤ] Y →+ SymSq Y := QuotientAddGroup.mk' (symRel Y)

theorem ofTensor_surjective : Function.Surjective (ofTensor Y) :=
  QuotientAddGroup.mk'_surjective _

theorem ker_ofTensor : (ofTensor Y).ker = symRel Y := QuotientAddGroup.ker_mk' _

variable {Y}

def mk : Bil Y (SymSq Y) :=
  LinearMap.mk₂ ℤ (fun y y' => ofTensor Y (y ⊗ₜ y'))
    (fun _ _ _ => by rw [add_tmul, map_add (f := _)])
    (fun n y y' => by rw [← map_zsmul]; rfl)
    (fun _ _ _ => by rw [tmul_add, map_add (f := _)])
    (fun n y y' => by rw [← map_zsmul, ← smul_tmul]; rfl)

theorem mk_apply (y y' : Y) : mk y y' = ofTensor Y (y ⊗ₜ y') := rfl

theorem mk_comm (y y' : Y) : mk y y' = mk y' y := by
  rw [mk_apply, mk_apply, ← sub_eq_zero, ← map_sub, ← AddMonoidHom.mem_ker, ker_ofTensor]
  exact AddSubgroup.subset_closure ⟨y, y', rfl⟩

@[ext high] theorem hom_ext {A : Type*} [AddCommGroup A] {f g : SymSq Y →ₗ[ℤ] A}
    (h : ∀ y y', f (mk y y') = g (mk y y')) : f = g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := ofTensor_surjective Y x
  induction x using TensorProduct.inductionOn with
  | tmul y y' => exact h y y'
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {A : Type*} [AddCommGroup A] [Module S A]

variable (S Y A) in
def lift : symForms S Y A ≃ₗ[S] (SymSq Y →ₗ[ℤ] A) where
  toFun b := AddMonoidHom.toIntLinearMap (M := SymSq Y) <|
    QuotientAddGroup.lift (symRel Y) (TensorProduct.lift b.1).toAddMonoidHom <|
      (AddSubgroup.closure_le _).2 <| by
        rintro _ ⟨y, y', rfl⟩
        rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub]
        exact sub_eq_zero.2 (b.2 y y')
  map_add' b c := hom_ext fun _ _ => rfl
  map_smul' s b := hom_ext fun _ _ => rfl
  invFun l := ⟨mk.compr₂ l, fun y y' => congrArg l (mk_comm y y')⟩
  left_inv b := by ext; rfl
  right_inv l := hom_ext fun _ _ => rfl

private theorem lift_mk (b : symForms S Y A) (y y' : Y) :
    lift S Y A b (mk y y') = (b : Bil Y A) y y' := rfl

private theorem lift_symm_apply (l : SymSq Y →ₗ[ℤ] A) (y y' : Y) :
    ((lift S Y A).symm l : Bil Y A) y y' = l (mk y y') := rfl

noncomputable def basis {ι : Type*} (e : Module.Basis ι ℤ Y) : Module.Basis (Sym2 ι) ℤ (SymSq Y) :=
  .ofRepr <| LinearEquiv.ofLinearMap
    (lift ℤ Y (Sym2 ι →₀ ℤ)
      ⟨e.constr ℤ fun i => e.constr ℤ fun j => Finsupp.single s(i, j) 1, by
        rw [mem_symForms_iff_flip]
        refine e.ext fun i => e.ext fun j => ?_
        simp only [LinearMap.flip_apply, Module.Basis.constr_basis, Sym2.eq_swap]⟩)
    (Finsupp.linearCombination ℤ (Sym2.lift ⟨fun i j => mk (e i) (e j), fun _ _ => mk_comm _ _⟩))
    (by
      refine Finsupp.lhom_ext' fun p => LinearMap.ext_ring ?_
      induction p using Sym2.ind with
      | h i j => simp [lift_mk])
    (by
      refine (lift ℤ Y (SymSq Y)).symm.injective (Subtype.ext ?_)
      refine e.ext fun i => e.ext fun j => ?_
      simp [lift_mk, lift_symm_apply])

instance [Module.Free ℤ Y] : Module.Free ℤ (SymSq Y) :=
  .of_basis (basis (Module.Free.chooseBasis ℤ Y))

instance [Module.Finite ℤ Y] : Module.Finite ℤ (SymSq Y) :=
by
  have h : Module.Finite ℤ (Y ⊗[ℤ] Y) := by
    convert Module.Finite.tensorProduct ℤ Y Y using 0
    congr!
  exact Module.Finite.of_surjective (ofTensor Y).toIntLinearMap (ofTensor_surjective Y)

theorem finrank_eq [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Module.finrank ℤ (SymSq Y) = (Module.finrank ℤ Y + 1).choose 2 := by
  classical
  rw [Module.finrank_eq_card_basis (basis (Module.Free.chooseBasis ℤ Y)), Sym2.card,
    Module.finrank_eq_card_chooseBasisIndex]



end SymSq

theorem finrank_symLattice [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Module.finrank ℤ (SymLattice Y) = (Module.finrank ℤ Y + 1).choose 2 := by
  rw [(SymSq.lift ℤ Y ℤ).finrank_eq, ← SymSq.finrank_eq]
  exact Module.finrank_linearMap_self ℤ ℤ _

end SymSq

section Balanced

variable {S : Type*} [Semiring S] (O : Type*) [CommRing O] [StarRing O] {Y Y' : Type*} [AddCommGroup Y] [Module O Y]
  [AddCommGroup Y'] [Module O Y'] {A : Type*} [AddCommGroup A]

def IsBalanced (b : Bil Y A) : Prop := ∀ (a : O) (y y' : Y), b (a • y) y' = b y (star a • y')

variable {O}

theorem IsBalanced.right {b : Bil Y A} (hb : IsBalanced O b) (a : O) (y y' : Y) :
    b y (a • y') = b (star a • y) y' := by
  rw [hb, star_star]

theorem IsBalanced.add_of_add_star {b : Bil Y A} (hb : IsBalanced O b) {w : O}
    (hw : w + star w = 1) (y y' : Y) : b y (w • y') + b (w • y) y' = b y y' := by
  rw [hb, ← map_add (f := _), ← add_smul, hw, one_smul]

variable [Module S A]

variable (S O Y A) in
def balForms : Submodule S (Bil Y A) where
  carrier := {b | b ∈ symForms S Y A ∧ IsBalanced O b}
  add_mem' {b c} hb hc := ⟨add_mem hb.1 hc.1, fun a y y' => by
    simp only [LinearMap.add_apply, hb.2 a y y', hc.2 a y y']⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' s b hb := ⟨Submodule.smul_mem _ s hb.1, fun a y y' => by
    simp only [LinearMap.smul_apply, hb.2 a y y']⟩














variable (O Y) in
def balRel : Submodule ℤ (SymSq Y) :=
  saturation (Submodule.span ℤ
    {x : SymSq Y | ∃ (a : O) (y y' : Y), x = SymSq.mk (a • y) y' - SymSq.mk y (star a • y')})

theorem mem_balRel {x : SymSq Y} : x ∈ balRel O Y ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ
    {x : SymSq Y | ∃ (a : O) (y y' : Y), x = SymSq.mk (a • y) y' - SymSq.mk y (star a • y')} :=
  mem_saturation_iff

variable (O Y) in
abbrev BalSq : Type _ := SymSq Y ⧸ balRel O Y

namespace BalSq

variable (O) in
def mk : Bil Y (BalSq O Y) := SymSq.mk.compr₂ (balRel O Y).mkQ

theorem mk_apply (y y' : Y) : mk O y y' = (balRel O Y).mkQ (SymSq.mk y y') := rfl

variable (O Y) in
theorem mk_mem_balForms : mk O ∈ balForms ℤ O Y (BalSq O Y) :=
  ⟨fun y y' => congrArg (balRel O Y).mkQ (SymSq.mk_comm y y'), fun a y y' =>
    (Submodule.Quotient.eq _).2 <| mem_balRel.2
      ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨a, y, y', rfl⟩⟩⟩

@[ext high] theorem hom_ext {f g : BalSq O Y →ₗ[ℤ] A}
    (h : ∀ y y', f (mk O y y') = g (mk O y y')) : f = g :=
  Submodule.linearMap_qext _ (SymSq.hom_ext h)

instance : Module.IsTorsionFree ℤ (BalSq O Y) := isTorsionFree_quotient_saturation _

variable (S O Y A) in
def lift [Module.IsTorsionFree ℤ A] : balForms S O Y A ≃ₗ[S] (BalSq O Y →ₗ[ℤ] A) where
  toFun b := (balRel O Y).liftQ (SymSq.lift S Y A ⟨b.1, b.2.1⟩) <| by
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_balRel.1 hx
    have h : n • x ∈ LinearMap.ker (SymSq.lift S Y A ⟨b.1, b.2.1⟩) := by
      refine Submodule.span_le.2 ?_ hx
      rintro _ ⟨a, y, y', rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 (b.2.2 a y y')
    rw [LinearMap.mem_ker, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left hn
  map_add' b c := hom_ext fun _ _ => rfl
  map_smul' s b := hom_ext fun _ _ => rfl
  invFun l := ⟨(mk O).compr₂ l, fun y y' => congrArg l ((mk_mem_balForms O Y).1 y y'),
    fun a y y' => congrArg l ((mk_mem_balForms O Y).2 a y y')⟩
  left_inv b := by ext; rfl
  right_inv l := hom_ext fun _ _ => rfl


end BalSq


end Balanced

section Level

variable {Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y']



end Level

end GlobalTheory.Forms
