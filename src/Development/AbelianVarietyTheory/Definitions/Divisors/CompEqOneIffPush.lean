module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

variable {S S' : Scheme.{0}} {O : Type} [Ring O]

section Basic

variable {A A' A'' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A'']
  [IsCommMonObj A'']

structure IsLin (ρ : RingAct A O) (ρ' : RingAct A' O) (f : A ⟶ A') : Prop where
  hom : IsMonHom f
  comm : ∀ a, ρ.act a ≫ f = f ≫ ρ'.act a

structure IsIsogDeg (f : A ⟶ A') (d : ℕ) : Prop where
  fin : IsFinite f.left
  flat : Flat f.left
  surj : Surjective f.left
  rank : ∀ y, f.left.finrank y = d

def KilledBy (ρ : RingAct A O) (𝔴 : Ideal O) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ a ∈ 𝔴, x ≫ ρ.act a = 1


omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in
theorem IsIsogDeg.of_isIso (f : A ⟶ A') [IsIso f] : IsIsogDeg f 1 := by
  have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget S).map f))
  exact ⟨inferInstance, inferInstance, inferInstance, congrFun (Scheme.Hom.finrank_eq_one_of_isIso _)⟩


omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A''] [IsCommMonObj A''] in
theorem IsIsogDeg.comp {f : A ⟶ A'} {g : A' ⟶ A''} {d e : ℕ} (hf : IsIsogDeg f d) (hg : IsIsogDeg g e) :
    IsIsogDeg (f ≫ g) (d * e) := by
  have := hf.fin; have := hf.flat; have := hf.surj
  have := hg.fin; have := hg.flat; have := hg.surj
  refine ⟨?_, ?_, ?_, fun y => ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left, FinrankComp.finrank_comp_of_const _ _ d hf.rank, hg.rank]



omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in
theorem IsIsogDeg.of_isPullback {C C' : Over S'} {f : A ⟶ A'} {g : C ⟶ C'} {d : ℕ} (hf : IsIsogDeg f d)
    {u : C.left ⟶ A.left} {v : C'.left ⟶ A'.left} (H : IsPullback u g.left f.left v) : IsIsogDeg g d := by
  have := hf.fin; have := hf.flat
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H hf.fin,
    MorphismProperty.of_isPullback (P := @Flat) H hf.flat,
    MorphismProperty.of_isPullback (P := @Surjective) H hf.surj,
    fun y => (Scheme.Hom.finrank_of_isPullback _ _ _ _ H y).trans (hf.rank _)⟩

abbrev ker (f : A ⟶ A') : Over S := pullback f η[A']


omit [GrpObj A] [IsCommMonObj A] [IsCommMonObj A'] in
theorem IsIsogDeg.ker {f : A ⟶ A'} {d : ℕ} (hf : IsIsogDeg f d) : IsIsogDeg (toUnit (ker f)) d := by
  rw [toUnit_unique (toUnit _) (pullback.snd f η[A'])]
  exact hf.of_isPullback ((IsPullback.of_hasPullback f η[A']).map (Over.forget S))

theorem killedBy_span (ρ : RingAct A O) (s : Set O) {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span s) x ↔ ∀ a ∈ s, x ≫ ρ.act a = 1 := by
  refine ⟨fun h a ha => h a (Ideal.subset_span ha), fun h a ha => ?_⟩
  have hadd : ∀ a b, x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  induction ha using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero =>
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  | add a b _ _ ha hb => rw [hadd, ha, hb, _root_.mul_one]
  | smul c a _ ha =>
    have := ρ.hom c
    rw [smul_eq_mul, ρ.map_mul, ← Category.assoc, ha, MonObj.one_comp]

theorem comp_eq_one_iff_push {C C' : Over S'} [GrpObj C] [GrpObj C'] {f : S' ⟶ S} {u : C.left ⟶ A.left}
    {v : C'.left ⟶ A'.left} (hu : IsGrpPullback C A f u) (hv : IsGrpPullback C' A' f v) {g : A ⟶ A'} {g' : C ⟶ C'}
    (hg : g'.left ≫ v = u ≫ g.left) {T : Over S'} (x : T ⟶ C) :
    x ≫ g' = 1 ↔ pushHom hu T x ≫ g = 1 := by
  have e : pushHom hv T (x ≫ g') = pushHom hu T x ≫ g := Over.OverMorphism.ext (by
    change (x.left ≫ g'.left) ≫ v = (x.left ≫ u) ≫ g.left
    rw [Category.assoc, hg, Category.assoc])
  have inj : Function.Injective (pushHom hv T) := fun y z h => Over.OverMorphism.ext
    (hv.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  rw [← e, map_eq_one_iff _ inj]

end Basic

variable {A : Over S} [GrpObj A] [IsCommMonObj A]

structure Chain (ρ : RingAct A O) (𝔴 : Ideal O) (d n : ℕ) where

  B : Fin (n + 1) → Over S
  [grp : ∀ i, GrpObj (B i)]
  [comm : ∀ i, IsCommMonObj (B i)]
  ab : ∀ i, IsAbelianScheme (B i)

  act : ∀ i, RingAct (B i) O

  φ : ∀ i : Fin n, B i.castSucc ⟶ B i.succ
  φ_lin : ∀ i, IsLin (act _) (act _) (φ i)
  φ_deg : ∀ i, IsIsogDeg (φ i) d

  π : ∀ i, A ⟶ B i
  π_zero_lin : IsLin ρ (act 0) (π 0)
  π_zero_iso : IsIso (π 0)
  π_succ : ∀ i : Fin n, π i.succ = π i.castSucc ≫ φ i
  ker_last : ∀ (T : Over S) (x : T ⟶ A), x ≫ π (Fin.last n) = 1 ↔ KilledBy ρ 𝔴 x

attribute [instance] Chain.grp Chain.comm

namespace Chain

variable {ρ : RingAct A O} {𝔴 : Ideal O} {d n : ℕ} (C : Chain ρ 𝔴 d n)

end Chain

structure ChainMap {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
    {𝔴 : Ideal O} {d n : ℕ} (C' : Chain ρ' 𝔴 d n) (C : Chain ρ 𝔴 d n) (f : S' ⟶ S) (u : A'.left ⟶ A.left) where

  ψ : ∀ i, (C'.B i).left ⟶ (C.B i).left
  cart : ∀ i, IsGrpPullback (C'.B i) (C.B i) f (ψ i)
  act : ∀ i a, ((C'.act i).act a).left ≫ ψ i = ψ i ≫ ((C.act i).act a).left
  π_comm : ∀ i, (C'.π i).left ≫ ψ i = u ≫ (C.π i).left

namespace ChainMap

variable {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
  {𝔴 : Ideal O} {d n : ℕ} {C' : Chain ρ' 𝔴 d n} {C : Chain ρ 𝔴 d n} {f : S' ⟶ S} {u : A'.left ⟶ A.left}

end ChainMap

section Unitary

variable {F : Type} [Field F] [NumberField F] [NumberField.IsCMField F] {D : UPel.Datum F} {p N : ℕ}

end Unitary

end GlobalTheory.IwLevel
