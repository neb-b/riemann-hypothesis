module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfLin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpObj

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem

def exHom : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
  MonoidHom.mk' (fun z => u.ex z.toAdd) fun z w => u.ex_add _ _

theorem ex_zsmul (n : ℤ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  have h := map_zpow (exHom u) (Multiplicative.ofAdd z) n
  rw [← ofAdd_zsmul] at h
  simpa [exHom] using h

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum [IsCommMonObj A] {I : Type} [Fintype I] (z : I → Fin g → ℂ) : u.ex (∑ i, z i) = ∏ i, u.ex (z i) := by
  classical
  have key : ∀ s : Finset I, u.ex (∑ i ∈ s, z i) = ∏ i ∈ s, u.ex (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact ex_zero u
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, u.ex_add, ih]
  exact key Finset.univ

end Unif

variable (laws : Out.Laws) (laws2 : Out.Laws2)
  (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
  (hT : ThetaUnifAV)
include laws laws2 hc hT

theorem hom_ext_of_lin (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
    (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (f f' : P.A ⟶ P'.A) (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f)
    (hf' : ∀ z, u'.ex (F z) = u.ex z ≫ f') (h1 : IsMonHom f) : f = f' := by
  have e : ∀ B : Over (Sp ℂ), ∀ [GrpObj B], (η[B] : 𝟙_ _ ⟶ B) = 1 := fun B _ => by rw [Hom.one_def]; simp
  have h2 : IsMonHom f' := laws.rigidity _ _ _ P.isAb P'.isAb f' (by
    rw [e, e, ← ex_zero u, ← hf', map_zero, ex_zero])
  refine (_root_.GlobalTheory.existsUnique_isMonHom_of_map_lattice laws laws2 hc hT P P' _ _ u u' F fun z hz => ?_).unique ⟨h1, hf⟩ ⟨h2, hf'⟩
  rw [← u'.ker, hf, (u.ker z).2 hz, MonObj.one_comp]

theorem exists_proj (P P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u₀ : HolUnif P₀.A P₀.L P₀.g)
    {I : Type} [Fintype I] (σ : I × Fin P₀.g ≃ Fin P.g)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ) :
    ∃ pr : I → (P.A ⟶ P₀.A), (∀ i, IsMonHom (pr i)) ∧ (∀ i z, u₀.ex (fun j => z (σ (i, j))) = u.ex z ≫ pr i) ∧
      ∀ (T : Over (Sp ℂ)) (y : I → (T ⟶ P₀.A)), ∃! x : T ⟶ P.A, ∀ i, x ≫ pr i = y i := by
  classical
  letI := P.isAb.comm
  letI := P₀.isAb.comm
  let R : I → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  let S : I → (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := fun i =>
    LinearMap.pi fun a => if (σ.symm a).1 = i then LinearMap.proj (σ.symm a).2 else 0
  have hRS : ∀ i i' z, R i (S i' z) = if i = i' then z else 0 := fun i i' z => by
    ext j
    by_cases e : i = i' <;> simp [R, S, LinearMap.funLeft_apply, e]
  have hSR : ∀ z, ∑ i, S i (R i z) = z := fun z => by
    ext a
    obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective a
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [R, S, LinearMap.funLeft_apply]
    · intro b _ hb
      simp [S, hb.symm]
    · simp
  choose pr hpr using fun i => (_root_.GlobalTheory.existsUnique_isMonHom_of_map_lattice laws laws2 hc hT P P₀ _ _ u u₀ (R i) fun z hz => (hΛ z).1 hz i).exists
  choose inc hinc using fun i => (_root_.GlobalTheory.existsUnique_isMonHom_of_map_lattice laws laws2 hc hT P₀ P _ _ u₀ u (S i) fun z hz => (hΛ _).2 fun i' => by
    change R i' (S i z) ∈ _
    rw [hRS]
    split_ifs
    exacts [hz, u₀.Λ.zero_mem]).exists
  haveI := fun i => (hpr i).1
  haveI := fun i => (hinc i).1
  have e1 : ∀ i, inc i ≫ pr i = 𝟙 _ := fun i =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ LinearMap.id _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i).2, hRS]; simp) (fun z => by simp) inferInstance
  have e2 : ∀ i i', i ≠ i' → inc i ≫ pr i' = 1 := fun i i' hi =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ 0 _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i').2, hRS]; simp [hi.symm])
      (fun z => by simp [ex_zero]) inferInstance
  have e3 : 𝟙 P.A = ∏ i, pr i ≫ inc i :=
    hom_ext_of_lin laws laws2 hc hT P P u u LinearMap.id _ _ (fun z => by simp) (fun z => by
      rw [PowMatrixLinear.comp_prod]
      simp only [← Category.assoc, ← (hpr _).2, ← (hinc _).2]
      rw [← ex_sum, hSR]; rfl) inferInstance
  refine ⟨pr, fun i => (hpr i).1, fun i => (hpr i).2, fun T y => ⟨∏ i, y i ≫ inc i, fun i => ?_, fun x hx => ?_⟩⟩
  · rw [PowMatrixLinear.prod_comp, Finset.prod_eq_single i]
    · rw [Category.assoc, e1, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, e2 _ _ hb, MonObj.comp_one]
    · simp
  · rw [← Category.comp_id x, e3, PowMatrixLinear.comp_prod]
    simp only [← Category.assoc, hx]

end GlobalTheory.SharpObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TrivDescentCompare

section General

theorem smooth_conn {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S}
    [GrpObj G] (Q : TQ G X) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  have := Q.q_hom
  have := Q.isAb.smooth
  have := Q.isAb.geomConnected
  have hs := Q.smooth_proj_of_free
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  have sq := (H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)
  have hc : GeometricallyConnected Q.q.left := by
    have h₁ : GeometricallyConnected ((Over.forget _).map (snd (splitTorus S X) G)) :=
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback _ _)
        (GlobalTheory.Diag.geometricallyConnected_hom S X)
    have h₂ : Surjective ((Over.forget _).map Q.q) := Q.q_surj
    exact @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ sq h₂ h₁
  rw [← Over.w Q.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

variable {Y Y' : Scheme.{0}} {L : LB Y} {L' : LB Y'} {F : Y' ⟶ Y}

theorem exists_iso_ratio (hL : L.IsLB) (hL' : L'.IsLB) {w₁ w₂ : LB.Iso L' (L.pull F)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) (j : L.ι) (k : L'.ι), F (r y) ∈ L.U j → r y ∈ L'.U k →
      gw w₁ r y j k = gm r y ⊤ u * gw w₂ r y j k := by
  have h₁ := (isGen_iff _).1 g₁
  have h₂ := (isGen_iff _).1 g₂
  let W : L.ι × L'.ι → Y'.Opens := fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2
  let v : ∀ p, Γ(Y', W p)ˣ := fun p => w₁.s (fun _ => p.1, p.2) * (w₂.s (fun _ => p.1, p.2))⁻¹
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) p, gm r y (W p) (v p) =
      gw w₁ r y p.1 p.2 * (gw w₂ r y p.1 p.2)⁻¹ := fun Z r y p =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩) v (fun p q x hx => by
      have a := h₁ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      rw [hv, hv, a, b, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r y j k hj hk => ?_⟩
  have hy : r y ∈ W (j, k) := ⟨mem_pull.2 hj, hk⟩
  rw [← gm_res r y (le_top : W (j, k) ≤ ⊤) hy u, hu, hv, inv_mul_cancel_right]

end General

section Restrict
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G' H' : Over S'}
  [GrpObj G'] [IsCommMonObj G'] [GrpObj H'] {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {E : H'.left ⟶ H.left} {P : CP G} {P' : CP G'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G} {i' : H' ⟶ G'}

end Restrict

section Lift
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]
  {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {P : CP G} {P' : CP G'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}

end Lift

section Nil
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X] {G : Over (Spec (CommRingCat.of A))}
  [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G'] [IsCommMonObj G']
  {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ red J} {P : CP G} {P' : CP G'}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i' : splitTorus _ X ⟶ G'}

end Nil

section Descent
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]

end Descent

section Iso
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {X : Type} [AddCommGroup X]

end Iso

section Endo
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G] {Q : TQ G X} {P : CP G}

end Endo

section Clauses
variable {S : Scheme.{0}}

end Clauses

section Along
variable {A : Type} [CommRing A] {J : Ideal A}

end Along

def IsThickPoint (A : Type) [CommRing A] : Prop := ∃ _ : IsLocalRing A, IsNilpotent (IsLocalRing.maximalIdeal A)

section Diag
open GlobalTheory.PairingLevels

variable {S : Scheme.{0}} {G : Over S} {Y : Over S} {L : LB G.left}

variable [GrpObj G] [IsCommMonObj G] {H : Over S} [GrpObj H] [IsCommMonObj H]

end Diag

section Invariant
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem act_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) (x : T ⟶ G) :
    ((t ≫ Q.i) * x).left ≫ Q.q.left = x.left ≫ Q.q.left := by
  have := Q.q_hom
  rw [← Over.comp_left, MonObj.mul_comp, Q.comp_i_q, _root_.one_mul, Over.comp_left]

end Invariant

section Torus
open GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

end Torus

def IsBase (A : Type) [CommRing A] : Prop :=
  ConnectedSpace (Spec (CommRingCat.of A)) ∧ ∃ J : Ideal A, IsNilpotent J ∧ IsReduced (A ⧸ J)

section MoreClauses
variable {S : Scheme.{0}}

end MoreClauses

end GlobalTheory.TrivDescentCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegPreBundleMulLeft
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem siegPre_bundle_mul_left : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → ∀ (T : Over (Sp K)) (x x' y : T ⟶ c.A), ∃ t : LB.Gen (LB.LinComb c.P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen := by
  intro hΘ K _ o _ s h k ζ c P pr hpr huniv T x x' y
  have := hpr 0
  have := hpr 1

  have hL : (c.P.pull (lift (pr 0) (pr 1)).left).IsLB := pull_isLB c.isLB _
  have hθ := hΘ (Sp K) P _ hL

  have hpt : ∀ z : T ⟶ P.A, CechPic.pull z.left (cls _ hL) =
      CechPic.pull (lift (z ≫ pr 0) (z ≫ pr 1)).left (cls c.P c.isLB) := by
    intro z
    rw [cls_pull c.isLB _ hL, ← pull_comp, ← Over.comp_left, comp_lift]

  have hax₁ : ∀ v : T ⟶ c.A, CechPic.pull (lift (1 : T ⟶ c.A) v).left (cls c.P c.isLB) = 0 := by
    intro v
    have e : lift (1 : T ⟶ c.A) v = v ≫ lift (1 : c.A ⟶ c.A) (𝟙 c.A) := by
      rw [comp_lift, comp_one, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, ← cls_pull c.isLB _ (pull_isLB c.isLB _),
      (cls_eq_zero_iff _).2 c.rig₁, map_zero]
  have hax₂ : ∀ u : T ⟶ c.A, CechPic.pull (lift u (1 : T ⟶ c.A)).left (cls c.P c.isLB) = 0 := by
    intro u
    have e : lift u (1 : T ⟶ c.A) = u ≫ lift (𝟙 c.A) (1 : c.A ⟶ c.A) := by
      rw [comp_lift, comp_one, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, ← cls_pull c.isLB _ (pull_isLB c.isLB _),
      (cls_eq_zero_iff _).2 c.rig₂, map_zero]

  obtain ⟨a, ha, -⟩ := huniv T (fun u => if u = 0 then x else 1)
  obtain ⟨b, hb, -⟩ := huniv T (fun u => if u = 0 then x' else 1)
  obtain ⟨d, hd, -⟩ := huniv T (fun u => if u = 1 then y else 1)
  have ha0 : a ≫ pr 0 = x := by simpa using ha 0
  have ha1 : a ≫ pr 1 = 1 := by simpa using ha 1
  have hb0 : b ≫ pr 0 = x' := by simpa using hb 0
  have hb1 : b ≫ pr 1 = 1 := by simpa using hb 1
  have hd0 : d ≫ pr 0 = 1 := by simpa using hd 0
  have hd1 : d ≫ pr 1 = y := by simpa using hd 1

  have key := lam_mul_left hL hθ a b d
  have e1 : x * x' * (1 : T ⟶ c.A) = x * x' := by rw [_root_.mul_one]
  have e3 : (1 : T ⟶ c.A) * 1 = 1 := by rw [_root_.one_mul]
  have e4 : x * (1 : T ⟶ c.A) = x := by rw [_root_.mul_one]
  have e5 : x' * (1 : T ⟶ c.A) = x' := by rw [_root_.mul_one]
  have e6 : (1 : T ⟶ c.A) * y = y := by rw [_root_.one_mul]
  simp only [lam, hpt, mul_comp, ha0, ha1, hb0, hb1, hd0, hd1, one_comp, e1, e3, e4, e5, e6] at key
  simp only [hax₁, hax₂, sub_zero, add_zero] at key
  refine (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).1 ?_
  rw [cls_linComb c.isLB, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_smul, neg_smul]
  rw [key]
  abel

end GlobalTheory
end
end

