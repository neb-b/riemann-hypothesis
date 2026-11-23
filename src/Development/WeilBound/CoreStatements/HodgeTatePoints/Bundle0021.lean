module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0013
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0016
public import ReciprocityTheory.DualLattices.Bundle0015
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MhBase
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Mh

section pb

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {X Y : Scheme.{0}}

def pb (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

def val (x : Spec (CommRingCat.of B) ⟶ X) : Γ(X, ⊤) →+* B :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom

theorem valAt_top (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)) : valAt x ⊤ h s = val x s := by
  simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem pb_ext {j j' : X ⟶ Spec (CommRingCat.of A)} (h : ∀ a, pb j a = pb j' a) : j = j' := by
  apply ext_of_isAffine
  have e : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j'.appTop := by
    ext a
    exact h a
  exact (cancel_epi _).1 e

theorem pb_comp (f : Y ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) : pb (f ≫ j) a = f.appTop (pb j a) := by
  unfold pb
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem val_comp (x : Spec (CommRingCat.of B) ⟶ Y) (f : Y ⟶ X) (s : Γ(X, ⊤)) :
    val (x ≫ f) s = val x (f.appTop s) := by
  unfold val
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem pb_spec (j : X ⟶ Spec (CommRingCat.of B)) (ψ : A →+* B) (a : A) :
    pb (j ≫ Spec.map (CommRingCat.ofHom ψ)) a = pb j (ψ a) := by
  simp only [pb, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem val_pb_id (b : B) : val (𝟙 _) (pb (𝟙 (Spec (CommRingCat.of B))) b) = b := by
  simp [val, pb]

theorem val_pb_comp (x : Spec (CommRingCat.of B) ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    val x (pb j a) = val (𝟙 _) (pb (x ≫ j) a) := by
  rw [pb_comp, ← val_comp, Category.id_comp]

theorem val_pb {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : x ≫ j = Spec.map (CommRingCat.ofHom φ)) (a : A) : val x (pb j a) = φ a := by
  have e := pb_spec (𝟙 (Spec (CommRingCat.of B))) φ a
  rw [Category.id_comp] at e
  rw [val_pb_comp, h, e, val_pb_id]

theorem val_id_injective : Function.Injective (val (𝟙 (Spec (CommRingCat.of B)))) := by
  intro s t hst
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) s) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) t) := by
    rw [hst]
  simpa [val] using e

theorem comp_eq_spec {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : ∀ a, val x (pb j a) = φ a) : x ≫ j = Spec.map (CommRingCat.ofHom φ) := by
  refine pb_ext fun a => val_id_injective ?_
  rw [← val_pb_comp, h, val_pb (Category.id_comp _)]

theorem exists_pb (φ : A →+* Γ(X, ⊤)) : ∃ j : X ⟶ Spec (CommRingCat.of A), ∀ a, pb j a = φ a := by
  refine ⟨(ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) (CommRingCat.ofHom φ).op,
    fun a => ?_⟩
  rw [pb, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  rfl

theorem spec_inj {φ ψ : A →+* B} (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_comp (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [← Spec.map_comp]
  rfl

end pb

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T]

theorem sec_ext (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)} (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') :
    s = s' := by
  rw [← sub_eq_zero]
  refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
  rw [valAt_top, map_sub, h, sub_self]

theorem hom_ext_pt (Γ : QFGroup R T) {A : Type} [CommRing A] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
  pb_ext fun a => sec_ext Γ fun t => by rw [val_pb_comp, h, ← val_pb_comp]

theorem mem_top_iff (Γ : QFGroup R T) (f : T → R) : f ∈ Γ.btOrder ⊤ ↔
    ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
  have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
      (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
    intro B _ X x U hx a b
    simp only [valAt, map_sub]
  constructor
  · intro hf t
    rw [Twhopf.mem_order] at hf
    have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
        ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
          valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
      fun g => hf t g (by simp)
    choose U hgU s hs using hreg
    obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
      (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
        intro g g'
        rw [← sub_eq_zero]
        apply Twhopf.sec_inj R T Γ _ _
        intro h hh
        have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
        have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
        refine (hsub _ _ hh _ _).trans ?_
        erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
        rw [hs, hs, sub_self])
    refine ⟨g0, fun h => ?_⟩
    have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
      Twhopf.top_le_of_mem _ z (hgU _)
    refine (valAt_top _ htop g0).symm.trans ?_
    refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
    erw [hglue ((Γ.pt h).left z)]
    exact hs _ h hh
  · intro hf
    rw [Twhopf.mem_order]
    intro t g _
    obtain ⟨s, hs⟩ := hf t
    unfold QFGroup.RegularAt
    exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩

omit [Finite T] in
theorem val_const (Γ : QFGroup R T) (t : T) (r : R) :
    val (Γ.pt t).left (pb Γ.G.hom r) = algebraMap R (FractionRing R) r :=
  val_pb (Over.w (Γ.pt t)) r

omit [Finite T] in
theorem val_emb {Γ : QFGroup R T} {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (a : A) :
    val (Γ.pt t).left (pb j a) = algebraMap R (FractionRing R) (a.1 t) :=
  val_pb (hj.pt t) a

theorem exists_emb (Γ : QFGroup R T) (A : Subalgebra R (T → R))
    (hA : ∀ a : A, ∃ s : Γ(Γ.G.left, ⊤), ∀ t, val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t)) :
    ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of A), Γ.IsEmb A j := by
  choose s hs using hA
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := sec_ext Γ fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => sec_ext Γ fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := sec_ext Γ fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => sec_ext Γ fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hom_ext_pt Γ fun t => by rw [hj'.pt, hpt]⟩
  apply hom_ext_pt Γ
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

end PositivityTheory.HtPt.Mh
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RaCoord
section
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section Count

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

lemma monomialCount_col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R)
    (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have h : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

lemma monomialCount_exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨fun i α => c α i, ?_⟩
  ext x α
  have := congrFun (hc α) x
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  rw [← this, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma monomialCount_prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))

end Count

lemma monomialCount_exponent (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → NNReal) :
    (∏ j, a j) ^ (Fintype.card (ι → ZMod p) * (p - 1)) =
      (∏ j, a j ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))) ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) :=
    Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (Fintype.card ι - 1) * p = p ^ Fintype.card ι := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  have hcard : Fintype.card (ι → ZMod p) = p ^ Fintype.card ι := by
    simp [ZMod.card]
  rw [Finset.prod_pow, ← pow_mul, hcard]
  congr 1
  calc p ^ Fintype.card ι * (p - 1) = p ^ (Fintype.card ι - 1) * p * (p - 1) := by rw [h3]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1)) := by ring
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2 * 2) := by rw [h2]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) * 2 := by ring

theorem cnt_coord_of (hsmith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j)))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) := by
  intro p _ C _ _ _ v R _ _ hv hp1 ι _ _ AA cA cN hA hN
  obtain ⟨Λ, ε, hΛ, hspan, hε, hlen⟩ := hsmith p C v R hv hp1 ι AA
  have hcA : cA = ∏ j, v (algebraMap R C (ε j)) := hasLen_unique hv hA hlen
  have hl := fun j => lifts p C v R hv hp1 ι AA (Λ j) (ε j)
    (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩) (hε j)
  choose u hu_mem hu_int hu_cong using hl

  let B' : Matrix (ι → ZMod p) (ι → ZMod p) C := Matrix.of fun (x α : ι → ZMod p) =>
    ∏ j, (algebraMap R C (ε j) * u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (ε j)) ^
      (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 ι Λ u hΛ hu_int hu_cong).2 fun j => algebraMap R C (ε j)
  have hsq : cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = v B'.det ^ 2 := by
    rw [hcA, hB'v]
    exact monomialCount_exponent p _

  have hp0 : v (p : C) ≠ 0 :=
    (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hε0 : ∀ j, v (algebraMap R C (ε j)) ≠ 0 := by
    intro j h0
    have hpp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    have := hε j
    rw [h0, zero_pow hpp] at this
    exact hp0 (le_antisymm this zero_le)
  have hB'0 : v B'.det ≠ 0 := by
    rw [hB'v]
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hε0 j)

  have hmem : ∀ α : ι → ZMod p, (fun x => B' x α) ∈ AA.carrier := by
    intro α
    exact monomialCount_prod_pow_mem AA (fun j y => algebraMap R C (ε j) * u j y)
      (fun j => (Submodule.mem_inf.1 (hu_mem j)).1) (fun j => (α j).val)
  obtain ⟨B, hAA, hBc⟩ := hN
  obtain ⟨W, hW⟩ := monomialCount_exists_factor (R := R) B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = cN * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det, hBc]; rfl
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hle : v B'.det ≤ cN := by
    rw [hdet]; exact mul_le_of_le_one_right zero_le hw1
  refine ⟨by rw [hsq]; exact pow_le_pow_left₀ zero_le hle 2, fun heq => ?_⟩
  have hBeq : v B'.det = cN := by
    rw [hsq] at heq
    exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 heq
  have hcN0 : cN ≠ 0 := hBeq ▸ hB'0
  have hw : v (algebraMap R C W.det) = 1 := by
    have h : cN * v (algebraMap R C W.det) = cN * 1 := by rw [← hdet, hBeq, mul_one]
    exact mul_left_cancel₀ hcN0 h
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq' : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  refine ⟨fun j y => algebraMap R C (ε j) * u j y, hu_mem, ?_⟩
  have hspan' : Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) =>
      ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan']
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := monomialCount_col_mem_span (R := R) B' (W⁻¹) j
    rwa [hBeq'] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

end PositivityTheory.HtPt.Ra
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Twhopf

theorem finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  exact ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) f,
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) f⟩

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) f U' hU' U.ι).ge
    (Set.mem_univ ⟨x, hx⟩)

theorem mem_of_finite {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI : IsFinite (h.left ≫ X.hom) := by rw [Over.w h]; exact hY
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) X.hom W hW h.left).ge
    (Set.mem_univ z)

theorem finite_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

theorem mem_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) → ∀ t, (⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U ↔ ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, toUnit (genPt R) ≫ σ = Γ.pt t) := by
  intro R _ _ _ _ T _ _ Γ U hfin hU t
  constructor
  · intro ht
    obtain ⟨σ, -, hσ⟩ := exists_section_of_generic_point R T Γ U hfin t ht
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩ z _
    have key := mem_of_finite U hU (𝟙_ _) (show IsFinite (𝟙 _) from inferInstance) σ
      ((toUnit (genPt R)).left z)
    rw [← hσ]
    simpa using key


open Polynomial in
theorem exists_root_near (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
    (a₀ : V) (n : ℕ) : ∀ f : V[X], f.Monic → f.natDegree = n → f.eval a₀ ∈ IsLocalRing.maximalIdeal V →
      ∃ a, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal V := by
  induction n with
  | zero =>
    intro f hf hn h
    rw [hf.natDegree_eq_zero.1 hn, eval_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  | succ n ih =>
    intro f hf hn h
    have hinj := IsFractionRing.injective V (FractionRing V)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (FractionRing V) hinj f
      (by rw [degree_eq_natDegree hf.ne_zero, hn]; exact_mod_cast n.succ_ne_zero)
    obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (⟨f, hf, by rwa [← aeval_def]⟩ : IsIntegral V x)
    have hr : f.IsRoot r := hinj (by rw [map_zero, ← hx, aeval_algebraMap_apply_eq_algebraMap_eval])
    obtain ⟨g, rfl⟩ := dvd_iff_isRoot.2 hr
    have hg : g.Monic := (monic_X_sub_C r).of_mul_monic_left hf
    rw [eval_mul] at h
    rcases (IsLocalRing.maximalIdeal.isMaximal V).isPrime.mem_or_mem h with h | h
    · refine ⟨r, hr, ?_⟩
      have := neg_mem h
      simpa using this
    · have hd : g.natDegree = n := by
        rw [(monic_X_sub_C r).natDegree_mul hg, natDegree_X_sub_C] at hn
        omega
      obtain ⟨a, ha, ha'⟩ := ih g hg hd h
      exact ⟨a, ha.dvd (dvd_mul_left _ _), ha'⟩

theorem henselian_of_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], HenselianLocalRing V := by
  intro V _ _ _ _
  exact ⟨fun f hf a₀ h _ => exists_root_near V a₀ _ f hf rfl h⟩

theorem padic_alg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C := by
  intro p _ C _ _ _ v O _ _ _ hv _ hO
  haveI := hO
  haveI hval : ValuationRing O := ValuationRing.of_integers v hv
  haveI hfr : IsFractionRing O C := hv.isFractionRing
  haveI hac : IsAlgClosed (FractionRing O) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
  exact ⟨(GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).1,
    henselian_of_algClosed O, inferInstance, hval, hac, hfr⟩

theorem prime_eq_bot_or_max : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O], v.Integers O → ∀ P : Ideal O, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  intro C _ v O _ _ _ _ hv P hP
  by_cases h0 : P = ⊥
  · exact .inl h0
  right
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun x hx => ?_
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have ha : 0 < v (algebraMap O C a) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 ((map_ne_zero_iff _ hv.hom_inj).2 ha0))
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one ha hx1
  have hd : a ∣ x ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (P.mem_of_dvd hd haP)

end PositivityTheory.HtPt.Twhopf
end

