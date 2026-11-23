module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {Y Z : Scheme.{0}}

theorem valAt_comp (y : Spec (CommRingCat.of B) ⟶ Y) (φ : Y ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ W) (f : Γ(Z, W)) :
    valAt (y ≫ φ) W h f = valAt y (φ ⁻¹ᵁ W) h ((φ.app W).hom f) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_spec (φ : B →+* B') (y : Spec (CommRingCat.of B) ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ y) ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ y) W h' f = φ (valAt y W h f) := by
  have e : (Spec.map (CommRingCat.ofHom φ) ≫ y).appLE W ⊤ h' =
      y.appLE W ⊤ h ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    have := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) y W ⊤ ⊤ h le_top
    rw [← this]
    simp [Scheme.Hom.appLE]
    rfl
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  simp only [valAt, e]
  exact congrArg (fun z => z.hom ((y.appLE W ⊤ h).hom f)) n

theorem valAt_congr {B : Type} [CommRing B] {Y : Scheme.{0}} {y y' : Spec (CommRingCat.of B) ⟶ Y} (e : y = y') (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y' ⁻¹ᵁ W) (f : Γ(Y, W)) : valAt y W h f = valAt y' W h' f := by
  subst e; rfl

end Pull

theorem reg_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  have h1 : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := e ▸ h1
  have h3 : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun z _ => by
    have hz : z = Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact h2 (by trivial)
  refine (Pull.valAt_comp _ F U h1 s).symm.trans ((Pull.valAt_congr e U h1 h2 s).trans ?_)
  rw [Pull.valAt_spec κ _ U h3, hs t h3]

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHt
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem tors_ext {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} {v v' : Y ⟶ Γ.G.left} (h1 : v ≫ Γ.G.hom = v' ≫ Γ.G.hom)
    (h2 : v ≫ i = v' ≫ i) : v = v' :=
  congrArg (·.left) (h.inj (Over.mk (v ≫ Γ.G.hom)) (Over.homMk v rfl) (Over.homMk v' h1.symm) h2)

theorem ht_add : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ χ' w w' ⟨s, hs, hv⟩ ⟨s', hs', hv'⟩
  have hm : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left),
      valAt y ⊤ le_top (s * s') = valAt y ⊤ le_top s * valAt y ⊤ le_top s' := fun y => by simp [valAt]
  refine ⟨s * s', fun t => ?_, fun e => ?_⟩
  · rw [hm, hs t, hs' t, ← map_mul]; rfl
  · obtain ⟨v, h1, h2, h3⟩ := hv e
    obtain ⟨v', h1', h2', h3'⟩ := hv' e
    obtain rfl : v = v' := tors_ext h (h1.trans h1'.symm) (h2.trans h2'.symm)
    refine ⟨v, h1, h2, ?_⟩
    rw [hm, h3, h3']
    ext <;> simp [add_comm]

theorem ht_olin : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M a _ α A hα hA χ w ⟨s, hs, hv⟩
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by
    have : ∀ n : ℕ, (g ≫ a) ^ n = (g ^ n) ≫ a := fun n => by
      induction n with
      | zero => simp [MonObj.one_comp]
      | succ n ih => rw [pow_succ, pow_succ, ih, MonObj.mul_comp]
    rw [this, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a'.left.appTop.hom s, fun t => ?_, fun e => ?_⟩
  · have : (Γ.pt t).left ≫ a'.left = (Γ.pt (α t)).left :=
      tors_ext h (by rw [Category.assoc, Over.w, Over.w, Over.w]) (by rw [Category.assoc, ha', hα])
    rw [← valAt_comp_top, this]
    exact hs (α t)
  · obtain ⟨v, ⟨h1, h2⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion R T Γ S G x N i h L M e
    obtain ⟨v', h1', h2', h3'⟩ := hv (A e)
    have : v ≫ a'.left = v' := tors_ext h (by rw [Category.assoc, Over.w, h1, h1']) (by
      rw [Category.assoc, ha', ← Category.assoc, h2, h2', hA e, Over.comp_left, Category.assoc])
    exact ⟨v, h1, h2, by rw [← valAt_comp_top, this, h3']; rfl⟩

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MjBase
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Mj

variable {R : Type} [CommRing R]

theorem exists_dual_family (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] :
    ∃ (n : ℕ) (l : Fin n → N →ₗ[R] R) (b : Fin n → N), ∀ a, ∑ i, l i a • b i = a := by
  classical
  obtain ⟨n, p, g, -, -, hpg⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  refine ⟨n, fun i => (LinearMap.proj i).comp g, fun i => p fun j => if i = j then 1 else 0, fun a => ?_⟩
  have hx : p (g a) = a := LinearMap.congr_fun hpg a
  rw [LinearMap.pi_apply_eq_sum_univ p (g a)] at hx
  exact hx

variable {X Y Z : Type}

def pspan (A : Subalgebra R (X → R)) (B : Subalgebra R (Y → R)) : Submodule R (X × Y → R) :=
  Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ B, g = fun z => a z.1 * b z.2}

theorem mul_mem_pspan {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} {a : X → R} {b : Y → R}
    (ha : a ∈ A) (hb : b ∈ B) : (fun z : X × Y => a z.1 * b z.2) ∈ pspan A B :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem pspan_comp {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} (N : Submodule R (Z → R))
    (σ : Z → X × Y) (h : ∀ a ∈ A, ∀ b ∈ B, (fun z => a (σ z).1 * b (σ z).2) ∈ N) {g : X × Y → R}
    (hg : g ∈ pspan A B) : (fun z => g (σ z)) ∈ N := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact h a ha b hb
  | zero => exact N.zero_mem
  | add g g' _ _ h h' => exact N.add_mem h h'
  | smul r g _ h => exact N.smul_mem r h

theorem slice_mem {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} {g : X × Y → R}
    (hg : g ∈ pspan A B) (y : Y) : (fun x => g (x, y)) ∈ A :=
  pspan_comp (Subalgebra.toSubmodule A) (fun x => (x, y)) (fun a ha b _ => by
    have := A.smul_mem ha (b y)
    rw [Subalgebra.mem_toSubmodule]
    convert this using 1
    funext x
    simp [mul_comm]) hg

theorem mem_pspan_of {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} [Module.Finite R A]
    [Module.Projective R A] {g : X × Y → R} (h1 : ∀ y, (fun x => g (x, y)) ∈ A)
    (h2 : ∀ l : A →ₗ[R] R, (fun y => l ⟨_, h1 y⟩) ∈ B) : g ∈ pspan A B := by
  obtain ⟨n, l, b, h⟩ := exists_dual_family (R := R) A
  have := Submodule.sum_mem (pspan A B) (t := Finset.univ) fun i _ => mul_mem_pspan (b i).2 (h2 (l i))
  convert this using 1
  funext z
  have e := congrFun (congrArg Subtype.val (h ⟨_, h1 z.2⟩)) z.1
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← e]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_tensor_equiv (A : Subalgebra R (X → R)) (B : Subalgebra R (Y → R)) [Module.Finite R A]
    [Module.Projective R A] (E : X × Y ≃ Z) (C : Subalgebra R (Z → R))
    (hC : ∀ f, f ∈ C ↔ (fun z => f (E z)) ∈ pspan A B) :
    ∃ e : A ⊗[R] B ≃ₐ[R] C, ∀ (a : A) (b : B) (x : X) (y : Y), (e (a ⊗ₜ b)).1 (E (x, y)) = a.1 x * b.1 y := by
  let p : A →ₐ[R] (Z → R) := (AlgHom.pi fun z => Pi.evalAlgHom R (fun _ : X => R) (E.symm z).1).comp A.val
  let q : B →ₐ[R] (Z → R) := (AlgHom.pi fun z => Pi.evalAlgHom R (fun _ : Y => R) (E.symm z).2).comp B.val
  let m : A ⊗[R] B →ₐ[R] (Z → R) := Algebra.TensorProduct.lift p q fun _ _ => Commute.all _ _
  have hm : ∀ (a : A) (b : B) z, m (a ⊗ₜ b) (E z) = a.1 z.1 * b.1 z.2 := fun a b z => by
    simp [m, p, q]
  have hmem : ∀ w, m w ∈ C := fun w => by
    induction w with
    | tmul a b =>
      rw [hC]
      simp only [hm]
      exact mul_mem_pspan a.2 b.2
    | add a b ha hb => rw [map_add (f := _)]; exact C.add_mem ha hb
  have hinj : Function.Injective m := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨n, l, b, h⟩ := exists_dual_family (R := R) A
    let c : (A →ₗ[R] R) → A ⊗[R] B →ₗ[R] B := fun l => (TensorProduct.lid R B).toLinearMap ∘ₗ l.rTensor B
    let s : Y → A ⊗[R] B →ₗ[R] A := fun y =>
      (TensorProduct.rid R A).toLinearMap ∘ₗ ((LinearMap.proj y).comp B.val.toLinearMap).lTensor A
    have h1 : ∀ y x w, (s y w).1 x = m w (E (x, y)) := fun y x w => by
      induction w with
      | tmul a b => rw [hm]; simp [s, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), AddMemClass.coe_add, Pi.add_apply, ha, hb]
    have h2 : ∀ l y w, (c l w).1 y = l (s y w) := fun l y w => by
      induction w with
      | tmul a b => simp [s, c, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), AddMemClass.coe_add, Pi.add_apply, ha, hb]
    have h3 : ∀ w, ∑ i, b i ⊗ₜ c (l i) w = w := fun w => by
      induction w with
      | tmul a b' =>
        conv_rhs => rw [← h a, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c, TensorProduct.smul_tmul]
      | add a b ha hb => simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib, ha, hb]
    have h4 : ∀ y, s y w = 0 := fun y => Subtype.ext (funext fun x => by rw [h1, hw]; rfl)
    have h5 : ∀ l, c l w = 0 := fun l => Subtype.ext (funext fun y => by rw [h2, h4, map_zero]; rfl)
    rw [← h3 w]
    simp [h5]
  refine ⟨AlgEquiv.ofBijective (m.codRestrict C hmem) ⟨fun u v huv => hinj (congrArg Subtype.val huv), ?_⟩,
    fun a b x y => hm a b (x, y)⟩
  rintro ⟨f, hf⟩
  have := pspan_comp (LinearMap.range m.toLinearMap) E.symm
    (fun a ha b hb => ⟨(⟨a, ha⟩ : A) ⊗ₜ (⟨b, hb⟩ : B), funext fun z => by
      have := hm ⟨a, ha⟩ ⟨b, hb⟩ (E.symm z)
      rwa [E.apply_symm_apply] at this⟩) ((hC f).1 hf)
  obtain ⟨w, hw⟩ := this
  refine ⟨w, Subtype.ext ?_⟩
  simp only [E.apply_symm_apply] at hw
  exact hw

variable {T H : Type} [CommGroup T] [CommGroup H]

theorem res_mem (ι : H →* T) {A : Subalgebra R (T → R)} {f : T → R} (hf : f ∈ A) :
    (fun h => f (ι h)) ∈ resOrder ι A := ⟨f, hf, rfl⟩

theorem mem_quotOrder {π : T →* H} {A : Subalgebra R (T → R)} {g : H → R} :
    g ∈ quotOrder π A ↔ (fun t => g (π t)) ∈ A := Iff.rfl

def resMap (ι : H →* T) (A : Subalgebra R (T → R)) : A →ₗ[R] resOrder ι A where
  toFun f := ⟨fun h => f.1 (ι h), res_mem ι f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resMap_surjective (ι : H →* T) (A : Subalgebra R (T → R)) : Function.Surjective (resMap ι A) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem res_hopf {ι : H →* T} (hι : Function.Injective ι) {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    (hp : Module.Projective R (resOrder ι A)) : IsHopfOrder (resOrder ι A) := by
  have := hA.finite
  refine ⟨Module.Finite.of_surjective _ (resMap_surjective ι A), hp, ?_, ?_, ?_⟩
  · obtain ⟨d, hd, h⟩ := hA.full
    refine ⟨d, hd, fun f => ⟨_, h (Function.extend ι f 0), ?_⟩⟩
    funext x
    change d * Function.extend ι f 0 (ι x) = d * f x
    rw [hι.extend_apply]
  · rintro _ ⟨f, hf, rfl⟩
    have := pspan_comp (prodSpan (resOrder ι A)) (fun z : H × H => (ι z.1, ι z.2))
      (fun a ha b hb => mul_mem_pspan (res_mem ι ha) (res_mem ι hb)) (hA.comul f hf)
    simp only [← map_mul] at this
    exact this
  · rintro _ ⟨f, hf, rfl⟩
    have := res_mem ι (hA.inv f hf)
    simp only [← map_inv] at this
    exact this

theorem res_hopf_of_section {ι : H →* T} (hι : Function.Injective ι) {A : Subalgebra R (T → R)}
    (hA : IsHopfOrder A) (s : (H → R) →ₗ[R] (T → R)) (hs : ∀ f ∈ A, s (fun h => f (ι h)) ∈ A)
    (hs' : ∀ g h, s g (ι h) = g h) : IsHopfOrder (resOrder ι A) := by
  have := hA.projective
  refine res_hopf hι hA (Module.Projective.of_split (M := A)
    (LinearMap.codRestrict (Subalgebra.toSubmodule A) (s ∘ₗ (resOrder ι A).val.toLinearMap) ?_) (resMap ι A) ?_)
  · rintro ⟨_, f, hf, rfl⟩
    exact hs f hf
  · ext g h
    exact hs' g h

end PositivityTheory.HtPt.Mj
end

