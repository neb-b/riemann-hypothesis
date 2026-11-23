module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BeTransSymmOfWitData
section
noncomputable section

namespace GlobalTheory.ThetaShiftProofs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}} (f : A →+* F) (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (z : Sp F) :
    ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
  let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
  refine ⟨Units.map g.toMonoidHom a, ?_⟩
  have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← toStk_valF _ U z hz]
  congr 1
  have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
  rw [valF, dite_eq_left ht]
  have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
  rw [e1]
  exact e3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k}

end GlobalTheory.ThetaShiftProofs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstFamComponentsBasisExpansion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

theorem finite_form_le {Y : Type} [AddCommGroup Y] [Module.Finite ℤ Y] (q : LinearMap.BilinForm ℤ Y)
    (hq : ∀ y, y ≠ 0 → 0 < q y y) (n : ℕ) : {y | q y y ≤ n}.Finite := by
  have h0 : ∀ y, 0 ≤ q y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hq y h).le
  have : AddGroup.FG Y := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Y (n := 4 * n + 1) (by omega)
  refine Set.Finite.of_finite_image (f := fun y => (QuotientAddGroup.mk y :
    Y ⧸ (nsmulAddMonoidHom (4 * n + 1) : Y →+ Y).range)) (Set.toFinite _) fun y hy y' hy' h => ?_
  obtain ⟨v, hv⟩ := QuotientAddGroup.eq.1 h
  obtain rfl : y' = y + (4 * n + 1) • v := by rw [show (4 * n + 1) • v = -y + y' from hv, add_neg_cancel_left]
  by_contra hne
  have hv0 : v ≠ 0 := fun e => hne (by rw [e, smul_zero, add_zero])
  have a₁ := hq v hv0
  have a₂ := h0 (y + (y + (4 * n + 1) • v))
  have a₃ : q y y ≤ n := hy
  have a₄ : q (y + (4 * n + 1) • v) (y + (4 * n + 1) • v) ≤ n := hy'
  simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at a₂ a₄
  push_cast at a₂ a₄
  have a₅ : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith [mul_nonneg (mul_nonneg a₅ a₅) a₁.le, mul_nonneg a₅ a₁.le, mul_nonneg a₅ (sub_nonneg.2 (Int.add_one_le_of_lt a₁))]


include hj in
theorem finite_expo_lt (α : a.D₀.X) (n : ℤ) : {mu | expo a j α mu < n}.Finite := by
  refine Set.Finite.subset ((finite_form_le a.be a.be_pos (2 * n + a.be α α).toNat).preimage
    (add_left_injective α).injOn) fun mu h => ?_
  have h₁ : expo a j α mu < n := h
  have h₂ := two_mul_expo a j α mu
  have h₃ := a.be_symm α mu
  have h₄ : 0 ≤ a.be mu mu := by
    by_cases h : mu = 0
    · simp [h]
    · exact (a.be_pos mu h).le
  have h₅ : a.be mu mu ≤ j * a.be mu mu := le_mul_of_one_le_left h₄ (by exact_mod_cast hj)
  show a.be (mu + α) (mu + α) ≤ _
  simp only [map_add (f := _), LinearMap.add_apply]
  omega

include hj in
theorem exists_expo_bound (α : a.D₀.X) : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ mu, 0 ≤ (m : ℤ) + expo a j α mu := by
  obtain ⟨n, hn⟩ := ((finite_expo_lt hj α 0).image fun mu => expo a j α mu).bddBelow
  refine ⟨(-n).toNat, fun m hm mu => ?_⟩
  by_cases h : expo a j α mu < 0
  · have : n ≤ expo a j α mu := hn ⟨mu, h, rfl⟩
    omega
  · omega

theorem map_add_nsmul (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (α mu : a.D₀.X) : e (α + j • mu) = e α + j • e mu := by
  rw [map_add (f := _), map_nsmul]

theorem eq_or_off (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (j : ℕ) (α : a.D₀.X) (χ : P.toPre.X) :
    (∃ mu, e (α + j • mu) = χ) ∨ ∀ mu, e α + j • mu ≠ χ := by
  by_cases h : ∃ mu, e α + j • mu = χ
  · obtain ⟨mu, rfl⟩ := h
    exact .inl ⟨e.symm mu, by rw [map_add_nsmul, e.apply_symm_apply]⟩
  · exact .inr fun mu h' => h ⟨mu, h'⟩

include hj in
theorem exists_isIntegralForm (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) {m : ℕ}
    (hm : ∀ mu, 0 ≤ (m : ℤ) + expo a j α mu) : ∃ f, IsIntegralForm hW j α s₀ m f := by
  have ex : ∀ χ, ∃ t : SecBMod P.toPre j χ, (∀ mu, e (α + j • mu) = χ → HEq t
      ((PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀))) ∧ ((∀ mu, e α + j • mu ≠ χ) → t = 0) := fun χ => by
    rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | h
    · refine ⟨(PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀), fun mu' h => ?_, fun h => absurd (map_add_nsmul e α mu).symm (h _)⟩
      obtain rfl := FamFree.add_nsmul_inj hj α _ _ (e.injective h)
      rfl
    · exact ⟨0, fun mu h' => absurd ((map_add_nsmul e α mu).symm.trans h') (h _), fun _ => rfl⟩
  choose f h₁ h₂ using ex
  exact ⟨f, fun mu => ⟨hm mu, eq_of_heq (h₁ _ mu rfl)⟩, h₂⟩


variable {hW} in
theorem IsIntegralForm.resF_eq {α : a.D₀.X} {s₀ : SecBMod a.D₀ j α} {m : ℕ} {f : ∀ χ, SecBMod P.toPre j χ}
    (h : IsIntegralForm hW j α s₀ m f) (χ : P.toPre.X) : resF P.toPre F j χ (f χ) =
      toF (R := PowerSeries k) F (PowerSeries.X ^ m) • famComp P.toPre F j χ (constFam hW F hG hj α s₀) := by
  rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | hχ
  · rw [(h.1 mu).2, map_smulₛₗ, resF_pullB, constFam_add_nsmul, smul_smul, map_pow, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (h.1 mu).1, zpow_add₀ (toF_X_ne_zero F), zpow_natCast]
  · rw [h.2 χ hχ, map_zero, constFam_off hW F hG hj α s₀ χ hχ, smul_zero]

variable {A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries k))))}
  {G : Over (Spec (CommRingCat.of (PowerSeries k)))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (Ideal.span {PowerSeries.X}) P A G)


include hG hj in
theorem exists_expandsAt (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
    ∃ (f : ∀ χ, SecBMod P.toPre j χ) (σ : H0 U.LG.L j), IsIntegralForm hW j α s₀ m f ∧
      ∀ n, U.toUnifPre.ExpandsAt n j σ f := by
  obtain ⟨s, ⟨r, hr, σ, f', -, hf', hE⟩, -⟩ := (U.expand j hj).2 (constFam hW _ hG hj α s₀)
  obtain ⟨n₀, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr PowerSeries.X_irreducible
  obtain ⟨m₁, hm₁⟩ := exists_expo_bound hj α
  refine ⟨max n₀ m₁, fun m hm => ?_⟩
  obtain ⟨f, hf⟩ := exists_isIntegralForm hW hj α s₀ (hm₁ m ((le_max_right _ _).trans hm))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ((le_max_left _ _).trans hm)
  refine ⟨f, SecOps.secScale (scal G.hom (u⁻¹.val * PowerSeries.X ^ d)) σ, hf, fun n =>
    expandsAt_secIsMul _ _ _ _ _ U.toUnifPre n j (u⁻¹.val * PowerSeries.X ^ d) σ _ f' f (fun _ => rfl)
      (fun χ => ?_) (hE n)⟩
  have e₁ : f χ = (u⁻¹.val * PowerSeries.X ^ d : PowerSeries k) • (show SecBMod P.toPre j χ from f' χ) := by
    refine resF_injective P.toPre (FractionRing (PowerSeries k)) j χ ?_
    rw [hf.resF_eq _ hG hj, map_smulₛₗ, (secScal_iff_resF P.toPre _ (famComp _ _ j χ _) _ _).1 (hf' χ), smul_smul,
      ← map_mul, _root_.mul_mul_mul_comm, Units.inv_mul, _root_.one_mul, ← pow_add, add_comm]
  rw [e₁]
  exact fun _ => rfl


include hG hj in
theorem exists_pow_smul_mem_span {C : Type} (rep : C → a.D₀.X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α)
    {Idx : C → Type} (bas : ∀ x, Module.Basis (Idx x) k (SecBMod a.D₀ j (rep x))) (m : (Σ x, Idx x) → ℕ)
    (f : (Σ x, Idx x) → ∀ χ, SecBMod P.toPre j χ)
    (σ : (Σ x, Idx x) → SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ))))
    (hf : ∀ i : Σ x, Idx x, IsIntegralForm hW j (rep i.1) (bas i.1 i.2) (m i) (f i))
    (hE : ∀ i n, U.toUnifPre.ExpandsAt n j (σ i) (f i))
    (s : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))) :
    ∃ n : ℕ, (PowerSeries.X : PowerSeries k) ^ n • s ∈ Submodule.span (PowerSeries k) (Set.range σ) := by
  obtain ⟨B, hB⟩ := exists_basis_constFam hW (FractionRing (PowerSeries k)) hG hj rep hrep bas
  obtain ⟨t, ht, h⟩ := exists_smul_mem_span_of_expandsAt U hj B B.span_eq (fun i => PowerSeries.X ^ m i)
    (fun i => pow_ne_zero _ PowerSeries.X_ne_zero) σ f (fun i χ => by
      rw [show B i = _ from hB i.1 i.2]; exact (hf i).resF_eq _ hG hj χ) hE s
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht PowerSeries.X_irreducible
  refine ⟨n, ?_⟩
  have := Submodule.smul_mem _ u⁻¹.val h
  rwa [smul_smul, Units.inv_mul_cancel_left] at this

end GlobalTheory.ConstFam

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsMaximalMemSpan
section
namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.TorusFourier
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}

def IsIsotropicSub (G : Matrix (Fin r) (Fin r) E) (V : Submodule E (Fin r → E)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, herm G v w = 0

theorem isIsotropicSub_span {G : Matrix (Fin r) (Fin r) E} {s : Set (Fin r → E)}
    (h : ∀ v ∈ s, ∀ w ∈ s, herm G v w = 0) : IsIsotropicSub G (Submodule.span E s) := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [herm, cc]
    | add y z _ _ hy hz =>
      have : herm G x (y + z) = herm G x y + herm G x z := by
        simp [herm, cc, mul_add, Finset.sum_add_distrib]
      rw [this, hy, hz, add_zero]
    | smul c y _ hy =>
      have : herm G x (c • y) = cc c * herm G x y := by
        simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hy, mul_zero]
  | zero => simp [herm]
  | add x y _ _ hx hy =>
    have : herm G (x + y) w = herm G x w + herm G y w := by
      simp [herm, add_mul, Finset.sum_add_distrib]
    rw [this, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_left', hx, mul_zero]

theorem exists_smul_mem (X : Data E r) (v : Fin r → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ X.Λ := by
  first
  | exact @_root_.GlobalTheory.SubmoduleScalarClosure.main
  | exact _root_.GlobalTheory.SubmoduleScalarClosure.main
  | (apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubmoduleScalarClosure.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubmoduleScalarClosure.main ..)

section Torus

variable (X : Data E r)

end Torus

section Main

variable (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P)
  (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
    Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)

include hP hχ

end Main

end

end GlobalTheory.MaxCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
section
noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

section Forms

variable (O : Type) [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X] {U U' : Type} [CommGroup U]
  [CommGroup U']

structure IsScalarForm (t : X → X → U) : Prop where
  add_right : ∀ y x x', t y (x + x') = t y x * t y x'
  symm : ∀ y x, t y x = t x y
  bal : ∀ (a : O) y x, t (a • y) x = t y (star a • x)

variable {O}

namespace IsScalarForm

variable {t s : X → X → U} (ht : IsScalarForm O t)
include ht

theorem add_left (y y' x : X) : t (y + y') x = t y x * t y' x := by
  rw [ht.symm, ht.add_right, ht.symm x, ht.symm x]

theorem zero_right (y : X) : t y 0 = 1 := by
  have := ht.add_right y 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem neg_right (y x : X) : t y (-x) = (t y x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ht.add_right, neg_add_cancel, ht.zero_right]

theorem neg_left (y x : X) : t (-y) x = (t y x)⁻¹ := by rw [ht.symm, ht.neg_right, ht.symm]

theorem nsmul_right (n : ℕ) (y x : X) : t y (n • x) = t y x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, ht.zero_right]
  | succ n ih => rw [succ_nsmul, pow_succ, ht.add_right, ih]

theorem nsmul_left (n : ℕ) (y x : X) : t (n • y) x = t y x ^ n := by rw [ht.symm, ht.nsmul_right, ht.symm]

theorem map (f : U →* U') : IsScalarForm O fun y x => f (t y x) :=
  ⟨fun y x x' => by rw [ht.add_right, map_mul], fun y x => by rw [ht.symm], fun a y x => by rw [ht.bal]⟩

theorem inv : IsScalarForm O fun y x => (t y x)⁻¹ := ht.map invMonoidHom

theorem pow (n : ℕ) : IsScalarForm O fun y x => t y x ^ n := ht.map (powMonoidHom n)

theorem mem_balForms : Forms.bilOfMul t ht.add_left ht.add_right ∈ Forms.balForms ℤ O X (Additive U) :=
  ⟨ht.symm, ht.bal⟩

theorem refine_add {w : O} (hw : w + star w = 1) (a b : X) :
    t (a + b) (w • (a + b)) = t a (w • a) * t b (w • b) * t a b := by
  have h : t a (w • b) * t b (w • a) = t a b := by
    rw [ht.symm b, ht.bal, ← ht.add_right, ← add_smul, hw, one_smul]
  rw [smul_add, ht.add_left, ht.add_right, ht.add_right, ← h]
  ac_rfl

theorem refine_neg (w : O) (a : X) : t (-a) (w • -a) = t a (w • a) := by
  rw [smul_neg, ht.neg_left, ht.neg_right, inv_inv]

end IsScalarForm

end Forms

section Constants

variable {A A' : Type} [CommRing A] [CommRing A'] {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K]
  [Fintype K']

def unitAt (q : Z ⟶ Sp A) (z : Z) : Aˣ →* (Z.presheaf.stalk z)ˣ :=
  (gm q z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom)

theorem unitAt_apply (q : Z ⟶ Sp A) (z : Z) (u : Aˣ) : unitAt q z u = gm q z ⊤ (unitOn u) := rfl

theorem unitAt_val (q : Z ⟶ Sp A) (z : Z) (u : Aˣ) : (unitAt q z u).val = gs q z ⊤ (unitOn u).val :=
  (gs_unit q z ⊤ trivial (unitOn u)).symm

theorem unitAt_spMap (q : Z ⟶ Sp A') (f : A →+* A') (z : Z) (u : Aˣ) :
    unitAt (q ≫ spMap f) z u = unitAt q z (Units.map f.toMonoidHom u) := by
  refine (gm_pull q (spMap f) z ⊤ trivial (unitOn u)).symm.trans (congrArg (gm q z ⊤) (Units.ext ?_))
  exact (congrArg (fun e => e.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem unitAt_injective {F : Type} [Field F] (y : Sp F) : Function.Injective (unitAt (𝟙 (Sp F)) y) :=
  fun u v h => (stalkUnits y).injective ((gm_unitOn y u).symm.trans (h.trans (gm_unitOn y v)))

theorem val_scale {φ : K → (Sp A ⟶ X)} {ε : K → ℤ} (u : Aˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Sp A) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : val (scaleGen (unitOn u) t) r z J = unitAt r z u * val t r z J :=
  val_scaleGen _ t r hJ

theorem val_powGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) : val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

end Constants

variable {R : Type} [CommRing R] [IsDomain R]

abbrev PsiFam (D : DegPre R) : Type :=
  ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1))

@[reducible] def withPsi (D : DegPre R) (ψ : PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) : DegPre R :=
  { D with psi := ψ, psi_gen := hψ }

@[reducible] def rescale (D : DegPre R) (q : D.X → (FractionRing R)ˣ) : DegPre R :=
  withPsi D (fun χ => scaleGen (unitOn (q χ)) (D.psi χ)) fun χ => scaleGen_isGen _ _ (D.psi_gen χ)

variable {O : Type} [CommRing O] [StarRing O]

@[reducible] def twist (D : DegPre R) [Module O D.X] (w : O) (t : D.X → D.X → (FractionRing R)ˣ) : DegPre R :=
  rescale D fun y => t y (w • y)

variable {D : DegPre R}

theorem val_tau (D : DegPre R) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) r z J = val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ *
      (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (q : D.X → (FractionRing R)ˣ) (a : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val ((rescale D q).psi a) r z J = unitAt r z (q a) * val (D.psi a) r z J :=
  val_scale (q a) (D.psi a) r hJ

theorem val_tau_rescale (q : D.X → (FractionRing R)ˣ) {a b : D.X} {x : (FractionRing R)ˣ}
    (hx : q (a + b) = q a * q b * x) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((rescale D q).tau a b) r z J = unitAt r z x * val (D.tau a b) r z J := by
  have e := val_tau (rescale D q) a b r hJ
  have e₁ := val_psi_rescale q (a + b) r hJ
  have e₂ := val_psi_rescale q a r hJ
  have e₃ := val_psi_rescale q b r hJ
  have e₄ := val_tau D a b r hJ
  rw [hx, map_mul, map_mul] at e₁
  have e₅ : val (rescale D q).rigK r z J = val D.rigK r z J := rfl
  rw [e₁, e₂, e₃, e₅] at e
  rw [e, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section Twist

variable [Module O D.X] {w : O} {t : D.X → D.X → (FractionRing R)ˣ}

theorem val_psi_twist (w : O) (t : D.X → D.X → (FractionRing R)ˣ) (a : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left)
    {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((twist D w t).psi a) r z J = unitAt r z (t a (w • a)) * val (D.psi a) r z J :=
  val_psi_rescale (fun y => t y (w • y)) a r hJ

variable (hw : w + star w = 1) (ht : IsScalarForm O t)
include ht

theorem psiEven_twist (w : O) (h : D.PsiEven) : (twist D w t).PsiEven := fun χ =>
  corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (h χ) (𝟙 _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_psi_twist w t (-χ) _ hJ) rfl).trans
      (Eq.trans ?_ (val_psi_twist w t χ _ hJ).symm))
    rw [ht.refine_neg, ← e, _root_.mul_assoc]

include hw

theorem val_tau_twist (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((twist D w t).tau a b) r z J = unitAt r z (t a b) * val (D.tau a b) r z J :=
  val_tau_rescale (fun y => t y (w • y)) (ht.refine_add hw a b) r hJ

theorem tauBimult_twist (h : D.TauBimult) : (twist D w t).TauBimult := fun a a' b =>
  corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht (a + a') b _ hJ) rfl).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_tau_twist hw ht a b _ hJ)
        (val_tau_twist hw ht a' b _ hJ))).symm))
    rw [ht.add_left, map_mul, _root_.mul_mul_mul_comm, ← e, _root_.mul_assoc]
    rfl

def twistAct (oa : D.OAct O) : (twist D w t).OAct O where
  onB := oa.onB
  c_lin := oa.c_lin
  tau_bal a u hu u₀ x x' := corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal a u hu u₀ x x') (𝟙 _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht (a • x) x' _ hJ) rfl).trans
      (Eq.trans ?_ (val_tau_twist hw ht x (star a • x') _ hJ).symm))
    rw [ht.bal, ← e, _root_.mul_assoc]
    rfl

theorem psi_weight_zero_twist {oa : D.OAct O} (h : TraceFormTwistIso D oa w) : TraceFormTwistIso (twist D w t) (twistAct hw ht oa) w := by
  obtain ⟨u, hu, u₀, h⟩ := h
  refine ⟨u, hu, u₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h x) (𝟙 _)).trans (val_mul hJ _ _ _))
  refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_tau_twist hw ht x (w • x) _ hJ) rfl).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_psi_twist w t x _ hJ) rfl)).symm))
  rw [_root_.mul_assoc, _root_.mul_assoc]
  exact congrArg _ e


end Twist

end GlobalTheory.TauTwist
end
end

