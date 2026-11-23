module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldPullbackBaseChangeDerivation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldBC

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : IsField W₀ d) (h : W₁ ≤ W₀) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h),
    fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

def derivOf {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (V : Z.Opens) (hV : V ≤ W₀) : Derivation ℤ Γ(Z, V) Γ(Z, V) :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' (d V) (hd.1 V hV)))
    (fun a b => by simp [hd.2.1 V hV a b, smul_eq_mul])

theorem exists_field_of_deriv {Z : Scheme.{0}} (V : Z.Opens) (hV : IsAffineOpen V)
    (δ : Derivation ℤ Γ(Z, V) Γ(Z, V)) :
    ∃ e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField V e ∧ ∀ a, e V a = δ a := by
  let σ : Γ(Z, V) →+* DualNumber Γ(Z, V) :=
    { toFun := fun a => TrivSqZeroExt.inl a + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext
        · simp
        · simp [δ.leibniz, smul_eq_mul]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  obtain ⟨d', hd', hd'v⟩ := GlobalTheory.SpecField.exists_isField Γ(Z, V) σ (fun a => by simp [σ])
  exact GlobalTheory.FieldTransport.exists_isField_transport Z V hV (fun a => δ a) d' hd'
    (fun a => by
      refine (hd'v a).trans ?_
      simp only [σ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rfl)

theorem sec_ext {Z : Scheme.{0}} (V : Z.Opens) (s t : Γ(Z, V))
    (h : ∀ x ∈ V, ∃ V' : Z.Opens, ∃ hV' : V' ≤ V, x ∈ V' ∧ resG Z hV' s = resG Z hV' t) : s = t := by
  refine TopCat.Presheaf.section_ext Z.sheaf V s t fun x hx => ?_
  obtain ⟨V', hV', hx', e⟩ := h x hx
  have := congrArg (Z.presheaf.germ V' x hx').hom e
  simp only [resG, TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem appLE_res {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (h : V' ≤ V) (r : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom r) = (f.appLE U V' (h.trans e)).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U U' : Y.Opens) (V : X.Opens) (h : U' ≤ U)
    (e : V ≤ f ⁻¹ᵁ U') (r : Γ(Y, U)) :
    (f.appLE U' V e).hom (resG Y h r) = (f.appLE U V (e.trans (f.preimage_mono h))).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem deriv_eq_zero_of_closure {B : Type} [CommRing B] (Δ : Derivation ℤ B B) (S : Set B)
    (hS : Subring.closure S = ⊤) (h : ∀ x ∈ S, Δ x = 0) (x : B) : Δ x = 0 := by
  have hx : x ∈ Subring.closure S := hS ▸ Subring.mem_top x
  induction hx using Subring.closure_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]
  | mul x y _ _ hx hy => simp [Derivation.leibniz, hx, hy]

theorem exists_field_pullback : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (W : Z.Opens) (hW : W ≤ p ⁻¹ᵁ U.1) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W d → (∀ r, d W ((p.appLE U.1 W hW).hom r) = (p.appLE U.1 W hW).hom (D r)) → ∃ d' : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O), IsField (φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1) d' ∧ (∀ (O' : Z'.Opens) (h' : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ φ ⁻¹ᵁ W → ∀ r, d' O' ((p'.appLE U'.1 O' h').hom r) = (p'.appLE U'.1 O' h').hom (D' r)) ∧ ∀ (O : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O), O ≤ W → O' ≤ p' ⁻¹ᵁ U'.1 → ∀ f, d' O' ((φ.appLE O O' h).hom f) = (φ.appLE O O' h).hom (d O f) := by
  intro Z Z' X X' p p' φ g hpb U U' hU D D' hD' W hW d hd hdD
  classical
  let A := {O : Z.affineOpens // O.1 ≤ W}
  have hOp : ∀ O : A, O.1.1 ≤ p ⁻¹ᵁ U.1 := fun O => O.2.trans hW
  let O' : A → Z'.Opens := fun O => φ ⁻¹ᵁ O.1.1 ⊓ p' ⁻¹ᵁ U'.1
  have hO'aff : ∀ O : A, IsAffineOpen (O' O) := fun O =>
    (_root_.GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).1
  have hgen : ∀ O : A, Subring.closure (Set.range (φ.appLE O.1.1 (O' O) inf_le_left).hom ∪
      Set.range (p'.appLE U'.1 (O' O) inf_le_right).hom) = ⊤ := fun O =>
    (_root_.GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).2
  let δ : ∀ O : A, Derivation ℤ Γ(Z, O.1.1) Γ(Z, O.1.1) := fun O => derivOf hd O.1.1 O.2
  have hδ : ∀ (O : A) r, δ O ((p.appLE U.1 O.1.1 (hOp O)).hom r) =
      (p.appLE U.1 O.1.1 (hOp O)).hom (D r) := by
    intro O r
    show d O.1.1 _ = _
    rw [← appLE_res p U.1 W O.1.1 hW O.2, hd.2.2 W O.1.1 O.2 le_rfl, hdD, appLE_res]
  choose δ' hδ'1 hδ'2 using fun O : A =>
    _root_.GlobalTheory.FibreDer.exists_der_fibre Z Z' X X' p p' φ g hpb U U' hU D D' hD' O.1 (hOp O) (δ O) (hδ O)
  choose e he1 he2 using fun O : A => exists_field_of_deriv (O' O) (hO'aff O) (δ' O)

  have hT : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (b : Γ(Z, O.1.1)),
      e O V ((φ.appLE O.1.1 V (hV.trans inf_le_left)).hom b) =
        (φ.appLE O.1.1 V (hV.trans inf_le_left)).hom (d O.1.1 b) := by
    intro O V hV b
    rw [← appLE_res φ O.1.1 (O' O) V inf_le_left hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'2,
      appLE_res]
    rfl
  have hP : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (r : Γ(X', U'.1)),
      e O V ((p'.appLE U'.1 V (hV.trans inf_le_right)).hom r) =
        (p'.appLE U'.1 V (hV.trans inf_le_right)).hom (D' r) := by
    intro O V hV r
    rw [← appLE_res p' U'.1 (O' O) V inf_le_right hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'1,
      appLE_res]

  let bas : (O : A) → Γ(Z, O.1.1) → A := fun O s =>
    ⟨⟨Z.basicOpen s, O.1.2.basicOpen s⟩, (Z.basicOpen_le s).trans O.2⟩
  have hKB : ∀ (O : A) (s : Γ(Z, O.1.1)) (V : Z'.Opens), V ≤ O' (bas O s) → ∀ f,
      e O V f = e (bas O s) V f := by
    intro O s
    have hle : O' (bas O s) ≤ O' O := inf_le_inf_right _ (φ.preimage_mono (Z.basicOpen_le s))
    refine _root_.GlobalTheory.LogKS.isField_eq_of_affine Z' (O' (bas O s)) (hO'aff (bas O s)) (e O) (e (bas O s))
      (isField_mono (he1 O) hle) (he1 (bas O s)) ?_
    intro a
    rw [he2 (bas O s)]
    let Δ := derivOf (he1 O) (O' (bas O s)) hle - δ' (bas O s)
    have hΔ : ∀ x, Δ x = e O (O' (bas O s)) x - δ' (bas O s) x := fun x => rfl
    suffices key : ∀ x, Δ x = 0 by
      have := key a
      rwa [hΔ, sub_eq_zero] at this
    refine deriv_eq_zero_of_closure Δ _ (hgen (bas O s)) ?_
    rintro x (⟨c, rfl⟩ | ⟨r, rfl⟩)
    · let ψ := (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
      have hres : ∀ b : Γ(Z, O.1.1), Δ (ψ (resG Z (Z.basicOpen_le s) b)) = 0 := by
        intro b
        rw [hΔ, sub_eq_zero]
        show e O (O' (bas O s)) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b)) = δ' (bas O s) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b))
        rw [hδ'2 (bas O s)]
        show _ = (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom (d (Z.basicOpen s) (resG Z (Z.basicOpen_le s) b))
        rw [res_appLE, hT O _ hle, hd.2.2 O.1.1 (Z.basicOpen s) (Z.basicOpen_le s) O.2, res_appLE]
      haveI := O.1.2.isLocalization_basicOpen s
      obtain ⟨⟨a₀, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) c
      change c * resG Z (Z.basicOpen_le s) m = resG Z (Z.basicOpen_le s) a₀ at hm
      have hunit : IsUnit (ψ (resG Z (Z.basicOpen_le s) m)) := by
        obtain ⟨n, hn⟩ := m.2
        rw [← hn, map_pow]
        exact ((RingedSpace.isUnit_res_basicOpen Z.toRingedSpace s).pow n).map ψ
      have h1 := congrArg (fun y => Δ (ψ y)) hm
      simp only [map_mul, Derivation.leibniz, hres, smul_zero, zero_add, smul_eq_mul, mul_zero] at h1
      exact (hunit.mul_right_eq_zero).1 h1
    · rw [hΔ, sub_eq_zero, hP O _ hle, hδ'1]
  have hcomp : ∀ (O₁ O₂ : A) (V : Z'.Opens), V ≤ O' O₁ → V ≤ O' O₂ → ∀ f, e O₁ V f = e O₂ V f := by
    intro O₁ O₂ V h1 h2 f
    apply sec_ext V
    intro x hx
    have hx1 : φ.base x ∈ O₁.1.1 ⊓ O₂.1.1 := ⟨(h1 hx).1, (h2 hx).1⟩
    obtain ⟨f₁, f₂, hf, hxf⟩ := exists_basicOpen_le_affine_inter O₁.1.2 O₂.1.2 _ hx1
    have hA : bas O₁ f₁ = bas O₂ f₂ := Subtype.ext (Subtype.ext hf)
    have hV1 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₁ f₁) := inf_le_right
    have hV2 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₂ f₂) := le_of_le_of_eq inf_le_right (congrArg O' hA)
    refine ⟨V ⊓ O' (bas O₁ f₁), inf_le_left, ⟨hx, hxf, (h1 hx).2⟩, ?_⟩
    rw [← (he1 O₁).2.2 V _ inf_le_left h1, ← (he1 O₂).2.2 V _ inf_le_left h2,
      hKB O₁ f₁ _ hV1, hKB O₂ f₂ _ hV2]
    exact congrArg (fun B => e B (V ⊓ O' (bas O₁ f₁)) (resG Z' inf_le_left f)) hA
  obtain ⟨d', hd'1, hd'2⟩ := _root_.GlobalTheory.LogKS.isField_glue Z' A O' e he1 hcomp
  have hcov : φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1 ≤ ⨆ O : A, O' O := by
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hx.1)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨O₀, hO₀⟩, hle⟩, hx0, hx.2⟩
  refine ⟨d', isField_mono hd'1 hcov, ?_, ?_⟩
  · intro V hV hVW r
    have hVc : V ≤ ⨆ O : A, O' O := (le_inf hVW hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hVW hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      hP B _ inf_le_right]
  · intro O V h hOW hV f
    have hVc : V ≤ ⨆ O : A, O' O :=
      (le_inf (h.trans (φ.preimage_mono hOW)) hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ O from h hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle.trans hOW⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      ← res_appLE φ O O₀ (V ⊓ O' B) hle (inf_le_right.trans inf_le_left) f,
      hT B _ inf_le_right, hd.2.2 O O₀ hle hOW, res_appLE]

end GlobalTheory.FieldBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentFormsSymmOfIsUnitTauOnToricChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.RigChart
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTauSymm

theorem exps_eq {σ k : Type} [Field k] [IsDomain (MvPowerSeries σ k)] {m : ℕ} (v : Fin m → σ)
    (hv : Function.Injective v) (A B : Fin m → ℤ) {x x' : MvPowerSeries σ k} (hx : IsUnit x) (hx' : IsUnit x')
    (he : (∏ i, algebraMap (MvPowerSeries σ k) (FractionRing (MvPowerSeries σ k)) (MvPowerSeries.X (v i)) ^ A i) *
        algebraMap _ _ x =
      (∏ i, algebraMap (MvPowerSeries σ k) (FractionRing (MvPowerSeries σ k)) (MvPowerSeries.X (v i)) ^ B i) *
        algebraMap _ _ x') :
    A = B := by
  set K := FractionRing (MvPowerSeries σ k)
  let n : Fin m → ℕ := fun i => (A i).natAbs + (B i).natAbs
  have hne : ∀ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ≠ 0 := fun i => by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
    intro e0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (v i) 1)) e0
    simp [MvPowerSeries.coeff_X] at this
  have H : ∀ C : Fin m → ℤ, (∀ i, 0 ≤ C i + n i) →
      (∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ C i) *
        ∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ n i =
        algebraMap _ K (∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ (C i + n i).toNat) := by
    intro C hC
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne i), Int.toNat_of_nonneg (hC i)]
  have hA : ∀ i, 0 ≤ A i + n i := fun i => by simp only [n]; omega
  have hB : ∀ i, 0 ≤ B i + n i := fun i => by simp only [n]; omega
  have he' := congrArg (· * ∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ n i) he
  rw [mul_right_comm, H A hA, mul_right_comm, H B hB, ← map_mul, ← map_mul] at he'
  have he'' := IsFractionRing.injective _ K he'
  have hmon : ∀ a : Fin m → ℕ, ∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ a i =
      MvPowerSeries.monomial (∑ i, Finsupp.single (v i) (a i)) 1 := by
    intro a
    simp_rw [MvPowerSeries.X_pow_eq]
    rw [MvPowerSeries.prod_monomial]
    simp
  have happ : ∀ (a : Fin m → ℕ) (i : Fin m), (∑ j, Finsupp.single (v j) (a j)) (v i) = a i := by
    classical
    intro a i
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      exact fun e => hj (hv e)
    · simp
  rw [hmon, hmon] at he''
  have hPM := GlobalTheory.MumFam.monomial_eq_of_mul_unit hx hx' he''
  funext i
  have := congrArg (fun f => f (v i)) hPM
  simp only [happ] at this
  have a1 := Int.toNat_of_nonneg (hA i)
  have b1 := Int.toNat_of_nonneg (hB i)
  omega

end GlobalTheory.UnitTauSymm

namespace GlobalTheory.UnitTauSymm

open GlobalTheory.LogKSChart ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem commGroup_four_factor_rearrange {G : Type} [CommGroup G] (a b c A B C D : G) :
    a * A * (b * B)⁻¹ * (c * C)⁻¹ * D⁻¹ = a * b⁻¹ * c⁻¹ * (A * B⁻¹ * C⁻¹ * D⁻¹) := by
  simp only [mul_inv]
  ac_rfl

theorem exists_units_rel {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) (y z : Q.X) (n1 n2 n3 : Fin m → ℕ)
    (p1 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c (y + z)).left) fun _ => -1))
    (p2 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c y).left) fun _ => -1))
    (p3 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c z).left) fun _ => -1))
    (hp1 : IsUnitPart Q t gam (y + z) n1 p1) (hp2 : IsUnitPart Q t gam y n2 p2) (hp3 : IsUnitPart Q t gam z n3 p3)
    (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left]
      ![-1, 1, 1, -1])) (hτ : τ₀.IsGen) (e : (FractionRing R)ˣ)
    (hv : ∀ zz J, Good Q.P.L zz J →
      val (Q.tau y z) (𝟙 _) zz J = gm (𝟙 (TK R).left) zz ⊤ (unitOn e) * val τ₀ (toUnit (TK R)).left zz J) :
    ∃ x x' : R, IsUnit x ∧ IsUnit x' ∧ (e : FractionRing R) * algebraMap R _ x =
      algebraMap R _ (∏ i, t i ^ n1 i) * (algebraMap R _ (∏ i, t i ^ n2 i))⁻¹ *
        (algebraMap R _ (∏ i, t i ^ n3 i))⁻¹ * algebraMap R _ x' := by
  obtain ⟨hg1, -, e1, he1, hv1⟩ := hp1
  obtain ⟨hg2, -, e2, he2, hv2⟩ := hp2
  obtain ⟨hg3, -, e3, he3, hv3⟩ := hp3
  have hc0 : Q.c 0 = η[Q.P.A] := by
    have h := Q.c_add 0 0
    rw [add_zero] at h
    have h' : Q.c 0 * Q.c 0 = Q.c 0 := h.symm
    have h1 : Q.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hc0' : (Q.c 0).left = eSec Q.P.A := by rw [hc0]; rfl
  let T := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ p1 (LB.invGen Q.P.L _ _ p2))
    (LB.invGen Q.P.L _ _ p3)) (LB.invGen Q.P.L _ _ Q.rig)
  have hT : T.IsGen :=
    LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _
      (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ hg1 (LB.isGen_invGen (L := Q.P.L) _ _ _ hg2))
      (LB.isGen_invGen (L := Q.P.L) _ _ _ hg3)) (LB.isGen_invGen (L := Q.P.L) _ _ _ Q.rig_gen)
  have hF : FormEq (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (Q.c (y + z)).left) (fun _ : PUnit => (Q.c y).left))
      (fun _ : PUnit => (Q.c z).left)) (fun _ : PUnit => eSec Q.P.A))
      (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => -(-1 : ℤ))) (fun _ : PUnit => -(-1 : ℤ)))
        (fun _ : PUnit => -(1 : ℤ)))
      (K' := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hc0', neg_neg]
    simp [Matrix.vecHead, Matrix.vecTail, hc0']
  obtain ⟨W', hW', hvW⟩ := exists_gen Q.P.isLB hF T hT
  let E : (FractionRing R)ˣ := e1 * e2⁻¹ * e3⁻¹
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  have hui : ∀ a : (FractionRing R)ˣ, unitOn a⁻¹ = (unitOn a)⁻¹ := fun a => map_inv (Units.map _) a
  have hvE : ∀ zz J, Good Q.P.L zz J → val (Q.tau y z) (𝟙 _) zz J =
      gm (𝟙 (TK R).left) zz ⊤ (unitOn E) * val W' (toUnit (TK R)).left zz J := by
    intro zz J hJ
    rw [hvW _ _ zz J hJ]
    simp only [DegPre.tau, DegPre.rigK, T, val_mul hJ, val_inv, val_pull hJ]
    rw [hv1 zz J hJ, hv2 zz J hJ, hv3 zz J hJ, Category.id_comp]
    rw [hu, hu, hui, hui, map_mul, map_mul, map_inv, map_inv]
    exact commGroup_four_factor_rearrange _ _ _ _ _ _ _
  obtain ⟨w, hw⟩ := GlobalTheory.ValueTwoGen.exists_unit_gen _ (TLinPf.linComb_cover Q.P.L Q.P.isLB _ _) τ₀ W' hτ hW'
  have key : ∀ zz J, Good Q.P.L zz J → val W' (toUnit (TK R)).left zz J =
      gm (toUnit (TK R)).left zz ⊤ w * val τ₀ (toUnit (TK R)).left zz J := by
    intro zz J hJ
    have hs : ∀ j, W'.s j = res le_top w * τ₀.s j := fun j => Units.ext (hw j)
    show gm _ zz _ (W'.s _) = _ * gm _ zz _ (τ₀.s _)
    erw [hs, MonoidHom.map_mul, gm_res _ zz le_top (hJ.mem _ _)]
  have k₁ : unitOn e * pullTop (jK R) (1 : Γ(Sp R, ⊤)ˣ) = unitOn E * pullTop (jK R) w :=
      GlobalTheory.TauLocal.eq_of_gm Q.P.isLB fun zz J hJ => by
    have s := (hv zz J hJ).symm.trans (hvE zz J hJ)
    rw [key zz J hJ, ← _root_.mul_assoc] at s
    have hg : gm (toUnit (TK R)).left zz ⊤ w = gm (𝟙 _) zz ⊤ (pullTop (jK R) w) :=
      (show gm (toUnit (TK R)).left zz ⊤ w = gm (𝟙 _ ≫ jK R) zz ⊤ w from rfl).trans
        (gm_pull (𝟙 _) (jK R) zz ⊤ trivial w).symm
    rw [map_mul, map_mul, ← hg, map_one, map_one, _root_.mul_one]
    exact mul_right_cancel s
  have nat := fun v : Γ(Sp R, ⊤)ˣ => congrArg (fun g => g.hom v.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have e₂ := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom v.val) k₁
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (1 : Γ(Sp R, ⊤)ˣ).val,
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val, (1 : Γ(Sp R, ⊤)ˣ).isUnit.map _, w.isUnit.map _, ?_⟩
  have hE : (E : FractionRing R) = algebraMap R _ (∏ i, t i ^ n1 i) * (algebraMap R _ (∏ i, t i ^ n2 i))⁻¹ *
      (algebraMap R _ (∏ i, t i ^ n3 i))⁻¹ := by
    simp only [E, Units.val_mul, Units.val_inv_eq_inv_val, he1, he2, he3]
  rw [← hE]
  refine Eq.trans ?_ (e₂.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w))))
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat 1)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply e.val
  · exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply E.val

end GlobalTheory.UnitTauSymm

namespace GlobalTheory.UnitTauSymm

open GlobalTheory.LogKSChart

theorem gam_symm_of_isUnitTau : ∀ (k : Type) [Field k] (m d : ℕ) (Q : DegPre (ChartRing k m d)) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q (bdParam k m d) gam → ∀ (mu α : Q.X) (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (mu + α)).left, (Q.c mu).left, (Q.c α).left, (Q.c 0).left] ![-1, 1, 1, -1])), IsUnitTau Q (bdParam k m d) gam mu α τ₀ → ∀ i, gam i mu α = gam i α mu := by
  intro k _ m d Q gam hM mu α τ₀ hτ i
  obtain ⟨n1, p1, hp1⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM (mu + α)
  obtain ⟨n2, p2, hp2⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM mu
  obtain ⟨n3, p3, hp3⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM α
  have hn1 := hp1.2.1 i
  have hn2 := hp2.2.1 i
  have hn3 := hp3.2.1 i
  obtain ⟨hτg, e, he, hv⟩ := hτ
  obtain ⟨x, x', hx, hx', hrel⟩ := exists_units_rel Q _ gam mu α n1 n2 n3 p1 p2 p3 hp1 hp2 hp3 τ₀ hτg e hv
  set K := FractionRing (ChartRing k m d)
  let a : Fin m → K := fun i => algebraMap (ChartRing k m d) K (bdParam k m d i)
  have hne : ∀ i, a i ≠ 0 := fun i => by
    simp only [a]
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
    intro e0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) e0
    simp [bdParam, MvPowerSeries.coeff_X] at this
  have hP : ∀ n : Fin m → ℕ, algebraMap (ChartRing k m d) K (∏ i, bdParam k m d i ^ n i) = ∏ i, a i ^ n i := fun n => by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => map_pow _ _ _
  have hP0 : ∀ n : Fin m → ℕ, ∏ i, a i ^ n i ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne i)
  rw [he, hP, hP, hP] at hrel
  have key : (∏ i, a i ^ (fun i => gam i mu α + n2 i + n3 i) i) * algebraMap _ K x =
      (∏ i, a i ^ (fun i => (n1 i : ℤ)) i) * algebraMap _ K x' := by
    have e1 : (∏ i, a i ^ (fun i => gam i mu α + n2 i + n3 i) i) =
        (∏ i, a i ^ gam i mu α) * (∏ i, a i ^ n2 i) * ∏ i, a i ^ n3 i := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_add₀ (hne i), zpow_add₀ (hne i), zpow_natCast, zpow_natCast]
    have e2 : (∏ i, a i ^ (fun i => (n1 i : ℤ)) i) = ∏ i, a i ^ n1 i := by
      refine Finset.prod_congr rfl fun i _ => ?_
      exact zpow_natCast _ _
    have hrel' : (∏ i, a i ^ gam i mu α) * algebraMap _ K x =
        (∏ i, a i ^ n1 i) * (∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n3 i)⁻¹ * algebraMap _ K x' := hrel
    rw [e1, e2]
    calc (∏ i, a i ^ gam i mu α) * (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) * algebraMap _ K x
        = ((∏ i, a i ^ gam i mu α) * algebraMap _ K x) * (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) := by ring
      _ = ((∏ i, a i ^ n1 i) * (∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n3 i)⁻¹ * algebraMap _ K x') *
          (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) := by rw [hrel']
      _ = (∏ i, a i ^ n1 i) * algebraMap _ K x' * ((∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n2 i)) *
          ((∏ i, a i ^ n3 i)⁻¹ * (∏ i, a i ^ n3 i)) := by ring
      _ = (∏ i, a i ^ n1 i) * algebraMap _ K x' := by
        rw [inv_mul_cancel₀ (hP0 n2), inv_mul_cancel₀ (hP0 n3), _root_.mul_one, _root_.mul_one]
  have hAB := congrFun (exps_eq (σ := Fin m ⊕ Fin d) (k := k) Sum.inl Sum.inl_injective _ _ hx hx' key) i
  simp only [map_add (f := _), LinearMap.add_apply] at hn1
  linarith

end GlobalTheory.UnitTauSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackAffineFunctionEqQuotientConst
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem fibre_restrict_scalar_compat : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  intro X Z p U m A q ι h V hV V' hV' r
  have hU : IsAffineOpen U.1 := U.2
  have e0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U.1 := by
    rw [hU.fromSpec_preimage_self]
  have e1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := e0
  have k0 : hU.fromSpec.appLE U.1 ⊤ e0 ≫ (Scheme.ΓSpecIso Γ(X, U.1)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
      ← Functor.map_comp_assoc]
    have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e0).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  have k1 : ∀ x : Γ(X, U.1), ((chart U).appLE U.1 ⊤ e1).hom x = (Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x := by
    intro x
    have := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso Γ(X, U.1)).inv).hom x) k0
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply, Iso.hom_inv_id_apply] at this
    exact this
  have kt : (spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top = (spMap (Ideal.Quotient.mk m)).appTop := by
    dsimp only [Scheme.Hom.appLE]
    exact (congrArg _ ((Sp (Γ(X, U.1) ⧸ m)).presheaf.map_id (Opposite.op ⊤))).trans (Category.comp_id _)
  have k2 : ∀ x : Γ(X, U.1), ((spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m x) := by
    intro x
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk m))
    have := congrArg (fun f => f.hom x) hn
    simp only [CommRingCat.comp_apply] at this
    rw [kt]
    exact this.symm
  have hF : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1 :=
    (le_top : ⊤ ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤).trans
      ((TopologicalSpace.Opens.map (spMap (Ideal.Quotient.mk m)).base).map (homOfLE e1)).le
  have step : ∀ (g : A ⟶ X) (hg : g = q ≫ (spMap (Ideal.Quotient.mk m) ≫ chart U)) (e : V' ≤ g ⁻¹ᵁ U.1),
      (g.appLE U.1 V' e).hom r = (q.appLE ⊤ V' le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
    rintro g rfl e
    rw [← Scheme.Hom.appLE_comp_appLE q (spMap (Ideal.Quotient.mk m) ≫ chart U) U.1 ⊤ V' hF le_top,
      ← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) (chart U) U.1 ⊤ ⊤ e1 le_top]
    simp only [CommRingCat.comp_apply]
    rw [k1, k2]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact step _ h _

end GlobalTheory
end

