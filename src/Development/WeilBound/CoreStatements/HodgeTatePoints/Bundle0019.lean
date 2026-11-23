module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfReg
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Htat.StalkDivisibility

def constSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (d : R) : Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)

section valAt

variable {B C R : Type} [CommRing B] [CommRing C] [CommRing R] {X Y : Scheme.{0}}

theorem valAt_congr {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

theorem valAt_res (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem valAt_mul (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

theorem valAt_sub (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem valAt_comp (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U)
    (s : Γ(X, U)) : valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem specMap_appLE_top (φ : B →+* C) (e) (r : Γ(Spec (CommRingCat.of B), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e).hom r) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom r) := by
  have h : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop := by
    exact (Scheme.Hom.app_eq_appLE _).symm
  rw [h]
  exact congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_spec (κ : B →+* C) (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ x) U h' s = κ (valAt x U h s) := by
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom κ)) x U ⊤ ⊤ h (fun _ _ => trivial)
  simp only [valAt]
  rw [← e]
  exact specMap_appLE_top κ _ _

theorem valAt_const (p : X ⟶ Spec (CommRingCat.of R)) (x : Spec (CommRingCat.of B) ⟶ X) (φ : R →+* B)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (d : R) :
    valAt x U h (constSec p U d) = φ d := by
  have e := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  have key : ∀ (y : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (_ : y = Spec.map (CommRingCat.ofHom φ)) (e' : ⊤ ≤ y ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE ⊤ ⊤ e').hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d := by
    intro y hy e'
    subst hy
    rw [specMap_appLE_top]
    simp
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
    ((p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d
  rw [e]
  exact key _ hx _

theorem constSec_res (p : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (i : V ⟶ U) (d : R) :
    (X.presheaf.map i.op).hom (constSec p U d) = constSec p V d :=
  congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d))
    (p.appLE_map (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) i.op)

theorem app_constSec {R' : Type} [CommRing R'] (p : X ⟶ Spec (CommRingCat.of R)) (p' : Y ⟶ Spec (CommRingCat.of R'))
    (F : Y ⟶ X) (φ : R →+* R') (hF : F ≫ p = p' ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (d : R) :
    (F.app U).hom (constSec p U d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
  have e₁ := Scheme.Hom.appLE_comp_appLE F p ⊤ U (F ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e₂ : ∀ (y : Y ⟶ Spec (CommRingCat.of R)) (_ : y = p' ≫ Spec.map (CommRingCat.ofHom φ)) (e' : F ⁻¹ᵁ U ≤ y ⁻¹ᵁ ⊤),
      (y.appLE ⊤ (F ⁻¹ᵁ U) e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
    intro y hy e'
    subst hy
    rw [Scheme.Hom.comp_appLE]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have n' := congrArg (fun ψ => ψ.hom d) n
    simp only [constSec]
    change (p'.appLE _ _ _).hom (((Spec.map (CommRingCat.ofHom φ)).appTop).hom _) = _
    exact congrArg (p'.appLE ⊤ (F ⁻¹ᵁ U) (fun _ _ => trivial)).hom n'.symm
  rw [← e₂ _ hF (fun _ _ => trivial), ← e₁, Scheme.Hom.app_eq_appLE]
  rfl

theorem dvd_of_stalkMap_dvd (r : Y ⟶ X) [Flat r] (z : Y) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact h

theorem top_le_of_spec_comp {K L : Type} [Field K] [Field L] (κ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro y _
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  obtain ⟨w⟩ := this
  have hw := h (show w ∈ (⊤ : (Spec (CommRingCat.of L)).Opens) from trivial)
  rw [Subsingleton.elim y (Spec.map (CommRingCat.ofHom κ) w)]
  simpa using hw

end valAt

theorem regularAt_of_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hfl κ hκ f g' hreg
  obtain ⟨U', hgU', s', hs'⟩ := hreg
  obtain ⟨d, hd0, U, hgU, s, hs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt R T Γ f (F g')
  have hφ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hfl)
  have hF : Flat F := MorphismProperty.of_isPullback (P := @Flat) hbc.cart.flip hφ
  have hsq : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := hbc.cart.w
  let W' : Γ'.G.left.Opens := (F ⁻¹ᵁ U) ⊓ U'
  have hgW' : g' ∈ W' := ⟨hgU, hgU'⟩
  let i₁ : W' ⟶ F ⁻¹ᵁ U := homOfLE inf_le_left
  let i₂ : W' ⟶ U' := homOfLE inf_le_right
  have key : (Γ'.G.left.presheaf.map i₁.op).hom ((F.app U).hom s) =
      constSec Γ'.G.hom W' (algebraMap R R' d) * (Γ'.G.left.presheaf.map i₂.op).hom s' := by
    refine sub_eq_zero.mp (PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' W' _ fun t h => ?_)
    have h₁ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ (F ⁻¹ᵁ U) := fun x hx => (h hx).1
    have h₂ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U' := fun x hx => (h hx).2
    have hpt := _root_.GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hbc κ hκ t
    have h₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := by
      rw [← hpt]; exact h₁
    have h₄ : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_spec_comp κ _ U h₃
    have hw' : (Γ'.pt t).left ≫ Γ'.G.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) := Over.w (Γ'.pt t)
    rw [valAt_sub, valAt_mul, valAt_res _ i₁ h h₁, valAt_res _ i₂ h h₂, hs' t h₂,
      valAt_const _ _ (algebraMap R' (FractionRing R')) hw', ← valAt_comp _ F U h₁,
      valAt_congr hpt U h₁ h₃, valAt_spec κ _ U h₄ h₃, hs t h₄, map_mul]
    have : κ (algebraMap R _ d) = algebraMap R' _ (algebraMap R R' d) := congrArg (fun ψ => ψ d) hκ
    rw [this, sub_self]
  have hdvd : Γ.G.left.presheaf.germ U (F g') hgU (constSec Γ.G.hom U d) ∣
      Γ.G.left.presheaf.germ U (F g') hgU s := by
    apply dvd_of_stalkMap_dvd F g'
    refine ⟨Γ'.G.left.presheaf.germ W' g' hgW' ((Γ'.G.left.presheaf.map i₂.op).hom s'), ?_⟩
    have e₁ := Scheme.Hom.germ_stalkMap_apply F U g' hgU s
    have e₂ := Scheme.Hom.germ_stalkMap_apply F U g' hgU (constSec Γ.G.hom U d)
    rw [app_constSec _ _ F _ hsq] at e₂
    have e₃ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' ((F.app U).hom s)
    have e₄ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' (constSec Γ'.G.hom (F ⁻¹ᵁ U) (algebraMap R R' d))
    rw [constSec_res] at e₄
    rw [key, map_mul] at e₃
    exact e₁.trans (e₃.symm.trans (by rw [e₄, ← e₂]))
  obtain ⟨x, hx⟩ := hdvd
  obtain ⟨W, hgW, s₀, rfl⟩ := Γ.G.left.presheaf.exists_germ_eq x
  let P : Γ.G.left.Opens := U ⊓ W
  have hgP : F g' ∈ P := ⟨hgU, hgW⟩
  let j₁ : P ⟶ U := homOfLE inf_le_left
  let j₂ : P ⟶ W := homOfLE inf_le_right
  have hP : Γ.G.left.presheaf.germ U (F g') hgU s = Γ.G.left.presheaf.germ P (F g') hgP
      (constSec Γ.G.hom P d * (Γ.G.left.presheaf.map j₂.op).hom s₀) := by
    rw [hx, map_mul, TopCat.Presheaf.germ_res_apply, ← constSec_res _ j₁, TopCat.Presheaf.germ_res_apply]
  obtain ⟨V, hV, iU, iP, hres⟩ := TopCat.Presheaf.germ_eq _ _ hgU hgP _ _ hP
  refine ⟨V, hV, (Γ.G.left.presheaf.map (iP ≫ j₂).op).hom s₀, fun t h => ?_⟩
  have hU : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun x hx => iU.le (h hx)
  have hPt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ P := fun x hx => iP.le (h hx)
  have hWt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ W := fun x hx => (iP ≫ j₂).le (h hx)
  have hw : (Γ.pt t).left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := Over.w (Γ.pt t)
  have hK : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa using hd0
  refine mul_left_cancel₀ hK ?_
  have e₁ := congrArg (valAt (Γ.pt t).left V h) hres
  rw [valAt_res _ iU h hU, hs t hU, valAt_res _ iP h hPt, valAt_mul, valAt_const _ _ _ hw,
    valAt_res _ j₂ hPt hWt] at e₁
  rw [valAt_res _ (iP ≫ j₂) h hWt]
  exact e₁.symm

end PositivityTheory.HtPt.Htat.StalkDivisibility

theorem PositivityTheory.HtPt.Htat.bt_reg_descent : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') :=
  @PositivityTheory.HtPt.Htat.StalkDivisibility.regularAt_of_baseChange
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.IsFractionRingOfIntegers
section
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped nonZeroDivisors

theorem isFractionRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsFractionRing O C := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 hv.hom_inj
  refine IsFractionRing.of_field O C fun z => ?_
  obtain ⟨a, h | h⟩ := hv.eq_algebraMap_or_inv_eq_algebraMap z
  · exact ⟨a, 1, by simp [h]⟩
  · exact ⟨1, a, by simp [← h]⟩

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (M : Submodule A Ω) (hM : M.IsFullLattice K) : finrank A M = finrank K Ω := by
  haveI : IsLocalizedModule A⁰ M.subtype :=
    { map_units := fun s => by
        rw [← (Algebra.lsmul A (A := K) A Ω).commutes]
        exact (IsLocalization.map_units K s).map _
      surj := fun y => by
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span A⁰ K (M : Set Ω) y
          (by rw [hM.span_eq_top]; trivial)
        rw [Submodule.span_eq] at ht
        exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.val_injective h]⟩ }
  rw [← IsLocalizedModule.finrank_eq A⁰ M.subtype le_rfl]
  exact (IsLocalization.finrank_eq K A⁰ le_rfl).symm

theorem rankAtStalk_eq_finrank {A : Type} [CommRing A] [IsDomain A] (M : Type) [AddCommGroup M]
    [Module A M] (p : PrimeSpectrum A) : rankAtStalk M p = finrank A M := by
  have hp : p.asIdeal.primeCompl ≤ A⁰ := p.asIdeal.primeCompl_le_nonZeroDivisors
  rw [rankAtStalk, IsLocalization.finrank_eq _ p.asIdeal.primeCompl hp,
    IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hp]

theorem finrank_baseChange_flat {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    [Algebra A O] (M : Type) [AddCommGroup M] [Module A M] [Module.Flat A M] [Module.Finite A M] :
    finrank O (O ⊗[A] M) = finrank A M := by
  rw [← rankAtStalk_eq_finrank (O ⊗[A] M) (⊥ : PrimeSpectrum O), rankAtStalk_baseChange,
    rankAtStalk_eq_finrank]

theorem exists_lift {A O : Type} [CommRing A] [CommRing O] [Algebra A O] {M : Type} [AddCommGroup M]
    [Module A M] {Ω' : Type} [AddCommGroup Ω'] [Module O Ω'] (ι : M →ₛₗ[algebraMap A O] Ω') :
    ∃ j : O ⊗[A] M →ₗ[O] Ω', (∀ x, j (1 ⊗ₜ x) = ι x) ∧
      LinearMap.range j = Submodule.span O (Set.range ι) := by
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι, map_smul' := fun a x => ι.map_smulₛₗ a x }
  refine ⟨f.liftBaseChange O, fun x => by simp [f], ?_⟩
  rw [LinearMap.range_liftBaseChange]
  rfl

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsFullLattice K → Module.Projective A M → L.IsFullLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hP hL hspan hrk
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := isFractionRing_of_integers hv
  haveI : Module.Finite A M := Module.Finite.iff_fg.2 hM.fg
  obtain ⟨j, hj, hr⟩ := exists_lift ι
  rw [hspan] at hr
  refine ⟨j, ?_, hr, hj⟩
  have h1 : finrank O (O ⊗[A] M) = finrank O (LinearMap.range j) := by
    rw [finrank_baseChange_flat, finrank_lattice M hM, hr, finrank_lattice L hL, hrk]
  have h2 := j.rank_range_add_rank_ker
  haveI : Module.Finite O (LinearMap.range j) := inferInstance
  rw [← finrank_eq_rank O (O ⊗[A] M), ← finrank_eq_rank O (LinearMap.range j), h1] at h2
  have h3 : Module.rank O (LinearMap.ker j) = 0 := by
    rw [add_comm] at h2
    exact (Cardinal.add_nat_inj _).1 (h2.trans (zero_add _).symm)
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.rank_eq_zero).1 h3

end PositivityTheory.HtPt.Gb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.LiftComul
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (spMap_comp spMap_id)

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

omit [GrpObj G] in
theorem spc {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap (ψ.comp φ) ≫ y = spMap ψ ≫ spMap φ ≫ y := by
  rw [← Category.assoc, spMap_comp]

omit [GrpObj G] in
theorem spc' {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap ψ ≫ spMap φ ≫ y = spMap (ψ.comp φ) ≫ y := (spc ψ φ y).symm

theorem tors_pow (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] (φ : T.A →ₐ[R] S) :
    (spMap φ ≫ T.y) ^ p = 1 := by
  rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]

theorem tors_ext (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] {φ φ' : T.A →ₐ[R] S}
    (h : spMap φ ≫ T.y = spMap φ' ≫ T.y) : φ = φ' := by
  exact (T.univ S _ (tors_pow T φ)).unique rfl h.symm

theorem lift_comul (T : TorsRep G p) (Δ : T.A →ₐ[R] TensorProduct R T.A T.A)
    (hΔ : spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y))
    {S : Type} [CommRing S] [Algebra R S] (F : TensorProduct R T.A T.A →ₐ[R] S) :
    spMap (F.comp Δ) ≫ T.y = (spMap (F.comp Algebra.TensorProduct.includeLeft) ≫ T.y) *
      (spMap (F.comp Algebra.TensorProduct.includeRight) ≫ T.y) := by
  rw [spc, hΔ, MonObj.comp_mul, spc', spc']

end

theorem tors_alg : ∀ (R : Type) [CommRing R] (p : ℕ), ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ T : TorsRep G p, ∃ (Δ : T.A →ₐ[R] TensorProduct R T.A T.A) (ε : T.A →ₐ[R] R) (s : T.A →ₐ[R] T.A), spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) ∧ spMap ε ≫ T.y = 1 ∧ (spMap s ≫ T.y) * T.y = 1 ∧ (Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp ((Algebra.TensorProduct.map Δ (AlgHom.id R T.A)).comp Δ) = (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp Δ ∧ (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp Δ = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp Δ = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp Δ = (Algebra.ofId R T.A).comp ε ∧ (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp Δ = Δ := by
  intro R _ p G _ _ T
  set iL : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeLeft with hiL
  set iR : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeRight with hiR
  have hz : ((spMap iL ≫ T.y) * (spMap iR ≫ T.y)) ^ p = 1 := by
    rw [mul_pow, tors_pow, tors_pow, _root_.one_mul]
  obtain ⟨Δ, hΔ, -⟩ := T.univ _ _ hz
  obtain ⟨ε, hε, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  have hz' : (T.y⁻¹) ^ p = 1 := by rw [inv_pow, T.y_p, inv_one]
  obtain ⟨s, hs, -⟩ := T.univ T.A _ hz'
  refine ⟨Δ, ε, s, hΔ, hε, by rw [hs, _root_.inv_mul_cancel], ?_, ?_, ?_, ?_, ?_⟩
  · apply tors_ext T
    rw [← AlgHom.comp_assoc, lift_comul T Δ hΔ, lift_comul T Δ hΔ]
    have e1 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iL = ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp Δ := by
      ext x; simp [hiL]
    have e2 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iR := by
      ext x; simp [hiR, Algebra.TensorProduct.one_def]
    have e3 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL]
    have e4 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp Δ := by
      ext x; simp [hiR]
    have e5 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL, Algebra.TensorProduct.one_def]
    have e6 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iL := by
      ext x; simp [hiL, hiR, Algebra.TensorProduct.one_def]
    rw [e1, e2, lift_comul T Δ hΔ, e5, e6, e3, e4, lift_comul T Δ hΔ, _root_.mul_assoc]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iL = (Algebra.TensorProduct.includeLeft : R →ₐ[R] TensorProduct R R T.A).comp ε := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iR = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.one_mul]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iL = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iR = (Algebra.TensorProduct.includeRight : R →ₐ[R] TensorProduct R T.A R).comp ε := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.mul_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iL = s := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iR = AlgHom.id R T.A := by
      ext x; simp [hiR]
    rw [e1, e2, spMap_id, Category.id_comp, hs, _root_.inv_mul_cancel, spc, hε, MonObj.comp_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ, hΔ]
    have e1 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iL = iR := by
      ext x; simp [hiL, hiR]
    have e2 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iR = iL := by
      ext x; simp [hiL, hiR]
    rw [e1, e2, _root_.mul_comm]

end PositivityTheory.HtPt.Rf
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LCentre.Centre

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have hab : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hab
    refine ⟨h0, a.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hab]
    exact b.2
  · rintro ⟨h0, -, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨(a : Ω)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem exists_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' hp'
  obtain ⟨c, hc, hreg⟩ := hp'
  haveI : IsLocalRing (regAt ξ' p') := (PositivityTheory.HtPt.Ma.reg_local X' Ω' ξ').1 p'
  let φ : chRing o x c →+* regAt ξ' p' :=
    (i.comp (chRing o x c).val.toRingHom).codRestrict (regAt ξ' p') (fun a => hreg a a.2)
  let P : Ideal (chRing o x c) := (IsLocalRing.maximalIdeal (regAt ξ' p')).comap φ
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p₀, ⟨hin, hP⟩, -⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω κ x M c hc P hPp
  have key : ∀ u : chRing o x c, unitAt M.ξ p₀ (u : Ω) ↔ unitAt ξ' p' (i u) := by
    intro u
    have h := hP u
    have h2 : u ∈ P ↔ ¬ unitAt ξ' p' (i u) := by
      change φ u ∈ IsLocalRing.maximalIdeal (regAt ξ' p') ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
      rfl
    tauto
  have hloc := fun (c₁ : κ) (p : Cpt M.ξ) (h : InChart M.ξ x c₁ p) =>
    PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ p h
  have hch : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := (hloc c p₀ hin).1
  have hdom : ∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have h1 := (key ⟨v, hv⟩).1 hvu
    rw [map_div₀, div_eq_mul_inv]
    exact mul_mem (hreg u hu) h1.2.2
  have hlift : ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a := by
    intro a ha hu'
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have hiu : unitAt ξ' p' (i u) := by
      have h1 : i u = i (u / v) * i v := by rw [← map_mul, div_mul_cancel₀ _ hvu.1]
      rw [h1]
      exact Flat.ZUnit.mul hu' ((key ⟨v, hv⟩).1 hvu)
    have hu0 : unitAt M.ξ p₀ u := (key ⟨u, hu⟩).2 hiu
    rw [div_eq_mul_inv]
    exact Flat.ZUnit.mul hu0 (Flat.ZUnit.inv hvu)
  have hchart : ∀ c₁, x c₁ ≠ 0 → (∀ j, i (x j / x c₁) ∈ regAt ξ' p') → InChart M.ξ x c₁ p₀ := by
    intro c₁ h1 hj
    have hmem : x c₁ / x c ∈ regAt M.ξ p₀ := hch _ (Algebra.subset_adjoin ⟨c₁, rfl⟩)
    have hunit : unitAt ξ' p' (i (x c₁ / x c)) := by
      refine ⟨(map_ne_zero i).2 (div_ne_zero h1 hc), hdom _ hmem, ?_⟩
      rw [← map_inv₀, inv_div]
      exact hj c
    have hu := hlift _ hmem hunit
    refine ⟨h1, fun j => ?_⟩
    have h2 : x j / x c₁ = x j / x c * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [h2]
    exact mul_mem (hch _ (Algebra.subset_adjoin ⟨j, rfl⟩)) hu.2.2
  refine ⟨p₀, ⟨hdom, hlift⟩, ?_, hchart⟩
  intro p hp
  rw [← PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p p₀]
  obtain ⟨c₁, hc₁⟩ := M.tie.cover p
  have hin₁ := hchart c₁ hc₁.1 (fun j => hp _ (hc₁.2 j))
  intro a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c₁ p hc₁).2 a).1 ha
  have hch₁ := (hloc c₁ p₀ hin₁).1
  have hv' : unitAt M.ξ p₀ v := hlift v (hch₁ v hv)
    ⟨(map_ne_zero i).2 hvu.1, hp v hvu.2.1, by rw [← map_inv₀]; exact hp _ hvu.2.2⟩
  rw [div_eq_mul_inv]
  exact mul_mem (hch₁ u hu) hv'.2.2

end PositivityTheory.HtPt.Mb.LCentre.Centre


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ :=
  @PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre
end

