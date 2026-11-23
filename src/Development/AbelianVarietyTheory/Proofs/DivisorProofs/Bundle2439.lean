module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPoint
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.PushSec

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

theorem injective_of_ff {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (h : (ψ : D →+* D').FaithfullyFlat) : Function.Injective ψ := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := h
  exact FaithfulSMul.algebraMap_injective D D'

theorem root_map {n : ℕ} {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E]
    [Algebra R E] (φ : D →ₐ[R] D') (ρ : D' →ₐ[R] E) (x : Pt A D) (z : Pt A D')
    (hz : (z ^ n : Pt A D') = spOver φ ≫ x) :
    ((spOver ρ ≫ z) ^ n : Pt A E) = spOver (ρ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow z n (spOver ρ), hz, ← Category.assoc, spOver_comp]

theorem pow_mul_inv_eq_one {n : ℕ} {E : Type} [CommRing E] [Algebra R E] {y w u : Pt A E} (hy : y ^ n = u)
    (hw : w ^ n = u) : (y * w⁻¹) ^ n = 1 := by
  rw [mul_pow, inv_pow, hy, hw, mul_inv_cancel]

section Fixed

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]

def val (b : Fn0 A) (z₀ : Pt A D₁) (a : D₁) {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F]
    (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F) (z : Pt A D') : F :=
  φ' a + b F ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹)

variable (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁)
  (hz₀ : (z₀ ^ n : Pt A D₁) = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)


include hz₀ in
theorem val_tors {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F)
    (h : ρ.comp φ = φ'.comp ψ) :
    ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹) ^ n = 1 :=
  pow_mul_inv_eq_one (root_map φ ρ x z hz) (by rw [root_map ψ φ' x z₀ hz₀, h])


include hb hz₀ in
theorem map_val {D' F G : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] [CommRing G] [Algebra R G]
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F)
    (h : ρ.comp φ = φ'.comp ψ) (g₁ : F →ₐ[R] G) :
    g₁ (val b z₀ a ρ φ' z) = val b z₀ a (g₁.comp ρ) (g₁.comp φ') z := by
  unfold val
  rw [map_add (f := _), ← hb.1 F G g₁ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h), MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
  rfl


include hb hz₀ ha in
theorem val_indep {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (α β : D₁ →ₐ[R] F)
    (hα : ρ.comp φ = α.comp ψ)
    (hβ : ρ.comp φ = β.comp ψ) : val b z₀ a ρ α z = val b z₀ a ρ β z := by
  unfold val
  have t1 := val_tors ψ x z₀ hz₀ φ z hz ρ β hβ
  have t2 : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
    pow_mul_inv_eq_one (by rw [root_map ψ β x z₀ hz₀, ← hβ]) (by rw [root_map ψ α x z₀ hz₀, ← hα])
  have e : (spOver ρ ≫ z) * (spOver α ≫ z₀)⁻¹ =
      ((spOver ρ ≫ z) * (spOver β ≫ z₀)⁻¹) * ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) := by
    rw [_root_.mul_assoc, _root_.inv_mul_cancel_left]
  rw [e, hb.2 F _ _ t1 t2, ha F α β (hα.symm.trans hβ)]
  abel

def IsVal {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D') (e : D') : Prop :=
  ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F), ρ.comp φ = φ'.comp ψ →
    ρ e = val b z₀ a ρ φ' z


include hb hz₀ ha in
theorem exists_isVal (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) :
    ∃ e : D', IsVal (b := b) ψ z₀ a φ z e := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  obtain ⟨e, he, -⟩ := GlobalTheory.ff_descent_pairs R D' E' ρ₀ hff (val b z₀ a ρ₀ φ₀ z) (by
    intro G _ _ g₁ g₂ hg₁g₂
    rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₁, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₂, ← hg₁g₂]
    refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
    · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
    · rw [hg₁g₂, AlgHom.comp_assoc, hsq, AlgHom.comp_assoc])
  refine ⟨e, fun F _ _ ρ φ' h ↦ ?_⟩
  obtain ⟨G, _, _, ρ₀', ρ', hff', hsq'⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D' E' F ρ₀ ρ hff
  apply injective_of_ff ρ₀' hff'
  rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ φ' h ρ₀']
  change (ρ₀'.comp ρ) e = _
  rw [hsq', AlgHom.comp_apply, he, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq ρ']
  refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
  · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
  · rw [← hsq', AlgHom.comp_assoc, h, AlgHom.comp_assoc]

theorem isVal_unique (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') {e e' : D'} (he : IsVal (b := b) ψ z₀ a φ z e) (he' : IsVal (b := b) ψ z₀ a φ z e') : e = e' := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  exact injective_of_ff ρ₀ hff ((he E' ρ₀ φ₀ hsq).trans (he' E' ρ₀ φ₀ hsq).symm)

end Fixed

section Sec

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]
  (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁)
  (hz₀ : (z₀ ^ n : Pt A D₁) = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)
  (hψ : (ψ : D →+* D₁).FaithfullyFlat)


open Classical in
def sec : RootFn A D := fun D' _ _ φ z ↦
  if h : (z ^ n : Pt A D') = spOver φ ≫ x then Classical.choose (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z h) else 0

theorem sec_spec {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D')
    (hz : (z ^ n : Pt A D') = spOver φ ≫ x) : IsVal (b := b) ψ z₀ a φ z (sec hb ψ x z₀ hz₀ a ha hψ D' φ z) := by
  unfold sec
  rw [dite_eq_left hz]
  exact Classical.choose_spec (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z hz)

theorem isSec_sec : IsSec n b x (sec hb ψ x z₀ hz₀ a ha hψ) := by
  refine ⟨fun D' _ _ D'' _ _ φ ψ₂ z hz ↦ ?_, fun D' _ _ φ z w hz hw ↦ ?_⟩
  · have hz' := root_map φ ψ₂ x z hz
    refine isVal_unique ψ z₀ a hψ (ψ₂.comp φ) _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hz') ?_
    intro F _ _ ρ φ' h
    change (ρ.comp ψ₂) _ = _
    rw [sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F (ρ.comp ψ₂) φ' (by rw [AlgHom.comp_assoc]; exact h)]
    unfold val
    rw [← Category.assoc, spOver_comp]
  · have hzw : ((z * w) ^ n : Pt A D') = spOver φ ≫ x := by rw [mul_pow, hz, hw, _root_.mul_one]
    refine isVal_unique ψ z₀ a hψ φ _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hzw) ?_
    intro F _ _ ρ φ' h
    have tw : (spOver ρ ≫ w) ^ n = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    rw [map_add (f := _), sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F ρ φ' h, ← hb.1 D' F ρ w hw]
    unfold val
    rw [add_assoc, ← hb.2 F _ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h) tw, MonObj.comp_mul, _root_.mul_right_comm]

end Sec

theorem exists_isSec : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n →
    ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ s : RootFn A D, IsSec n b x s := by
  intro R _ A _ _ n hR b hb D _ _ x
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  obtain ⟨a, ha⟩ := GlobalTheory.FlatDescent.cocycle_descends R D D₁ ψ hψ
    (fun E _ _ α β ↦ b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹)) (by
      intro E _ _ E' _ _ α β g hαβ
      have t : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ β x z₀ hz₀) (by rw [root_map ψ α x z₀ hz₀, hαβ])
      show b E' _ = g (b E _)
      rw [← hb.1 E E' g _ t, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spOver_comp,
        spOver_comp]) (by
      intro E _ _ f₁ f₂ f₃ h12 h23
      have t1 : ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₂ x z₀ hz₀) (by rw [root_map ψ f₁ x z₀ hz₀, h12])
      have t2 : ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₃ x z₀ hz₀) (by rw [root_map ψ f₂ x z₀ hz₀, h23])
      have e : (spOver f₃ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹ =
          ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) * ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) := by
        rw [_root_.mul_comm ((spOver f₂ ≫ z₀) * _), _root_.mul_assoc, _root_.inv_mul_cancel_left]
      show b E _ = b E _ + b E _
      rw [e, hb.2 E _ _ t1 t2])
  exact ⟨_, isSec_sec hb ψ x z₀ hz₀ a (fun E _ _ α β h ↦ ha E α β h) hψ⟩

end GlobalTheory.PtExt.PushSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAf
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.InvForm

namespace GlobalTheory.InvFormRetract

theorem dVal_smul {R B D : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D] (φ : B →ₐ[R] DualNumber D) (b : B) (x : Ω[B⁄R]) : dVal φ (b • x) = redHom φ b * dVal φ x := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.restrictScalars_apply, LinearMap.map_smul]
  rfl

theorem injective_baseChange {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hab : IsAbelianScheme A) (U : AffOp A.left) :
    Function.Injective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  haveI : CompactSpace A.left := ⟨by simpa using QuasiCompact.isCompact_preimage (f := A.hom) Set.univ isOpen_univ isCompact_univ⟩
  haveI : Algebra.Smooth R (Sec A.hom U.unop.1) := smooth_sec_affine A.hom U.unop
  haveI : Module.Flat R (Sec A.hom U.unop.1) := Algebra.Smooth.flat R _
  obtain ⟨n, V, hV⟩ := _root_.GlobalTheory.CoverForms.eq_zero_of_cover R A.left A.hom inferInstance
  let f : ∀ k, InvForm A →ₗ[R] Ω[Sec A.hom (V k).unop.1⁄R] := fun k => evForm A.hom (V k) ∘ₗ (InvForm A).subtype
  let F : InvForm A →ₗ[R] ((k : Fin n) → Ω[Sec A.hom (V k).unop.1⁄R]) := LinearMap.pi f
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hV w.1 fun k => congrFun hw k)
  have hFB : Function.Injective (LinearMap.lTensor (Sec A.hom U.unop.1) F) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hF
  have hk : ∀ (k : Fin n) (z : Sec A.hom U.unop.1 ⊗[R] InvForm A), TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])
      (LinearMap.lTensor (Sec A.hom U.unop.1) F z) k = LinearMap.lTensor (Sec A.hom U.unop.1) (f k) z := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w => simp [F]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply hFB
  rw [map_zero]
  apply (TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])).injective
  rw [map_zero]
  funext k
  rw [hk, Pi.zero_apply]
  haveI : Algebra.Smooth R (Sec A.hom (V k).unop.1) := smooth_sec_affine A.hom (V k).unop
  refine _root_.GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish R (Sec A.hom U.unop.1) _ inferInstance _ (fun θ hθ => ?_)
  obtain ⟨ψ, hfst, hψ⟩ := _root_.GlobalTheory.InvForm.exists_transl_val R A U (V k) θ hθ
  have key : ∀ y, LinearMap.liftBaseChange (Sec A.hom U.unop.1) θ (LinearMap.lTensor (Sec A.hom U.unop.1) (f k) y) =
      dVal ψ (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, dVal_smul]
      have h1 : redHom ψ b = b ⊗ₜ 1 := hfst b
      rw [h1, Algebra.smul_def]
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, hψ]
      rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [key, hz, map_zero]

theorem retract : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  intro R _ A _ g hab hdim U
  have hsurj : Function.Surjective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← _root_.GlobalTheory.InvSpan.span_invForm_eq_top R A g hab hdim U, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp⟩
  let e := LinearEquiv.ofBijective _ ⟨injective_baseChange A hab U, hsurj⟩
  refine ⟨e.symm.toLinearMap, fun w => ?_⟩
  apply e.injective
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change _ = LinearMap.liftBaseChange _ _ (1 ⊗ₜ w)
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end GlobalTheory.InvFormRetract
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem glue_field_points (R : Type) [CommRing R]
    (P : (K : Type) → [Field K] → (R →+* K) → K → Prop)
    (huniq : ∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v)
    (hloc : ∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c)) :
    ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  classical
  have hloc' : ∀ k : {p : Ideal R // p.IsPrime}, ∃ f ∉ k.1, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c) := fun k => hloc k.1 k.2
  choose f hf c hc using hloc'
  have hsurj : ∀ k : {p : Ideal R // p.IsPrime}, ∃ (a : R) (n : ℕ),
      c k * algebraMap R _ (f k ^ n) = algebraMap R _ a := by
    intro k
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (f k) (c k)
    exact ⟨a, n, by rw [map_pow]; exact h⟩
  choose a n ha using hsurj

  have key : ∀ (K : Type) [Field K] (i : R →+* K) (k : {p : Ideal R // p.IsPrime}),
      i (f k) ≠ 0 → ∃ v, P K i v ∧ v * i (f k) ^ n k = i (a k) := by
    intro K _ i k hk
    let j : Localization.Away (f k) →+* K :=
      IsLocalization.Away.lift (f k) (isUnit_iff_ne_zero.mpr hk)
    have hj : j.comp (algebraMap R _) = i := by first | exact IsLocalization.Away.lift_comp _ | exact IsLocalization.lift_comp _
    refine ⟨j (c k), ?_, ?_⟩
    · have := hc k K j
      rwa [hj] at this
    · have h2 := congrArg j (ha k)
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hj, map_pow] at h2
      exact h2

  have hnil : ∀ k l : {p : Ideal R // p.IsPrime},
      IsNilpotent (f k * f l * (a k * f l ^ n l - a l * f k ^ n k)) := by
    intro k l
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro q hq
    haveI : q.IsPrime := hq
    by_cases hk : f k ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_right _ hk)
    by_cases hl : f l ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_left _ hl)
    apply q.mul_mem_left
    have hker : RingHom.ker (algebraMap R q.ResidueField) = q := Ideal.ker_algebraMap_residueField q
    have hik : algebraMap R q.ResidueField (f k) ≠ 0 := fun h => hk (hker ▸ RingHom.mem_ker.mpr h)
    have hil : algebraMap R q.ResidueField (f l) ≠ 0 := fun h => hl (hker ▸ RingHom.mem_ker.mpr h)
    obtain ⟨v, hv, hv'⟩ := key _ (algebraMap R q.ResidueField) k hik
    obtain ⟨w, hw, hw'⟩ := key _ (algebraMap R q.ResidueField) l hil
    have hvw := huniq _ _ v w hv hw
    subst hvw
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, ← hv', ← hw']
    ring

  let g : {p : Ideal R // p.IsPrime} → R := fun k => f k ^ (n k + 1)
  let α : {p : Ideal R // p.IsPrime} → R := fun k => f k * a k
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let k : {p : Ideal R // p.IsPrime} := ⟨m, hm.isPrime⟩
    exact hf k (hm.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨k, rfl⟩)))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range g) := by
    rw [← Ideal.span, hspan]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  let π := Ideal.Quotient.mk (nilradical R)
  have hrel : ∀ k l, π (g l) * π (α k) = π (g k) * π (α l) := by
    intro k l
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, mem_nilradical]
    have e : g l * α k - g k * α l = f k * f l * (a k * f l ^ n l - a l * f k ^ n k) := by
      simp only [g, α]; ring
    rw [e]; exact hnil k l
  obtain ⟨c0, hc0⟩ := Ideal.Quotient.mk_surjective (I := nilradical R)
    (b.sum fun k r => π r * π (α k))
  have hb' : (b.sum fun k r => π r * π (g k)) = 1 := by
    have := congrArg π hb
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Finsupp.sum, map_sum, smul_eq_mul] using this
  have hglue : ∀ l, IsNilpotent (g l * c0 - α l) := by
    intro l
    rw [← mem_nilradical, ← Ideal.Quotient.eq]
    calc π (g l * c0) = b.sum (fun k r => π r * π (g k) * π (α l)) := by
          rw [map_mul]
          change π (g l) * Ideal.Quotient.mk (nilradical R) c0 = _
          rw [hc0, Finsupp.mul_sum]
          refine Finsupp.sum_congr fun k _ => ?_
          linear_combination π (b k) * hrel k l
      _ = π (α l) := by rw [← Finsupp.sum_mul, hb', _root_.one_mul]
  refine ⟨c0, fun K _ i => ?_⟩
  let k : {p : Ideal R // p.IsPrime} := ⟨RingHom.ker i, RingHom.ker_isPrime i⟩
  have hik : i (f k) ≠ 0 := fun h => hf k (RingHom.mem_ker.mpr h)
  obtain ⟨v, hv, hv'⟩ := key K i k hik
  have h0 : i (g k * c0 - α k) = 0 := ((hglue k).map i).eq_zero
  have hcv : i c0 = v := by
    have hp : i (f k) ^ (n k + 1) ≠ 0 := pow_ne_zero _ hik
    apply mul_left_cancel₀ hp
    simp only [g, α, map_sub, map_mul, map_pow, sub_eq_zero] at h0
    rw [h0, ← hv']; ring
  rw [hcv]; exact hv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomMatrixLiftOfOrderActionExponential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpLin

theorem exists_ringHom_matrix_lift : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (O : Type) [Ring O] (act : O → (G ⟶ G)), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ ρ' : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a z, e (ρ' a *ᵥ z) = e z ≫ act a := by
  intro X G _ _ g O _ act hab hsm hhom h1 hmul hadd y e he
  have H := fun a => _root_.GlobalTheory.ExpLin.existsUnique_linear_lift X G g hab hsm y e e (act a) he he (hhom a)
  let M : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => (H a).exists.choose
  have hM : ∀ a z, e (M a z) = e z ≫ act a := fun a => (H a).exists.choose_spec
  have key : ∀ a (N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, e (N z) = e z ≫ act a) → N = M a :=
    fun a N hN => (H a).unique hN (hM a)
  have M1 : M 1 = LinearMap.id := (key 1 LinearMap.id (fun z => by simp [h1])).symm
  have Mmul : ∀ a b, M (a * b) = M a ∘ₗ M b := fun a b =>
    (key (a * b) (M a ∘ₗ M b) (fun z => by
      simp only [LinearMap.comp_apply, hM, hmul, Category.assoc])).symm
  have Madd : ∀ a b, M (a + b) = M a + M b := fun a b =>
    (key (a + b) (M a + M b) (fun z => by
      rw [LinearMap.add_apply, he.1, hM, hM, hadd, MonObj.comp_mul])).symm
  let f : O →* Matrix (Fin g) (Fin g) ℂ :=
    { toFun := fun a => LinearMap.toMatrix' (M a)
      map_one' := by simp only [M1, LinearMap.toMatrix'_id]
      map_mul' := fun a b => by simp only [Mmul, LinearMap.toMatrix'_comp] }
  refine ⟨RingHom.mk' f (fun a b => by simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Madd, map_add (f := _)]), ?_⟩
  intro a z
  show e (LinearMap.toMatrix' (M a) *ᵥ z) = _
  rw [LinearMap.toMatrix'_mulVec, hM]

end GlobalTheory.ExpLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackCommutingEndomorphismGenera
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secK_pullMul_gen : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  intro X Y L hL β g h hc k k' u hu σ
  have hu' := DVR.pullGen_isGen L _ _ u hu β
  have hF : FormEq (Sum.elim (fun i => g ≫ (fun _ : Fin 1 => β) i) (fun i => β ≫ (![𝟙 X, h] : Fin 2 → (X ⟶ X)) i))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![(k' : ℤ), -(k : ℤ)]) (fun _ : Fin 1 => β) (fun _ => (k' : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, hc, zpow_neg]
    rw [mul_comm (f β ^ _)]
    exact mul_inv_cancel_left _ _
  obtain ⟨σ₂, hσ₂⟩ := exists_sec hL hF (pullMulSec σ g (LB.pullGen L _ _ u β) hu')
  refine ⟨σ₂, fun Z r z J hJ => ?_⟩
  rw [hσ₂ Z r z J hJ, sval_pullMulSec σ g _ hu' r z hJ, val_pull hJ u β r, mul_comm]

end GlobalTheory.Mum
end

