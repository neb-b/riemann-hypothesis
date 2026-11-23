module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProdUnifSq

variable {g : ℕ}

def halfL (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.castAdd g k)

def halfR (g : ℕ) : (Fin (g + g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (Fin.natAdd g k)

theorem halfL_apply (v : Fin (g + g) → ℂ) : halfL g v = fun k => v (Fin.castAdd g k) := rfl
theorem halfR_apply (v : Fin (g + g) → ℂ) : halfR g v = fun k => v (Fin.natAdd g k) := rfl

theorem halfL_append (x y : Fin g → ℂ) : halfL g (Fin.append x y) = x := by
  funext k; simp [halfL_apply]
theorem halfR_append (x y : Fin g → ℂ) : halfR g (Fin.append x y) = y := by
  funext k; exact Fin.append_right x y k

theorem append_halves (v : Fin (g + g) → ℂ) : Fin.append (halfL g v) (halfR g v) = v := by
  funext q
  refine Fin.addCases (fun k => ?_) (fun k => ?_) q
  · rw [Fin.append_left, halfL_apply]
  · rw [Fin.append_right, halfR_apply]

def sqLat (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin (g + g) → ℂ) :=
  Λ.comap ((halfL g).toLinearMap.restrictScalars ℤ) ⊓ Λ.comap ((halfR g).toLinearMap.restrictScalars ℤ)

theorem mem_sqLat (Λ : Submodule ℤ (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    v ∈ sqLat Λ ↔ halfL g v ∈ Λ ∧ halfR g v ∈ Λ := Iff.rfl

theorem sqLat_discrete (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] : DiscreteTopology (sqLat Λ) := by
  refine DiscreteTopology.of_continuous_injective (β := Λ × Λ)
    (f := fun z => (⟨halfL g z.1, z.2.1⟩, ⟨halfR g z.1, z.2.2⟩))
    (Continuous.prodMk (((halfL g).continuous.comp continuous_subtype_val).subtype_mk _)
      (((halfR g).continuous.comp continuous_subtype_val).subtype_mk _)) fun z z' h => ?_
  refine Subtype.ext ?_
  rw [← append_halves z.1, ← append_halves z'.1]
  simp only [Prod.mk.injEq] at h
  have h1 : halfL g z.1 = halfL g z'.1 := congrArg Subtype.val h.1
  have h2 : halfR g z.1 = halfR g z'.1 := congrArg Subtype.val h.2
  rw [h1, h2]

def appendL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

def appendR (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin (g + g) → ℂ) where
  toFun y := Fin.append 0 y
  map_add' x y := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]
  map_smul' c x := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, add_zero,
        smul_zero, RingHom.id_apply]

theorem sqLat_full (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) = ⊤ := by
  have hL : Set.range (appendL g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendL g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append x 0) ∈ Λ
        rw [halfL_append]; exact hx
      · change halfR g (Fin.append x 0) ∈ Λ
        rw [halfR_append]; exact Λ.zero_mem
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  have hR : Set.range (appendR g) ⊆ Submodule.span ℝ (sqLat Λ : Set (Fin (g + g) → ℂ)) := by
    have : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map (appendR g) ≤ Submodule.span ℝ (sqLat Λ : Set _) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · change halfL g (Fin.append 0 x) ∈ Λ
        rw [halfL_append]; exact Λ.zero_mem
      · change halfR g (Fin.append 0 x) ∈ Λ
        rw [halfR_append]; exact hx
    rintro _ ⟨x, rfl⟩
    exact this ⟨x, by rw [h]; trivial, rfl⟩
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = appendL g (halfL g v) + appendR g (halfR g v) := by
    conv_lhs => rw [← append_halves v]
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [appendL, appendR, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Fin.append_left, Fin.append_right,
        Pi.zero_apply, add_zero, zero_add]
  rw [hv]
  exact Submodule.add_mem _ (hL ⟨_, rfl⟩) (hR ⟨_, rfl⟩)

variable (A : Over (Sp ℂ)) [GrpObj A]

abbrev trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def sqUnif {L : LB A.left} (u : HolUnif A L g) : HolUnif (A ⊗ A) (trivLB (A ⊗ A).left) (g + g) where
  ex v := lift (u.ex (halfL g v)) (u.ex (halfR g v))
  ex_add z w := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst, map_add (f := _), u.ex_add]
    · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd, map_add (f := _), u.ex_add]
  ex_onto p := by
    obtain ⟨x, hx⟩ := u.ex_onto (p ≫ fst _ _)
    obtain ⟨y, hy⟩ := u.ex_onto (p ≫ snd _ _)
    refine ⟨Fin.append x y, ?_⟩
    show lift (u.ex (halfL g (Fin.append x y))) (u.ex (halfR g (Fin.append x y))) = p
    rw [halfL_append, halfR_append, hx, hy]
    exact (CartesianMonoidalCategory.hom_ext _ _ (lift_fst _ _) (lift_snd _ _))
  Λ := sqLat u.Λ
  ker z := by
    rw [mem_sqLat, ← u.ker, ← u.ker]
    constructor
    · intro h
      constructor
      · have := congrArg (· ≫ fst A A) h
        simpa only [lift_fst, MonObj.one_comp] using this
      · have := congrArg (· ≫ snd A A) h
        simpa only [lift_snd, MonObj.one_comp] using this
    · rintro ⟨h1, h2⟩
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst, MonObj.one_comp, h1]
      · rw [lift_snd, MonObj.one_comp, h2]
  discrete := by
    have := u.discrete
    exact sqLat_discrete u.Λ
  full := sqLat_full u.Λ u.full
  hol := by
    have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
    refine GlobalTheory.PowUnif.isHolFamily_tensor A A _ ?_ ?_
    · simp only [lift_fst]
      exact hd.precomp (halfL g).differentiable
    · simp only [lift_snd]
      exact hd.precomp (halfR g).differentiable
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat i j z h := by
    rw [Units.val_one, valAt'_one _ h, _root_.one_mul]

end GlobalTheory.ProdUnifSq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.BaseInj

theorem fnOf_appLE_top {Y S : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ S) (U : Y.Opens) (e : U ≤ q ⁻¹ᵁ ⊤)
    (h : genericPoint Y ∈ U) (x : Γ(S, ⊤)) :
    fnOf U h ((q.appLE ⊤ U e).hom x) = fnOf ⊤ trivial (q.appTop.hom x) :=
  fnOf_resG (X := Y) (U := ⊤) (V := U) le_top h (q.appTop.hom x)

theorem app_appLE_top {Y Z S : Scheme.{0}} (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens) (x : Γ(S, ⊤)) :
    (f.app U).hom ((s.appLE ⊤ U le_top).hom x) = ((f ≫ s).appLE ⊤ (f ⁻¹ᵁ U) le_top).hom x := by
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun t => t.hom x) (Scheme.Hom.appLE_comp_appLE f s ⊤ U (f ⁻¹ᵁ U) le_top le_rfl)

theorem fnOf_app_appLE_top {Y Z S : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Z) (s : Z ⟶ S) (U : Z.Opens)
    (h : genericPoint Y ∈ f ⁻¹ᵁ U) (x : Γ(S, ⊤)) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom ((s.appLE ⊤ U le_top).hom x)) = fnOf ⊤ trivial ((f ≫ s).appTop.hom x) :=
  (congrArg _ (app_appLE_top f s U x)).trans (fnOf_appLE_top (f ≫ s) (f ⁻¹ᵁ U) le_top h x)

theorem const_agree {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P Z : Scheme.{0}} (p : P ⟶ Sp R)
    (g : Z ⟶ P) (s : Z ⟶ Sp R₁) (w : g ≫ p = s ≫ spMap ρ) (V : P.Opens) (r : R) :
    (g.app V).hom ((p.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (s.appLE ⊤ (g ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (ρ r)) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (ρ r) =
      (spMap ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) :=
    congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  rw [h1, app_appLE_top, w]
  rfl

theorem app_injective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Injective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ _ ρ hρ hc Y _ _ _ q θ D₁ hθ hld _ _ m hff hloc hm k hk b hb
  by_cases hb0 : b = 0
  · have hV : Dp k b = ⊥ :=
      eq_bot_iff.2 fun x hx => ((hM.gen k hk b hb).1 (gen_mem hx) hb0).elim
    rw [hV]
    have : Subsingleton Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ (⊥ : P.Opens)) :=
      inferInstanceAs (Subsingleton Γ(pullback p (spMap ρ), ⊥))
    exact fun _ _ _ => Subsingleton.elim _ _
  have hV : genericPoint P ∈ Dp k b := (hM.gen k hk b hb).2 hb0
  have hY : genericPoint Y ∈ m ⁻¹ᵁ Dp k b :=
    (hloc k hk b hb _).2 (CartierDiv.generatesAt_genericPoint _ ((map_ne_zero θ).2 hb0))
  generalize hf : pullback.lift m q hm = f
  have hf1 : f ≫ pullback.fst p (spMap ρ) = m := by rw [← hf, pullback.lift_fst]
  have hf2 : f ≫ pullback.snd p (spMap ρ) = q := by rw [← hf, pullback.lift_snd]
  clear hf hm hloc
  subst hf1 hf2
  refine (injective_iff_map_eq_zero (f.app _).hom).2 fun x hx => ?_
  obtain ⟨n, a, r, rfl⟩ := _root_.GlobalTheory.BaseChangeSpan.sections_preimage_affine_eq_sum R R₁ ρ P p (Dp k b) (hM.affine k hk b hb) x
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R Γ(P, Dp k b) :=
    ((p.appLE ⊤ (Dp k b) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
  have hsum : ∑ i, θ ((ψ.comp (fnOf (Dp k b) hV)) (a i)) * GlobalTheory.Desc.cst (f ≫ pullback.snd p (spMap ρ)) (r i) = 0 := by
    have := congrArg (fnOf (f ⁻¹ᵁ (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) hY) hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul]
    congr 1
    · exact (_root_.GlobalTheory.Desc.fnOf_app_of_pff P Y _ _ hff (Dp k b) hV hY (a i)).symm
    · exact (fnOf_app_appLE_top f _ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) hY _).symm
  have hz := _root_.GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj R R₁ Γ(P, Dp k b) F Y.functionField hρ c₀ (ψ.comp (fnOf (Dp k b) hV)) _ θ hc
    (ψ.injective.comp (fnOf_injective _ hV))
    (by
      rw [← hM.const]
      ext t
      exact congrArg ψ (fnOf_appLE_top p _ le_top hV _)) hθ hld n a r hsum
  let g := (pullback.fst p (spMap ρ)).app (Dp k b)
  let s : R₁ →+* Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) :=
    ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  letI : Algebra R Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (s.comp ρ).toAlgebra
  let gA : Γ(P, Dp k b) →ₐ[R] Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) :=
    ⟨g.hom, fun t => const_agree ρ p _ _ pullback.condition _ t⟩
  let sA : R₁ →ₐ[R] Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := ⟨s, fun _ => rfl⟩
  have := congrArg (Algebra.TensorProduct.lift gA sA fun _ _ => Commute.all _ _) hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at this
  simp only [Algebra.TensorProduct.lift_tmul] at this
  exact this

end GlobalTheory.Desc.BaseInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalarNsmulEqUnitMulPowSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem evenCube_nsmul_pow {X U : Type*} [AddCommGroup X] [CommGroup U] (κ : X → U)
    (hneg : ∀ x, κ (-x) = κ x)
    (hcube : ∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z))
    (x : X) (n : ℕ) : κ (n • x) = κ x ^ (n ^ 2) := by
  have h0 : κ 0 = 1 := by
    have h := hcube 0 0 0
    simp only [add_zero] at h
    exact mul_eq_left.1 h
  have hpow : ∀ n : ℕ, κ (n • x) = κ x ^ (n ^ 2) ∧ κ ((n + 1) • x) = κ x ^ ((n + 1) ^ 2) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := hcube ((n + 1) • x) x (-x)
      have e1 : (n + 1) • x + x + -x = (n + 1) • x := by abel
      have e2 : (n + 1) • x + x = (n + 1 + 1) • x := by rw [succ_nsmul _ (n + 1)]
      have e3 : (n + 1) • x + -x = n • x := by rw [succ_nsmul]; abel
      have e4 : x + -x = 0 := by abel
      rw [e1, e2, e3, e4, hneg, h0, ih.1, ih.2, _root_.mul_one] at h
      have hx : κ x ^ ((n + 1) ^ 2) * κ x ^ ((n + 1) ^ 2) * κ x * κ x
          = κ x ^ ((n + 1 + 1) ^ 2) * κ x ^ (n ^ 2) := by
        rw [← pow_add, ← pow_succ, ← pow_succ, ← pow_add]; congr 1; ring
      exact mul_right_cancel (h.symm.trans hx)
  exact (hpow n).1

theorem unitsQuot_eq_iff {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (p q : Kˣ) :
    QuotientGroup.mk' (Units.map (algebraMap R K).toMonoidHom).range p =
      QuotientGroup.mk' (Units.map (algebraMap R K).toMonoidHom).range q ↔
    ∃ u : Rˣ, (p : K) = algebraMap R K (u : R) * (q : K) := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, h⟩
    exact ⟨u, by rw [← h, mul_comm q]; rfl⟩
  · rintro ⟨u, h⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [h, mul_comm q]; rfl)⟩

theorem psiScal_nsmul_eq_unit_mul_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → D.PsiEven → D.TauBimult → ∀ (χ : D.X) (n : ℕ), ∃ u : Rˣ, ((a (n • χ) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) (u : R) * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2) := by
  intro R _ _ _ D ga a h hE hB χ n
  obtain ⟨hc, he⟩ := GlobalTheory.PsiScalUnit.main R D ga a h
  have key := evenCube_nsmul_pow
    (fun x => QuotientGroup.mk' (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range (a x))
    (fun x => (unitsQuot_eq_iff _ _).2 (he hE x))
    (fun x y z => by
      have := (unitsQuot_eq_iff _ _).2 (hc hB x y z)
      simpa only [map_mul] using this) χ n
  obtain ⟨u, hu⟩ := (unitsQuot_eq_iff (R := R) _ _).1 (key.trans (map_pow _ _ _).symm)
  exact ⟨u, hu.trans (by rw [Units.val_pow_eq_pow_val])⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem valF_psi_of_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (r : R), Formalism.L2.Pj.PsiCoord D χ r → ∃ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧ valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  intro R _ _ D χ r h
  obtain ⟨j, hj, h, e⟩ := h
  refine ⟨j, hj, ?_⟩
  unfold valF
  rw [dite_eq_left (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiValUnit
open GlobalTheory.BXOf

theorem psi_val_unit_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  intro R _ _ D W χ hW F _ _ T _ φ₁ hφ hP J₀ h₀ J hJ
  have hmem : spMap φ₁ (closedPoint T) ∈ W ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U (J₀ ((D.c χ).left (spMap φ₁ (closedPoint T)))) :=
    ⟨hP, h₀ _⟩
  obtain ⟨V, hVa, hPV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R).isBasis_affineOpens) hmem
  set j₀ := J₀ ((D.c χ).left (spMap φ₁ (closedPoint T))) with hj₀
  have hxK : D.xK χ = jK R ≫ (D.c χ).left := by
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1
  have hwch : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => j₀) :=
    fun x hx => Set.mem_iInter.2 fun _ => by
      show D.xK χ x ∈ D.P.L.U j₀
      rw [hxK]
      exact (hVle hx).2
  obtain ⟨r, hr, hre⟩ := hW (fun _ => j₀) V hVa (fun x hx => (hVle hx).1) (fun x hx => (hVle hx).2) hwch
  have hcomp : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R = spMap T.subtype ≫ spMap φ₁ := by
    rw [Over.id_left, Category.id_comp]
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  have hch : J (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ) = j₀ := by
    have e : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = spMap T.subtype ≫ (spMap φ₁ ≫ (D.c χ).left) := by
      rw [hxK, ← Category.assoc, hcomp, Category.assoc]
    rw [e, hJ]
    rfl
  have e1 := val_of (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J (fun _ => j₀) (fun _ => hch)
  have hin : jK R (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F)) ∈ V := by
    show (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R) (closedPoint F) ∈ V
    rw [hcomp]
    exact top_le_of_mem (spMap φ₁) hPV trivial
  have e2 : res hwch ((D.psi χ).s fun _ => j₀) = pullU (jK R) V hr.unit := Units.ext hre.symm
  have e3 := gm_res ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) hwch hin ((D.psi χ).s fun _ => j₀)
  rw [e2, gm_pull ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (jK R) (closedPoint F) V hin hr.unit, hcomp] at e3
  have e4 := sig_nat T.subtype (spMap φ₁) hPV hr.unit
  refine ⟨sig T (gm (spMap φ₁) (closedPoint T) V hr.unit), ?_⟩
  exact (congrArg (fun u => (sig F u : F)) (e1.trans e3.symm)).trans (congrArg Units.val e4).symm

end GlobalTheory.PsiValUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullMulAddPullMulInv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSemiOpen

theorem isAb_pullback_open {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsSemiAbelian A) (U : S.Opens)
    (hU : IsProper (A.hom ∣_ U)) : IsAbelianScheme ((Over.pullback U.ι).obj A) := by
  have hB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback U.ι A hA
  refine ⟨hB.comm, hB.smooth, ?_, hB.geomConnected⟩
  change IsProper (pullback.snd A.hom U.ι)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

end GlobalTheory.SquareSemiOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointCompStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField), PFF (𝟙 _) π θ → ∀ (y : Y) (u : X.functionField), GlobalTheory.Cartier.RegAt (π y) u → GlobalTheory.Cartier.RegAt y (θ u) := by
  first | exact @GlobalTheory.Desc.RegPull.regAt_map | exact GlobalTheory.Desc.RegPull.regAt_map | (intros; apply GlobalTheory.Desc.RegPull.regAt_map <;> assumption)
end

