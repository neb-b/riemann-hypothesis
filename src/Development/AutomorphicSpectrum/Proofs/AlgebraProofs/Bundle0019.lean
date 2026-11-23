module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharacterDataBaseChange
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FirstLatticeBaseChange
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLattice
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem afQuot_equiv_coords : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) :=
  PositivityTheory.HtPt.Rh.afquot

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_ideal_principal_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ AA _ χ
  obtain ⟨B, hB, hM⟩ := AA.lat
  have key : ∀ d : R, d ∈ xIdeal AA.carrier χ ↔
      (d • fun a => algebraMap R C (χ a)) ∈ AA.carrier := fun d => by
    simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have smul_char (c : R) :
      (c • fun a => algebraMap R C (χ a)) = fun a => algebraMap R C (c * χ a) := by
    funext a
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_denominator v hv (B⁻¹ *ᵥ fun a => algebraMap R C (χ a))
    refine ⟨c, hc0, ?_⟩
    ext d
    rw [key, hM, mem_span_cols_iff B hB, ← hc d]
    refine forall_congr' fun j => exists_congr fun r => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  · intro g
    constructor
    · rintro ⟨hgM, hg⟩
      have hint : ∀ x, ∃ r : R, algebraMap R C r = g x := AA.le_int hgM
      obtain ⟨r, hr⟩ := hint 1
      have hgf : g = fun a => algebraMap R C (r * χ a) := by
        funext a
        have h := hg a 1
        rw [smul_eq_mul, mul_one] at h
        rw [h, ← hr, map_mul]
        exact mul_comm _ _
      refine ⟨r, ?_, hgf⟩
      rw [key, smul_char, ← hgf]
      exact hgM
    · rintro ⟨c, hc, rfl⟩
      rw [key, smul_char] at hc
      refine ⟨hc, fun a x => ?_⟩
      simp only [smul_eq_mul, map_mul]
      ring
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualEigenSubDegreeTranspose
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.EigDual

theorem eig_dual_deg : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) :=
  PositivityTheory.HtPt.Ci.eig_dual

end GlobalTheory.CompanionTheory.Ar.Crv.EigDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenspaceFrobeniusTwist
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eig_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) :=
  PositivityTheory.HtPt.Ci.eig_frob

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsIntegralPosDefPerturbation
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem frame_congr_posDef_on_places : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef :=
  @PositivityTheory.Xgf.exists_integral_posDef_perturbation

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupScheme
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

section Abstract

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def ptSub {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1)
    (T : C) : Subgroup (T ⟶ A) where
  carrier := {f | ∃ a : T ⟶ X, a ≫ h = f}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨lift a b ≫ m, ?_⟩
    rw [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  one_mem' := ⟨toUnit T ≫ e, by rw [Category.assoc, he, MonObj.comp_one]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a ≫ i, ?_⟩
    rw [eq_inv_iff_mul_eq_one, Category.assoc, ← MonObj.comp_mul, hi, MonObj.comp_one]

def ptFunctor {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (ptSub h m e i hm he hi (unop T))
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨f.unop ≫ a, by rw [Category.assoc, ha]⟩⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.id_comp x.1))
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.assoc _ _ x.1))

def ptRep {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    (ptFunctor h m e i hm he hi ⋙ forget _).RepresentableBy X where
  homEquiv {T} := Equiv.ofBijective
    (fun a => (⟨a ≫ h, a, rfl⟩ : ptSub h m e i hm he hi T))
    ⟨fun a b hab => (cancel_mono h).1 (congrArg Subtype.val hab),
      fun x => by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨a, Subtype.ext ha⟩⟩
  homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _)

theorem exists_grpObj_of_mono {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by
  let α := ptRep h m e i hm he hi
  letI G : GrpObj X := GrpObj.ofRepresentableBy X _ α
  have key : ∀ {T : C} (a b : T ⟶ X), (a * b) ≫ h = (a ≫ h) * (b ≫ h) := fun {T} a b =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_mul a b)
  have key1 : ∀ {T : C}, (1 : T ⟶ X) ≫ h = 1 := fun {T} =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_one)
  refine ⟨G, ⟨?_, ?_⟩⟩
  · have := key1 (T := 𝟙_ C)
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using this
  · have := key (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this, Hom.mul_def]
    congr 1
    ext <;> simp

end Abstract

section Scheme

variable {R : Type} [CommRing R]

theorem exists_eq_spMap {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩

theorem exists_sp_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by
  have hU := isAffineOpen_top T.left
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, ⊤) := ρ.hom.toAlgebra
  let j : sp (R₀ := R) Γ(T.left, ⊤) ⟶ T := Over.homMk hU.fromSpec hρ.symm
  have : IsIso j.left := by
    change IsIso hU.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hj : IsIso ((Over.forget _).map j) := ‹IsIso j.left›
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, j, isIso_of_reflects_iso j (Over.forget _)⟩

variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}

theorem affine_mono (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) (hab : a ≫ h = b ≫ h) : a = b := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  have := H.mono S φ φ' (by rw [← hφ, ← hφ', Category.assoc, Category.assoc, hab])
  rw [← cancel_epi j, hφ, hφ', this]

theorem affine_mul (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = (a ≫ h) * (b ≫ h) := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  obtain ⟨χ, hχ⟩ := H.mul S φ φ'
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [Category.assoc, hχ, ← hφ, ← hφ', MonObj.comp_mul, Category.assoc, Category.assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]

theorem affine_one (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] :
    ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨χ, hχ⟩ := H.one S
  exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩

theorem affine_inv (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, (c ≫ h) * (a ≫ h) = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨χ, hχ⟩ := H.inv S φ
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [← hφ] at hχ
  have := congrArg (inv j ≫ ·) hχ
  simp only [MonObj.comp_mul, MonObj.comp_one, Category.assoc, IsIso.inv_hom_id_assoc] at this
  simpa [Category.assoc] using this

theorem mono_of_isFinFlatSub (H : IsFinFlatSub A B h) : Mono h := by
  constructor
  intro T a b hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineCover _ _ fun i => ?_
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f i ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
  haveI : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have := affine_mono H (j ≫ a) (j ≫ b) (by rw [Category.assoc, Category.assoc, hab])
  exact congrArg (·.left) this

theorem grpObj_of_isFinFlatSub (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type)
    [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A) (H : IsFinFlatSub A B h) :
    ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  have hmono := mono_of_isFinFlatSub H
  haveI : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
    inferInstanceAs (IsAffine (pullback (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom))
  obtain ⟨m, hm⟩ := affine_mul H (fst _ _) (snd _ _)
  obtain ⟨e, he⟩ := affine_one H (T := 𝟙_ _)
  obtain ⟨i, hi⟩ := affine_inv H (𝟙 _)
  rw [Category.id_comp] at hi
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e i hm he hi
  exact ⟨G, hG, hmono⟩

end Scheme

end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeIntOfProjectiveRingOfIntegers
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem finite_int_of_finite_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] : Module.Finite ℤ L :=
  Module.Finite.trans (𝓞 E) L

theorem free_int_of_projective_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Free ℤ L := by
  haveI : Module.Finite ℤ L := finite_int_of_finite_ringOfIntegers E L
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) L)
  have hinj : Function.Injective s := fun x y hxy => by
    have := congrArg (Finsupp.linearCombination (𝓞 E) id) hxy
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  haveI : Module.IsTorsionFree ℤ (L →₀ 𝓞 E) := inferInstance
  haveI : Module.IsTorsionFree ℤ L :=
    hinj.moduleIsTorsionFree (R := ℤ) s fun r m => by simp
  infer_instance

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariants
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem genAF_of_map_eq_invFun : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K :=
  PositivityTheory.HtPt.Rh.sub_pull

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsAddCharacters
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem addChar_mem_hopfOrder : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier :=
  @PositivityTheory.HtPt.Ra.charmem

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHolds
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_base_change_larger_ring : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) :=
  @PositivityTheory.Xgn.character_data_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, LocFree R n (D.af R p (χ τ)) ∧ LocFree R n (D.hh R p (χ τ)) ∧ D.af R p (χ τ) ≤ stdLat R _ ∧ ∀ i, LocFree R 1 (D.xId (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₁ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).af RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.af R p (χ τ)) ∧ (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.hh R p (χ τ)) ∧ ∀ i, (D.bc RC).xId (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
  exact @PositivityTheory.Xgn.good_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalMatrixCoprimeDecomposition
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Split

theorem isotropic_residue_injective_splits : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 :=
  @PositivityTheory.HtPt.Cg.split_local

end GlobalTheory.CompanionTheory.Ar.Split
end

