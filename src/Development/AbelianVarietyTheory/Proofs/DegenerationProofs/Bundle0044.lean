module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGen_one_of_g_eq_one {X : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) :
    (⟨fun _ => 1⟩ : LB.Gen L).IsGen := fun i j =>
  (map_one _).trans ((congrArg₂ (· * ·) (h i j) (map_one _)).trans (_root_.mul_one _)).symm

theorem div_g_eq_one {X : Scheme.{0}} (M L : LB X) (hM : ∀ i j, M.g i j = 1) (hL : ∀ i j, L.g i j = 1)
    (i j : (LB.div M L).ι) : (LB.div M L).g i j = 1 := by
  simp only [LB.div, hM, hL, map_one, inv_one, _root_.mul_one]
  rfl

theorem isGen_one_linComb_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.LinComb (Out.Inh.trivLB X) φ ε)).IsGen :=
  isGen_one_of_g_eq_one _ (Out.Inh.linComb_triv_g φ ε)

def splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) : SplitExt S where
  B := B
  isAbelian := h
  X := PUnit
  O := fun _ => ⟨Out.Inh.trivLB _, ⟨fun _ => 1⟩, Out.Inh.trivLB_isLB _, isGen_one_linComb_triv _ _⟩
  addIso := fun _ _ => ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _
    (div_g_eq_one _ _ (div_g_eq_one _ _ (fun _ _ => rfl) fun _ _ => rfl) fun _ _ => rfl)⟩
  zeroTriv := ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _ fun _ _ => rfl⟩
  primitive := fun _ => ⟨⟨fun _ => 1⟩, isGen_one_linComb_triv _ _⟩

theorem isGt_splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) :
    (splitExtOfAbelian B h).IsGt B := by
  have := h.comm
  have := isIso_toUnit_splitTorus_punit S
  have hk : IsPullback (toUnit (splitTorus S PUnit) ≫ η[B]) (toUnit _) (𝟙 B) η[B] :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  refine CoordToExt.isGt_of_units (splitExtOfAbelian B h) (𝟙 B) (toUnit _ ≫ η[B])
    (inferInstanceAs (IsMonHom (𝟙 B)))
    (inferInstanceAs (IsMonHom (toUnit (splitTorus S PUnit) ≫ η[B])))
    (inferInstanceAs (Flat (𝟙 B.left))) (inferInstanceAs (Surjective (𝟙 B.left)))
    (inferInstanceAs (IsAffineHom (𝟙 B.left))) hk (fun _ _ => 1) ?_ ?_ ?_
  · intro χ Z r z a a' _ _
    exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · intro χ a Z t g z _
    have e : charUnit S PUnit χ = 1 := by
      have e₀ : Multiplicative.ofAdd (α := PUnit) χ = 1 := rfl
      unfold charUnit
      rw [e₀]
      simp only [map_one]
      exact (congrArg _ (map_one _)).trans (map_one _)
    exact (map_one _).trans ((congrArg₂ (· * ·) ((congrArg _ e).trans (map_one _)) (map_one _)).trans
      (_root_.mul_one _)).symm
  · intro χ a y _
    exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)

section

variable {T V Z G H : Scheme.{0}} {f : H ⟶ G} {s : H ⟶ V} {t : G ⟶ Z} {y₀ : V ⟶ Z}

end

section

variable (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated π] (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (A : Over Z) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom)

end

end GlobalTheory.ZJ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open IsLocalRing

theorem nonempty_torusExtension_of_comp_eq {K : Type} [Field K] {S S₁ S₂ : Scheme.{0}} {a : S₁ ⟶ S}
    {b : Spec (CommRingCat.of K) ⟶ S₁} {c : S₂ ⟶ S} {d : Spec (CommRingCat.of K) ⟶ S₂} (e : b ≫ a = d ≫ c)
    (G : Over S) [GrpObj G] (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback d).obj ((Over.pullback c).obj G))) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  have h₁ : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := ⟨torusExtOfIso (pullCompIso b a G).symm T⟩
  rw [e] at h₁
  obtain ⟨T₁⟩ := h₁
  exact ⟨torusExtOfIso (pullCompIso d c G) T₁⟩

theorem exists_finite_dvr_torusExtension_specialFibre : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [IsAdicComplete (IsLocalRing.maximalIdeal V') V'] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], IsSemiAbelian G → ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V'') V'') (_ : Algebra V' V''), Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧ IsLocalHom (algebraMap V' V'') ∧ IsSemiAbelian (baseChange V' V'' G) ∧ Nonempty (TorusExtension (specialFibre V'' (baseChange V' V'' G))) := by
  intro V' _ _ _ _ G _ hG
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue V'))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField V'
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  haveI : Finite s := hs.to_subtype
  haveI : FiniteDimensional k (IntermediateField.adjoin k s) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, e, he⟩ := nb V' (IntermediateField.adjoin k s)
  refine ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, IsSemiAbelian.pullback _ G hG, ?_⟩
  have hT := H _ (ResidueField.map (algebraMap V' V''))
    ((algebraMap (IntermediateField.adjoin k s) Ω).comp e.symm.toRingHom)
    (by
      rw [← he]
      ext x
      simp [k])
    (fun x hx => ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp⟩)
  refine nonempty_torusExtension_of_comp_eq ?_ G hT
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ResidueField.map_comp_residue]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteIsAbelianSchemeDescends
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS GlobalTheory.FieldModel

namespace GlobalTheory

theorem exists_finite_isAbelianScheme_range {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (β : k₁ →+* K), s ⊆ Set.range β →
      ∃ (B₁ : Over (Sp k₁)) (_ : GrpObj B₁) (φ : B.left ⟶ B₁.left),
        IsAbelianScheme B₁ ∧ IsGrpPullback B B₁ (spMap β) φ := by
  have := hB.proper
  obtain ⟨s₀, hs₀⟩ := hasModel B
  let k₀ := Subfield.closure (s₀ : Set K)
  obtain ⟨B₀, φ₀, H₀⟩ := hs₀ k₀ k₀.subtype fun x hx => ⟨⟨x, Subfield.subset_closure hx⟩, rfl⟩
  have lB : LocallyOfFiniteType B.hom := inferInstance
  have pBB : IsProper (B ⊗ B).hom := inferInstanceAs (IsProper (pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨sm, hm⟩ := _root_.GlobalTheory.hom_descends_to_subfield_containing_finset k₀ K _ _ _ _ _ _ _ (isPullback_sq H₀) H₀ inferInstance inferInstance lB μ[B]
  obtain ⟨si, hi⟩ := _root_.GlobalTheory.hom_descends_to_subfield_containing_finset k₀ K _ _ _ _ _ _ _ H₀ H₀ inferInstance inferInstance lB ι[B]
  obtain ⟨se, he⟩ := _root_.GlobalTheory.hom_descends_to_subfield_containing_finset k₀ K _ _ _ _ _ _ _ (isPullback_unit _) H₀
    (inferInstanceAs (QuasiCompact (𝟙 (Sp K)))) (inferInstanceAs (QuasiSeparated (𝟙 (Sp K)))) lB η[B]
  refine ⟨s₀ ∪ (sm ∪ (si ∪ se)), by simp, fun k₁ _ β hs => ?_⟩
  simp only [Set.union_subset_iff] at hs
  obtain ⟨b₀, bm, bi, be⟩ := hs
  obtain ⟨ρ, hρ⟩ := exists_factor β (s₀ : Set K) b₀
  obtain ⟨φ₁, eφ, H₁⟩ := exists_baseChange (spMap_comp hρ) H₀
  have P₁ : IsPullback (pullback.fst B₀.hom (spMap ρ)) ((Over.pullback (spMap ρ)).obj B₀).hom B₀.hom (spMap ρ) :=
    .of_hasPullback _ _
  obtain ⟨m₁, hm₁⟩ := hm k₁ ρ β hρ bm _ _ (sq H₁.w) _ φ₁ _ (isPullback_sq P₁) P₁ (sq_comp eφ _ _ _) eφ
    (isPullback_sq H₁).w H₁.w
  obtain ⟨i₁, hi₁⟩ := hi k₁ ρ β hρ bi _ _ φ₁ _ φ₁ _ P₁ P₁ eφ eφ H₁.w H₁.w
  obtain ⟨e₁, he₁⟩ := he k₁ ρ β hρ be (𝟙_ _) _ (spMap β) _ φ₁ _ (isPullback_unit (spMap ρ)) P₁ (spMap_comp hρ) eφ
    (isPullback_unit (spMap β)).w H₁.w
  obtain ⟨gB, ab, gpB⟩ := _root_.GlobalTheory.isAbelianScheme_descends_subfield k₁ K β B _ φ₁ hB H₁ m₁ i₁ e₁ _ (sq_fst _) (sq_snd _) hm₁ hi₁ he₁
  exact ⟨_, gB, φ₁, ab, gpB⟩

theorem exists_finite_isAbelianScheme_descends : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (B₁ : Over (Sp L)) (_ : GrpObj B₁) (e : (Over.pullback (spMap (algebraMap L Ω))).obj B₁ ≅ B), IsAbelianScheme B₁ ∧ IsMonHom e.hom := by
  intro K Ω _ _ _ _ B _ hB
  obtain ⟨s, hs, h⟩ := exists_finite_isAbelianScheme_range B hB
  have := hs.to_subtype
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨B₁, g, φ, ab, gp⟩ := h _ (algebraMap (IntermediateField.adjoin K s) Ω)
    fun x hx => ⟨⟨x, IntermediateField.subset_adjoin K s hx⟩, rfl⟩
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B₁ _) gp
  exact ⟨IntermediateField.adjoin K s, IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, B₁, g, e, ab, he⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomogenisation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ConeClosed

theorem exists_homogenisation {k J : Type} [Field k] (i : J) (P : MvPolynomial J k) :
    ∃ (n : ℕ) (Q : MvPolynomial J k), ∀ w : J → k, w i ≠ 0 →
      MvPolynomial.eval w Q = w i ^ n * MvPolynomial.eval (fun j => w j / w i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun w _ => by simp⟩
  | add P P' h h' =>
    obtain ⟨n, Q, hQ⟩ := h
    obtain ⟨n', Q', hQ'⟩ := h'
    refine ⟨n + n', MvPolynomial.X i ^ n' * Q + MvPolynomial.X i ^ n * Q', fun w hw => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.eval_X, hQ w hw, hQ' w hw]
    ring
  | mul_X P j h =>
    obtain ⟨n, Q, hQ⟩ := h
    refine ⟨n + 1, Q * MvPolynomial.X j, fun w hw => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, hQ w hw]
    field_simp
    ring

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem exists_point {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (hU : IsAffineOpen U) (φ : Γ(X, U) →+* k) (hφ : ∀ a, φ (constFn p U a) = a) :
    ∃ x : Sp k ⟶ X, x ≫ p = 𝟙 _ ∧ ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ f, GlobalTheory.ZH.valR x U f = φ f := by
  let ψ : Γ(X, U) ⟶ CommRingCat.of k := CommRingCat.ofHom φ
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (Spec.map ψ ≫ hU.fromSpec) U f = φ f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map ψ ≫ hU.fromSpec, ?_, hx, hv⟩
  rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ p), ← Spec.map_id]
  congr 1
  ext a
  rw [← GlobalTheory.Points.valR_constFn p _ U hx, hv, hφ]
  rfl

theorem valR_eval₂ {k J : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (x : Sp k ⟶ X) (hp : x ≫ p = 𝟙 _) (hx : ⊤ ≤ x ⁻¹ᵁ U) (r : J → Γ(X, U)) (P : MvPolynomial J k) :
    GlobalTheory.ZH.valR x U (MvPolynomial.eval₂Hom (constHom p U) r P) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) P := by
  have e : (CrdCalc.valHom x U hx).comp (MvPolynomial.eval₂Hom (constHom p U) r) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, ← CrdCalc.valR_eq]
      exact GlobalTheory.Points.valR_constFn_of_section p x hp U hx a
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, ← CrdCalc.valR_eq]
  rw [CrdCalc.valR_eq x U hx, ← e]
  rfl

theorem mem_cone_of_vanishing : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ v : J → k, (∃ i ∈ J₀, v i ≠ 0) → (∀ Pf ∈ MvPolynomial.vanishingIdeal k (cone p H s), MvPolynomial.eval v Pf = 0) → v ∈ cone p H s) := by
  intro k _ _ X p H J _ s J₀ hH him v ⟨i, hi, hvi⟩ hv
  obtain ⟨hU, r, hr, hgen⟩ := him.2 i hi
  let Φ : MvPolynomial J k →+* Γ(X, (Out.nonzeroLocus (s i))) := MvPolynomial.eval₂Hom (constHom p (Out.nonzeroLocus (s i))) r
  have hsurj : Function.Surjective Φ := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval fun j => v j / v i) := by
    intro P hP
    obtain ⟨n, Q, hQ⟩ := exists_homogenisation i P
    have hmem : MvPolynomial.X i * Q ∈ MvPolynomial.vanishingIdeal k (cone p H s) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro w ⟨x, hp, hw⟩
      rw [MvPolynomial.aeval_eq_eval, map_mul, MvPolynomial.eval_X]
      by_cases hwi : w i = 0
      · rw [hwi, zero_mul]
      have hx : ⊤ ≤ x ⁻¹ᵁ (Out.nonzeroLocus (s i)) := (CrdCalc.crd_isUnit_iff i hw).1 (Ne.isUnit hwi)
      have e : (fun j => w j / w i) = fun j => GlobalTheory.ZH.valR x (Out.nonzeroLocus (s i)) (r j) := funext fun j => by
        rw [CrdCalc.crd_ratio hw (hr j) hx, mul_div_cancel_right₀ _ hwi]
      rw [hQ w hwi, e, ← valR_eval₂ p x hp hx r P, RingHom.mem_ker.1 hP, CrdCalc.valR_eq x (Out.nonzeroLocus (s i)) hx, map_zero,
        mul_zero, mul_zero]
    have h := hv _ hmem
    rw [map_mul, MvPolynomial.eval_X, hQ v hvi] at h
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hvi)).resolve_left (pow_ne_zero _ hvi)
  let φ : Γ(X, (Out.nonzeroLocus (s i))) →+* k := Φ.liftOfSurjective hsurj ⟨_, hker⟩
  have hφ : ∀ P, φ (Φ P) = MvPolynomial.eval (fun j => v j / v i) P := fun P =>
    RingHom.liftOfSurjective_comp_apply Φ hsurj ⟨_, hker⟩ P
  obtain ⟨x, hp, hx, hval⟩ := exists_point p hU φ fun a => by
    have := hφ (MvPolynomial.C a)
    rwa [MvPolynomial.eval_C, show Φ (MvPolynomial.C a) = constFn p (Out.nonzeroLocus (s i)) a from
      MvPolynomial.eval₂Hom_C _ _ _] at this
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists hH s x
  have hwi : w i ≠ 0 := ((CrdCalc.crd_isUnit_iff i hw).2 hx).ne_zero
  refine ⟨x, hp, ?_⟩
  have h := CrdCalc.crd_smul (Units.mk0 (v i / w i) (div_ne_zero hvi hwi)) hw
  convert h using 2 with j
  have h₁ := hφ (MvPolynomial.X j)
  rw [MvPolynomial.eval_X, show Φ (MvPolynomial.X j) = r j from MvPolynomial.eval₂Hom_X' _ _ _] at h₁
  rw [CrdCalc.crd_ratio hw (hr j) hx, hval, h₁, Units.val_mk0]
  field_simp

end GlobalTheory.ZH.ConeClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowEqTorus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorsLift

theorem exists_pow_eq_hom {X M : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup M] (n : ℕ)
    (h : ∀ m : M, ∃ r : M, r ^ n = m) (f : Multiplicative X →* M) :
    ∃ g : Multiplicative X →* M, g ^ n = f := by
  choose r hr using h
  let b := Module.Free.chooseBasis ℤ X
  let g : X →ₗ[ℤ] Additive M :=
    b.constr ℤ fun i => Additive.ofMul (r (f (Multiplicative.ofAdd (b i))))
  have hg : n • g = (MonoidHom.toAdditiveRight f).toIntLinearMap := by
    refine b.ext fun i => ?_
    simp only [g, LinearMap.smul_apply, Module.Basis.constr_basis]
    rw [← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft g.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hg x.toAdd)

theorem exists_pow_eq_unit (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 1 ≤ n)
    (m : Γ(Sp k, ⊤)ˣ) : ∃ r : Γ(Sp k, ⊤)ˣ, r ^ n = m := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e m.val) (n := n) hn
  have h1 : (e.symm z) ^ n = m.val := by
    rw [← map_pow, hz, RingEquiv.symm_apply_apply]
  have hu : IsUnit (e.symm z) := (isUnit_pow_iff (by omega : n ≠ 0)).1 (h1 ▸ m.isUnit)
  exact ⟨hu.unit, Units.ext (by simpa using h1)⟩

theorem exists_pow_eq_torus (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] (n : ℕ) (hn : 1 ≤ n) (t : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X) :
    ∃ s : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X, s ^ n = t := by
  let e := splitTorusPointsEquiv (Sp k) X (Out.baseOver (Sp k))
  obtain ⟨g, hg⟩ := exists_pow_eq_hom n (exists_pow_eq_unit k n hn) (e t)
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_pow, e.apply_symm_apply]
  exact hg

theorem points_lift :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G) (n : ℕ), 1 ≤ n → (∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b) ∧ (∀ b : Out.baseOver (Sp k) ⟶ E.B, b ^ n = 1 → ∃ x : Out.baseOver (Sp k) ⟶ G, x ^ n = 1 ∧ x ≫ D.q = b) ∧ ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 → ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
  intro k _ _ E G _ _ D n hn
  have := D.q_hom
  have := D.i_hom
  have h1 : ∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b :=
    RatLift.exists_point_over k E G D
  have h3 : ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 →
      ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_pow_eq_torus k E.X n hn (D.isKernel.lift x (toUnit _) hx)
    refine ⟨s ≫ D.i, ?_, ?_⟩
    · rw [Category.assoc, D.isKernel.w, ← Category.assoc, comp_toUnit]
      rfl
    · rw [← MonObj.pow_comp, hs, D.isKernel.lift_fst]
  refine ⟨h1, fun b hb => ?_, h3⟩
  obtain ⟨x, hx⟩ := h1 b
  obtain ⟨y, hy, hyx⟩ := h3 (x ^ n) (by rw [MonObj.pow_comp, hx, hb])
  refine ⟨x * y⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hyx, mul_inv_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, hx, hy, inv_one, _root_.mul_one]

end GlobalTheory.TorsLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfSplitAll
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem SplitAll.fieldPoint {Z : Scheme.{0}} {G : Over Z} [GrpObj G] (h : SplitAll G) (K : Type) [Field K]
    (t : Sp K ⟶ Z) : ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G) := by
  obtain ⟨z, r, rfl⟩ : ∃ (z : Z) (r : Sp K ⟶ Sp (Z.residueField z)), t = r ≫ Z.fromSpecResidueField z :=
    ⟨_, _, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z t).symm⟩
  obtain ⟨E, ⟨d⟩⟩ := h z
  have : IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).inv)
  obtain ⟨E', _, _, _, _, hE'⟩ := gtBaseChange _ _ r E _ ⟨d⟩
  exact ⟨E', isGt_of_iso (pullCompIso r (Z.fromSpecResidueField z) G).symm hE'⟩

theorem isSemiAbelian_of_splitAll : ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom], SplitAll G → IsSemiAbelian G ∧ (∀ (K : Type) [Field K] (t : Sp K ⟶ Z), ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G)) ∧ ∀ x : Z, ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField x) k), FiniteDimensional (Z.residueField x) k ∧ Algebra.IsSeparable (Z.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField x) k)) ≫ Z.fromSpecResidueField x)).obj G) := by
  intro Z G _ hc hs hsep hq h
  refine ⟨⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩, h.fieldPoint, fun x => ⟨Z.residueField x, inferInstance, inferInstance, inferInstance,
      inferInstance, h.fieldPoint _ _⟩⟩
  · obtain ⟨E, hE⟩ := h.fieldPoint K q
    have hg : GeometricallyConnected (pullback.snd G.hom q) :=
      (UnitRigidity.smooth_geometricallyConnected_of_isGt E _ hE).2
    rw [← (pullbackLeftPullbackSndIso G.hom q (𝟙 _) ≪≫ pullback.congrHom rfl (Category.id_comp q)).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K (𝟙 _)
  · obtain ⟨E, hE⟩ := h.fieldPoint Ω q
    exact nonempty_torusExtension_of_isGt E _ hE

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusWeightTestGenericPointRationalPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  first | exact @GlobalTheory.SS.WtRat.wt_of_genericPoint | exact GlobalTheory.SS.WtRat.wt_of_genericPoint | (intros; apply GlobalTheory.SS.WtRat.wt_of_genericPoint <;> assumption)
end

