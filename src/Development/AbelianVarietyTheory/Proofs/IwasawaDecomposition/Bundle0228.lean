module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

namespace GlobalTheory.BijPointsIso

universe u

variable {X Y : Scheme.{u}}

theorem universallyInjective_of_injective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    UniversallyInjective f := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro z
  let K := AlgebraicClosure ((pullback f f).residueField z)
  let φ : Spec (.of K) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField z) K)) ≫
      (pullback f f).fromSpecResidueField z
  have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
    h K (by simp only [Category.assoc, pullback.condition])
  have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [hφ₁]
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨(φ ≫ pullback.fst f f) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem surjective_of_surjective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Surjective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    Function.Surjective f := by
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  obtain ⟨g, hg⟩ := h K (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
    Y.fromSpecResidueField y)
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨g pt, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  simp only at hg
  rw [hg, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem bijective_residue_of_isField {R : Type*} [CommRing R] [IsLocalRing R] (hR : IsField R) :
    Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨fun a b e ↦ ?_, Ideal.Quotient.mk_surjective⟩
  change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b at e
  rw [Ideal.Quotient.eq, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR, Ideal.mem_bot,
    sub_eq_zero] at e
  exact e

theorem isIso_stalkMap_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [UniversallyInjective f] [IsDominant f]
    (hc : CharZero (Y.residueField (f (genericPoint X)))) :
    IsIso (f.stalkMap (genericPoint X)) := by
  set x := genericPoint X
  have h3 : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective.{u} f).out 1 3).mp ‹_›
  have hpi := h3.2 x
  have hr : Function.Bijective (f.residueFieldMap x) := by
    algebraize [(f.residueFieldMap x).hom]
    have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hpi
    exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _
  have hX : IsField (X.presheaf.stalk x) := Field.toIsField X.functionField
  have hY : IsField (Y.presheaf.stalk (f x)) := by
    rw [GlobalTheory.apply_genericPoint_of_isDominant f]
    exact Field.toIsField Y.functionField
  have hsq := Scheme.residue_residueFieldMap f x
  have hsq' : ∀ a, X.residue x (f.stalkMap x a) = f.residueFieldMap x (Y.residue (f x) a) :=
    fun a ↦ (congrArg (fun g ↦ g.hom a) hsq).symm
  have bX := bijective_residue_of_isField hX
  have bY := bijective_residue_of_isField hY
  rw [ConcreteCategory.isIso_iff_bijective]
  have : Function.Bijective (X.residue x ∘ f.stalkMap x) := by
    have e : (X.residue x ∘ f.stalkMap x) = (f.residueFieldMap x ∘ Y.residue (f x)) := funext hsq'
    rw [e]; exact hr.comp bY
  exact (Function.Bijective.of_comp_iff' bX _).mp this

end GlobalTheory.BijPointsIso

namespace GlobalTheory.BijPointsIso

theorem charZero_residueField {F : Type} [Field F] [CharZero F] (Y : Var F) (y : Y.X) :
    CharZero (Y.X.residueField y) := by
  let ψ : F →+* Y.X.residueField y :=
    (Y.X.residue y).hom.comp ((Y.X.presheaf.germ ⊤ y trivial).hom.comp (algebraMap F Γ(Y.X, ⊤)))
  exact charZero_of_injective_ringHom ψ.injective

theorem isIso_of_bijective_points : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F)
    (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str →
      (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) →
        IsIso h := by
  intro F _ _ Y₁ Y₂ h hc hb
  have : UniversallyInjective h :=
    universallyInjective_of_injective_algClosed h fun K _ _ ↦ (hb K).1
  have : IsProper (h ≫ Y₂.str) := hc ▸ inferInstance
  have : IsProper h := IsProper.of_comp h Y₂.str
  have hs : Function.Surjective h := surjective_of_surjective_algClosed h fun K _ _ ↦ (hb K).2
  have : IsDominant h := ⟨hs.denseRange⟩
  have := isIso_stalkMap_genericPoint h (charZero_residueField Y₂ _)
  have hN := Y₂.isNormalScheme
  exact GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap h hN.isIntegrallyClosed_stalk

end GlobalTheory.BijPointsIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGL
section
open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.IwasawaFinAd

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def coordV (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def locM (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  RingHom.mapMatrix (coordV v) M

def locGL (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin n) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (coordV v)).toMonoidHom

theorem locM_mul (v : HeightOneSpectrum (𝓞 F)) (M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    locM v (M * N) = locM v M * locM v N := map_mul _ _ _

theorem locM_one (v : HeightOneSpectrum (𝓞 F)) :
    locM v (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = 1 := map_one _

theorem matrix_ext_loc {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ v, locM v M = locM v N) : M = N := by
  refine Matrix.ext fun i j => FiniteAdeleRing.ext F fun v => ?_
  exact congrFun (congrFun (h v) i) j

theorem gl_ext_loc {g h : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)} (e : ∀ v, locGL v g = locGL v h) :
    g = h :=
  Units.ext (matrix_ext_loc fun v => congrArg Units.val (e v))

def IntAt (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ v.adicCompletionIntegers F

theorem intAt_one (v : HeightOneSpectrum (𝓞 F)) : IntAt v (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (v.adicCompletionIntegers F).one_mem
  · exact (v.adicCompletionIntegers F).zero_mem

def glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (⟨fun v => x v i j, hx.mono fun v h => h i j⟩ :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem locM_glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) (v : HeightOneSpectrum (𝓞 F)) :
    locM v (glueM x hx) = x v := by
  ext i j
  rfl

def glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) where
  val := glueM (fun v => (x v).val) (hx.mono fun _ h => h.1)
  inv := glueM (fun v => (x v)⁻¹.val) (hx.mono fun _ h => h.2)
  val_inv := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.mul_inv (x v)
  inv_val := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.inv_mul (x v)

theorem locGL_glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) (v : HeightOneSpectrum (𝓞 F)) :
    locGL v (glueGL x hx) = x v :=
  Units.ext (locM_glueM _ (hx.mono fun _ h => h.1) v)

theorem eventually_intAt (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v in Filter.cofinite, IntAt v (locM v M) := by
  unfold IntAt
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact (M i j).2

theorem upper_eq_uni_mul_diag {K : Type} [Field K] (b : GL (Fin n) K) (hb : b.val.BlockTriangular id) :
    ∃ u t : GL (Fin n) K, PIW.ClassFinD.IsUpperUni u.val ∧ PIW.ClassFinD.IsDiagM t.val ∧ b = u * t := by
  have hdet0 : b.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  have hne : ∀ i, b.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let t : GL (Fin n) K :=
    ⟨diagonal (fun i => b.val i i), diagonal (fun i => (b.val i i)⁻¹),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (b * t⁻¹).val i j = b.val i j * (b.val j j)⁻¹ := by
    intro i j
    change (b.val * diagonal (fun i => (b.val i i)⁻¹)) i j = _
    rw [mul_diagonal]
  refine ⟨b * t⁻¹, t, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, by group⟩
  · rw [hU, hb hij, zero_mul]
  · rw [hU, mul_inv_cancel₀ (hne i)]
  · exact diagonal_apply_ne _ hij

theorem isUpperUni_one {K : Type} [CommRing K] : PIW.ClassFinD.IsUpperUni (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isDiagM_one {K : Type} [CommRing K] : PIW.ClassFinD.IsDiagM (1 : Matrix (Fin n) (Fin n) K) :=
  fun i j hij => Matrix.one_apply_ne hij

theorem intAt_of_glint (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (v.adicCompletion F))
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) : IntAt v k.val ∧ IntAt v k⁻¹.val := by
  obtain ⟨K, rfl⟩ := hk
  refine ⟨fun i j => (K.val i j).2, fun i j => ?_⟩
  rw [← map_inv]
  exact ((K⁻¹).val i j).2

end GlobalTheory.IwasawaFinAd

namespace GlobalTheory.IwasawaFinAd

open PIW.ClassFinD

theorem iwasawaAf : PIW.ClassFinD.IwasawaAf := by
  classical
  intro F _ _ n g
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    IntAt v (locGL v g).val ∧ IntAt v (locGL v g)⁻¹.val
  have hgood : ∀ᶠ v in Filter.cofinite, good v := by
    refine (eventually_intAt g.val).and ((eventually_intAt (g⁻¹).val).mono fun v h => ?_)
    rw [← map_inv]
    exact h
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u t k : GL (Fin n) (v.adicCompletion F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ IntAt v k.val ∧ IntAt v k⁻¹.val ∧ locGL v g = u * t * k ∧
      (good v → u = 1 ∧ t = 1 ∧ k = locGL v g) := by
    intro v
    by_cases hv : good v
    · exact ⟨1, 1, locGL v g, isUpperUni_one, isDiagM_one, hv.1, hv.2, by rw [one_mul, one_mul],
        fun _ => ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨b, k, hb, hk, hbk⟩ := Formalism.UG.P.spherical_iwasawa F v (locGL v g)
      obtain ⟨u, t, hu, ht, rfl⟩ := upper_eq_uni_mul_diag b hb
      obtain ⟨hk1, hk2⟩ := intAt_of_glint v k hk
      exact ⟨u, t, k, hu, ht, hk1, hk2, hbk, fun h => absurd h hv⟩
  choose uL tL kL huL htL hkL hkL' hgL hgoodL using hloc
  have hu : ∀ᶠ v in Filter.cofinite, IntAt v (uL v).val ∧ IntAt v (uL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have ht : ∀ᶠ v in Filter.cofinite, IntAt v (tL v).val ∧ IntAt v (tL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).2.1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have hk : ∀ᶠ v in Filter.cofinite, IntAt v (kL v).val ∧ IntAt v (kL v)⁻¹.val :=
    Filter.Eventually.of_forall fun v => ⟨hkL v, hkL' v⟩
  refine ⟨glueGL uL hu, glueGL tL ht, glueGL kL hk, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_,
    ⟨fun i j v => hkL v i j, fun i j v => hkL' v i j⟩, ?_⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i j) = coordV v 0
    rw [map_zero]
    exact (huL v).1 i j hij
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i i) = coordV v 1
    rw [map_one]
    exact (huL v).2 i
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL tL ht).val i j) = coordV v 0
    rw [map_zero]
    exact htL v i j hij
  · refine gl_ext_loc fun v => ?_
    rw [map_mul, map_mul, locGL_glueGL, locGL_glueGL, locGL_glueGL]
    exact hgL v

end GlobalTheory.IwasawaFinAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureLeOfCover
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselIntegrable

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {𝓕 K : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hK : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) : μ 𝓕 ≤ μ K := by
  rw [h.measure_eq_tsum K]
  refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hK n
  exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩

theorem norm_besChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B) : ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
    rw [e]
    exact hψ _
  · exact norm_one

theorem besInt : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, BesInt D := by
  intro hP D θ hθ ψ hψ A B ι hι d μ 𝓕 hq μN 𝓕N hμN h𝓕N s hs φ F hφ hF hA
  obtain ⟨-, a2, a3, a4, a5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, b2, b3, b4, b5, -, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have : Countable (NFlagQ B d.e) :=
    Function.Injective.countable (f := fun x : NFlagQ B d.e => (⟨x.1.1, x.2⟩ : GQ B))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ B => z.1) h))
  have : SecondCountableTopology (NFlag B d.e) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨⟨K, hK, hcov⟩, -⟩ := _root_.GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B d.ρ d.e d.e_iso
  have hfin : μN 𝓕N < ⊤ := (measure_le_of_cover _ μN h𝓕N hcov).trans_lt hK.measure_lt_top
  obtain ⟨C, hC⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ hF.1 hF.2
  obtain ⟨s', hs', hs'', -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  have hsc : Continuous s := by
    rw [show s = s' from funext fun h => (hs'' h _).1 (hs h)]
    exact hs'
  have hχ := (_root_.GlobalTheory.BesselChar.besChar_laws D ψ hψ A B ι hι d).2.2.1
  have hb : ∀ (h : GA D A) (n : NFlag B d.e), ‖star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B))‖ ≤ ‖φ h‖ * C := fun h n => by
    rw [norm_mul, norm_mul, norm_star, norm_star, norm_besChar hψ.1.2.1, mul_one]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hc : Continuous fun p : GA D A × NFlag B d.e => star (φ p.1) * F ((p.2 : GA D B) * s p.1 * (d.y : GA D B)) *
      star (besChar ψ d (p.2 : GA D B)) :=
    ((hφ.cont.comp continuous_fst).star.mul (hF.1.cont.comp
      (((continuous_subtype_val.comp continuous_snd).mul (hsc.comp continuous_fst)).mul continuous_const))).mul
      (hχ.comp continuous_snd).star
  refine ⟨fun h => Measure.integrableOn_of_bounded (M := ‖φ h‖ * C) hfin.ne
    (hc.comp (Continuous.prodMk_right h)).measurable.aestronglyMeasurable (.of_forall (hb h)), ?_⟩
  have hcusp : IsCuspForm θ A φ := ⟨hφ, hA.elim (fun h r C hC => absurd hC (h r C)) id⟩
  have hint := GlobalTheory.Mem.Th.petInt_of_cuspRapidDecay hP D θ hθ A μ 𝓕 hq (fun _ => 1) φ (isAutFunSm_const θ A 1) hcusp
  simp only [star_one, one_mul] at hint
  have : IsFiniteMeasure (μN.restrict 𝓕N) := isFiniteMeasure_restrict.2 hfin.ne
  refine Integrable.mono' ((hint.norm.mul_const C).mul_const (μN.real 𝓕N))
    (hc.stronglyMeasurable.integral_prod_right' (ν := μN.restrict 𝓕N)).aestronglyMeasurable (.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hfin fun n _ => hb h n

end GlobalTheory.Mem.BesselIntegrable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.MinorHarmonic

theorem pderiv_comm {σ R : Type*} [CommRing R] (i j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
      intro a b
      rw [MvPolynomial.pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, h]
    ring

def ker {σ : Type*} (v : σ) : Subring (MvPolynomial σ ℂ) where
  carrier := {f | MvPolynomial.pderiv v f = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Derivation.leibniz, ha, hb]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]

theorem det_mem {R : Type*} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

variable {D : D7} {m n : ℕ}

theorem varF_mem (τ τ' : D.what₂.Tau) (a : Fin m) (c : Fin n) (i j : ℕ)
    (h : τ' = τ → i = a → j = c → False) :
    (varF τ' i j : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  classical
  unfold varF
  split_ifs with h1
  · show MvPolynomial.pderiv _ _ = 0
    apply MvPolynomial.pderiv_X_of_ne
    intro he
    simp only [Prod.mk.injEq] at he
    exact h he.1 (congrArg Fin.val he.2.1) (congrArg Fin.val he.2.2)
  · exact Subring.zero_mem _

theorem delta_mem (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ n)
    (τ : D.what₂.Tau) (a : Fin m) (c : Fin n)
    (h : ((a : ℕ) < p τ ∧ p τ ≤ c) ∨ (p τ ≤ (a : ℕ) ∧ (c : ℕ) < p τ)) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  unfold delta deltaAt
  refine Subring.prod_mem _ fun τ' _ => Subring.mul_mem _ ?_ ?_
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := α.2
    have := β.2
    omega
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := hpq τ'
    omega

theorem laplacian_delta : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  intro D m n p q ap am hpq τ a b ha hb
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge (c : ℕ) (p τ) with hc | hc
  · rw [pderiv_comm]
    have : MvPolynomial.pderiv (τ, a, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ a c (Or.inr ⟨ha, hc⟩)
    rw [this, map_zero]
  · have : MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ b c (Or.inl ⟨hb, hc⟩)
    rw [this, map_zero]

end GlobalTheory.MinorHarmonic

end
end

