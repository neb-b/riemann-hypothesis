module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesInhabited
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassTorsionPointLocalScheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_section_of_isDominant {D G X' V Y₀ Y : Scheme.{0}} [IsReduced D] (g : G ⟶ X') [IsSeparated g]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (σ : D ⟶ G) (s : V ⟶ G) (hs : s ≫ g = ℓ) (y₀ : Y₀ ⟶ D) [IsDominant y₀]
    (z₀ : Y₀ ⟶ V) (h₀ : y₀ ≫ σ = z₀ ≫ s) (y : Y ⟶ D) (z : Y ⟶ V) (h : y ≫ σ ≫ g = z ≫ ℓ) :
    y ≫ σ = z ≫ s := by
  have h₀' : y₀ ≫ σ ≫ g = z₀ ≫ ℓ := by rw [reassoc_of% h₀, hs]
  have : IsReduced (pullback (σ ≫ g) ℓ) := isReduced_of_isOpenImmersion (pullback.fst (σ ≫ g) ℓ)
  have hd : IsDominant (pullback.lift y₀ z₀ h₀') := by
    constructor
    have h1 : Dense (Set.range y₀) := y₀.denseRange
    have h2 := h1.preimage (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.isOpenMap
    refine h2.mono ?_
    rintro u ⟨t, ht⟩
    refine ⟨t, (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.injective ?_⟩
    rw [← ht, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have key : pullback.fst (σ ≫ g) ℓ ≫ σ = pullback.snd (σ ≫ g) ℓ ≫ s := by
    refine ext_of_isDominant_of_isSeparated (s := g) ?_ (pullback.lift y₀ z₀ h₀') ?_
    · rw [Category.assoc, Category.assoc, hs, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₀]
  have := pullback.lift y z h ≫= key
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this

theorem fromSpecStalk_killed {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) [Etale (torsion G n).hom]
    (a : G ⟶ G) [IsMonHom a] (ha : a ≫ mulN G n = mulN G n ≫ a)
    (K : Type) [Field K] (P : Sp K ⟶ (torsion G n).left)
    (hP : P ≫ (torsion.ι G n).left ≫ a.left =
      P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K) :
    (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left ≫ a.left =
      (torsion G n).left.fromSpecStalk (P x) ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
  have h0 : (MonObj.one : 𝟙_ (Over X') ⟶ G) ≫ mulN G n = (MonObj.one : 𝟙_ (Over X') ⟶ G) := by
    have e : (MonObj.one : 𝟙_ (Over X') ⟶ G) = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, e, one_pow]
  obtain ⟨u₁, hu₁⟩ := exists_lift_torsion n (torsion.ι G n ≫ a)
    (by rw [Category.assoc, ha, ← Category.assoc, hι, MonObj.one_comp])
  obtain ⟨u₂, hu₂⟩ := exists_lift_torsion n (1 : torsion G n ⟶ G)
    (by rw [Hom.one_def, Category.assoc, h0])
  have e₁ : u₁.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ a.left := congrArg (·.left) hu₁
  have e₂ : u₂.left ≫ (torsion.ι G n).left = (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have := congrArg (·.left) hu₂
    simp only [Hom.one_def, Over.comp_left] at this
    rw [this]
    congr 1
  have := mono_torsion_ι G n
  have key : (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₁.left =
      (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₂.left := by
    refine _root_.GlobalTheory.TorsSpec.eq_of_unramified_of_closedPoint (torsion G n).hom _ _ _ ?_ K (Spec.map (Scheme.stalkClosedPointTo P)) ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, Over.w]
    · intro x
      obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact IsLocalRing.comap_closedPoint (Scheme.stalkClosedPointTo P).hom
    · rw [← Category.assoc, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
        ← cancel_mono (torsion.ι G n).left, Category.assoc, Category.assoc, e₁, e₂, hP]
  rw [← e₁, ← e₂, reassoc_of% key]

theorem exists_valAt : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom] (act : OAct (𝓞 E) G) (I : Ideal (𝓞 E))
    (hex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (P : Sp Ω ⟶ G.left), P ≫ G.hom = x ≫ ℓ →
      (∀ a ∈ I, P ≫ (act.act a).left = P ≫ G.hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) → ∃ c, P = x ≫ w c)
    (K : Type) [Field K] [IsAlgClosed K] (P : Sp K ⟶ (torsion G n).left)
    (hP : ∀ a ∈ I, P ≫ (torsion.ι G n).left ≫ (act.act a).left = P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K), ∃ c, GlobalTheory.TorsSpec.ValAt G n ℓ w (P x) c := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ act I hex K _ _ P hP x
  have := GlobalTheory.GrpTangent.etale_torsion G hn
  have := isDomain_stalk_of_etale (torsion G n).hom (P x)
  obtain ⟨Ω, _, _, y₀, hy₀, _⟩ := _root_.GlobalTheory.exists_geomGeneric_dominant ((torsion G n).left.presheaf.stalk (P x))
  obtain ⟨z₀, hz₀⟩ := _root_.GlobalTheory.lift_of_stalk_generic_flat (torsion G n).hom (P x) ℓ Ω y₀ hy₀
  have hw' : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  obtain ⟨c, hc⟩ := hex Ω z₀ (y₀ ≫ (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left)
    (by rw [Category.assoc, Category.assoc, hw', hz₀]) (fun a ha => by
      have := act.hom a
      have h := fromSpecStalk_killed G n (act.act a)
        (by rw [← act_natCast act, ← act.mul, ← act.mul, mul_comm]) K P (hP a ha) x
      simp only [Category.assoc]
      rw [h, reassoc_of% hw'])
  refine ⟨c, fun Ω' _ _ y z h => ?_⟩
  exact eq_section_of_isDominant G.hom ℓ _ (w c) (hw c) y₀ z₀ hc y z (by rw [Category.assoc, hw', h])

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualKernel

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem evc_ker_iff {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over S} (x : T ⟶ A) :
    evc hP (fst T B ≫ x) (snd T B) = 0 ↔ evc hP (snd B T ≫ x) (fst B T) = 0 := by
  constructor
  · intro h
    have e := congrArg (CechPic.pull (lift (snd B T) (fst B T)).left) h
    rwa [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  · intro h
    have e := congrArg (CechPic.pull (lift (snd T B) (fst T B)).left) h
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem evc_ker_mul {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x y : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) (hy : evc hP (fst T B ≫ y) (snd T B) = 0) :
    evc hP (fst T B ≫ (x * y)) (snd T B) = 0 := by
  rw [MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, hy, add_zero]

theorem evc_ker_one {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) (T : Over S) :
    evc hP (fst T B ≫ (1 : T ⟶ A)) (snd T B) = 0 := by
  rw [MonObj.comp_one]
  exact hA.evc_one hP _

theorem evc_ker_inv {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) : evc hP (fst T B ≫ x⁻¹) (snd T B) = 0 := by
  have e := evc_ker_one hP hA T
  rw [← mul_inv_cancel x, MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, zero_add] at e
  exact e

end GlobalTheory.DualKernel

namespace GlobalTheory.DualKernel

theorem exists_closed_subgroup_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P →
    ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧
      Triv (ev P (fst N B ≫ i) (snd N B)) ∧
      ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  intro K _ _ A B _ _ P hA hB hD
  have hP := hD.isLB
  have hs : (swap P).IsLB := pull_isLB hP _
  have ht : (LB.triv (B ⊗ A).left).IsLB := LB.isLB_triv _
  have h0 : ∀ (Y : Over (Sp K)) (b : Y ⟶ B) (a : Y ⟶ A), evc ht b a = 0 := fun _ _ _ ↦ map_zero _
  have hN : Fam B (swap P) := ⟨hs, isDual_isAdditive_swap _ A B P hB hD⟩
  have hN' : Fam B (LB.triv (B ⊗ A).left) :=
    ⟨ht, (isAdditive_iff ht).2 fun _ _ _ _ ↦ by simp only [h0, add_zero]⟩
  haveI := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨N, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp K) B A hB (swap P) _ hN hN'
  have key : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      evc hP (fst T B ≫ x) (snd T B) = 0 ↔ ∃ z : T ⟶ N, z ≫ i = x := fun T x ↦ by
    rw [← hG, same_iff hs ht, h0, evc_swap hP hs, evc_ker_iff]
  have hK : ∀ (T : Over (Sp K)) (z : T ⟶ N), evc hP (fst T B ≫ z ≫ i) (snd T B) = 0 :=
    fun T z ↦ (key T _).2 ⟨z, rfl⟩
  haveI : Mono i.left := inferInstance
  haveI : Mono i := Over.mono_of_mono_left i
  have hl : ∀ {T : Over (Sp K)} (x : T ⟶ A), evc hP (fst T B ≫ x) (snd T B) = 0 →
      ∃ z : T ⟶ N, z ≫ i = x := fun x h ↦ (key _ x).1 h
  obtain ⟨o, ho⟩ := hl (η[A] : 𝟙_ (Over (Sp K)) ⟶ A) (by
    have e := evc_ker_one hP hD.additive (𝟙_ (Over (Sp K)))
    rwa [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] at e)
  obtain ⟨m, hm⟩ := hl ((i ⊗ₘ i) ≫ μ[A]) (by
    have e := evc_ker_mul hP hD.additive (fst N N ≫ i) (snd N N ≫ i) (hK _ _) (hK _ _)
    rwa [Hom.mul_def, ← lift_map_assoc, lift_fst_snd, Category.id_comp] at e)
  obtain ⟨n, hn⟩ := hl (i ≫ GrpObj.inv) (by
    have e := evc_ker_inv hP hD.additive i (by simpa using hK N (𝟙 N))
    rwa [Hom.inv_def] at e)
  obtain ⟨g, hg⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  refine ⟨N, g, i, hg, hi, (triv_ev_iff hP _ _).2 (by simpa using hK N (𝟙 N)), fun T x hx ↦ ?_⟩
  exact (key T x).1 ((triv_ev_iff hP _ _).1 hx)

end GlobalTheory.DualKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDef
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TraceLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem cast_trace_mul_bar (x y : 𝓞 E) :
    ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℝ) = GlobalTheory.LatticeBoundTests.trBil E x y := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := ((x * H.bar y : 𝓞 E) : E))
  rw [← Algebra.coe_trace_int, ← (RingHom.equivRatAlgHom E ℂ).sum_comp] at h1
  rw [GlobalTheory.LatticeBoundTests.trBil_apply, ← Complex.re_sum]
  have h2 : ∑ σ : E →+* ℂ, σ (x : E) * starRingEnd ℂ (σ (y : E))
      = ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℂ) := by
    rw [← map_intCast (algebraMap ℚ ℂ), h1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, ← map_mul]
    rfl
  rw [h2]; simp

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem exists_traceForm_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  intro E _ _ _ H
  classical
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let q : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let e : Module.Basis (Fin (Fintype.card J)) ℤ (𝓞 E) := (RingOfIntegers.basis E).reindex q
  refine ⟨Fintype.card J, Matrix.of fun i j => Algebra.trace ℤ (𝓞 E) (e i * H.bar (e j)),
    (Algebra.leftMulMatrix e).toRingHom, ?_, ?_, ?_, ?_⟩
  · rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact Module.finrank_pos
  · ext i j
    apply Int.cast_injective (α := ℝ)
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [cast_trace_mul_bar, cast_trace_mul_bar, GlobalTheory.LatticeBoundTests.trBil_symm]
  · have h := (GlobalTheory.LatticeBoundTests.trBil_posDef E).submatrix q.symm.injective
    convert h using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply, cast_trace_mul_bar, e,
      Module.Basis.reindex_apply]
  · intro a
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.leftMulMatrix_eq_repr_mul]
    have h1 : ∑ k, e.repr (a * e i) k * Algebra.trace ℤ (𝓞 E) (e k * H.bar (e j))
        = Algebra.trace ℤ (𝓞 E) (a * e i * H.bar (e j)) := by
      conv_rhs => rw [← e.sum_repr (a * e i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc, map_zsmul, smul_eq_mul]
    have h2 : ∑ k, Algebra.trace ℤ (𝓞 E) (e i * H.bar (e k)) * e.repr (H.bar a * e j) k
        = Algebra.trace ℤ (𝓞 E) (e i * H.bar (H.bar a * e j)) := by
      conv_rhs => rw [← e.sum_repr (H.bar a * e j)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, mul_smul_comm, map_zsmul, smul_eq_mul, mul_comm]
    rw [h1, h2, map_mul H.bar, bar_bar]
    congr 1; ring

end GlobalTheory.TraceLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.LatFull.CMInt

theorem exists_coeff_denom_intWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * AddMonoidAlgebra.coeff G μ) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he0
  classical
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all E H Dw l Xo c z f La hz e k he0
  choose x hx0 hx using _root_.GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime E H Dw l Xo c z f La hz e k he0
  refine ⟨∏ p ∈ S, x p, Finset.prod_ne_zero_iff.2 fun p _ => hx0 p, fun F hF hv G hG μ => ?_⟩
  have hint : ∀ r : 𝓞 z.K, ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K), p.valuation z.K (r : z.K) ≤ 1 :=
    fun r p => p.valuation_le_one r
  have hv1 : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
      p.valuation z.K (((∏ q ∈ S, x q : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
    intro p
    by_cases hp : p ∈ S
    · rw [← Finset.mul_prod_erase S x hp]
      have e1 : (((x p * ∏ q ∈ S.erase p, x q : 𝓞 z.K)) : z.K) * AddMonoidAlgebra.coeff G μ =
          ((∏ q ∈ S.erase p, x q : 𝓞 z.K) : z.K) * (((x p : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) := by
        push_cast; ring
      rw [e1, map_mul]
      exact mul_le_one' (hint _ p) (hx p F hF hv G hG μ)
    · rw [map_mul]
      exact mul_le_one' (hint _ p) (hS p hp F hF hv G hG μ)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one z.K _ hv1
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

end GlobalTheory.LatFull.CMInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullDegTraitAndBaseUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CommonPull

open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem exists_rig_iso_of_eq {S : Scheme.{0}} {H : Over S} [GrpObj H] (L₁ L₂ : RigLB H) (h : L₁ = L₂) :
    ∃ w : LB.Iso L₂.L L₁.L, w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec H) (fun _ => 1)) L₂.rig L₁.rig := by
  subst h
  exact ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso L₁.L, idIso_isGen L₁.isLB, fun p => L₁.rigGen p.1 p.2⟩

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → UnifTrait D G L →
    ∀ (D₂ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U₂ : Unif (maximalIdeal R) D₂ A G),
    U₂.LG.L = L → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (φ : R →+* W) (D' : DegPre W),
      Function.Injective φ ∧ Nonempty (IsPullDeg φ D.toPre D') ∧ Nonempty (IsPullDeg φ D₂.toPre D') := by
  intro R _ _ _ hR D G _ _ L _ hG hT D₂ A U₂ hL
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφ, hloc, hβ, hLβ, hD⟩ := hT
  subst hL
  obtain ⟨hLw, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have h6 := GlobalTheory.sixthLaws_and_unifUniq.2
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap φ))
  haveI := mbc
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)

  have sq : spMap (fracMap hφ) ≫ jK R = jK W ≫ spMap φ := (fracMap_sq hφ).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hLw.polBaseChange _ _ (spMap (fracMap hφ)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hφ)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₂.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK W)).obj G') G (spMap (fracMap hφ) ≫ jK R)
      (pullback.fst G'.hom (jK W) ≫ β) :=
    ((isGrpPullback_pullback G' (jK W)).comp hβ).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₂.gen.inv.left ≫ U₂.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₂.LG.L.pull (pullback.fst G'.hom (jK W) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₂.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₂.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₂.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₂.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₂.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · show pullback.fst G'.hom (jK W) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
      rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G := by
    show eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
    rw [hbc]; exact (cubeMapOf hβ).e_comm
  obtain ⟨wL, gwL, rwL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G G'
    (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) he U₂.LG U'.LG (by
      show ∃ w : LB.Iso U'.LG.L (U₂.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap φ))), w.IsGen
      rw [hbc]; exact hLβ)
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R (maximalIdeal R) hR.1 D₂
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) ∈ Wo := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hWo
  obtain ⟨D₂', hD₂, U₂', hLG, -, -⟩ := h4.unifBaseChange R W (maximalIdeal R) (maximalIdeal W) hR.1 hW' φ
    (map_maximalIdeal_le φ) D₂ A G hG U₂ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gwL rwL
  obtain ⟨wU, gU, rU⟩ := exists_rig_iso_of_eq U₂'.LG U'.LG hLG
  obtain ⟨hU, -⟩ := h6 W (maximalIdeal W) hW' D₂' D' A'' A' G' hG' U₂' U' wU gU rU
  obtain ⟨hD'⟩ := hD
  refine ⟨W, inferInstance, inferInstance, φ, D'.toPre, hφ, ⟨hD'⟩, ?_⟩
  exact RingHom.id_comp φ ▸ GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ Function.injective_id hD₂ hU

end GlobalTheory.Mum.CommonPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegree
section
open IsLocalRing

namespace GlobalTheory.LocExt

theorem exists_isCN_integralClosure_of_isUnit_finrank : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.TorRef.IsCN V → ∀ (K' : Type) [Field K'] [Algebra (FractionRing V) K'] [FiniteDimensional (FractionRing V) K'], IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (j : V' →+* K'), GlobalTheory.TorRef.IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ Function.Injective j ∧ j.comp io = (algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V)) ∧ ∀ x : K', (∃ P : Polynomial V, P.Monic ∧ P.eval₂ ((algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V))) x = 0) → ∃ y, j y = x := by
  intro V _ _ _ hV K' _ _ _ hunit
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hV
  let K := FractionRing V
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := integralClosure V K'
  haveI hWf : Module.Finite V W := IsIntegralClosure.finite V K K' W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
  have hVL : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinjW : Function.Injective (algebraMap V W) := fun x y h => hVL (congrArg Subtype.val h)
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have h1 : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal W))
  have hlocW : IsLocalHom (algebraMap V W) := ((local_hom_tfae _).out 1 5).2 h1
  haveI : IsFractionRing W K' := IsIntegralClosure.isFractionRing_of_finite_extension V K K' W
  have hrank : Module.finrank V W = Module.finrank K K' := (IsFractionRing.finrank_eq V K W K').symm
  have hunit' : IsUnit ((Module.finrank V W : ℕ) : V) := by rw [hrank]; exact hunit
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, (integralClosure V K').val.toRingHom,
    ⟨IsNoetherianRing.of_finite V W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      CompleteFiniteExtension.isAdicComplete_of_finite_local V W, inferInstance⟩, hinjW,
    RingHom.finite_algebraMap.2 hWf, hlocW,
    GlobalTheory.Poinc.Sep.comap_map_eq_of_isUnit_finrank V W hinjW hunit',
    Subtype.val_injective, RingHom.ext fun _ => rfl, ?_⟩
  rintro x ⟨P, hmon, hP⟩
  exact ⟨⟨x, P, hmon, hP⟩, rfl⟩

end GlobalTheory.LocExt
end

