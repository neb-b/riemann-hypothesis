module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionModelOfExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

private theorem exists_monoidHom_aut_of_lies {𝒞 : Type*} [Category 𝒞] {U X : 𝒞} (j : U ⟶ X)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).asIso.hom ≫ j)
    (lies : Γ → (X ⟶ X) → Prop) (h1 : lies 1 (𝟙 X)) (hrl : ∀ g, lies g (r g))
    (hml : ∀ g h, lies (g * h) (r h ≫ r g))
    (hj : ∀ g a b, lies g a → lies g b → j ≫ a = j ≫ b → a = b) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).asIso.hom = r g := by
  have hone : r 1 = 𝟙 X := by
    refine hj 1 _ _ (hrl 1) h1 ?_
    rw [hr 1, map_one, Category.comp_id]
    exact Category.id_comp j
  have hmul : ∀ g h, r (g * h) = r h ≫ r g := by
    intro g h
    refine hj (g * h) _ _ (hrl _) (hml g h) ?_
    have hm : ∀ a b : Aut U, (a * b).asIso.hom = b.asIso.hom ≫ a.asIso.hom := fun _ _ => rfl
    rw [hr (g * h), map_mul, hm, Category.assoc, reassoc_of% (hr h), hr g]
  have hinv : ∀ g, r g ≫ r g⁻¹ = 𝟙 X ∧ r g⁻¹ ≫ r g = 𝟙 X := fun g =>
    ⟨by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩
  exact ⟨{ toFun := fun g => Aut.of ⟨r g, r g⁻¹, (hinv g).1, (hinv g).2⟩
           map_one' := Aut.ext (Iso.ext hone)
           map_mul' := fun g h => Aut.ext (Iso.ext (hmul g h)) }, fun g => rfl⟩

theorem exists_action_of_extends {U X : Scheme.{0}} (j : U ⟶ X) (hj : ∀ a b : X ⟶ X, j ≫ a = j ≫ b → a = b)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).asIso.hom ≫ j) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).asIso.hom = r g :=
  exists_monoidHom_aut_of_lies j ρ₀ r hr (fun _ _ => True) trivial (fun _ => trivial) (fun _ _ => trivial)
    (fun _ a b _ _ h => hj a b h)

theorem exists_action_model_of_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) {Z : Scheme.{0}}
    (q : C.X ⟶ Z) {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left)
    (ν : ∀ g, SABMap t t (ρ₀ g).asIso.hom) (hβ : IsDedFrac β) (hq : IsIntegralHom q) (hν : ∀ g, (ν g).φ = (τ₀ g).asIso.hom)
    (hZ : ∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).asIso.hom ≫ C.j ≫ q)
    (hext : ∀ (r : U ⟶ U) (n : SABMap t t r) (f : C.X ⟶ C.X), C.j ≫ f = r ≫ C.j →
      ∃ mu : SABMap C.t C.t f, C.m.φ ≫ mu.φ = n.φ ≫ C.m.φ) :
    ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom),
      ∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧
        C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have : IsFractionRing O F := hfr
  obtain ⟨hnoeth, _, hsep, hpre, hflat, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have := hnoeth
  have := hsep
  have : QuasiCompact C.j := hqc
  have : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨-, -, hsd, -⟩ := densePart_basic C.X U C.j hpre hflat hdom hqc
  have : IsSchemeTheoreticallyDominant C.j := hsd ‹_›
  have hj1 : ∀ a b : C.X ⟶ C.X, C.j ≫ a = C.j ≫ b → a = b := fun a b h =>
    ExtUnique.hom_ext_of_dominant (terminal.from C.X) (terminal.hom_ext _ _) C.j h
  have hlift : ∀ g, ∃ a : C.X ⟶ C.X, C.j ≫ a = (ρ₀ g).asIso.hom ≫ C.j := by
    intro g
    obtain ⟨ρZ, hρZ⟩ := hZ g
    obtain ⟨a, ⟨ha, -⟩, -⟩ := existsUnique_lift_of_densePart C.X U Z C.X C.j C.normal hpre hflat hdom hqc
      q (q ≫ ρZ) ((ρ₀ g).asIso.hom ≫ C.j) hq (by rw [Category.assoc, hρZ])
    exact ⟨a, ha⟩
  choose r hr using hlift
  obtain ⟨ρ, hρ⟩ := exists_action_of_extends C.j hj1 ρ₀ r hr
  have hjρ : ∀ g, C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j := fun g => by rw [hρ]; exact hr g
  have hmu : ∀ g, ∃ mu : SABMap C.t C.t (ρ g).asIso.hom, C.m.φ ≫ mu.φ = (ν g).φ ≫ C.m.φ :=
    fun g => hext _ (ν g) _ (hjρ g)
  choose mu hmu using hmu
  obtain ⟨hGf, hGs⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian C.t.G C.t.semi
  have := hGf
  have := hGs
  have hcan : ∀ (e : C.X ≅ C.X) (a b : C.t.G.left ⟶ C.t.G.left), a ≫ C.t.G.hom = C.t.G.hom ≫ e.hom →
      b ≫ C.t.G.hom = C.t.G.hom ≫ e.hom → C.m.φ ≫ a = C.m.φ ≫ b → a = b := by
    intro e a b ha hb hab
    have : IsSeparated (Over.mk (C.t.G.hom ≫ e.inv)).hom := by
      show IsSeparated (C.t.G.hom ≫ e.inv)
      infer_instance
    have key := ExtUnique.over_hom_ext_of_isPullback (j := C.j) (X := C.t.G)
      (Y := Over.mk (C.t.G.hom ≫ e.inv)) C.m.cart.1
      (f := Over.homMk a (by simp [reassoc_of% ha])) (g := Over.homMk b (by simp [reassoc_of% hb])) hab
    exact congrArg (fun k => k.left) key
  have hw : ∀ g, (mu g).φ ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).asIso.hom := fun g => (mu g).cart.1.w
  obtain ⟨τ, hτ⟩ := exists_monoidHom_aut_of_lies C.m.φ τ₀ (fun g => (mu g).φ)
    (fun g => by rw [hmu, hν]) (fun g a => a ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).asIso.hom)
    (by rw [map_one]; exact (Category.id_comp _).trans (Category.comp_id _).symm) hw
    (fun g h => by
      show ((mu h).φ ≫ (mu g).φ) ≫ C.t.G.hom = C.t.G.hom ≫ (ρ (g * h)).asIso.hom
      have hm : ∀ a b : Aut C.X, (a * b).asIso.hom = b.asIso.hom ≫ a.asIso.hom := fun _ _ => rfl
      rw [map_mul, hm, Category.assoc, hw g, reassoc_of% (hw h)])
    (fun g a b ha hb hab => hcan (ρ g).asIso a b ha hb hab)
  refine ⟨ρ, τ, mu, fun g => ⟨(hτ g).symm, hjρ g, ?_⟩⟩
  rw [hτ]
  exact (hmu g).trans (by rw [hν])

theorem exists_action_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (C : Cpt c t β) (Z : Scheme.{0}) (q : C.X ⟶ Z) (Γ : Type) [Group Γ] [Finite Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ν : ∀ g, SABMap t t (ρ₀ g).asIso.hom), IsDedFrac β → Algebra.FiniteType ℤ O → IsProper t.G.hom → IsIntegralHom q → (∀ g, (ν g).φ = (τ₀ g).asIso.hom) → (∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).asIso.hom ≫ C.j ≫ q) → ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), ∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ := by
  intro hN E _ _ _ H U F O _ _ c t β C Z q Γ _ _ ρ₀ τ₀ ν hβ hfin hprop hq hν hZ
  exact exists_action_model_of_ext C q ρ₀ τ₀ ν hβ hq hν hZ
    (fun r n f h => Models.exists_sabMap_extending hN E H U F O c t β U F O c t β C C r n f hβ hfin hprop h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  first | exact @GlobalTheory.ModelOfOutput.exists_zOn | exact GlobalTheory.ModelOfOutput.exists_zOn | (intros; apply GlobalTheory.ModelOfOutput.exists_zOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodThetaObjectEmbeddingData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.GoodFibre

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap, Sp]

theorem exists_retraction {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, ψ.comp φ = RingHom.id K := by
  have hsurj : Function.Surjective (spMap φ) := by
    intro q
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, Subsingleton.elim _ _⟩
  haveI : Surjective (spMap φ) := ⟨hsurj⟩
  haveI : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, inferInstance⟩
  obtain ⟨ψ', hψ'⟩ := Spec.map_surjective (inv (spMap φ))
  refine ⟨ψ'.hom, ?_⟩
  have key : Spec.map (CommRingCat.ofHom φ ≫ ψ') = Spec.map (𝟙 _) := by
    rw [Spec.map_comp, hψ', Spec.map_id]
    exact IsIso.inv_hom_id (spMap φ)
  have := Spec.map_injective key
  ext a
  exact congrArg (fun f => f.hom a) this

theorem secCoord_of_local {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {K R' : Type} [Field K]
    [CommRing R'] {y : Sp K ⟶ X} {v : I → K} (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ)) (p : Sp K)
    (hp : p ∈ Set.range (spMap φ)) (h : SecCoord M th (spMap φ ≫ y) (fun i => φ (v i))) : SecCoord M th y v := by
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ p hp
  have h' := GlobalTheory.ZM.Coord.baseChange h ψ
  have e1 : spMap ψ ≫ spMap φ ≫ y = y := by
    rw [← Category.assoc, GlobalTheory.ZM.spMap_comp_ringHom_comp, hψ, spMap_id, Category.id_comp]
  have e2 : (fun i => ψ (φ (v i))) = v :=
    funext fun i => congrArg (fun f : K →+* K => f (v i)) hψ
  rw [e1, e2] at h'
  exact h'

theorem span_theta (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (n : ℕ) (v : Ix g (N' ^ 2) → K)
    (h2 : 2 ≤ n) (hn : n ∣ N') (hth : t.HasTh (𝟙 _) v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  have hc := GlobalTheory.coset_of_hasTh l1 l2 o g N' J b (Sp K) s t n K (𝟙 _) v q h2 hn hth hq.isPrime
  unfold Coset at hc
  obtain ⟨c, hc⟩ := hc 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem exists_fibData : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), ∃ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), FibData b Mat κ β v (n ^ 2) p hh Q d := by
  intro l1 l2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.cutBy_embedded_abelian l1 l2 g J Mat κ n hn hodd
  refine ⟨max j₁ 4, fun j hj o _ b R _ β v => ?_⟩
  have hjc : j₁ ≤ j := le_of_max_le_left hj
  have hj4 : 4 ≤ j := le_of_max_le_right hj
  have hoddN : Odd (n ^ j) := hodd.pow
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (by omega)
  have hdvd2 : (n ^ 2) ^ 2 ∣ n ^ j := by
    rw [← pow_mul]
    exact pow_dvd_pow n (by omega)
  have htwo : 2 ≤ n ^ 2 := le_trans hn.two_le (Nat.le_self_pow (by norm_num) n)
  obtain ⟨e, idx, hto⟩ := GlobalTheory.torsion_secCoord l1 l2 g (n ^ 2) (n ^ j) hoddN hdvd2
  obtain ⟨Hh, hfin, hh, Q, d, hcut⟩ := hj₁ j hjc o b
  refine ⟨fun h a => β (b.ζ ^ e a h : oˣ) * v (idx a h), Hh, hfin, hh, Q, d, ?_⟩
  intro K _ _ x s t hgood
  obtain ⟨hs, -, hth⟩ := hgood
  rw [GlobalTheory.ZM.spMap_comp_ringHom_comp] at hs
  subst hs
  obtain ⟨σ, hemb, hproj⟩ := _root_.GlobalTheory.ZM.EmbField.exists_emb_field l1 l2 o g (n ^ j) J b K _ t (n ^ 2) (fun a => x (v a)) hdvd2 htwo hth
  have hLB := (_root_.GlobalTheory.embSec_veryAmple_periodic l1 l2 o g (n ^ j) J b K (x.comp β) t (n ^ 2) σ hoddN hdvd htwo hemb).2.1
  have hspan : Ideal.span (Set.range fun a => x (v a)) = ⊤ :=
    span_theta l1 l2 t n (fun a => x (v a)) hn.two_le (dvd_pow_self n (by omega)) hth
  have hsec : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left
      (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
    intro h
    have hy : ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab h)
        = t.lab h := by
      ext
      simp
    obtain ⟨R', _, φ, hφ, hp, hc⟩ := hto o J b (Sp K) _ t K (x.comp β) (𝟙 _) (fun a => x (v a)) σ
      (Category.id_comp _) hth hspan hemb h _ (by rw [hy]) (IsLocalRing.closedPoint K)
    have key := secCoord_of_local hLB φ hφ _ hp hc
    have hv : (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h)))
        = (fun a => (x.comp β) (b.ζ ^ e a h : oˣ) * x (v (idx a h))) := by
      funext a
      simp
    rw [hv]
    exact key
  refine ⟨σ, _, hemb, hproj, ideals_homogeneous.1 _ _ _ _ _ _ σ _ hLB, ?_, hsec⟩
  exact hcut K (x.comp β) t σ _ hemb fun h => hsec (hh h)

end GlobalTheory.ZM.GoodFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace ModelJoin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isOpenImmersion_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) : IsOpenImmersion (spMap b) := by
  letI := b.toAlgebra
  exact IsOpenImmersion.of_isLocalization (R := O) (S := R) a

theorem mem_range_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) (x : Sp O) (hx : a ∉ x.asIdeal) :
    x ∈ Set.range (spMap b) := by
  letI := b.toAlgebra
  have := PrimeSpectrum.localization_away_comap_range R a
  have h2 : (x : PrimeSpectrum O) ∈ Set.range (PrimeSpectrum.comap (algebraMap O R)) := by
    rw [this]; exact hx
  exact h2

theorem arith_base (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra.FiniteType ℤ O] :
    LocallyOfFiniteType (spMap (algebraMap ℤ O)) ∧ Flat (spMap (algebraMap ℤ O)) := by
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

end ModelJoin

open ModelJoin

theorem exists_join_of_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  intro hext E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hω hspan hft hprop
  obtain ⟨⟨hdom, hded⟩, hchar, hfrac⟩ := id hβ
  obtain ⟨X, s, jQ, f, hn, hproj, hflat, hover, hopen, hdense, hf⟩ :=
    _root_.GlobalTheory.JoinModels.exists_join_scheme E H U F O c t β I R a b ω C hβ hω hspan hchar
  have hpo : IsPreimmersion (jQ ≫ pullback.fst s (spMap β)) ∧ Flat (jQ ≫ pullback.fst s (spMap β)) ∧
      IsDominant (jQ ≫ pullback.fst s (spMap β)) ∧ QuasiCompact (jQ ≫ pullback.fst s (spMap β)) := by
    letI := β.toAlgebra
    exact (genericPart_dense_proOpen O F X U s jQ hflat hproj hopen hdense).2.2.2
  have hβp : IsPreimmersion (spMap β) := by
    letI := β.toAlgebra
    exact IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  have hfp : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβp
  have hb : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => isOpenImmersion_away (a i) (b i) (hω i).2.2
  have hβe : ∀ i, spMap β = spMap (ω i) ≫ spMap (b i) := fun i => by
    rw [← (hω i).2.1]; exact Spec.map_comp (CommRingCat.ofHom (b i)) (CommRingCat.ofHom (ω i))
  have hsp : IsProper s := projProper O X s hproj
  let V : I → X.Opens := fun i => (pullback.fst s (spMap (b i))).opensRange
  let e : ∀ i, pullback s (spMap (b i)) ≅ (V i).toScheme := fun i =>
    (pullback.fst s (spMap (b i))).isoOpensRange
  have he : ∀ i, (e i).hom ≫ (V i).ι = pullback.fst s (spMap (b i)) := fun i =>
    Scheme.Hom.isoOpensRange_hom_ι _
  have hcov' : ∀ x : X, ∃ i, x ∈ Set.range (pullback.fst s (spMap (b i))) := by
    intro x
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hc
      push Not at hc
      refine (s x).isPrime.ne_top (top_le_iff.mp ?_)
      rw [← hspan, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hc i
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact mem_range_away (a i) (b i) (hω i).2.2 _ hi
  have hcov : ⨆ i, V i = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi⟩ := hcov' x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hw : ∀ i, (jQ ≫ pullback.fst s (spMap β)) ≫ s = (c ≫ spMap (ω i)) ≫ spMap (b i) := fun i => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hover, Category.assoc, ← hβe]
  let g : ∀ i, U ⟶ pullback s (spMap (b i)) := fun i => pullback.lift _ _ (hw i)
  have hg : ∀ i, g i ≫ pullback.fst _ _ = jQ ≫ pullback.fst s (spMap β) := fun i => pullback.lift_fst _ _ _
  choose tV mV using fun i => exists_pull ((e i).inv ≫ f i) (C i).t
  replace mV := fun i => (mV i).some
  choose t₁ k using fun i => exists_pull (e i).hom (tV i)
  replace k := fun i => (k i).some
  choose aV haV using fun i => cancel_of_eq (g := g i ≫ (e i).hom) (mV i) (C i).m (by
    rw [Category.assoc, Iso.hom_inv_id_assoc]; exact (hf i).2.1 _ (hg i))
  obtain ⟨hz₁, hz₂⟩ := arith_base O
  obtain ⟨t', a', n, hn'⟩ := _root_.GlobalTheory.exists_sab_glue_of_common_generic hext E H X U (jQ ≫ pullback.fst s (spMap β)) t I V
    (fun i => g i ≫ (e i).hom) tV aV inferInstance
    ⟨hn, s ≫ spMap (algebraMap ℤ O), inferInstance, inferInstance⟩ hpo.1 hpo.2.1 hpo.2.2.1 hpo.2.2.2 hprop hcov
    (fun i => by rw [Category.assoc, he, hg])
  choose m₁ hm₁ using fun i => comp_of_eq (n i) (k i) (he i)
  choose m₂ hm₂ using fun i => comp_of_eq (h := f i) (mV i) (k i) (Iso.hom_inv_id_assoc _ _)
  have hab : pullback.fst s (spMap β) ⁻¹' abLocus t'.G = Set.range jQ := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, w, hw'⟩ := hcov' (pullback.fst s (spMap β) z)
      have h1 : w ∈ abLocus (t₁ i).G :=
        (abLocus_pullback abLocusOne t'.semi (m₁ i).cart.1 w).1 (by rw [hw']; exact hz)
      have h2 : f i w ∈ abLocus (C i).t.G :=
        (abLocus_pullback abLocusOne (C i).t.semi (m₂ i).cart.1 w).2 h1
      have h3 : f i w ∈ Set.range (pullback.fst (C i).s (spMap (ω i))) := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨pullback.snd s (spMap β) z, (spMap (b i)).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, ← hβe, ← Scheme.Hom.comp_apply, ← pullback.condition,
          ← Scheme.Hom.comp_apply (f i), (hf i).1, ← Scheme.Hom.comp_apply, ← pullback.condition,
          Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw']
      obtain ⟨z', hz'⟩ := h3
      have h4 : z' ∈ Set.range (C i).jQ := by
        rw [← (C i).ab_gen]
        show _ ∈ abLocus (C i).t.G
        rw [hz']; exact h2
      obtain ⟨u, hu⟩ := h4
      obtain ⟨u', hu'⟩ := (hf i).2.2 w ⟨u, by rw [Cpt.j, Scheme.Hom.comp_apply, hu, hz']⟩
      refine ⟨u', (pullback.fst s (spMap β)).isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hu', hw']
    · rintro _ ⟨u, rfl⟩
      exact range_subset_abLocus_of_isProper t'.semi a'.cart.1 ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  refine ⟨⟨X, s, hn, hproj, hflat, jQ, hover, hopen, hdense, t', a', hab⟩, fun i => ?_⟩
  refine ⟨f i, t₁ i, m₁ i, m₂ i, (hf i).1, (hf i).2.1, fun y hy => ?_⟩
  have hmono : IsOpenImmersion (n i).φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n i).cart.1.flip inferInstance
  have hy' : y ≫ (k i).φ = (aV i).φ := by
    rw [← cancel_mono (n i).φ, Category.assoc, ← hm₁, hn']; exact hy
  rw [hm₂, ← Category.assoc, hy', haV]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem semiAbelian_model_determined_by_generic_fibre : ExtVStatement :=
  GlobalTheory.ModelUniqueChecks.extV_holds

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TraitDataOfDataAtTraits
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataOfIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section
variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem map_comp {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m' : SABMap t'' t' g) (m : SABMap t' t f)
    (h : g ≫ f = k) : ∃ n : SABMap t'' t k, n.φ = m'.φ ≫ m.φ := by
  subst h
  exact ObjMaps.exists_sab_comp m m'

theorem map_cancel {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (n : SABMap t'' t k) (m : SABMap t' t f)
    (h : g ≫ f = k) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst h
  exact ObjMaps.exists_sab_cancel m n

end

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.TraitDataOfIntrinsic
end

