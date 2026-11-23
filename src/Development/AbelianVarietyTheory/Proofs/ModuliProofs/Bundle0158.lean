module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientModelByTameFiniteGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.QuotModel

theorem injective_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Function.Injective β := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  exact IsFractionRing.injective O F

theorem mono_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) : Mono (spMap β) := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  have : Epi (CommRingCat.ofHom β) := ⟨fun {Z} g₁ g₂ hg => by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (j := g₁.hom) (k := g₂.hom) ?_
    have e := congrArg CommRingCat.Hom.hom hg
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    exact e⟩
  exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom β).op

theorem mem_range_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : Function.Injective β) (p : Sp O) :
    p ∈ Set.range (spMap β) ↔ p.asIdeal = ⊥ := by
  have hk : RingHom.ker β = ⊥ := (RingHom.injective_iff_ker_eq_bot β).mp h
  constructor
  · rintro ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    show Ideal.comap β q.asIdeal = ⊥
    rw [hq, ← RingHom.ker_eq_comap_bot, hk]
  · intro hp
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap β ⊥ = p.asIdeal
    rw [hp, ← RingHom.ker_eq_comap_bot, hk]

theorem densePart {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) {X U : Scheme.{0}}
    (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (h₁ : Flat s) (h₂ : IsProjOver s) (h₃ : IsOpenImmersion jQ)
    (h₄ : Dense (Set.range jQ)) :
    IsLocallyNoetherian X ∧ genericPoints X ⊆ Set.range (jQ ≫ pullback.fst _ _ : U ⟶ X) ∧
      ∀ u : U, IsIso ((jQ ≫ pullback.fst _ _ : U ⟶ X).stalkMap u) := by
  obtain ⟨⟨hdom, hded⟩, -, hfr⟩ := h
  let _ := β.toAlgebra
  obtain ⟨hN, -, -, hpre, hfl, hdo, hqc⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ h₁ h₂ h₃ h₄
  obtain ⟨hg, hst, -⟩ := GlobalTheory.densePart_basic X U _ hpre hfl hdo hqc
  exact ⟨hN, hg, hst⟩

private theorem isReduced_of_isNormalScheme' (X : Scheme.{0}) (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

end GlobalTheory.QuotModel


open GlobalTheory.QuotModel in
theorem GlobalTheory.Models.exists_quotient_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst C.t.G.hom x ≫ (τ g).asIso.hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' Γ _ _ C b k r ν ρ₀ τ₀ ρ τ mu hβ hβ' hcomp hfin hrc hr hprop hmu hqp
    htame hin hgood hpush

  have sq : ∀ {S S' : Scheme.{0}} {ta : SAB H S} {tb : SAB H S'} {f : S ⟶ S'} (m : SABMap ta tb f),
      m.φ ≫ tb.G.hom = ta.G.hom ≫ f := fun m => m.cart.1.w
  have sqm : C.m.φ ≫ C.t.G.hom = t.G.hom ≫ C.j := sq C.m

  obtain ⟨X', π, s', jQ, hπ, hπfin, hπs, hnorm, hproj, hflat, hjover, hjopen, hjdense, hjc, hgen⟩ :=
    GlobalTheory.exists_quotient_model_scheme E H U F O c t β Γ C U' F' O' c' β' b k r ρ₀ ρ hβ hβ' hcomp hfin hrc hr
      (fun g => (hmu g).2.1)
  obtain ⟨hN', -, -⟩ := densePart hβ' s' jQ hflat hproj hjopen hjdense
  obtain ⟨-, hgenC, hstC⟩ := densePart hβ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hredX : IsReduced C.X := isReduced_of_isNormalScheme' _ C.normal
  have hgab : genericPoints C.X ⊆ abLocus C.t.G := by
    intro x hx
    obtain ⟨u, rfl⟩ := hgenC hx
    have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
      rw [C.ab_gen]; exact ⟨u, rfl⟩
    exact hu

  obtain ⟨t₁, ν', hν'τ, hgood'⟩ :=
    _root_.GlobalTheory.exists_sab_descent_of_tame_quotient E H Γ O C.X X' ρ π C.t C.s τ mu hπ hπfin hqp ⟨hredX, hgab⟩ (fun g => (hmu g).1) htame hin
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' C.m
  have key : ∀ (f : U ⟶ X') (n : SABMap t t₁ f), f = r ≫ jQ ≫ pullback.fst _ _ →
      ∃ n' : SABMap t t₁ (r ≫ jQ ≫ pullback.fst _ _), n'.φ = n.φ := by
    rintro f n rfl; exact ⟨n, rfl⟩
  obtain ⟨n₂, hn₂⟩ := key _ n hjc.symm

  have hredU : IsReduced U := by
    have : ∀ u : U, _root_.IsReduced (U.presheaf.stalk u) := by
      intro u
      have hI : IsIso ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u) := hstC u
      exact isReduced_of_injective (inv ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u)).hom
        (ConcreteCategory.bijective_of_isIso _).1
    exact isReduced_of_isReduced_stalk U
  have hmono : Mono C.j := by
    have := mono_spMap hβ
    have := C.jQ_open
    dsimp only [Cpt.j]; infer_instance
  have hτ : ∀ g, (τ₀ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ₀ g).asIso.hom ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ ∧
      (τ₀ g).asIso.hom ≫ n₂.φ = n₂.φ := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hmu g
    refine ⟨(cancel_mono C.j).mp ?_, h4, ?_⟩
    · calc ((τ₀ g).asIso.hom ≫ t.G.hom) ≫ C.j = ((τ₀ g).asIso.hom ≫ C.m.φ) ≫ C.t.G.hom := by
            simp only [Category.assoc]; rw [← sqm]
        _ = (C.m.φ ≫ (mu g).φ) ≫ C.t.G.hom := by rw [← h3, h1]
        _ = C.m.φ ≫ C.t.G.hom ≫ (ρ g).asIso.hom := by simp only [Category.assoc]; rw [sq (mu g)]
        _ = t.G.hom ≫ C.j ≫ (ρ g).asIso.hom := by rw [← Category.assoc, sqm, Category.assoc]
        _ = (t.G.hom ≫ (ρ₀ g).asIso.hom) ≫ C.j := by rw [h2, Category.assoc]
    · rw [hn₂, hn, ← Category.assoc, ← h3, Category.assoc, hν'τ g]
  obtain ⟨m', hm'⟩ := _root_.GlobalTheory.exists_sabMap_of_quotient E H Γ U U' X' ρ₀ r t t' t₁ τ₀ ν _ n₂ hr hredU hprop hτ

  have hπsurj : Function.Surjective π := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ C.X X' ρ π hπ).2.1.surj
  have hrsurj : Function.Surjective r := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ U U' ρ₀ r hr).2.1.surj
  have habπ : ∀ x, π x ∈ abLocus t₁.G ↔ x ∈ abLocus C.t.G := fun x =>
    abLocus_pullback abLocusOne t₁.semi ν'.cart.1 x

  have hbint : ∀ p : Sp O, (spMap b p).asIdeal = ⊥ → p.asIdeal = ⊥ := by
    intro p hp
    obtain ⟨⟨hdO, -⟩, -, -⟩ := hβ
    obtain ⟨⟨hdO', -⟩, -, -⟩ := hβ'
    let _ := b.toAlgebra
    have h2 : IsFinite (Spec.map (CommRingCat.ofHom b)) := hfin
    rw [IsFinite.SpecMap_iff] at h2
    have : Module.Finite O' O := h2
    have : Algebra.IsIntegral O' O := inferInstance
    exact Ideal.eq_bot_of_comap_eq_bot (R := O') hp
  have hpre : Function.Injective (pullback.fst s' (spMap β')) := by
    obtain ⟨-, -, hfr'⟩ := hβ'
    let _ := β'.toAlgebra
    have : IsPreimmersion (spMap β') := IsPreimmersion.of_isLocalization (nonZeroDivisors O')
    exact (pullback.fst s' (spMap β')).isEmbedding.injective
  have hab : pullback.fst s' (spMap β') ⁻¹' abLocus t₁.G = Set.range jQ := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx⟩ := hπsurj (pullback.fst s' (spMap β') w)
      have hxab : x ∈ abLocus C.t.G := (habπ x).1 (by rw [hx]; exact hw)
      have hs' : (s' (pullback.fst s' (spMap β') w)).asIdeal = ⊥ := by
        have e : s' (pullback.fst s' (spMap β') w) = spMap β' (pullback.snd s' (spMap β') w) := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        rw [e]
        exact (mem_range_spMap (injective_of_isDedFrac hβ') _).1 ⟨_, rfl⟩
      have hsx : (C.s x).asIdeal = ⊥ := by
        apply hbint
        have e : spMap b (C.s x) = s' (π x) := by
          rw [← Scheme.Hom.comp_apply, ← hπs, Scheme.Hom.comp_apply]
        rw [e, hx]
        exact hs'
      obtain ⟨q, hq⟩ := (mem_range_spMap (injective_of_isDedFrac hβ) (C.s x)).2 hsx
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.s) (g := spMap β) x q hq.symm
      have hz : z ∈ Set.range C.jQ := by
        rw [← C.ab_gen]
        show pullback.fst C.s (spMap β) z ∈ abLocus C.t.G
        rw [hz1]
        exact hxab
      obtain ⟨u, rfl⟩ := hz
      obtain ⟨u', hu'⟩ := (hgen x).2 ⟨u, hz1⟩
      exact ⟨u', hpre (hu'.trans hx)⟩
    · rintro ⟨u', rfl⟩
      obtain ⟨u, rfl⟩ := hrsurj u'
      have e : pullback.fst s' (spMap β') (jQ (r u)) = π (C.j u) := by
        have h5 := congrArg (fun f : U ⟶ X' => f u) hjc
        simpa only [Scheme.Hom.comp_apply] using h5
      show pullback.fst s' (spMap β') (jQ (r u)) ∈ abLocus t₁.G
      rw [e, habπ]
      have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
        rw [C.ab_gen]; exact ⟨u, rfl⟩
      exact hu
  refine ⟨⟨X', s', hnorm, hproj, hflat, jQ, hjover, hjopen, hjdense, t₁, m', hab⟩, hgood' hgood hpush,
    ⟨⟨π, hπs, ?_, ν', hjc.symm, ?_⟩⟩⟩
  · refine MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _ (pullback.fst s' (spMap b))
      inferInstance ?_
    rw [pullback.lift_fst]
    exact hπfin
  · rw [hm', hn₂, hn]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionNeZeroFibreOfGenericSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericSection
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem exists_ker_ne_zero {R K K' : Type} [CommRing R] [Field K] [Field K'] (g : R →+* K) (g' : R →+* K')
    (hg : Function.Injective g) {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (h : (D.map g).mulVec v = 0) : ∃ v' : Fin a → K', v' ≠ 0 ∧ (D.map g').mulVec v' = 0 := by
  by_contra hno
  push Not at hno
  have hind : LinearIndependent K' (fun j : Fin a => fun i : Fin b => (D.map g') i j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hc0
    push Not at hc0
    have hc' : c ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := hc0
      exact hj (by rw [h0]; rfl)
    apply hno c hc'
    funext i
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨e, -, he⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent K' b (Fin a) _ hind
  have hdet : (D.submatrix e id).det ≠ 0 := by
    intro h0
    apply he
    have : (Matrix.of fun k j => (D.map g') (e k) j) = (D.submatrix e id).map g' := by
      ext k j
      rfl
    have hm := RingHom.map_det g' (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm, h0, map_zero]
  have hdetK : ((D.map g).submatrix e id).det ≠ 0 := by
    have : (D.map g).submatrix e id = (D.submatrix e id).map g := rfl
    have hm := RingHom.map_det g (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm]
    exact fun h0 => hdet (hg (by rw [h0, map_zero]))
  apply hv
  apply Matrix.eq_zero_of_mulVec_eq_zero hdetK
  funext k
  have := congrFun h (e k)
  simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using this

def zeroSec {X : Scheme.{0}} (M : LB X) : LB.Sec M where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem exists_sec_iff {X X' Y : Scheme.{0}} {L : LB Y} {p : X ⟶ Y} {R R' : Type} [CommRing R] [CommRing R']
    {f : X ⟶ Spec (CommRingCat.of R)} (F : Perf f (L.pull p)) (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {q : X' ⟶ Y} (e : q = π ≫ p) :
    (∃ (s : (L.pull q).Sec) (j : _), s.f j ≠ 0) ↔ ∃ v : Fin F.a → R', v ≠ 0 ∧ (F.D₀.map g).mulVec v = 0 := by
  subst e
  unfold LB.pull at F ⊢
  let c : R' →+* Γ(X', ⊤) := f'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
  obtain ⟨h1, h2, h3⟩ := SecBC.rep_main (F := F) (ψ := fun _ => π ≫ p) (fun _ => rfl) g f' H c (fun _ => rfl)
  have h0 : SecBC.Rep π (fun _ => π ≫ p) F c 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))).f := by
    have hs := SecBC.Rep.sum (F := F) (ψ := fun _ => π ≫ p) (c := c) (fun _ => rfl) (I := Empty)
      (w := Empty.elim) (b := Empty.elim) (fun l => l.elim) Empty.elim
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
    exact hs
  constructor
  · rintro ⟨s, j, hs⟩
    obtain ⟨v, hv, hrep⟩ := h2 s
    refine ⟨v, fun hv0 => hs ?_, hv⟩
    subst hv0
    rw [SecBC.Rep.sec_eq (fun _ => rfl) hrep h0]
    rfl
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨s, hs⟩ := h1 v hv
    by_contra hno
    push Not at hno
    apply hv0
    have hz : s = zeroSec _ := SecBC.sec_ext (fun j => hno s j)
    rw [hz] at hs
    exact h3 v 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))) hv (Matrix.mulVec_zero _) hs h0

theorem exists_ringHom {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (t : Sp R ⟶ S) [IsOpenImmersion t]
    (x : Sp K ⟶ S) (h : Set.range x ⊆ Set.range t) :
    ∃ g : R →+* K, Spec.map (CommRingCat.ofHom g) ≫ t = x := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift t x h)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac t x h

theorem exists_isPullback {A S T T' : Scheme.{0}} (a : A ⟶ S) (t : T ⟶ S) (u : T' ⟶ T) (x : T' ⟶ S)
    (h : u ≫ t = x) : ∃ π : pullback a x ⟶ pullback a t,
      IsPullback π (pullback.snd a x) (pullback.snd a t) u ∧ pullback.fst a x = π ≫ pullback.fst a t := by
  subst h
  have hc : pullback.fst a (u ≫ t) ≫ a = (pullback.snd a (u ≫ t) ≫ u) ≫ t := by
    rw [pullback.condition, Category.assoc]
  refine ⟨pullback.lift _ _ hc, ?_, (pullback.lift_fst _ _ hc).symm⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback a t)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback a (u ≫ t)

theorem exists_sec_ne_zero_of_generic : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  intro hLaws S _ P N K K' _ _ x y s hN hx hs
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y (IsLocalRing.closedPoint K') ∈ (⊤ : S.Opens) from trivial)
  let t : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hrange : Set.range t = W := hW.range_fromSpec
  have hgen : genericPoint S ∈ (W : Set S) := by
    rw [(genericPoint_spec S).mem_open_set_iff W.isOpen]
    exact ⟨_, trivial, hyW⟩
  have : Nonempty W := ⟨⟨_, hyW⟩⟩
  have hxr : Set.range x ⊆ Set.range t := by
    rw [hx, hrange]
    simpa using hgen
  have hyr : Set.range y ⊆ Set.range t := by
    rintro _ ⟨z, rfl⟩
    rw [hrange, Subsingleton.elim z (IsLocalRing.closedPoint K')]
    exact hyW
  obtain ⟨gx, hgx⟩ := exists_ringHom t x hxr
  obtain ⟨gy, hgy⟩ := exists_ringHom t y hyr
  have hinj : Function.Injective gx := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hne : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hr0⟩
    have hop : IsOpen (t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W)))) :=
      t.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen r).isOpen
    have hg2 : genericPoint S ∈ t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))) := by
      rw [(genericPoint_spec S).mem_open_set_iff hop]
      obtain ⟨q, hq⟩ := hne
      exact ⟨_, trivial, q, hq, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hg2
    have hxpt : x (IsLocalRing.closedPoint K) = genericPoint S := by
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      exact hm
    have hq2 : q = Spec.map (CommRingCat.ofHom gx) (IsLocalRing.closedPoint K) := by
      apply t.isOpenEmbedding.injective
      rw [hqe, ← hxpt, ← hgx]
      rfl
    rw [hq2] at hq
    apply (PrimeSpectrum.mem_basicOpen _ _).1 hq
    show r ∈ (PrimeSpectrum.comap gx (IsLocalRing.closedPoint K)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hr]
    exact zero_mem _
  have H0 : IsPullback (pullback.fst P.A.hom t) (pullback.snd P.A.hom t) P.A.hom t :=
    IsPullback.of_hasPullback _ _
  obtain ⟨n, -, m, σ, hlb, hva⟩ := polAV_veryAmpleBy hLaws.polBaseChange S P Γ(S, W) t _ _ _ H0
  have : Smooth P.A.hom := by
    have := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g P.A.hom
  have hproj : IsProjBy (pullback.snd P.A.hom t) := ⟨_, hlb, m, σ, hva⟩
  obtain ⟨F⟩ := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy Γ(S, W) _ (pullback.snd P.A.hom t) inferInstance hproj
    (N.pull (pullback.fst P.A.hom t)) (LB.isLB_pull hN _)
  obtain ⟨πx, hπx, hex⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gx)) x hgx
  obtain ⟨πy, hπy, hey⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gy)) y hgy
  obtain ⟨v, hv, hker⟩ := (exists_sec_iff F gx hπx hex).1 ⟨s, hs⟩
  obtain ⟨v', hv', hker'⟩ := exists_ker_ne_zero gx gy hinj F.D₀ v hv hker
  exact (exists_sec_iff F gy hπy hey).2 ⟨v', hv', hker'⟩

end GlobalTheory.GenericSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelLevelOneDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.RaisedDescends

theorem map_nsmul_eq_pow {A Q : Type*} [AddMonoid A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (m : ℕ) (a : A) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.mp h
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (_root_.GlobalTheory.BaseRing.isDedFrac_RZ E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem Cpt_j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem levComp_comp {D : Datum H} {l l' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    (m : ObjMap o'' o' g) {ν : SABMap o'.t o.t r} (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r))
    (e : ν'.φ = m.toSABMap.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := h.1 a
    rw [← map_nsmul_eq_pow _ o'.eta_add] at h1
    rw [← map_nsmul_eq_pow _ o''.eta_add, e, ← Category.assoc, m.eta, Category.assoc, h1, Category.assoc]
  · have h1 := h.2 a
    rw [← map_nsmul_eq_pow _ o'.etaA_add] at h1
    rw [← map_nsmul_eq_pow _ o''.etaA_add, e, ← Category.assoc, m.etaA, Category.assoc, h1, Category.assoc]

theorem descends_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  intro h1 h2 h3 E _ _ _ H D Xo n N T hN l₀ B l c O _ β Y hn hd hA hβ hR
  obtain ⟨b, r, ν, hb, hlev, ⟨a⟩⟩ := hR
  obtain ⟨k, r₁, ν₁, hr₁, hk, hlev₁, hfin, -⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN l₀ l hd
  have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
  have hD₀ : IsDedFrac B.β := isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc
  have hD₁ : IsDedFrac (k.comp B.β) :=
    isDedFrac_of_isInc l _ 1 hS hA rfl _ fun x => (hk (B.β x)).trans (B.β_inc x)
  have hsm : Smooth (Xo l).s := by
    have := (Xo l).smooth
    exact SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨C', ⟨a'⟩⟩ := _root_.GlobalTheory.Models.Cpt.exists_above E H _ _ _ _ _ B.β _ _ _ (Xo l).s (Xo l).univ.t (k.comp B.β) B.C (RingHom.id _) k r₁ hr₁ ν₁
    hD₀ hD₁ (RingHom.comp_id _)
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1 hfin
  have hbβ : β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp (k.comp B.β) := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hred : IsReduced ((Xo l).XF c) :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (pullback.snd _ _) inferInstance).1
  obtain ⟨ν₂, hν₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₁ Y.m0.toSABMap
  have hover : r ≫ (Xo l₀).s = (pullback.fst _ _ ≫ r₁) ≫ (Xo l₀).s := by
    have := mono_spMap_of_isDedFrac hD₀
    rw [← cancel_mono (spMap B.β), Category.assoc, ← Cpt_j_over B.C, ← Category.assoc, ← a.j_comm, Category.assoc,
      a.π_over, ← Category.assoc, Cpt_j_over, Category.assoc, ← spMap_comp, hbβ, spMap_comp, spMap_comp,
      Category.assoc, Category.assoc, reassoc_of% hr₁, pullback.condition_assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique h1 h2 h3 E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r _ ν ν₂ hred hover hlev
    (levComp_comp Y.m0 hlev₁ ν₂ hν₂)
  obtain ⟨h, mu', hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C C' (ofModel Y) (RingHom.id _) b (IntermediateField.inclusion c.le).toRingHom r₁ ν₁ a' (pullback.fst _ _)
    Y.m0.toSABMap a.π a.mu a.π_over hβ hbβ pullback.condition
    (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₂, Category.assoc])
  exact GlobalTheory.descends_of_above E H D l (Xo l) c O β Y _ (k.comp B.β) C' b ⟨h, hh, hf a.fin, mu', hj, hφ⟩ hD₁ hβ hbβ

end GlobalTheory.RaisedDescends

end
end

