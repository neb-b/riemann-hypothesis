module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0816
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTransfer

theorem spMap_comp_of {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_completion (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮.IsMaximal) :
    ∃ (T : Formalism.L2.Pj.CDVR) (a : 𝓞 K →+* T.V) (j : T.V →+* ℂ), j.comp a = σ.comp (algebraMap (𝓞 K) K) ∧
      ∀ x, a x ∈ IsLocalRing.maximalIdeal T.V ↔ x ∈ 𝔮 := by
  let la : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨𝔮, h𝔮.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔮 (RingOfIntegers.not_isField K)⟩
  obtain ⟨T, io, ho, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K la
  obtain ⟨em, hem⟩ := GlobalTheory.ComplexEmbedding.exists_embedding_fractionField K σ T hfin io
  have hv : ∀ x : K, Formalism.L2.Pj.valV T.V (io x) = la.valuation K x := fun x => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hex : ∀ x : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = io (algebraMap (𝓞 K) K x) := fun x =>
    GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (by
      rw [hv]; exact la.valuation_le_one x)
  choose f hf using hex
  have hinj := IsFractionRing.injective T.V T.Fr
  refine ⟨T, { toFun := f
               map_one' := hinj (by rw [hf, map_one, map_one, map_one])
               map_mul' := fun x y => hinj (by rw [map_mul, hf, hf, hf, map_mul, map_mul])
               map_zero' := hinj (by rw [hf, map_zero, map_zero, map_zero])
               map_add' := fun x y => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)]) },
    em.comp (algebraMap T.V T.Fr), RingHom.ext fun x => ?_, fun x => ?_⟩
  · change em (algebraMap T.V T.Fr (f x)) = σ (algebraMap (𝓞 K) K x)
    rw [hf, ← hem]; rfl
  · change f x ∈ _ ↔ _
    rw [← GlobalTheory.PlaceCompletion.valV_algebraMap_lt_one_iff (K' := T.Fr), hf, hv]
    exact la.valuation_lt_one_iff_mem x

theorem pow_eq_one_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (y : Over.mk (𝟙 S') ⟶ G') (z : Over.mk f ⟶ G)
    (e : z.left = y.left ≫ φ) (n : ℕ) : y ^ n = 1 ↔ z ^ n = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h (Over.mk (𝟙 S'))
  have key : ∀ {g : S' ⟶ S} (_ : g = f) (w : Over.mk g ⟶ G), w.left = z.left → (w ^ n = 1 ↔ z ^ n = 1) := by
    intro g hg w hw
    subst hg
    rw [Over.OverMorphism.ext hw]
  rw [← key (Category.id_comp f) (Φ y) ((hΦ y).trans e.symm), ← map_pow, MulEquiv.map_eq_one_iff]

noncomputable def restrict {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} (y : Over.mk (𝟙 S) ⟶ G) : Over.mk f ⟶ G :=
  (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 S)) ≫ y

theorem restrict_pow {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {y : Over.mk (𝟙 S) ⟶ G} {n : ℕ}
    (hy : y ^ n = 1) : restrict f y ^ n = 1 := by
  rw [restrict, ← MonObj.comp_pow, hy, MonObj.comp_one]

theorem exists_isGrpPullback_of_inertia : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  intro hFA hGM N _ P W _ r s hW q hq 𝔮 h𝔮 hq𝔮 hrs τ hτ A _ ψ hψ
  set i : 𝓞 N →+* ℂ := (algebraMap N ℂ).comp (algebraMap (𝓞 N) N) with hi
  have hinj : Function.Injective i := (algebraMap N ℂ).injective.comp (IsFractionRing.injective (𝓞 N) N)
  choose σ₀ hσ₀ hσ₁ using hτ
  have hσ : ∀ x, i (σ₀ x) = τ (i x) := hσ₀
  let σ : 𝓞 N →+* 𝓞 N :=
    { toFun := σ₀
      map_one' := hinj (by rw [hσ, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, hσ, hσ, hσ, map_mul, map_mul])
      map_zero' := hinj (by rw [hσ, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add (f := _), hσ, hσ, hσ, map_add (f := _), map_add (f := _)]) }
  obtain ⟨T, a, j, hj, ha⟩ := exists_completion N (algebraMap N ℂ) 𝔮 h𝔮
  let b : 𝓞 N →+* T.V := a.comp σ
  have hab : ∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T.V := fun x => by
    have := (ha _).2 (𝔮.neg_mem (hσ₁ x))
    rwa [neg_sub, map_sub] at this
  have hqT : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    have := (ha _).2 hq𝔮
    rwa [map_natCast] at this
  have hu : IsUnit (a (r - s)) := by
    by_contra h
    exact hrs ((ha _).1 h)
  obtain ⟨B, _, φ, hφ⟩ : ∃ (B : Over (Sp T.V)) (_ : GrpObj B) (φ : B.left ⟶ P.A.left),
      IsGrpPullback B P.A (spMap a) φ := ⟨_, inferInstance, _, isGrpPullback_pullback P.A (spMap a)⟩
  obtain ⟨φ', hφ', hred⟩ := _root_.GlobalTheory.PureTower.exists_isGrpPullback_of_congr hFA hGM (𝓞 N) P.A P.g P.isAb P.smoothDim W r s hW T.V T.cpl q hq hqT a b
    hab hu B φ hφ
  have ea : spMap j ≫ spMap a = spMap i := spMap_comp_of hj
  have eb : spMap j ≫ spMap b = spMap (τ : ℂ →+* ℂ) ≫ spMap i :=
    (spMap_comp_of (RingHom.ext fun x => (RingHom.congr_fun hj (σ x)).trans (hσ x))).trans
      (spMap_comp_of (f := i) (g := (τ : ℂ →+* ℂ)) rfl).symm
  have er : spMap (IsLocalRing.residue T.V) ≫ spMap a = spMap (IsLocalRing.residue T.V) ≫ spMap b :=
    (spMap_comp_of (RingHom.ext fun x => Ideal.Quotient.eq.2 (hab x))).trans
      (spMap_comp_of (f := b) (g := IsLocalRing.residue T.V) rfl).symm
  have w₁ : ψ ≫ P.A.hom = (A.hom ≫ spMap j) ≫ spMap a := by rw [Category.assoc, ea, hψ.1.w]
  obtain ⟨χ, hχ₁, hχ₂⟩ : ∃ χ : A.left ⟶ B.left, χ ≫ φ = ψ ∧ χ ≫ B.hom = A.hom ≫ spMap j :=
    ⟨hφ.1.lift _ _ w₁, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  have hχ : IsGrpPullback A B (spMap j) χ := hφ.cancel (hψ.congr ea.symm hχ₁.symm) hχ₂
  have hc := (hχ.comp hφ').congr eb rfl
  have w₂ : (χ ≫ φ') ≫ P.A.hom = (A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap i := by rw [hc.1.w, Category.assoc]
  obtain ⟨io, hio₁, hio₂⟩ : ∃ io : A.left ⟶ A.left, io ≫ ψ = χ ≫ φ' ∧ io ≫ A.hom = A.hom ≫ spMap (τ : ℂ →+* ℂ) :=
    ⟨hψ.1.lift _ _ w₂, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  refine ⟨io, hψ.cancel (hc.congr rfl hio₁.symm) hio₂, fun n hn y hy x hx₁ hx₂ => ?_⟩
  have hnu : IsUnit (n : T.V) := by
    by_contra h
    have h' : (n : T.V) ∈ IsLocalRing.maximalIdeal T.V := h
    have hc : IsCoprime (q : T.V) (n : T.V) := by
      simpa using (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom T.V)
    obtain ⟨u, v, huv⟩ := hc
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2
      (huv ▸ add_mem (Ideal.mul_mem_left _ u hqT) (Ideal.mul_mem_left _ v h')))
  have hyw : y.left ≫ P.A.hom = 𝟙 (Sp (𝓞 N)) := Over.w y
  have w₃ : (spMap a ≫ y.left) ≫ P.A.hom = 𝟙 (Sp T.V) ≫ spMap a := by
    rw [Category.assoc, hyw, Category.comp_id, Category.id_comp]
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Sp T.V ⟶ B.left, t ≫ φ = spMap a ≫ y.left ∧ t ≫ B.hom = 𝟙 _ :=
    ⟨hφ.1.lift _ _ w₃, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  let yT : Over.mk (𝟙 (Sp T.V)) ⟶ B := Over.homMk t ht₂
  have hyT : yT ^ n = 1 := (pow_eq_one_iff hφ yT (restrict (spMap a) y) ht₁.symm n).2 (restrict_pow _ hy)
  let z : Over.mk (spMap b) ⟶ P.A := Over.homMk (t ≫ φ') (by
    change (t ≫ φ') ≫ P.A.hom = spMap b
    rw [Category.assoc, hφ'.1.w, reassoc_of% ht₂])
  have hz : z ^ n = 1 := (pow_eq_one_iff hφ' yT z rfl n).1 hyT
  have hzy : z = restrict (spMap b) y := _root_.GlobalTheory.TorsionReduction.eq_of_residue_eq (𝓞 N) P T.V b n hnu z _ hz (restrict_pow _ hy) (by
    change spMap (IsLocalRing.residue T.V) ≫ t ≫ φ' = spMap (IsLocalRing.residue T.V) ≫ spMap b ≫ y.left
    rw [← Category.assoc, ← hred _ (by rw [Category.assoc, ht₂, Category.comp_id]), Category.assoc, ht₁,
      reassoc_of% er])
  have hzy' : t ≫ φ' = spMap b ≫ y.left := congrArg (fun u => u.left) hzy
  have hxχ : x ≫ χ = spMap j ≫ t := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, hχ₁, hx₂, Category.assoc, ht₁, reassoc_of% ea]
    · rw [Category.assoc, hχ₂, reassoc_of% hx₁, Category.assoc, ht₂, Category.comp_id]
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hio₁, reassoc_of% hxχ, hzy', reassoc_of% eb, Category.assoc, hx₂]
  · rw [Category.assoc, hio₂, reassoc_of% hx₁, Category.assoc, hx₁, Category.comp_id]

end GlobalTheory.InertiaTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalCoefficientCoinvariantEq
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Topology

noncomputable section

namespace GlobalTheory.UnipCoefInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (a b : ℕ) (s : kˣ) : Set (Fin a → Fin b → k) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => cball s

theorem mem_box {a b : ℕ} {s : kˣ} {X : Fin a → Fin b → k} :
    X ∈ box a b s ↔ ∀ p q, X p q ∈ cball s := by
  simp [box, Set.mem_univ_pi]

theorem isOpen_box (a b : ℕ) (s : kˣ) : IsOpen (box a b s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s

theorem isCompact_box (a b : ℕ) (s : kˣ) : IsCompact (box a b s) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s

theorem box_mono {a b : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    box a b s ⊆ box a b t := by
  intro X hX
  rw [mem_box] at hX ⊢
  intro p q
  exact le_trans (show valuation k (X p q) ≤ valuation k (s : k) from hX p q) h

theorem add_mem_box_iff {a b : ℕ} {s : kˣ} {X Y : Fin a → Fin b → k} (hY : Y ∈ box a b s) :
    X + Y ∈ box a b s ↔ X ∈ box a b s := by
  rw [mem_box] at hY
  simp only [mem_box, Pi.add_apply]
  constructor
  · intro h p q
    simpa using add_mem_cball (h p q) (neg_mem_cball (hY p q))
  · intro h p q
    exact add_mem_cball (h p q) (hY p q)

theorem exists_mem_box {a b : ℕ} (X : Fin a → Fin b → k) : ∃ s : kˣ, X ∈ box a b s := by
  set γ : ValueGroupWithZero k := ∏ pq : Fin a × Fin b, max 1 (valuation k (X pq.1 pq.2)) with hγ
  have h1 : ∀ pq ∈ (Finset.univ : Finset (Fin a × Fin b)), 1 ≤ max 1 (valuation k (X pq.1 pq.2)) :=
    fun _ _ => le_max_left _ _
  have hγ1 : 1 ≤ γ := Finset.one_le_prod' h1
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective γ
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy ▸ hγ1) (by simp)
  refine ⟨Units.mk0 y hy0, mem_box.mpr fun p q => ?_⟩
  show valuation k (X p q) ≤ valuation k y
  rw [hy]
  exact (le_max_right _ _).trans (Finset.single_le_prod' h1 (Finset.mem_univ (p, q)))

theorem directed_box (a b : ℕ) : Directed (· ⊆ ·) (box (k := k) a b) := by
  intro s t
  rcases le_total (valuation k (s : k)) (valuation k (t : k)) with h | h
  · exact ⟨t, box_mono h, subset_rfl⟩
  · exact ⟨s, subset_rfl, box_mono h⟩

theorem exists_subset_box {a b : ℕ} {K : Set (Fin a → Fin b → k)} (hK : IsCompact K) :
    ∃ s : kˣ, K ⊆ box a b s :=
  hK.elim_directed_cover _ (isOpen_box a b) (fun X _ => Set.mem_iUnion.mpr (exists_mem_box X))
    (directed_box a b)

section Meas
variable [MeasurableSpace k] [BorelSpace k]

theorem main : ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro N V _ _ π hπ a b μ hμ u hu hadd l w hw F hF hFw
  haveI := secondCountable k
  haveI := t2Space k
  haveI : OpensMeasurableSpace (Fin b → k) := inferInstance
  haveI : OpensMeasurableSpace (Fin a → Fin b → k) := inferInstance
  have hu0 : u 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

  have hcont : ∀ y : V, Continuous fun X => l (π (u X) y) := by
    intro y
    have hlc : IsLocallyConstant fun X => π (u X) y := by
      refine (IsLocallyConstant.iff_eventually_eq _).mpr fun X₀ => ?_
      have hO : IsOpen ((fun X => u (X - X₀)) ⁻¹' {g | π g y = y}) :=
        (hπ y).preimage (hu.comp (continuous_id.sub continuous_const))
      have hX₀ : X₀ ∈ (fun X => u (X - X₀)) ⁻¹' {g | π g y = y} := by
        simp [hu0]
      filter_upwards [hO.mem_nhds hX₀] with X hX
      have hX' : π (u (X - X₀)) y = y := hX
      have e : X = X₀ + (X - X₀) := by abel
      rw [e, hadd, map_mul, Module.End.mul_apply, hX']
    exact (hlc.comp l).continuous
  have hmeas : ∀ s : kˣ, MeasurableSet (box a b s) := fun s => (isOpen_box a b s).measurableSet
  have hint : ∀ (y : V) (s : kˣ), IntegrableOn (fun X => l (π (u X) y)) (box a b s) μ :=
    fun y s => (hcont y).continuousOn.integrableOn_compact (isCompact_box a b s)

  have hshift : ∀ (y : V) (s : kˣ) (Y : Fin a → Fin b → k), Y ∈ box a b s →
      ∫ X in box a b s, l (π (u (X + Y)) y) ∂μ = ∫ X in box a b s, l (π (u X) y) ∂μ := by
    intro y s Y hY
    rw [← integral_indicator (hmeas s), ← integral_indicator (hmeas s)]
    have : ∀ X, (box a b s).indicator (fun X => l (π (u (X + Y)) y)) X =
        (box a b s).indicator (fun X => l (π (u X) y)) (X + Y) := by
      intro X
      by_cases hX : X ∈ box a b s
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem ((add_mem_box_iff hY).mpr hX)]
      · rw [Set.indicator_of_notMem hX,
          Set.indicator_of_notMem (fun h => hX ((add_mem_box_iff hY).mp h))]
    simp only [this]
    exact integral_add_right_eq_self (μ := μ) (fun X => (box a b s).indicator (fun X => l (π (u X) y)) X) Y

  have key : ∀ w' ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y},
      ∃ s₀ : kˣ, ∀ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) →
        ∫ X in box a b s, l (π (u X) w') ∂μ = 0 := by
    intro w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, y, rfl⟩ := hx
      obtain ⟨s₀, hs₀⟩ := exists_mem_box Y
      refine ⟨s₀, fun s hs => ?_⟩
      have hY : Y ∈ box a b s := box_mono hs hs₀
      have e : ∀ X, l (π (u X) (π (u Y) y - y)) = l (π (u (X + Y)) y) - l (π (u X) y) := by
        intro X
        rw [map_sub, map_sub, hadd, map_mul, Module.End.mul_apply]
      simp only [e]
      have hi2 : IntegrableOn (fun X => l (π (u (X + Y)) y)) (box a b s) μ :=
        ((hcont y).comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact (isCompact_box a b s)
      rw [integral_sub hi2 (hint y s), hshift y s Y hY, sub_self]
    | zero => exact ⟨1, fun s _ => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨s₁, h₁⟩ := hx
      obtain ⟨s₂, h₂⟩ := hz
      rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
      · refine ⟨s₂, fun s hs => ?_⟩
        simp only [map_add (f := _)]
        rw [integral_add (hint x s) (hint z s), h₁ s (h.trans hs), h₂ s hs, add_zero]
      · refine ⟨s₁, fun s hs => ?_⟩
        simp only [map_add (f := _)]
        rw [integral_add (hint x s) (hint z s), h₁ s hs, h₂ s (h.trans hs), add_zero]
    | smul c x _ hx =>
      obtain ⟨s₀, h₀⟩ := hx
      refine ⟨s₀, fun s hs => ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [integral_const_mul, h₀ s hs, mul_zero]
  obtain ⟨s₀, hs₀⟩ := key w hw
  obtain ⟨s₁, hs₁⟩ := exists_subset_box hF
  obtain ⟨s, hs0, hs1⟩ : ∃ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) ∧
      box a b s₁ ⊆ box a b s := by
    rcases le_total (valuation k (s₀ : k)) (valuation k (s₁ : k)) with h | h
    · exact ⟨s₁, h, subset_rfl⟩
    · exact ⟨s₀, le_rfl, box_mono h⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := box a b s)
    (fun X hX => image_eq_zero_of_notMem_tsupport (fun h => hX (hs1 (hs₁ h))))]
  simp only [hFw]
  exact hs₀ s hs0

end Meas

theorem integral_coef_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro k _ _ _ _ _ _
  exact main

end GlobalTheory.UnipCoefInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteMulByNatAbelianVariety
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulFinite

theorem isFinite_mul : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ n : ℕ, 1 ≤ n → IsFinite (𝟙 A ^ n : A ⟶ A).left := by
  intro k _ _ B _ hB n hn1
  have hG := GlobalTheory.laws_without_cohomology.1
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hq : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn1
  have hproj := _root_.GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (LB.isLB_pull hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := _root_.GlobalTheory.UU.lbIso_pw_pull_pow_local k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  exact _root_.GlobalTheory.PullAmpleFinite.isFinite_of_pull_iso_pow k _ _ B.hom _ H H m s (n ^ 2) hH hH inferInstance (by rw [hφ]; exact hs) hq hiso

end GlobalTheory.MulFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_stalkMap {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) :
    gm r z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm (𝟙 X) (r z) U a) := by
  apply Units.ext
  rw [gm_val r z U h, Units.coe_map, gm_val (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a.val).symm

theorem pull_isLB_of_isOn : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X), IsOn W L → (∀ z, r z ∈ W) →
    (L.pull r).IsLB := by
  intro X Z W L r hL hr
  have coc : ∀ (z : Z) (a b c : L.ι), r z ∈ L.U a → r z ∈ L.U b → r z ∈ L.U c →
      gm r z _ (L.g a b) * gm r z _ (L.g b c) = gm r z _ (L.g a c) := by
    intro z a b c ha hb hc
    rw [gm_eq_stalkMap r z (L.U a ⊓ L.U b) ⟨ha, hb⟩, gm_eq_stalkMap r z (L.U b ⊓ L.U c) ⟨hb, hc⟩,
      gm_eq_stalkMap r z (L.U a ⊓ L.U c) ⟨ha, hc⟩, ← map_mul,
      hL.coc (r z) a b c ha hb hc]
  refine ⟨?_, ?_, ?_⟩
  · refine top_le_iff.1 fun z _ => ?_
    obtain ⟨a, ha⟩ := hL.cov (r z) (hr z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => a, mem_pull.2 ha⟩
  · intro J
    refine unit_ext fun z hz => ?_
    rw [gm_res (𝟙 Z) z _ hz, map_one, gm_pull_g L r (𝟙 Z) z J J hz hz, Category.id_comp]
    have hJ := mem_pull.1 hz
    exact mul_eq_left.1 (coc z _ _ _ hJ hJ hJ)
  · intro I J K
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_pull_g L r (𝟙 Z) z I J hz.1.1 hz.1.2,
      gm_pull_g L r (𝟙 Z) z J K hz.1.2 hz.2, gm_pull_g L r (𝟙 Z) z I K hz.1.1 hz.2, Category.id_comp]
    exact coc z _ _ _ (mem_pull.1 hz.1.1) (mem_pull.1 hz.1.2) (mem_pull.1 hz.2)

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSnd
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_app_iso_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) (V : Z.Opens)
    (h : Function.Bijective (g.app V).hom) : Function.Bijective ((f ≫ g).app V).hom := by
  have : IsIso (g.app V) := (ConcreteCategory.isIso_iff_bijective _).2 h
  have : IsIso (f.app (g ⁻¹ᵁ V)) := inferInstance
  have : IsIso ((f ≫ g).app V) := by
    rw [Scheme.Hom.comp_app]; exact IsIso.comp_isIso' ‹_› ‹_›
  exact ConcreteCategory.bijective_of_isIso _

theorem fnBij_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  intro S A T _ hA V
  have e : (snd A T).left = (β_ A T).hom.left ≫ (fst T A).left := by
    rw [← Over.comp_left, braiding_hom_fst]
  have : IsIso (β_ A T).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (β_ A T).hom))
  rw [e]
  exact bijective_app_iso_comp _ _ V
    (GlobalTheory.CubeLawCompare.bijective_app_fst GlobalTheory.SemiRigid.globalFns hA T V)

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoordsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  first | (exact @GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (exact GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (intros; apply GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig  <;> assumption)
end

