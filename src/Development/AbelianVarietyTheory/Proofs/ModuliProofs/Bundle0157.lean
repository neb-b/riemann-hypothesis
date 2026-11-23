module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0153
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassIsSymmOfLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZM.GraphMor

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_chart_two {Y X₁ X₂ : Scheme.{0}} {σ₁ σ₂ : Type} {M₁ : LB X₁} {M₂ : LB X₂} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂) (t : Y) :
    ∃ (A : Type) (_ : CommRing A) (y : Sp A ⟶ Y) (_ : IsOpenImmersion y) (v₁ : σ₁ → A) (v₂ : σ₂ → A),
      t ∈ Set.range y ∧ SecCoord M₁ th₁ (y ≫ a₁) v₁ ∧ SecCoord M₂ th₂ (y ≫ a₂) v₂ := by
  obtain ⟨W, hW, j, hj, ht, hc⟩ := RepUniq.exists_affine_secCoord h₁ th₁ a₁ t
  obtain ⟨t', rfl⟩ : t ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact ht
  obtain ⟨W', hW', j', hj', ht', hc'⟩ := RepUniq.exists_affine_secCoord h₂ th₂ (hW.fromSpec ≫ a₂) t'
  obtain ⟨t'', rfl⟩ : t' ∈ Set.range hW'.fromSpec := by rw [hW'.range_fromSpec]; exact ht'
  obtain ⟨β, hβ⟩ := RepUniq.exists_spMap (R := Γ(Y, W)) (A := Γ(Spec Γ(Y, W), W')) hW'.fromSpec
  have hb := Coord.baseChange hc β
  rw [← hβ] at hb
  exact ⟨Γ(Spec Γ(Y, W), W'), inferInstance, hW'.fromSpec ≫ hW.fromSpec,
    (inferInstance : IsOpenImmersion (hW'.fromSpec ≫ hW.fromSpec)), _, _, ⟨t'', rfl⟩, hb, hc'⟩

theorem exists_coord_field {X : Scheme.{0}} {σ : Type} {M : LB X} (h : M.IsLB) (th : σ → M.Sec) {K : Type} [Field K]
    (y : Sp K ⟶ X) : ∃ v, SecCoord M th y v := by
  let t : Sp K := (default : PrimeSpectrum K)
  obtain ⟨j, hj⟩ := LB.mem_of_cover h (y t)
  have hle : (⊤ : (Sp K).Opens) ≤ y ⁻¹ᵁ M.U j := fun t' _ => by
    obtain rfl : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hj
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((y.appLE _ ⊤ hle).hom ((th i).f j)),
    RepUniq.secCoord_of_frame h ⟨j, hle, 1, isUnit_one, fun i => ?_⟩⟩
  simp [RepUniq.fn]

theorem hom_ext_chart {Y X : Scheme.{0}} (a b : Y ⟶ X)
    (h : ∀ t : Y, ∃ (T : Scheme.{0}) (y : T ⟶ Y) (_ : IsOpenImmersion y), t ∈ Set.range y ∧ y ≫ a = y ≫ b) : a = b := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨T, y, _, ht, e⟩ := h t
  refine ⟨y.opensRange, ht, ?_⟩
  rw [← y.isoOpensRange_inv_comp, Category.assoc, Category.assoc, e]

theorem exists_common_field {R K K' : Type} [CommRing R] [Field K] [Field K'] (x : R →+* K) (β : R →+* K')
    (h : RingHom.ker x = RingHom.ker β) :
    ∃ (L : Type) (_ : Field L) (a : K' →+* L) (b : K →+* L), spMap a ≫ spMap β = spMap b ≫ spMap x := by
  let t : Sp K := (default : PrimeSpectrum K)
  let t' : Sp K' := (default : PrimeSpectrum K')
  have e : spMap β t' = spMap x t := PrimeSpectrum.ext (by
    rw [VeryDenseFibres.spMap_apply_asIdeal, VeryDenseFibres.spMap_apply_asIdeal, h])
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap β) (g := spMap x) t' t e
  let L : Type := (pullback (spMap β) (spMap x)).residueField z
  obtain ⟨a, ha⟩ := RepUniq.exists_spMap (R := K') (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.fst _ _)
  obtain ⟨b, hb⟩ := RepUniq.exists_spMap (R := K) (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.snd _ _)
  refine ⟨L, inferInstance, a, b, ?_⟩
  rw [← ha, ← hb, Category.assoc, Category.assoc, pullback.condition]

theorem smooth_of_veryDense {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) [IsProper s] [Flat s]
    [LocallyOfFinitePresentation s] {P : Set (Ideal R)} (hP : VeryDense P)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ Smooth (pullback.snd s (spMap x))) :
    Smooth s := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine VeryDenseFibres.eq_top_of_forall_mem s P (fun q hq => ?_) _ fun z hz => ?_
  · obtain ⟨p, h1, h2, h3, -⟩ := hP q 1 hq ((Ideal.ne_top_iff_one _).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  · obtain ⟨K, _, x, hx, hs⟩ := h _ hz
    let w : Sp K := (default : PrimeSpectrum K)
    have hw : s z = spMap x w := PrimeSpectrum.ext (by rw [VeryDenseFibres.spMap_apply_asIdeal, hx])
    refine VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    exact VeryDenseFibres.smooth_fiber_of_smooth_fiber s (spMap x) w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s (spMap x)) ((Sp K).fromSpecResidueField w))))

theorem dense_of_veryDense {R : Type} [CommRing R] {P : Set (Ideal R)} (hP : VeryDense P) :
    Dense {q : Sp R | q.asIdeal ∈ P} := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ ⟨q, hq⟩
  obtain ⟨p, h1, h2, -, h4⟩ := hP q.asIdeal f q.isPrime hq
  exact ⟨⟨p, h2⟩, h4, h1⟩

theorem exists_pair {S Y : Scheme.{0}} (Z₁ Z₂ : Over S) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left)
    (h : a₁ ≫ Z₁.hom = a₂ ≫ Z₂.hom) :
    ∃ c : Y ⟶ (Z₁ ⊗ Z₂).left, c ≫ (fst Z₁ Z₂).left = a₁ ∧ c ≫ (snd Z₁ Z₂).left = a₂ :=
  ⟨pullback.lift a₁ a₂ h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem mem_of_components {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {F : MvPolynomial σ R}
    (h : ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) : F ∈ I := by
  rw [← MvPolynomial.sum_homogeneousComponent F]
  exact Ideal.sum_mem _ fun e _ => h e

theorem eval_eq_zero_of_mem_idealOf {R σ : Type} [CommRing R] {Y : Scheme.{0}} {s : Y ⟶ Sp R} {M : LB Y}
    {th : σ → M.Sec} {F : MvPolynomial σ R} (hF : F ∈ idealOf s M th (𝟙 Y)) {T : Type} [CommRing T] {β : R →+* T}
    {y : Sp T ⟶ Y} {v : σ → T} (hy : y ≫ s = spMap β) (hv : SecCoord M th y v) : MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf] at hF
  exact hF T inferInstance β y v ⟨hy, by rwa [Category.comp_id]⟩

theorem exists_hom_of_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (f : _), RingHom.ker x = q ∧ G K x f} → ∃ F : Z₁ ⟶ Z₂, ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f = pullback.fst _ _ ≫ F.left := by
  intro R σ₁ σ₂ Hh _ _ _ _ _ _ Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h₁ h₂ hp₁ hp₂ hsm hG hP
  obtain ⟨Γ', M, th, hΓ, -, hflat, hlfp, hfib⟩ := _root_.GlobalTheory.ZM.FlatFamily.exists_flat_projRep_vanIdeal R (σ₁ × σ₂) Hh
    (fun h i => p₁ h i.1 * p₂ h i.2) Q d
    (fun K _ x I => ∃ f, G K x f ∧
      I = graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f)
    (by
      rintro K _ x _ ⟨f, hf, rfl⟩
      exact ⟨ideals_homogeneous.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.1 h₂.1, (hG K x f hf).2⟩)
    (fun q r hq hr => by
      obtain ⟨p, ⟨K, _, x, f, hx, hf⟩, hp⟩ := hP q r hq hr
      exact ⟨p, ⟨K, _, x, _, hx, f, hf, rfl⟩, hp⟩)
  have hpr : IsProper Γ'.hom := (projRep_projective_ample R _ _ Γ' M th hΓ).2.1

  have good : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧
      ∀ (T : Type) [CommRing T] (y : Sp T ⟶ pullback Z₁.hom (spMap x)) (v₁ : σ₁ → T) (v₂ : σ₂ → T),
        SecCoord M₁ th₁ (y ≫ pullback.fst _ _) v₁ → SecCoord M₂ th₂ (y ≫ f) v₂ →
        SecCoord M th (y ≫ φ) (fun i => v₁ i.1 * v₂ i.2) := by
    intro K _ x f hf
    obtain ⟨N, ty, hN, hc⟩ := _root_.GlobalTheory.ZM.GraphSegre.projRep_graph R K σ₁ σ₂ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ _ (pullback.snd _ _)
      (pullback.fst _ _) f h₁ h₂ (IsPullback.of_hasPullback _ _) (hG K x f hf).1
    obtain ⟨φ, hφ, -, hφc⟩ := hfib K x _ _ _ N ty ⟨f, hf, rfl⟩ hN
    exact ⟨φ, hφ, fun T _ y v₁ v₂ e₁ e₂ => (hφc T y _).1 (hc T y v₁ v₂ e₁ e₂)⟩
  have hsmΓ : Smooth Γ'.hom := smooth_of_veryDense Γ'.hom hP (by
    rintro _ ⟨K, _, x, f, rfl, hf⟩
    obtain ⟨φ, hφ, -⟩ := good K x f hf
    refine ⟨K, _, x, rfl, ?_⟩
    rw [← hφ.isoPullback_inv_snd]
    infer_instance)
  have hred : IsReduced Γ'.left := GlobalTheory.isReduced_of_smooth_of_isReduced Γ'.hom
  obtain ⟨I₃, M₃, th₃, h₃', hseg⟩ := SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ h₁ h₂
  have h₃ := ideals_homogeneous.2.2 R _ _ _ _ _ _ h₃'
  have w₁ : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  have w₂ : (snd Z₁ Z₂).left ≫ Z₂.hom = (Z₁ ⊗ Z₂).hom := Over.w _

  have hle : idealOf (Z₁ ⊗ Z₂).hom M₃ th₃ (𝟙 _) ≤ idealOf Γ'.hom M th (𝟙 _) := fun F hF => by
    refine mem_of_components fun e => ?_
    refine DenseFib.mem_idealOf_of_dense R _ _ _ M th _ _ e hred hflat hlfp hΓ.1 (dense_of_veryDense hP)
      (MvPolynomial.homogeneousComponent_isHomogeneous e F) ?_
    intro K' _ _ β y v hy hβ hv
    have hF' := ideals_homogeneous.1 R _ _ _ _ _ _ _ h₃.1 F hF e
    obtain ⟨K, _, x, f, hx, hf⟩ := hβ ⟨(default : PrimeSpectrum K'), rfl⟩
    rw [VeryDenseFibres.spMap_apply_asIdeal] at hx
    obtain ⟨L, _, a, b, hab⟩ := exists_common_field x β hx
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    have hw : (spMap a ≫ y) ≫ Γ'.hom = spMap b ≫ spMap x := by rw [Category.assoc, hy, hab]
    let z := hφ.lift _ _ hw
    obtain ⟨v₁, hv₁⟩ := exists_coord_field h₁.1 th₁ (z ≫ pullback.fst _ _)
    obtain ⟨v₂, hv₂⟩ := exists_coord_field h₂.1 th₂ (z ≫ f)
    have hz := hc L z v₁ v₂ hv₁ hv₂
    rw [hφ.lift_fst] at hz
    obtain ⟨u, hu⟩ := Coord.unique hΓ.1 hz (Coord.baseChange hv a)
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have hs := Coord.scale (hseg L (z ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])) u
    have hb : (z ≫ c) ≫ (Z₁ ⊗ Z₂).hom = spMap (a.comp β) := by
      rw [spMap_comp_hom, hab, ← w₁, Category.assoc, reassoc_of% g₁, pullback.condition, hφ.lift_snd_assoc]
    have h0 := eval_eq_zero_of_mem_idealOf hF' hb hs
    apply a.injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h0]
    congr 1
    exact funext hu
  obtain ⟨g, hg, -, hgc, -⟩ := RepMap.exists_map_of_coord R _ _ _ _ _ Γ'.hom M₃ M th₃ th h₃ hΓ.1
    (fun T _ β y v hy hv => ⟨(hΓ.2.1 T β y v hy hv).1, fun F hF => eval_eq_zero_of_mem_idealOf (hle hF) hy hv⟩)
  have fib : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧ φ ≫ g ≫ (fst Z₁ Z₂).left = pullback.fst _ _ ∧
      φ ≫ g ≫ (snd Z₁ Z₂).left = f := by
    intro K _ x f hf
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have e : φ ≫ g = c := hom_ext_chart _ _ fun t => by
      obtain ⟨A, _, y, hy, v₁, v₂, ht, hv₁, hv₂⟩ := exists_chart_two h₁.1 h₂.1 th₁ th₂ (pullback.fst _ _) f t
      refine ⟨_, y, hy, ht, ?_⟩
      have c₁ := (hgc A _ _).1 (hc A y v₁ v₂ hv₁ hv₂)
      have c₂ := hseg A (y ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])
      obtain ⟨β, hβ⟩ := RepUniq.exists_spMap ((y ≫ c) ≫ (Z₁ ⊗ Z₂).hom)
      obtain ⟨k₁, k₂⟩ := h₃.2.1 A β _ _ hβ c₂
      rw [← Category.assoc]
      refine (h₃.2.2 A β _ k₁ k₂).unique ⟨?_, c₁⟩ ⟨hβ, c₂⟩
      rw [← hβ, Category.assoc, hg, Category.assoc, hφ.w, Category.assoc, ← w₁, reassoc_of% g₁, pullback.condition]
    exact ⟨φ, hφ, by rw [reassoc_of% e, g₁], by rw [reassoc_of% e, g₂]⟩
  have hπ : (g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom = Γ'.hom := by rw [Category.assoc, w₁, hg]
  have hππ : IsProper ((g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom) := hπ ▸ hpr
  have hiso : IsIso (g ≫ (fst Z₁ Z₂).left) := DenseFibreIso.main R _ _ Z₁.hom _ _ hP hp₁ inferInstance
    (IsProper.of_comp _ Z₁.hom) (hπ ▸ hflat) (by
      rintro _ ⟨K, _, x, f, rfl, hf⟩
      obtain ⟨φ, hφ, e₁, -⟩ := fib K x f hf
      refine ⟨K, _, x, rfl, ?_⟩
      have hq : IsPullback φ (𝟙 _) (g ≫ (fst Z₁ Z₂).left) (pullback.fst Z₁.hom (spMap x)) :=
        IsPullback.of_bot (by rwa [Category.id_comp, hπ]) (by rw [e₁, Category.id_comp])
          (IsPullback.of_hasPullback Z₁.hom (spMap x))
      rw [← hq.isoPullback_inv_snd]
      infer_instance)
  refine ⟨Over.homMk (inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left) ?_, fun K _ x f hf => ?_⟩
  · rw [Category.assoc, Category.assoc, w₂, hg, ← hπ, IsIso.inv_hom_id_assoc]
  · obtain ⟨φ, -, e₁, e₂⟩ := fib K x f hf
    change f = pullback.fst _ _ ≫ inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left
    rw [← e₁, Category.assoc, IsIso.hom_inv_id_assoc, e₂]

end GlobalTheory.ZM.GraphMor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricallyConnectedAwayOfFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ConnSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  refine ⟨fun U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩ => ?_⟩
  by_contra hne
  let O : Bool → Y.Opens := fun i => bif i then ⟨U, hU⟩ else ⟨W, hW⟩
  have hd : O true ⊓ O false = ⊥ := le_bot_iff.1 fun y hy => hne ⟨y, trivial, hy⟩
  have hcov : ⨆ i, O i = ⊤ := top_unique fun y _ => by
    rcases hc (Set.mem_univ y) with h | h
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩
  obtain ⟨s, hs⟩ := TLinPf.glue O hcov (fun i => bif i then 1 else 0) (fun i j => by
    have sub : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT => by
      subst hT; infer_instance
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm)
  rcases H s with h | h
  · have h₁ : u ∈ Y.basicOpen s := (mem_basicOpen_rs (le_top : O true ≤ ⊤) s hu).1 (by
      rw [show rs Y (le_top : O true ≤ ⊤) s = 1 from hs true]
      exact mem_of_isUnit isUnit_one hu)
    rw [h] at h₁
    exact h₁
  · have h₁ := (mem_basicOpen_rs (le_top : O false ≤ ⊤) s hw).2 (h.ge (Set.mem_univ w))
    rw [show rs Y (le_top : O false ≤ ⊤) s = 0 from hs false, Scheme.basicOpen_zero] at h₁
    exact h₁

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

theorem exists_geometricallyConnected_away_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ GeometricallyConnected (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s K _ x hp hs hc
  have hp' : IsProjBy s := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := isProper_of_isProjBy R Z s hp'
  have h₀ : IsPullback (pullback.fst s (spMap x)) (pullback.snd s (spMap x)) s
      (Spec.map (CommRingCat.ofHom x)) := IsPullback.of_hasPullback _ _
  have hbij := bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K _
    (pullback.snd s (spMap x)) inferInstance inferInstance hc
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀, -⟩ := (pullback.snd s (spMap x)).surjective (⊥ : PrimeSpectrum K)
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul K (0 : Fin P.a → K), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector x P.D₀ v hv0 (hline hbij.2)
  let p : PrimeSpectrum R := s ((pullback.fst s (spMap x)) x₀)
  have hpx : ∀ a : R, a ∉ p.asIdeal → x a ≠ 0 := fun a ha h0 => by
    have e : p = Spec.map (CommRingCat.ofHom x) (pullback.snd s (spMap x) x₀) :=
      congrArg (fun t => t x₀) h₀.w
    apply ha
    rw [e]
    change x a ∈ (pullback.snd s (spMap x) x₀).asIdeal
    rw [h0]
    exact zero_mem _
  obtain ⟨_, ⟨ε, rfl⟩, hε, hεs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (Set.range s : Set (PrimeSpectrum R)) from ⟨_, rfl⟩) s.isOpenMap.isOpen_range
  refine ⟨δ * ε, by rw [map_mul]; exact mul_ne_zero hδ (hpx ε hε), ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap (Localization.Away (δ * ε)) F).comp (algebraMap R _)
  have hg : IsUnit (g δ * g ε) := by
    rw [← map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (δ * ε)) (δ * ε)).map
      (algebraMap (Localization.Away (δ * ε)) F)
  have h' : IsPullback (fst ≫ pullback.fst s (spMap (algebraMap R (Localization.Away (δ * ε))))) snd s
      (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s _)
    rwa [← Spec.map_comp] at this
  have hmem : Spec.map (CommRingCat.ofHom g) (⊥ : PrimeSpectrum F) ∈ Set.range s :=
    hεs fun h0 : g ε ∈ (⊥ : Ideal F) => (isUnit_of_mul_isUnit_right hg).ne_zero h0
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨y, -⟩ := Scheme.exists_preimage_of_isPullback h' z _ hz
  have := preconnectedSpace_of_line P h' _ (hker F _ (isUnit_of_mul_isUnit_left hg))
  exact ⟨⟨y⟩⟩

end GlobalTheory.ConnSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_level_quotient_by_finite_group : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left :=
  GlobalTheory.LevQuot.exists_level_quotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8FormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) [IsLocallyNoetherian S] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.RelAmple G L → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  first | exact @GlobalTheory.PowerForm.relAmple_diag | exact GlobalTheory.PowerForm.relAmple_diag | (intros; apply GlobalTheory.PowerForm.relAmple_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentInjectsSymmetricAntilinearCommuting
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS

theorem tangent_injects_symm_antilinear : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))), (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∃ (t₀ : TObj g k J b (spMap (algebraMap o ℂ))) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ) (κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ), GoodU u Hm χ ∧ (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) ∧ Function.Injective κ ∧ ∀ D, IsSymm Hm (κ D) ∧ ∀ (f : t.A ⟶ t.A) (f₀ : t₀.pol.A ⟶ t₀.pol.A) (F : (Fin t₀.pol.g → ℂ) →ₗ[ℂ] (Fin t₀.pol.g → ℂ)), f₀.left ≫ m = m ≫ f.left → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm (κ D) F := by
  intro h1 h2 hU o _ g k J b R _ _ _ _ _ t hun
  have hcomp : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [IsScalarTower.algebraMap_eq o R ℂ]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap o R)) (CommRingCat.ofHom (algebraMap R ℂ))).symm
  obtain ⟨t₀, m, hm⟩ := _root_.GlobalTheory.tObj_pull o g k J b _ _ _ _ (spMap (algebraMap R ℂ)) t hcomp
  obtain ⟨u, Hm, χ, hG, -⟩ := _root_.GlobalTheory.KSInh.exists_goodU_ksRel hU t₀.pol
  have hsm : Smooth t.A.hom := by
    haveI := t.dim
    exact SmoothOfRelativeDimension.smooth g _
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.KS.Lin.ks_linear t₀.pol u Hm χ hG o R t.A.left t.A.hom m hsm hm.1.1
  refine ⟨t₀, m, u, Hm, χ, κ, hG, hm, ?_, fun D => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro D hD
    obtain ⟨s, hs⟩ := hκ D
    rw [hD] at hs
    exact _root_.GlobalTheory.KS.KerZero.derivation_eq_zero_of_ks_zero h1 h2 hU o g k J b R t _ t₀ m u Hm χ hG hm hun D s hs
  · obtain ⟨s, hs⟩ := hκ D
    refine ⟨_root_.GlobalTheory.KS.isSymm_of_lift t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs t.L t.isLB hm.2.1, ?_⟩
    intro f f₀ F hf hF
    exact _root_.GlobalTheory.KS.Endo.comm_of_endo t₀.pol u Hm χ hG R _ t.A.left t.A.hom m hsm hm.1.1 _ _ s hs f.left f₀ F (Over.w f) hf hF

end GlobalTheory.KS
end

