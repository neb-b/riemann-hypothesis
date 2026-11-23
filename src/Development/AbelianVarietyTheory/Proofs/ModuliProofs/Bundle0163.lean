module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomNearGoodPrimeOfGraphs
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biadditive_of_trivial_on_axes : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → ∀ (Pb : LB (G2 A).left), Pb.IsLB → (∃ t : (Pb.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Pb.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen := by
  first | exact @GlobalTheory.Biadditive.biadditive_of_triv_axes | exact GlobalTheory.Biadditive.biadditive_of_triv_axes | (intros; apply GlobalTheory.Biadditive.biadditive_of_triv_axes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem cube_of_exists_relAmple {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {H₀ : LB B.left} (hH : H₀.IsLB) (hamp : Out.RelAmple B H₀)
    {M : LB B.left} (hM : M.IsLB) : ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have hG := GlobalTheory.laws_without_cohomology.1
  exact GlobalTheory.Biadditive.triv_of_faces hG hB hH hamp hM (thφ B (x3 B)) thε
    (fun r i b h => GlobalTheory.AbLaw.CubeGen.trivAt_of_formal hM r (GlobalTheory.AbLaw.CubeGen.prod_face r i b h))
    (fun r b h U _ k => GlobalTheory.AbLaw.CubeGen.prod_face r 0 b h U k)

theorem cube_of_relAmple :
    ∀ (S : Scheme.{0}) [IsReduced S] (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ t : LB.Gen (Theta B M), t.IsGen := fun _ _ _ _ _ _ hB hM hamp => cube_of_exists_relAmple hB hM hamp hM

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawLocal

theorem dense_affine {S X : Scheme.{0}} (f : X ⟶ S) (N : LB X) {R : Type} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion j]
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K),
      p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen}) :
    Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ pullback f j) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' (pullback.snd f j) (Spec.map (CommRingCat.ofHom g)) ∧
      Triv ((N.pull (pullback.fst f j)).pull π)} := by
  refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
  rintro q ⟨K, hK, x, Y, ρ, h, ⟨z, hz⟩, hpb, c, hc⟩
  have hsub : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    exact ⟨q, by rw [Subsingleton.elim w z]; exact hz.symm⟩
  obtain ⟨x', hx'⟩ : ∃ x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), x' ≫ j = x :=
    ⟨IsOpenImmersion.lift j x hr, IsOpenImmersion.lift_fac j x hr⟩
  have hmap : Spec.map (CommRingCat.ofHom (Spec.preimage x').hom) = x' := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨K, hK, (Spec.preimage x').hom, Y,
    pullback.lift ρ (h ≫ x') (by rw [hpb.w, Category.assoc, hx']), h, ?_, ?_, ?_⟩
  · have h1 : j (x' z) = j q := by rw [← hz, ← hx']; rfl
    have h2 : x' z = q := j.isOpenEmbedding.injective h1
    have h3 : Spec.map (Spec.preimage x') z = q := by rw [Spec.map_preimage]; exact h2
    rw [← h3]
    change RingHom.ker (Spec.preimage x').hom =
      Ideal.comap (Spec.preimage x').hom (z : PrimeSpectrum K).asIdeal
    rw [@Ideal.eq_bot_of_prime K _ (z : PrimeSpectrum K).asIdeal (z : PrimeSpectrum K).isPrime]
    exact RingHom.ker_eq_comap_bot _
  · rw [hmap]
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)
    rw [pullback.lift_fst, hx']
    exact hpb
  · apply CubeOpen.triv_pull_pull
    rw [pullback.lift_fst]
    exact ⟨c, hc⟩

theorem triv_locally_of_dense : ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ c : (N.pull (f ⁻¹ᵁ U).ι).Gen, c.IsGen := by
  intro S₀ B _ M hA hM hRel S X _ t π f N hpb hN hd s
  obtain ⟨R, j, hj, ⟨pt, hpt⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := s) (U := ⊤) trivial
  have hRed : _root_.IsReduced R := by
    have := isReduced_of_isOpenImmersion j
    exact (affine_isReduced_iff R).mp inferInstance
  have hsq : IsPullback (pullback.fst f j ≫ π) (pullback.snd f j) B.hom (j ≫ t) :=
    (IsPullback.of_hasPullback f j).paste_horiz hpb
  obtain ⟨hP, hSm, hPr, hGI⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral
    S₀ B M hA hM hRel R (j ≫ t) _ _ _ hsq
  obtain ⟨r, hr, H⟩ := SeesawReduced.triv_locally_of_dense R (pullback f j) (pullback.snd f j)
    (N.pull (pullback.fst f j)) (pull_isLB hN _) hSm hPr hGI hP (dense_affine f N j hd) pt
  set p : PrimeSpectrum R := pt with hp
  have h0 : p ∈ PrimeSpectrum.basicOpen r := hr
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at h0
  obtain ⟨w, hw⟩ := h0
  obtain ⟨j', hj'⟩ : ∃ j' : Spec (CommRingCat.of (Localization.Away r)) ⟶ S,
      j' = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ j := ⟨_, rfl⟩
  have hjo : IsOpenImmersion j' := by rw [hj']; infer_instance
  refine ⟨j'.opensRange, ?_, ?_⟩
  · show s ∈ Set.range j'
    refine ⟨w, ?_⟩
    rw [hj']
    change j ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) w) = s
    rw [← hpt]
    exact congrArg j hw
  · have hU : IsPullback (f ⁻¹ᵁ j'.opensRange).ι (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        f j' := by
      have hb : IsPullback j'.opensRange.ι j'.isoOpensRange.inv (𝟙 S) j' :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      simpa using (isPullback_morphismRestrict f j'.opensRange).flip.paste_vert hb
    obtain ⟨π₀, h₁, h₂⟩ : ∃ π₀ : (f ⁻¹ᵁ j'.opensRange).toScheme ⟶ pullback f j,
        π₀ ≫ pullback.fst f j = (f ⁻¹ᵁ j'.opensRange).ι ∧
        π₀ ≫ pullback.snd f j = (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) :=
      ⟨pullback.lift _ _ (by rw [hU.w]; simp only [Category.assoc]; rw [← hj']), pullback.lift_fst _ _ _,
        pullback.lift_snd _ _ _⟩
    have hsq' : IsPullback π₀ (morphismRestrict f j'.opensRange ≫ j'.isoOpensRange.inv)
        (pullback.snd f j) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
      refine IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback f j)
      rw [h₁, ← hj']
      exact hU
    obtain ⟨c, hc⟩ := H (Localization.Away r) (algebraMap R (Localization.Away r)) _ π₀ _ hsq'
      (IsLocalization.Away.algebraMap_isUnit r)
    obtain ⟨d, hd'⟩ := GlobalTheory.exists_isGen_linComb_of_pull N _ _ π₀ c hc
    exact CubeOpen.triv_comp (f := π₀ ≫ pullback.fst f j) (𝟙 _) (by rw [Category.id_comp, h₁]) ⟨d, hd'⟩

end GlobalTheory.SeesawLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem exists_hom_of_graphs_of_isUnit : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ f : R, x₀ f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Y : Scheme.{0}) (π : Y ⟶ Z₁.left) (sY : Y ⟶ Sp R'), π ≫ Z₁.hom = sY ≫ spMap ρ → ∃ F : Y ⟶ Z₂.left, F ≫ Z₂.hom = sY ≫ spMap ρ ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ Y, io ≫ π = pullback.fst _ _ → φ = io ≫ F := by
  intro R σ₁ σ₂ Hh _ _ _ _ _ _ Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h1 h2 h3 h4 h5 h6 h7 K₀ _ x₀ φ₀ h0
  obtain ⟨f, F₀, hf, hF, hG⟩ :=
    _root_.GlobalTheory.ZM.LocalGraph.exists_hom_near_of_graphs R σ₁ σ₂ Hh Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h1 h2 h3 h4 h5 h6 h7 K₀ x₀ φ₀ h0
  refine ⟨f, hf, fun R' _ ρ hρ Y π sY hπ => ?_⟩
  have e : (IsLocalization.Away.lift f hρ : Localization.Away f →+* R').comp
      (algebraMap R (Localization.Away f)) = ρ := IsLocalization.Away.lift_comp _ _
  have w : π ≫ Z₁.hom = (sY ≫ spMap (IsLocalization.Away.lift f hρ : Localization.Away f →+* R')) ≫
      spMap (algebraMap R (Localization.Away f)) := by
    rw [Category.assoc, ← spMap_comp, e, hπ]
  refine ⟨pullback.lift π _ w ≫ F₀, ?_, fun K _ x φ hφ io hio => ?_⟩
  · rw [Category.assoc, hF, pullback.lift_fst_assoc, hπ]
  · rw [← Category.assoc]
    exact hG K x φ hφ _ (by rw [Category.assoc, pullback.lift_fst, hio])

end GlobalTheory.ZM.NearBuild
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaDvr

theorem app_eq_zero_of_not_mem {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [Smooth G.hom]
    {U : G.left.Opens} (a : Γ(G.left, U))
    (h : ∀ x ∈ G.left.basicOpen a, G.hom x ≠ IsLocalRing.closedPoint V) :
    ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom a = 0 := by

  have hk : _root_.IsReduced (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := by
    rw [zero_add, pow_one]
    infer_instance
  have : IsReduced (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0))

  have hpt : ∀ y : ↥(pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)),
      G.hom (pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0) y) = IsLocalRing.closedPoint V := by
    intro y
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · exact (Ideal.ne_top_iff_one _).mpr (PrimeSpectrum.isPrime _).one_notMem
    · intro r hr
      have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [zero_add, pow_one]; exact hr)
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r ∈
        ((pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y).asIdeal
      rw [h0]
      exact Ideal.zero_mem _

  have hbot : (fstG (IsLocalRing.maximalIdeal V) 0 G).left ⁻¹ᵁ G.left.basicOpen a = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => (h _ hy (hpt y)).elim
  rw [Scheme.preimage_basicOpen] at hbot
  exact (@basicOpen_eq_bot_iff _ this _ _).mp hbot

private lemma secIsMul_trans' {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB Y} {a b : R} {σ τ τ' : LB.Sec L} (h : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ)
    (h' : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p b τ τ') : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p (a * b) σ τ' := by
  intro k
  rw [h k, h' k, ← _root_.mul_assoc]
  congr 1
  simp only [resTop, scal, map_mul]

private lemma gs_id_eq_germ_moduli {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)) (z : X) (hz : z ∈ U) :
    gs (𝟙 X) z U a = (X.presheaf.germ U z hz).hom a := by
  unfold gs
  rw [dite_eq_left (show (𝟙 X) z ∈ U from hz)]
  rfl

theorem exists_sec_unit_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left)
    (hN : N.IsLB) (s : LB.Sec (N.pull (pullback.fst G.hom (jK V)))) (j) (hj : s.f j ≠ 0) :
    ∃ (θ : LB.Sec N) (k : N.ι), ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hflat : (algebraMap V (FractionRing V)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (FractionRing V) (nonZeroDivisors V))
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  have hpb : IsPullback (pullback.fst G.hom (jK V)) (pullback.snd G.hom (jK V)) G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) := IsPullback.of_hasPullback _ _

  obtain ⟨n, c, u, hu⟩ := GlobalTheory.FlatSec.exists_comb_of_flat V (FractionRing V) _ hflat G.left G.hom _
    (pullback.fst G.hom (jK V)) _ hpb N hN s
  have hne : ∃ i k, (u i).f k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hj
    apply TopCat.Presheaf.section_ext (pullback G.hom (jK V)).sheaf
    intro z hz
    have hj' : j = fun _ => j PUnit.unit := funext fun x => by cases x; rfl
    have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := by
      rw [hj'] at hz
      simpa [LB.pull, LB.LinComb, LB.wchart] using hz
    have h1 := hu z (j PUnit.unit) hz'
    rw [← hj'] at h1
    rw [gs_id_eq_germ_moduli _ _ z hz] at h1
    refine Eq.trans ?_ (map_zero _).symm
    change ((pullback G.hom (jK V)).presheaf.germ _ z hz).hom (s.f j) = 0
    rw [h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcon i (j PUnit.unit)]
    simp [gs]
  obtain ⟨i, k₀, hk₀⟩ := hne
  set θ₀ := u i

  have hjac : IsLocalRing.maximalIdeal V ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hex : ∃ m, ∃ k, ((fstG (IsLocalRing.maximalIdeal V) m G).left.app _).hom (θ₀.f k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk₀ ((GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings V _ hjac G).1 N hN θ₀ hcon k₀)
  classical

  have hunit : ∀ (θ : LB.Sec N) (k : N.ι), ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (θ.f k) ≠ 0 →
      ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
    intro θ k hθ
    by_contra hcon
    push Not at hcon
    exact hθ (app_eq_zero_of_not_mem G (θ.f k) hcon)

  obtain ⟨k₁, hk₁⟩ := Nat.find_spec hex
  rcases hm : Nat.find hex with _ | e
  · rw [hm] at hk₁
    obtain ⟨x, hx, hxc⟩ := hunit θ₀ k₁ hk₁
    exact ⟨θ₀, k₁, x, hx, hxc⟩
  · have hlt : ¬ ∃ k, ((fstG (IsLocalRing.maximalIdeal V) e G).left.app _).hom (θ₀.f k) ≠ 0 :=
      Nat.find_min hex (by omega)
    push Not at hlt
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ e).1 hlt
    have hτ0 : ∃ k, ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (τ.f k) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨τ', hτ'⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N τ 0).1 hcon
      have h2 := secIsMul_trans' G.hom hτ hτ'
      rw [← pow_add] at h2
      have h3 := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ (e + 1)).2 ⟨τ', h2⟩
      rw [hm] at hk₁
      exact hk₁ (h3 k₁)
    obtain ⟨k, hk⟩ := hτ0
    obtain ⟨x, hx, hxc⟩ := hunit τ k hk
    exact ⟨τ, k, x, hx, hxc⟩

theorem thetaNZ_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)), GlobalTheory.LN.PolAt t (jK V) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro hL hL2 E _ _ _ H V _ _ _ t ht
  obtain ⟨A, oA, gen, -, hiso, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt hL hL2 E H V t ht
  have hsa := t.4
  have : Smooth t.G.hom := hsa.2
  have : IsSeparated t.G.hom := hsa.3
  have : QuasiCompact t.G.hom := hsa.4
  have : GeometricallyConnected t.G.hom := hsa.5
  have hLt : t.PP.L.IsLB := t.PP.3

  have hP := GlobalTheory.PushInv.pushInvertible_any hL2.1 hL.1 _ A
  obtain ⟨W, hxW, θ, hθ, -, hnz⟩ := hP (IsLocalRing.closedPoint (FractionRing V))
  obtain ⟨g, i, -, hg⟩ := hnz _ hxW
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hO : ⊤ ≤ gen.hom.left ⁻¹ᵁ (A.A.hom ⁻¹ᵁ W) := by
    intro y _
    change A.A.hom (gen.hom.left y) ∈ W
    rwa [Subsingleton.elim (A.A.hom (gen.hom.left y)) (IsLocalRing.closedPoint (FractionRing V))]
  obtain ⟨θ', hθ'⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (LB.isLB_pull hLt _) gen.hom.left w hw hO θ hθ
  have hgy : gen.hom.left (gen.inv.left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, gen.inv_hom_id, Over.id_left]
    rfl
  obtain ⟨k, hk⟩ := hθ' (gen.inv.left g) i (by rwa [hgy])
  have hk0 : θ'.f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk

  obtain ⟨σ, l, x, hx, hxc⟩ := exists_sec_unit_closed_fibre V t.G t.PP.L hLt θ' k hk0

  refine ⟨σ, fun y => ?_⟩
  have hy : y ⤳ t.G.hom x := hxc ▸ IsLocalRing.specializes_closedPoint y
  obtain ⟨x', hx', hx'y⟩ := Flat.generalizingMap t.G.hom hy
  exact ⟨x', l, hx'y, hx'.mem_open (t.G.left.basicOpen (σ.f l)).isOpen hx⟩

end GlobalTheory.ThetaDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueDescentAutomorphismInvariantMorphism
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.InvariantMorDescent

theorem exists_equalizer_ideal {Z Y S : Scheme.{0}} (z : Y ⟶ S) [IsSeparated z] (a b : Z ⟶ Y)
    (h : a ≫ z = b ≫ z) :
    ∃ I : Z.IdealSheafData, ∀ (T : Scheme.{0}) (t : T ⟶ Z), I ≤ t.ker ↔ t ≫ a = t ≫ b := by
  let i := pullback.fst (pullback.lift a b h) (pullback.diagonal z)
  have hi : i ≫ a = i ≫ b := by
    have c : i ≫ _ = _ := pullback.condition (f := pullback.lift a b h) (g := pullback.diagonal z)
    have c₁ := congrArg (· ≫ pullback.fst z z) c
    have c₂ := congrArg (· ≫ pullback.snd z z) c
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd] at c₁ c₂
    exact c₁.trans c₂.symm
  refine ⟨i.ker, fun T t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · rw [← IsClosedImmersion.lift_fac i t ht, Category.assoc, Category.assoc, hi]
  · have e : t ≫ pullback.lift a b h = (t ≫ a) ≫ pullback.diagonal z := by
      apply pullback.hom_ext
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd, ht]
    rw [← pullback.lift_fst t (t ≫ a) e]
    exact Scheme.Hom.le_ker_comp _ _

theorem fst_comp_eq_snd_comp {K L : Type} [Field K] [Field L] [Algebra K L] {G : Type*}
    (s : G → L →ₐ[K] L) (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    {X X' Y S : Scheme.{0}} {p : X ⟶ Spec (.of K)} {q : X' ⟶ Spec (.of L)} {π : X' ⟶ X}
    (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (z : Y ⟶ S) [IsSeparated z] (f : X' ⟶ Y) (u : X ⟶ S) (hu : f ≫ z = π ≫ u)
    (hf : ∀ g, GaloisDescent.twist H (s g) ≫ f = f) :
    pullback.fst π π ≫ f = pullback.snd π π ≫ f := by
  have hp : IsPullback (pullback.fst π π) (pullback.snd π π ≫ q) (π ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsPullback.of_hasPullback π π).paste_vert H
  obtain ⟨I, hI⟩ := exists_equalizer_ideal z (pullback.fst π π ≫ f) (pullback.snd π π ≫ f) (by
    rw [Category.assoc, Category.assoc, hu, pullback.condition_assoc])
  have h₂ : ∀ g, GaloisDescent.twist hp (s g) ≫ pullback.snd π π =
      pullback.snd π π ≫ GaloisDescent.twist H (s g) := fun g => by
    apply H.hom_ext
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst, ← pullback.condition,
        GaloisDescent.twist_fst_assoc]
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_snd, GaloisDescent.twist_snd,
        Category.assoc]
  obtain ⟨J, hJ, -⟩ := (GaloisDescent.idealSheaf_stable_iff_exists_comap hp s hs I).1 fun g => by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
    refine (hI _ _).2 ?_
    rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst_assoc, reassoc_of% (h₂ g), hf]
    exact (hI _ _).1 I.ker_subschemeι.ge
  have h₃ : I ≤ (pullback.diagonal π).ker := (hI _ _).2 (by simp)
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le, ← hJ,
    ← Scheme.IdealSheafData.comap_comp, pullback.diagonal_fst,
    Scheme.IdealSheafData.comap_id, le_bot_iff] at h₃
  rw [h₃, Scheme.IdealSheafData.comap_bot] at hJ
  simpa using (hI _ (𝟙 _)).1 (hJ ▸ bot_le)

theorem existsUnique_desc : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [IsAlgClosed C] [Algebra K C] (S : Scheme.{0}) (b : Sp K ⟶ S) (X Y : Over S), IsSeparated Y.hom → ∀ κ : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk b, κ.left = spMap (algebraMap K C) → ∀ f : Over.mk (spMap (algebraMap K C) ≫ b) ⊗ X ⟶ Y, (∀ (σ : C ≃ₐ[K] C) (s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b)), s.left = spMap (σ : C →+* C) → s ▷ X ≫ f = f) → ∃! g : Over.mk b ⊗ X ⟶ Y, κ ▷ X ≫ g = f := by
  intro K C _ _ _ _ _ S b X Y hY κ hκ f hf
  have f₁ : Flat κ.left := by
    rw [hκ]
    change Flat (spMap (algebraMap K C))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective κ.left := ⟨fun y =>
    ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have f₃ : QuasiCompact κ.left := by
    rw [hκ]
    exact inferInstanceAs (QuasiCompact (spMap (algebraMap K C)))
  have H : IsPullback (κ ▷ X).left (fst _ X).left (fst (Over.mk b) X).left
      (Spec.map (CommRingCat.ofHom (algebraMap K C))) := by
    have := (SemiRigid.isPullback_whiskerRight κ X).flip
    rw [hκ] at this
    exact this
  have key := fst_comp_eq_snd_comp (fun σ : C ≃ₐ[K] C => σ.toAlgHom)
    GaloisDescent.mem_range_algebraMap_of_forall_algEquiv H Y.hom f.left (Over.mk b ⊗ X).hom
    ((Over.w f).trans (Over.w (κ ▷ X)).symm) fun σ => by
      have hσ : spMap (σ : C →+* C) ≫ spMap (algebraMap K C) = spMap (algebraMap K C) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact σ.toAlgHom.comp_algebraMap
      let s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b) :=
        Over.homMk (spMap (σ : C →+* C)) (by
          change spMap (σ : C →+* C) ≫ spMap (algebraMap K C) ≫ b = spMap (algebraMap K C) ≫ b
          rw [reassoc_of% hσ])
      have hsκ : s ≫ κ = κ := Over.OverMorphism.ext (by
        rw [Over.comp_left, hκ]; exact hσ)
      have e : GaloisDescent.twist H σ.toAlgHom = (s ▷ X).left := by
        apply H.hom_ext
        · rw [GaloisDescent.twist_fst, ← Over.comp_left, ← comp_whiskerRight, hsκ]
        · rw [GaloisDescent.twist_snd]
          exact congrArg (·.left) (whiskerRight_fst s X).symm
      rw [e]
      exact congrArg (·.left) (hf σ s rfl)
  obtain ⟨g, hg⟩ := SemiRigid.exists_desc (κ ▷ X) f fun Z a c h => by
    have h' : a.left ≫ (κ ▷ X).left = c.left ≫ (κ ▷ X).left := congrArg (·.left) h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← pullback.lift_fst a.left c.left h', Category.assoc, key,
      pullback.lift_snd_assoc]
  have := SemiRigid.epi_of_fpqc (κ ▷ X)
  exact ⟨g, hg, fun g' hg' => (cancel_epi (κ ▷ X)).1 (hg'.trans hg.symm)⟩

end GlobalTheory.InvariantMorDescent
end

