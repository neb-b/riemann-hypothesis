module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
section
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups

variable {X : Scheme.{u}}

theorem transitionMap_def (s : SequenceOfBlowups X) {i i' : ℕ} (h : i ≤ i') :
    s.transitionMap h = s.tower.map (homOfLE h).op := rfl

theorem transitionMap_trans (s : SequenceOfBlowups X) {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    s.transitionMap hjl ≫ s.transitionMap hij = s.transitionMap (hij.trans hjl) :=
  (s.tower.map_comp (homOfLE hjl).op (homOfLE hij).op).symm

theorem transitionMap_self (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) : s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [transitionMap_def, show (homOfLE h).op = 𝟙 (op i) from rfl, s.tower.map_id]

theorem blowupMorphism_eq_transitionMap (s : SequenceOfBlowups X) (i : ℕ) :
    s.transitionMapSucc i = s.transitionMap (Nat.le_succ i) := rfl

theorem isBlowupAlongIdealSheaf_blowupMorphism (s : SequenceOfBlowups X) (i : ℕ) (h : i < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowup i h

theorem projectionToBase_def (s : SequenceOfBlowups X) (i : ℕ) :
    s.projectionToBase i = s.transitionMap (Nat.zero_le i) ≫ s.isoZero.hom := rfl

theorem projectionToBase_zero (s : SequenceOfBlowups X) : s.projectionToBase 0 = s.isoZero.hom := by
  rw [projectionToBase_def, s.transitionMap_self, Category.id_comp]

theorem projectionToBase_succ (s : SequenceOfBlowups X) (i : ℕ) :
    s.projectionToBase (i + 1) = s.transitionMapSucc i ≫ s.projectionToBase i := by
  rw [blowupMorphism_eq_transitionMap]
  exact (s.transitionMap_comp_projectionToBase (Nat.le_succ i)).symm

theorem lastStructMap_eq_projectionToBase (s : SequenceOfBlowups X) : s.lastStructMap = s.projectionToBase s.length := rfl

theorem pullbackTransitionMap_fst (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.fst φ (s.projectionToBase i) = pullback.fst φ (s.projectionToBase i') :=
  Eq.trans (pullback.lift_fst _ _ _) (Category.comp_id _)

theorem pullbackTransitionMap_snd (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i)
      = pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h :=
  pullback.lift_snd _ _ _

end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def imageIdealSheaf {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) : X.IdealSheafData :=
  (I.subschemeι ≫ σ).ker

theorem map_eq_imageIdealSheaf {S X : Scheme.{u}} (f : S ⟶ X) (I : S.IdealSheafData) :
    I.map f = imageIdealSheaf f I := rfl

theorem imageIdealSheaf_comp {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) (I : W.IdealSheafData) :
    imageIdealSheaf (g ≫ w) I = imageIdealSheaf w (imageIdealSheaf g I) := by
  simp only [← map_eq_imageIdealSheaf, Scheme.IdealSheafData.map_comp]

theorem imageIdealSheaf_eq_ker {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) :
    imageIdealSheaf σ I = (I.subschemeι ≫ σ).ker := rfl

def SequenceOfBlowups.Isomorphic {X : Scheme.{u}} (B B' : SequenceOfBlowups X) : Prop :=
  B.length = B'.length ∧
    ∃ e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i),
      ((e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (B'.center i).comap (e i hi.le).hom = B.center i)

theorem SequenceOfBlowups.isomorphic_refl {X : Scheme.{u}} (B : SequenceOfBlowups X) : B.Isomorphic B := by
  refine ⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩ <;> simp

def IsPushforwardBlowupSeq {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) : Prop :=
  BS.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ BS.length → (BS.schemeAt i ⟶ B.schemeAt i),
      (∀ i : ℕ, ∀ hi : i ≤ BS.length, IsClosedImmersion (σ i hi)) ∧
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        σ (i + 1) hi ≫ B.transitionMapSucc i = BS.transitionMapSucc i ≫ σ i hi.le) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        B.center i = imageIdealSheaf (σ i hi.le) (BS.center i)) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        (σ (i + 1) hi).ker =
          Blowup.strictTransform (B.transitionMapSucc i) (B.center i) (σ i hi.le).ker)

def IsStrictPullbackBlowupSeq {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (B' : SequenceOfBlowups X') (B : SequenceOfBlowups X) : Prop :=
  B'.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ B'.length → (B'.schemeAt i ⟶ B.schemeAt i),
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = B'.isoZero.hom ≫ φ) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        IsPullback (σ (i + 1) hi) (B'.transitionMapSucc i) (B.transitionMapSucc i) (σ i hi.le)) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        B'.center i = (B.center i).comap (σ i hi.le))

private def schemeAtHomOfEqZero {X' X : Scheme.{u}} (g : X' ⟶ X) (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (i : ℕ) (hi0 : i = 0) : t.schemeAt i ⟶ s.schemeAt i :=
  eqToHom (congrArg t.schemeAt hi0) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
    eqToHom (congrArg s.schemeAt hi0).symm

theorem IsStrictPullbackBlowupSeq.of_length_zero {X' X : Scheme.{u}} (g : X' ⟶ X) (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s := by
  refine ⟨ht.trans hs.symm,
    fun i hi => schemeAtHomOfEqZero g t s i (Nat.eq_zero_of_le_zero (le_of_le_of_eq hi ht)),
    ?_, ?_, ?_⟩
  · simp [schemeAtHomOfEqZero]
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)

theorem IsStrictPullbackBlowupSeq.length_eq {X' X : Scheme.{u}} {φ : X' ⟶ X}
    {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq φ B' B) :
    B'.length = B.length := h.1

end FunctorialResolution.EmbeddedResolution
end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.CartierDivisorComponents
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_closure_singleton_iff_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (a b : PrimeSpectrum Γ(X, U)) :
    a ∈ closure ({b} : Set (PrimeSpectrum Γ(X, U))) ↔
      hU.fromSpec a ∈ closure ({hU.fromSpec b} : Set (X : Type u)) := by
  have hoi : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hind := (Scheme.Hom.isOpenEmbedding hU.fromSpec).toIsEmbedding.toIsInducing
  constructor
  · intro hab
    have h1 : b ⤳ a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mpr h1)
  · intro hab
    have h1 : hU.fromSpec b ⤳ hU.fromSpec a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mp h1)

private theorem mem_primeIdealOf_of_notMem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : (X : Type u)} (hx : x ∈ U) {f : Γ(X, U)}
    (hb : x ∉ X.basicOpen f) : f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  by_contra hfn
  apply hb
  have h1 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [hU.fromSpec_preimage_basicOpen f]
    exact (PrimeSpectrum.mem_basicOpen f _).mpr hfn
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h1
  rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h2
  exact h2

private theorem mem_primeIdealOf_of_mem_support {X : Scheme.{u}} {I : X.IdealSheafData}
    {U : X.affineOpens} {x : (X : Type u)} (hx : x ∈ U.1) {f : Γ(X, U.1)}
    (hf : f ∈ I.ideal U) (hxs : x ∈ I.support) :
    f ∈ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hz : x ∈ X.zeroLocus (I.ideal U : Set Γ(X, U.1)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem hx).mp hxs
  rw [Scheme.mem_zeroLocus_iff] at hz
  exact mem_primeIdealOf_of_notMem_basicOpen U.2 hx (hz f hf)

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.not_irreducibleComponent_subset_support
    {X : Scheme.{u}} {D : X.IdealSheafData} (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D)
    {Z : Set (X : Type u)} (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    ¬ Z ⊆ (D.support : Set (X : Type u)) := by
  intro hsub
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 hZcl
  have hξ' : closure ({ξ} : Set (X : Type u)) = Z := hξ
  have hξZ : ξ ∈ Z := by rw [← hξ']; exact subset_closure rfl
  obtain ⟨U, f, hxU, hf, hDU⟩ := hD ξ
  have hfD : f ∈ D.ideal U := by rw [hDU]; exact Ideal.subset_span rfl
  have hfp : f ∈ (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal :=
    EmbeddedResolution.mem_primeIdealOf_of_mem_support hxU hfD (hsub hξZ)
  have hmin : (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal ∈ minimalPrimes Γ(X, U.1) := by
    refine ⟨⟨(U.2.primeIdealOf ⟨ξ, hxU⟩).isPrime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hqle
    have hqle' : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ≤ U.2.primeIdealOf ⟨ξ, hxU⟩ := hqle
    have hxy : (U.2.primeIdealOf ⟨ξ, hxU⟩) ∈
        closure ({(⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} : Set (PrimeSpectrum Γ(X, U.1))) :=
      (PrimeSpectrum.le_iff_mem_closure ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mp hqle'
    have hξcl : ξ ∈ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      have h2 := (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mp hxy
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩] at h2
      exact h2
    have hZsub : Z ⊆ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      rw [← hξ']
      exact closure_minimal (Set.singleton_subset_iff.mpr hξcl) isClosed_closure
    have hyZ : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ Z :=
      hZ.2 isIrreducible_singleton.closure hZsub (subset_closure rfl)
    have hy : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))
        ∈ closure ({ξ} : Set (X : Type u)) := by
      rw [hξ']; exact hyZ
    have hprimeLe : (U.2.primeIdealOf ⟨ξ, hxU⟩) ≤ (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) := by
      refine (PrimeSpectrum.le_iff_mem_closure (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mpr ?_
      refine (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mpr ?_
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩]
      exact hy
    exact hprimeLe
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hfp hmin hf

end FunctorialResolution.EmbeddedResolution
end
end

