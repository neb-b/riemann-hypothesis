module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbProj

theorem isProjBy_of_isPullback {S : Scheme.{0}} (P : PolAV S) {R : Type} [CommRing R]
    {t : Spec (CommRingCat.of R) ⟶ S} {X : Scheme.{0}} {π : X ⟶ P.A.left}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : IsPullback π f P.A.hom t) : IsProjBy f := by
  obtain ⟨N, -, m, s, hL, hs⟩ := polAV_veryAmpleBy
    (polBaseChange_of_relAmple_local AmpleLocal.relAmple_of_locally) S P R t X π f h
  exact ⟨_, hL, m, s, hs⟩

theorem abelian_projective_baseChange : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (IsProjBy P.A.hom ∧ IsSeparated P.A.hom) ∧ ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsProjBy f ∧ IsSeparated f ∧ Smooth f ∧ UniversallyClosed f ∧ Surjective f ∧ IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := by
  intro K _ _ P
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have hsur : Surjective P.A.hom := inferInstance
  refine ⟨⟨isProjBy_of_isPullback P (IsPullback.id_horiz _), inferInstance⟩, ?_⟩
  intro R _ t Y π f h
  have h₀ : IsPullback (snd P.A P.A).left (fst P.A P.A).left P.A.hom P.A.hom :=
    (IsPullback.of_hasPullback P.A.hom P.A.hom).flip
  have h₁ : IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := h.paste_horiz h₀
  exact ⟨isProjBy_of_isPullback P h₁,
    MorphismProperty.of_isPullback (P := @IsSeparated) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Smooth) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective) h₁ hsur, h₁⟩

end GlobalTheory.AbProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw.HighTwist

theorem nontrivial_of_invertible (A L : Type) [CommRing A] [Nontrivial A] [AddCommGroup L]
    [Module A L] [Module.Invertible A L] : Nontrivial L := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact not_subsingleton A
    (Module.Invertible.bijective (R := A) (M := L)).2.subsingleton

variable {Y : Scheme.{0}} {H M : LB Y}

theorem sec_eq_zero (σ : LB.Sec M) (h : ∀ i, σ.f i = 0) : σ = 0 := by
  have key : ∀ s t : LB.Sec M, s.f = t.f → s = t := by
    rintro ⟨_, _⟩ ⟨_, _⟩ rfl
    rfl
  exact key _ _ (funext h)

def secPwOne (s : LB.Sec H) : LB.Sec (pw H 1) where
  f := s.f
  compat i j := (s.compat i j).trans (by
    change _ = (H.g i j ^ (1 : ℤ)).val * _
    rw [zpow_one]
    rfl)

theorem exists_restrict_ne_zero (s : LB.Sec H) {t₀ : ℤ} (a : SecOn (tw M H t₀) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus s ≤ ⊤) a ≠ 0) (t : ℤ) (ht : t₀ ≤ t) :
    ∃ b : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : nonzeroLocus s ≤ ⊤) b ≠ 0 := by
  induction t, ht using Int.leInduction with
  | base => exact ⟨a, ha⟩
  | succ n _ ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨SecOn.mulSec M n s ⊤ b, fun h => hb ?_⟩
    rw [← SecOn.mulSec_restrict] at h
    exact (SecOn.mulSec_bijective s le_rfl).1 (h.trans (map_zero _).symm)

end GlobalTheory.AbLaw.HighTwist

namespace GlobalTheory.AbLaw

open HighTwist

theorem exists_sec_tw_ne_zero : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (σ : LB.Sec (tw M H t)) (i : (tw M H t).ι), σ.f i ≠ 0 := by
  intro R _ Y f hY H m s M hH hM hs
  obtain ⟨x⟩ := hY
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := hs.1 ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have : Nonempty (nonzeroLocus (s i)) := ⟨⟨x, hi⟩⟩
  have := SecOn.invertible (isLB_tw hM hH 0) (hs.2 i).1
  have := nontrivial_of_invertible Γ(Y, nonzeroLocus (s i))
    (SecOn (tw M H 0) (nonzeroLocus (s i)))
  obtain ⟨y, hy⟩ := exists_ne (0 : SecOn (tw M H 0) (nonzeroLocus (s i)))
  obtain ⟨hc, hq, -⟩ := VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hs
  obtain ⟨k, a, ha⟩ := exists_tw_extend_pow_mul Y H M 1 (secPwOne (s i)) (nonzeroLocus (s i)) 0
    hH hM rfl hc hq y
  have hne : SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a ≠ 0 := by
    refine fun h => hy (SecOn.tw_ext fun p l => ?_)
    have e := ha p l
    have h0 : SecOn.twCoord (SecOn.restrict _ (le_top : nonzeroLocus (s i) ≤ ⊤) a) p l = 0 := by
      rw [h]; rfl
    rw [SecOn.twCoord_restrict] at h0
    have hu := (SecOn.isUnit_rs_of_le_nonzeroLocus (s i) l
      (inf_le_right.trans inf_le_right : nonzeroLocus (s i) ⊓ (M.U p ⊓ H.U l) ≤ H.U l)
      inf_le_left).pow k
    exact hu.mul_right_eq_zero.1 (e.symm.trans h0)
  refine ⟨0 + k * 1, fun t ht => ?_⟩
  obtain ⟨b, hb⟩ := exists_restrict_ne_zero (s i) a hne t ht
  by_contra hn
  push Not at hn
  have h0 : SecOn.topEquiv _ b = 0 := sec_eq_zero _ (hn _)
  rw [(SecOn.topEquiv _).map_eq_zero_iff.1 h0] at hb
  exact hb (map_zero _)

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToCharts
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem eval₂Hom_xProd_pow {ι : Type} {R B : Type*} [CommRing R] [CommRing B] (c : R →+* B)
    (b : ι → B) (I : Finset ι) (k : ℕ) :
    MvPolynomial.eval₂Hom c b (xProd R I ^ k) = (∏ i ∈ I, b i) ^ k := by
  rw [map_pow, map_prod]
  simp only [MvPolynomial.eval₂Hom_X']

theorem twisted_sections_localise : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (I : Finset (Fin (m + 1))), (∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : (⨅ i ∈ I, nonzeroLocus (s i)) ≤ ⊤) a = 0 → ∃ k : ℕ, xProd R I ^ k • GrSum.of (hx ⊤) t a = 0) ∧ ∀ (t : ℤ) (y : SecOnR f (tw M H t) (⨅ i ∈ I, nonzeroLocus (s i))), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤), GrSum.of (hx _) t' (SecOnR.restrict f _ le_top a) = xProd R I ^ k • GrSum.of (hx _) t y := by
  intro R _ Y f H m s M hH hM hv hx I
  obtain ⟨hc, hq, -⟩ := GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hv
  obtain ⟨σ, hσ, hV⟩ := GlobalTheory.exists_prod_sec_nonzeroLocus Y H _ s I hH
  refine ⟨fun t a ha => ?_, fun t y => ?_⟩
  · obtain ⟨k, hk⟩ := exists_pow_mul_twCoord_eq_zero Y H M _ σ _ t hH hM hV.symm hc
      ((SecOnR.of f _ ⊤).symm a) ha
    obtain ⟨y', e, hy'⟩ := exists_smul_of_twCoord R Y f H m s M hx ⊤ _ _ t _
      ((SecOnR.of f _ ⊤).symm a) (xProd_pow_mem R I k) rfl
    have h0 : y' = 0 := SecOn.tw_ext fun p l => by
      rw [hy', eval₂Hom_xProd_pow, map_pow]
      have := hk p l
      rw [hσ] at this
      exact this
    refine ⟨k, e.trans ?_⟩
    rw [h0, map_zero, map_zero]
  · obtain ⟨k, a, hk⟩ := exists_tw_extend_pow_mul Y H M _ σ _ t hH hM hV.symm hc hq
      ((SecOnR.of f _ _).symm y)
    obtain ⟨y', e, hy'⟩ := exists_smul_of_twCoord R Y f H m s M hx _ _ _ t _
      ((SecOnR.of f _ _).symm y) (xProd_pow_mem R I k) rfl
    have h0 : SecOn.restrict _ le_top a = y' := SecOn.tw_ext fun p l => by
      rw [hy', eval₂Hom_xProd_pow, map_pow, SecOn.twCoord_restrict]
      have := hk p l
      rw [hσ] at this
      exact this
    refine ⟨k, _, SecOnR.of f _ ⊤ a, Eq.trans ?_ e.symm⟩
    rw [← h0, SecOnR.restrict_of]

end GlobalTheory.AbLaw
end

