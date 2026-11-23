module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteType
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoFT

theorem finiteType_affine {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType q] {W : X.Opens} (hW : IsAffineOpen W) :
    letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  have h1 : (q.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
  have h3 : (strV q W).FiniteType := by
    have : strV q W = (q.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := rfl
    rw [this]
    exact h1.comp h2
  letI := (strV q W).toAlgebra
  exact RingHom.finiteType_algebraMap.1 h3

end GlobalTheory.CompanionTheory.GeoFT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicOverTorusOfIntegral
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTorus

theorem isAlgebraic_unit_inv {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) : IsAlgebraic A ((u⁻¹ : Rˣ) : R) := by
  refine ⟨Polynomial.C (⟨u, hu⟩ : A) * Polynomial.X - 1, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h
    simp at h1
  · simp [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul]

theorem isAlgebraic_unit_zpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) (m : ℤ) : IsAlgebraic A ((u ^ m : Rˣ) : R) := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · have h : IsAlgebraic A (u : R) := isAlgebraic_algebraMap (⟨u, hu⟩ : A)
    simpa using h.pow n
  · simpa using (isAlgebraic_unit_inv A u hu).pow n

theorem isAlgebraic_tpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ}
    (t : Fin d → Rˣ) (m : Fin d → ℤ) :
    IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) (tpow t m) := by
  set A := Algebra.adjoin K (Set.range fun k => (t k : R))
  have hmem : ∀ k, (t k : R) ∈ A := fun k => Algebra.subset_adjoin ⟨k, rfl⟩
  have key : ∀ s : Finset (Fin d), IsAlgebraic A (((∏ k ∈ s, t k ^ m k : Rˣ)) : R) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isAlgebraic_one : IsAlgebraic A (1 : R))
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul]
      exact (isAlgebraic_unit_zpow A (t a) (hmem a) (m a)).mul ih
  exact key Finset.univ

theorem isAlgebraic_of_integral_torusS : ∀ {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ), (∀ r : R, IsIntegral (torusS K t Finset.univ) r) → Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  intro K R _ _ _ _ d t hint
  set A := Algebra.adjoin K (Set.range fun k => (t k : R)) with hA
  let S : Subalgebra A R := Subalgebra.algebraicClosure A R
  have hle : ∀ b : torusS K t Finset.univ, (b : R) ∈ S := by
    rintro ⟨b, hb⟩
    have : torusS K t Finset.univ ≤ S.restrictScalars K := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨m, -, rfl⟩
      exact (Subalgebra.mem_algebraicClosure A R).2 (isAlgebraic_tpow t m)
    exact this hb
  let φ : torusS K t Finset.univ →+* S :=
    { toFun := fun b => ⟨b, hle b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨fun r => ?_⟩
  obtain ⟨p, hm, hp⟩ := hint r
  have hS : IsIntegral S r := by
    refine ⟨p.map φ, hm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  set_option synthInstance.maxHeartbeats 200000 in
    exact hS.isAlgebraic.restrictScalars A

end GlobalTheory.CompanionTheory.GeoTorus
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenEvalSurjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem evV_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  intro K _ X N i hi g e hg he
  have hU : IsAffineOpen (Proj.basicOpen (grK K N) g) := Proj.isAffineOpen_basicOpen (grK K N) g hg he
  have hiso : IsIso (Proj.awayToSection (grK K N) g) := (Proj.basicOpenIsoAway (grK K N) g hg he).isIso_hom
  have h1 : Function.Surjective (Proj.awayToSection (grK K N) g).hom :=
    (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grK K N) g)).2
  have h2 : Function.Surjective (i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective _ hU
  exact h2.comp h1

end GlobalTheory.CompanionTheory.Geo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZero
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem preimage_basicOpen_nonempty_of_mk_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}
    (i : X ⟶ PSpace K N) (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hne : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  by_contra hE
  apply hne
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.subset_span
  have hg' : g ∈ grK K N (e • 1) := by simpa using hg
  refine ⟨e, hg', fun j => ?_⟩
  have hy : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) e g hg' =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
  rw [hy, ← basicOpen_eq_bot_iff]
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hg he
  have h2 : X.basicOpen (evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) =
      i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
        (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) := by
    rw [Scheme.preimage_basicOpen]
    simp only [evV, Scheme.Hom.appLE_eq_app]
    rfl
  rw [h2, hb, eq_bot_iff]
  intro x hx
  exact hE ⟨x, hx.2⟩

end GlobalTheory.CompanionTheory.Geo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCover

theorem X_mem_of_finite {K : Type} [Field K] {n m : ℕ}
    (I P : Ideal (MvPolynomial (Fin n) K)) [hPp : P.IsPrime] (hIP : I ≤ P)
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (y : Fin m → MvPolynomial (Fin n) K) (hy : ∀ k, y k ∈ P)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))
    (j : Fin n) : (MvPolynomial.X j : MvPolynomial (Fin n) K) ∈ P := by
  classical
  by_contra hj
  let φ : (MvPolynomial (Fin n) K ⧸ I) →+* (MvPolynomial (Fin n) K ⧸ P) := Ideal.Quotient.factor hIP
  have hφ : ∀ g, φ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk P g := fun g => rfl
  let Q : Ideal (MvPolynomial (Fin n) K ⧸ I) := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  have hc0 : ∀ r ∈ Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)),
      ∃ c : K, φ r = Ideal.Quotient.mk P (MvPolynomial.C c) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨0, by rw [hφ, map_zero, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hy k)⟩
    | algebraMap c => exact ⟨c, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [φ.map_add, hc, hd, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_add, (Ideal.Quotient.mk P).map_add]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c * d, by rw [map_mul, hc, hd, map_mul, map_mul]⟩
  have h1 : (1 : MvPolynomial (Fin n) K ⧸ P) ≠ 0 := by
    intro h
    have : (1 : MvPolynomial (Fin n) K) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h)
    exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hmax : (Q.comap (algebraMap (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => h1 ?_, fun J x hle hx hxJ => ?_⟩
    · have : φ 1 = 0 := by simpa [Q, RingHom.mem_ker, Ideal.mem_comap] using h
      simpa using this
    · obtain ⟨c, hc⟩ := hc0 x.1 x.2
      have hc' : c ≠ 0 := by
        rintro rfl
        apply hx
        rw [Ideal.mem_comap]
        change φ x.1 = 0
        rw [hc, map_zero, map_zero]
      have hm : x * algebraMap K _ c⁻¹ - 1 ∈ J := by
        apply hle
        rw [Ideal.mem_comap]
        change φ (x.1 * algebraMap K _ c⁻¹ - 1) = 0
        rw [φ.map_sub, φ.map_mul, hc, φ.map_one]
        change _ * Ideal.Quotient.mk P (MvPolynomial.C c⁻¹) - 1 = 0
        rw [← map_mul (Ideal.Quotient.mk P), ← map_mul MvPolynomial.C, mul_inv_cancel₀ hc', map_one, map_one, sub_self]
      have := J.sub_mem (J.mul_mem_right (algebraMap K _ c⁻¹) hxJ) hm
      simpa using this
  have hQ : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) Q hmax
  have hjQ : Ideal.Quotient.mk I (MvPolynomial.X j) ∉ Q := fun h =>
    hj (Ideal.Quotient.eq_zero_iff_mem.1 ((hφ _).symm.trans (RingHom.mem_ker.1 h)))
  obtain ⟨a, b, hb, hab⟩ := hQ.exists_inv hjQ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h2 : Ideal.Quotient.mk P (g * MvPolynomial.X j - 1) = 0 := by
    have := congrArg φ hab
    rw [φ.map_add, φ.map_mul, hφ, hφ, show φ b = 0 from hb, add_zero, map_one] at this
    rw [(Ideal.Quotient.mk P).map_sub, (Ideal.Quotient.mk P).map_mul, this, (Ideal.Quotient.mk P).map_one, sub_self]
  have h3 : MvPolynomial.homogeneousComponent 0 (g * MvPolynomial.X j - 1) ∈ P := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact hP 0 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  have h4 : AddMonoidAlgebra.coeff (g * MvPolynomial.X j - 1) 0 = -1 := by
    have : MvPolynomial.constantCoeff (g * MvPolynomial.X j - 1) = -1 := by simp only [(MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_sub, (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_mul, MvPolynomial.constantCoeff_X, mul_zero, (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_one, zero_sub]
    rwa [MvPolynomial.constantCoeff_eq] at this
  rw [MvPolynomial.homogeneousComponent_zero, h4, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_neg, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_one] at h3
  exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.neg_mem h3))

theorem mem_of_evV_eq_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (p : X)
    (j : Fin (N + 1)) (hj : i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    {d : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (d • 1))
    (h : evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    f ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
  by_contra hfP
  have hf' : f * MvPolynomial.X j ∈ grK K N (d + 1) := by
    have := SetLike.mul_mem_graded hf (xv_mem K N j)
    simpa using this
  have e : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf' := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
    exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by
      change MvPolynomial.X j ^ (d + 1) * f = MvPolynomial.X j ^ d * (f * MvPolynomial.X j)
      ring))
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hf' (Nat.succ_pos d)
  have hx : i p ∈ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := by
    erw [hb]
    refine ⟨hj, fun hm => ?_⟩
    exact ((i p : ProjectiveSpectrum (grK K N)).isPrime.mem_or_mem hm).elim hfP hj
  have hp : p ∈ i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := hx
  rw [Scheme.preimage_basicOpen, ← e] at hp
  have h0 : i.app _ (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf)) = 0 := by
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  rw [h0, Scheme.basicOpen_zero] at hp
  exact hp

theorem iSup_preimage_eq_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  intro K _ X N i m e _ y _ hfin
  rw [_root_.eq_top_iff]
  intro p _
  by_contra hcon
  obtain ⟨j, hj⟩ : ∃ j, i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
    have : i p ∈ (⨆ j : Fin (N + 1), Proj.basicOpen (grK K N) (MvPolynomial.X j)) := by
      erw [GroundTheory.Arith.SchemeCoh.ProjSpace.iSup_basicOpen_X]
      trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  have hy : ∀ k, y k ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    intro k
    by_contra hk
    apply hcon
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, hk⟩
  have hle : homIdeal i ≤ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    rw [homIdeal, Ideal.span_le]
    rintro f ⟨d, hf, hv⟩
    exact mem_of_evV_eq_zero i p j hj hf (hv j)
  haveI : (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal.IsPrime :=
    (i p : ProjectiveSpectrum (grK K N)).isPrime
  exact hj (X_mem_of_finite _ _ hle
    (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).isHomogeneous y hy hfin j)

end GlobalTheory.CompanionTheory.GeoCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUniqueStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_base_change_map_unique : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T), (∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) → (∀ b, θ₂ (poly n K S b) = toR C T (phi C b)) → ∀ (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)), IsBaseChange (Aa C) (thetaLin C θ' hθ') → θ₁ = θ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChange
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem toR_empty_bijective {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A]
    (C : ChartRings K A n d) : Function.Bijective (toR C ∅) := by
  have h : (toR C ∅ : A → C.R ∅) = C.base.symm := funext fun a => C.res_id ∅ _ _
  rw [h]
  exact C.base.symm.bijective

theorem theta_empty : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d),
    ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C
  let e : Bp K n d ≃ₐ[K] R0 K n d ∅ := AlgEquiv.ofBijective (poly n K ∅) PolyBij.poly_bijective
  let θ : R0 K n d ∅ →ₐ[K] C.R ∅ := (toR C ∅).comp ((phi C).comp e.symm.toAlgHom)
  have hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b) := fun b => by
    have hb : e.symm (poly n K ∅ b) = b := e.symm_apply_apply b
    change toR C ∅ (phi C (e.symm (poly n K ∅ b))) = _
    rw [hb]
  refine ⟨θ, hθ, ?_⟩
  let eM : Bp K n d ≃ₗ[Bp K n d] R0 K n d ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Bp K n d) (R0 K n d ∅)) PolyBij.poly_bijective
  let eN : Aa C ≃ₗ[Aa C] Rb C ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Aa C) (Rb C ∅)) (toR_empty_bijective C)
  refine (IsBaseChange.iff_of_equiv_comm (f := Algebra.linearMap (Bp K n d) (Aa C)) eM eN ?_).mp
    (IsBaseChange.linearMap (Bp K n d) (Aa C))
  refine LinearMap.ext fun b => ?_
  exact hθ b

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChangeStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_forms_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) → ∀ a : ℕ, IsBaseChange (Aa C) (psi C θ hθ a) := by
  intro K _ n d A _ _ C S θ hθ hb a
  exact GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi C θ hθ hb a
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDim
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.CoordCard

theorem card_eq_of_etale {K L : Type} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] {m n : ℕ}
    [Algebra (MvPolynomial (Fin m) K) L] [IsScalarTower K (MvPolynomial (Fin m) K) L]
    [Algebra.FormallyEtale (MvPolynomial (Fin m) K) L]
    [Algebra.IsStandardSmoothOfRelativeDimension n K L] : m = n := by
  let b := KaehlerDifferential.mvPolynomialBasis K (Fin m)
  let b' := (b.baseChange L).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial (Fin m) K) L)
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := L) n
  have h1 := b'.mk_eq_rank''
  rw [hr] at h1
  simpa using h1

theorem card_eq_of_away {K A L : Type} [Field K] [CommRing A] [CommRing L] [Nontrivial L] [Algebra A L] {m n : ℕ}
    (t : A) [IsLocalization.Away t L] (g : K →+* A) (φ : MvPolynomial (Fin m) K →+* A)
    (hφ : ∀ r, φ (MvPolynomial.C r) = g r) (hE : φ.Etale)
    (hf : RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap A L).comp g)) : m = n := by
  letI iPA : Algebra (MvPolynomial (Fin m) K) A := φ.toAlgebra
  letI iKL : Algebra K L := ((algebraMap A L).comp g).toAlgebra
  letI iPL : Algebra (MvPolynomial (Fin m) K) L := ((algebraMap A L).comp φ).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin m) K) A L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (MvPolynomial (Fin m) K) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap A L (g r) = algebraMap A L (φ (MvPolynomial.C r))
      rw [hφ]
  haveI : Algebra.Etale (MvPolynomial (Fin m) K) A := hE
  haveI : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) K) L := Algebra.FormallyEtale.comp _ A _
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K L := hf
  exact card_eq_of_etale (K := K) (L := L)

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  intro K _ X q n hn V hV m c
  obtain ⟨x, hx⟩ := hV
  have hnt : Nontrivial Γ(X, V) := (X.presheaf.germ V x hx).hom.domain_nontrivial
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) q hn
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, c.affine⟩ le_top
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hf : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X, V) (Localization.Away t)).comp (strV q V)) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e h₁
  exact card_eq_of_away (L := Localization.Away t) t (strV q V) (MvPolynomial.eval₂Hom (strV q V) c.t)
    (fun r => by simp) c.etale hf

end GlobalTheory.CompanionTheory.CoordCard
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoordsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_derivations_of_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra; ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | exact GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | (intros; apply GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmoothStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_representation_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | exact GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr <;> assumption)
end

