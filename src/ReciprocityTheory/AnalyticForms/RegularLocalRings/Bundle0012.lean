module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial IsLocalRing

noncomputable section

variable {σ : Type} [Fintype σ]

abbrev renC (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  renameEquiv ℂ (Fintype.equivFin σ)

abbrev renR (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  (renC σ).toRingEquiv

abbrev renPt (z : σ → ℂ) : Fin (Fintype.card σ) → ℂ := z ∘ (Fintype.equivFin σ).symm

theorem eval_renC (z : σ → ℂ) (h : MvPolynomial σ ℂ) : eval (renPt z) (renC σ h) = eval z h := by
  simp only [renC, renPt, renameEquiv_apply, eval_rename]
  rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

theorem map_primeCompl_renC (z : σ → ℂ) :
    Submonoid.map (renR σ).toMonoidHom (ptIdealOf z).primeCompl = (ptIdeal (renPt z)).primeCompl := by
  have key : ∀ x : MvPolynomial σ ℂ, eval (renPt z) ((renR σ).toMonoidHom x) = eval z x :=
    fun x => eval_renC z x
  have key' : ∀ y, (renR σ).toMonoidHom ((renR σ).symm y) = y := fun y => (renR σ).apply_symm_apply y
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro hy
    apply hx
    change x ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hy
    rw [RingHom.mem_ker] at hy ⊢
    rw [← key x]
    exact hy
  · intro hy
    refine ⟨(renR σ).symm y, ?_, key' y⟩
    intro hx
    apply hy
    change y ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [← key' y, key]
    exact hx

def locPtEquiv (z : σ → ℂ) : Localization.AtPrime (ptIdealOf z) ≃+* locPt (renPt z) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (ptIdealOf z)) (locPt (renPt z))
    (renR σ) (map_primeCompl_renC z)

theorem locPtEquiv_algebraMap (z : σ → ℂ) (x : MvPolynomial σ ℂ) :
    locPtEquiv z (algebraMap _ _ x) = algebraMap _ (locPt (renPt z)) (renC σ x) := by
  unfold locPtEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x

def locAtEquiv (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    locAt I z ≃+* locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z) :=
  Ideal.quotientEquiv _ _ (locPtEquiv z) (by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun x => ?_
    exact (locPtEquiv_algebraMap z x).symm)

theorem mem_map_renR_iff (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial (Fin (Fintype.card σ)) ℂ) :
    h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _) ↔ (renR σ).symm h ∈ I := by
  rw [Ideal.map_comap_of_equiv]
  exact Iff.rfl

theorem renPt_zero (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (hz : ∀ h ∈ I, eval z h = 0) :
    ∀ h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _), eval (renPt z) h = 0 := by
  intro h hh
  rw [mem_map_renR_iff] at hh
  have e := eval_renC z ((renR σ).symm h)
  rw [show renC σ ((renR σ).symm h) = h from (renR σ).apply_symm_apply h] at e
  rw [e]
  exact hz _ hh

theorem finrank_cotangentSpace_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (f : A ≃+* B) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank (ResidueField B) (CotangentSpace B) := by
  classical
  let g : A →ₐ[ℤ] B := f.toRingHom.toIntAlgHom
  let g' : B →ₐ[ℤ] A := f.symm.toRingHom.toIntAlgHom
  have hmax : ∀ x : A, f x ∈ maximalIdeal B ↔ x ∈ maximalIdeal A := by
    intro x
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff f x)
  have hA : maximalIdeal A ≤ (maximalIdeal B).comap g := fun x hx => (hmax x).2 hx
  have hB : maximalIdeal B ≤ (maximalIdeal A).comap g' := fun y hy => by
    show f.symm y ∈ maximalIdeal A
    rw [← hmax, f.apply_symm_apply]
    exact hy
  let j₁ := Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) g hA
  let j₂ := Ideal.mapCotangent (maximalIdeal B) (maximalIdeal A) g' hB
  let j : CotangentSpace A ≃+ CotangentSpace B :=
    { toFun := j₁
      invFun := j₂
      left_inv := fun m => by
        obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective m
        simp only [j₁, j₂, Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (f.symm_apply_apply (x : A))
      right_inv := fun m => by
        obtain ⟨y, rfl⟩ := (maximalIdeal B).toCotangent_surjective m
        simp only [j₁, j₂, Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (f.apply_symm_apply (y : B))
      map_add' := j₁.map_add }
  let i : ResidueField A ≃+* ResidueField B := ResidueField.mapEquiv f
  have hc : ∀ (r : ResidueField A) (m : CotangentSpace A), j (r • m) = i r • j m := by
    intro r m
    obtain ⟨a, rfl⟩ := residue_surjective r
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective m
    have e1 : (residue A a : ResidueField A) • ((maximalIdeal A).toCotangent x : CotangentSpace A) =
        (maximalIdeal A).toCotangent (a • x) := by
      rw [map_smul]
      exact algebraMap_smul (ResidueField A) a _
    have e3 : (residue B (f a) : ResidueField B) •
        ((maximalIdeal B).toCotangent ⟨g x, hA x.2⟩ : CotangentSpace B) =
        (maximalIdeal B).toCotangent (f a • ⟨g x, hA x.2⟩) := by
      rw [map_smul]
      exact algebraMap_smul (ResidueField B) (f a) _
    have e2 : i (residue A a) = residue B (f a) := by
      first
        | rfl
        | exact IsLocalRing.ResidueField.map_residue (f : A →+* B) a
        | simp [i]
    have hj : ∀ m, j m = j₁ m := fun _ => rfl
    rw [hj, hj, e1, e2, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, e3]
    congr 1
    apply Subtype.ext
    show f (a * (x : A)) = f a * f x
    exact map_mul f a x
  have h2 := congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv (⇑i) j i.bijective hc)
  rw [Cardinal.toNat_lift, Cardinal.toNat_lift] at h2
  exact h2

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjBCompl
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

def projBCompl (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (projX P hP).Opens :=
  ⟨(projB P D hP : Set (projX P hP))ᶜ, (projB P D hP).isClosed.isOpen_compl⟩


variable (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) in
structure WData where

  W : Scheme.{0}
  π : W ⟶ projX P hP
  lft : LocallyOfFiniteType (π ≫ toSpecC hP)

  J : (projX P hP).IdealSheafData
  blowup : FinalTheorems.Blowup π J
  support_le : (J.support : Set (projX P hP)) ⊆ projB P D hP
  regular : ∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)
  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal
    ⟨π.base ⁻¹' (projB P D hP : Set (projX P hP)),
      IsClosed.preimage π.base.hom.continuous (projB P D hP).2⟩)
  isIso_off : IsIso (π ∣_ projBCompl P D hP)

  m : ((k : K) → ι k) → ℕ

  g : ∀ p, Fin (m p) → Γ(projX P hP, (chartOpen hP p).1)
  span_g : ∀ p, Ideal.span (Set.range (g p)) = J.ideal (chartOpen hP p)

  pres : ∀ p, Fin (m p) → AffPres (π ≫ toSpecC hP)
  le_pres : ∀ p i, (pres p i).V ≤ π ⁻¹ᵁ (chartOpen hP p).1
  iSup_pres : ∀ p, (⨆ i, (pres p i).V) = π ⁻¹ᵁ (chartOpen hP p).1

  t : ∀ p i, Fin (m p) → Γ(W, (pres p i).V)
  t_self : ∀ p i, t p i i = 1
  g_eq : ∀ p i k, π.appLE _ (pres p i).V (le_pres p i) (g p k) =
    t p i k * π.appLE _ (pres p i).V (le_pres p i) (g p i)
  inter : ∀ p i j, (pres p i).V ⊓ (pres p j).V = W.basicOpen (t p i j)
  t_cocycle : ∀ p i j k,
    W.presheaf.map (homOfLE (inf_le_right : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p j k) *
      W.presheaf.map (homOfLE (inf_le_left : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p i j) =
    W.presheaf.map (homOfLE (inf_le_left : (pres p i).V ⊓ (pres p j).V ≤ _)).op (t p i k)

  yq : ∀ p i, (Σ k, ι k) → Fin (pres p i).n

  yt : ∀ p i, Fin (m p) → Fin (pres p i).n
  sec_yq : ∀ p i q, (pres p i).secHom (X (yq p i q)) =
    π.appLE _ (pres p i).V (le_pres p i) (chartCoord hP p q)
  sec_yt : ∀ p i k, (pres p i).secHom (X (yt p i k)) = t p i k

  gen : ∀ p i (l : Fin (pres p i).n), ∃ F : MvPolynomial (Fin (pres p i).n) ℂ,
    F.vars ⊆ Finset.univ.image (yq p i) ∪ Finset.univ.image (yt p i) ∧ X l - F ∈ (pres p i).K

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjLogResCOfCR
section
open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

namespace FinalTheorems

def GFLogStC : Prop :=
  ∀ (X : Scheme.{0}) [IsNoetherian X], (∃ f : X ⟶ Spec (CommRingCat.of ℂ), LocallyOfFiniteType f) →
    QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B

theorem gfLogStC_of_CR (h : GFLogStCR.{0}) : GFLogStC := fun X _ _ a b c B d e => h X a b c B d e

end FinalTheorems

def ProjLogResC : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P), IsMultiHomogIdeal D → P.IsRadical →
    (∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0) →
    (∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q) → FinalTheorems.LogResStC (projX P hP) (projB P D hP)

theorem projLogResC_of_C (hC : FinalTheorems.GFLogStC) (hQ : FinalTheorems.FinTypeQE) : ProjLogResC :=
  fun _ _ _ _ _ P _ hP hD hrad hsing hmin => by
    have hft : LocallyOfFiniteType (toSpecC hP) := by
      classical
      let := segreGraded hP
      let A := MvPolynomial ((k : _) → _) ℂ ⧸ segreIdeal P
      have : Algebra.FiniteType ℂ A :=
        Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (segreIdeal P))
          (Ideal.Quotient.mkₐ_surjective ℂ _)
      have : IsScalarTower ℂ (segreGrading P 0) A :=
        IsScalarTower.of_algebraMap_eq fun c => by
          rw [← SetLike.GradeZero.coe_algebraMap (segreGrading P) c]
          rfl
      have : Algebra.FiniteType (segreGrading P 0) A :=
        Algebra.FiniteType.of_restrictScalars_finiteType ℂ (segreGrading P 0) A
      have hsurj : Function.Surjective (algebraMap ℂ (segreGrading P 0)) := by
        rintro ⟨x, hx⟩
        obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hx
        have hq' : q.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 q).1 hq
        refine ⟨q.coeff 0, ?_⟩
        apply Subtype.ext
        rw [SetLike.GradeZero.coe_algebraMap]
        by_cases h0 : q = 0
        · subst q
          simp
        · have hCq : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (hq'.totalDegree h0)
          show _ = (Ideal.Quotient.mkₐ ℂ (segreIdeal P)) q
          nth_rewrite 2 [hCq]
          exact ((Ideal.Quotient.mkₐ ℂ _).commutes (q.coeff 0)).symm
      have hbase : LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.FiniteType.of_surjective _ hsurj
      have hproj : LocallyOfFiniteType (Proj.toSpecZero (segreGrading P)) := inferInstance
      exact @locallyOfFiniteType_comp _ _ _ (Proj.toSpecZero (segreGrading P)) _ hproj hbase
    exact hC (projX P hP) ⟨toSpecC hP, hft⟩
      (qe_projX hP hQ) (isReduced_projX hP hrad) (fFinRes_projX hP) _
      (sing_subset_projB hP hD hQ hsing) (interior_projB hP hD hmin)

theorem projLogResC_of_CR (hC : FinalTheorems.GFLogStCR.{0}) (hQ : FinalTheorems.FinTypeQE) : ProjLogResC :=
  projLogResC_of_C (FinalTheorems.gfLogStC_of_CR hC) hQ

end ReciprocityTheory.AnForm.R
end

