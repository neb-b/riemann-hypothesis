module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.DescendLam
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.descendLam :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A') (D' : GDet n A' G), Function.Injective ι →
    (∀ i ≤ n, ∀ g : G, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range) → ∃! D : GDet n A G, D.map ι = D' := by
  intro n A G _ _ A' _ ι D' hι h
  refine UpperTheory.V.AlgebraTools.Det.descend ι D' hι fun m g β => ?_
  refine (Subring.closure_le (t := ι.range)).2 ?_ (UpperTheory.V.AlgebraTools.Det.amitsurSub D' m g β)
  rintro a ⟨i, hi, s, rfl⟩
  exact h i hi s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtDense
section
open Polynomial TensorProduct UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extDense :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [T2Space A] [TopologicalSpace G] (D D' : GDet n A G) (S : Set G), Dense S →
    (∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1)) →
    (∀ i ≤ n, Continuous fun g : G => D'.lam i (MonoidAlgebra.single g 1)) →
    (∀ g ∈ S, D.chi (MonoidAlgebra.single g 1) = D'.chi (MonoidAlgebra.single g 1)) → D = D' := by
  intro n A G _ _ _ _ _ D D' S hS hc hc' hchi
  have hlam (g : G) (i : ℕ) (hi : i ≤ n) :
      D.lam i (MonoidAlgebra.single g 1) = D'.lam i (MonoidAlgebra.single g 1) := by
    have h := Continuous.ext_on hS (hc i hi) (hc' i hi) (fun x hx => by
      show (-1) ^ i * (D.chi _).coeff (n - i) = (-1) ^ i * (D'.chi _).coeff (n - i)
      rw [hchi x hx])
    exact congrFun h g
  have htoDet (F : GDet n A G) (y : MonoidAlgebra A G) (i : ℕ) :
      F.toDet.lam i y = F.lam i y := by
    have h : F.toDet.chi y = F.chi y := by
      change F.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
        F.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
      congr 1
      rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def,
        MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rfl
    unfold Det.lam GDet.lam
    rw [h]
  have hdet : D.toDet = D'.toDet := by
    refine UpperTheory.V.CA.d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_
    · rw [Submodule.eq_top_iff']
      intro x
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | single g r =>
        have h : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A) := by simp
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rintro x ⟨g, rfl⟩ i _ hi
      rw [htoDet, htoDet]
      exact hlam g i hi
  rw [← GDet.ofDet_toDet D, hdet, GDet.ofDet_toDet]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.PolarIffLam
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_single_X_sub_mapRingHom_C {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (x : MonoidAlgebra R F.G₀) :
    F.star O R[X] n (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C x) = MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C (F.star O R n x) := by
  have h1 : pushCh (C : R →+* R[X]) (F.eps O R) = F.eps O R[X] := by
    ext x
    simp [GFrame.eps, pushCh, Polynomial.coeff_C, Finsupp.single_apply, eq_comm]
  have he : ∀ (h : F.G₀) (k : ℤ), (C : R →+* R[X]) ((F.eps O R h ^ k : Rˣ) : R) = ((F.eps O R[X] h ^ k : R[X]ˣ) : R[X]) := by
    intro h k
    rw [← h1, pushCh, MonoidHom.comp_apply, ← map_zpow (Units.map ((C : R →+* R[X]) : R →* R[X]))]
    rfl
  have hs : ∀ (S : Type) [CommRing S] [Algebra O S] (h : F.G₀) (r : S), F.star O S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hadd : ∀ (S : Type) [CommRing S] [Algebra O S] (a b : MonoidAlgebra S F.G₀), F.star O S n (a + b) = F.star O S n a + F.star O S n b := by
    intro S _ _ a b
    simp [GFrame.star]
  have hsub : ∀ a b : MonoidAlgebra R[X] F.G₀, F.star O R[X] n (a - b) = F.star O R[X] n a - F.star O R[X] n b := by
    intro a b
    simp [GFrame.star]
  have hz : ∀ (S : Type) [CommRing S] [Algebra O S], F.star O S n 0 = 0 := by
    intro S _ _
    simp [GFrame.star]
  have hone : F.star O R[X] n (MonoidAlgebra.single 1 X) = MonoidAlgebra.single 1 X := by
    rw [hs]
    simp
  have hmap : MonoidAlgebra.mapRingHom F.G₀ C (F.star O R n x) = F.star O R[X] n (MonoidAlgebra.mapRingHom F.G₀ C x) := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => rw [hz, map_zero, hz]
    | add a b ha hb => rw [hadd, map_add (f := _), ha, hb, map_add (f := _), hadd]
    | single h r =>
      rw [hs, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, hs, map_mul, he]
  rw [hsub, hone, hmap]

theorem UpperTheory.V.AlgebraTools.Det.polarIffLam :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), F.IsPolar O D ↔
    ∀ i g, D.lam i (F.star O R n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1) := by
  intro l _ F O _ _ R _ _ n D
  obtain ⟨D', hD'⟩ := AlgebraTools.Det.starDet F O R n D
  have hchi : ∀ y, D'.chi y = D.chi (F.star O R n y) := by
    intro y
    simp only [GDet.chi]
    rw [hD' R[X], star_single_X_sub_mapRingHom_C]
  have hlam : ∀ i y, D'.lam i y = D.lam i (F.star O R n y) := by
    intro i y
    simp only [GDet.lam, hchi]
  constructor
  · intro hP i g
    have hc : D.chi (F.star O R n (MonoidAlgebra.single g 1)) = D.chi (MonoidAlgebra.single g 1) := by
      simp only [GDet.chi]
      rw [← star_single_X_sub_mapRingHom_C]
      exact hP R[X] _
    simp only [GDet.lam, hc]
  · intro h
    have hDD : D' = D := by
      apply CA.d_gext
      intro g i _ _
      rw [hlam]
      exact h i g
    intro B _ _ _ _ y
    rw [← hD' B y, hDD]
end

