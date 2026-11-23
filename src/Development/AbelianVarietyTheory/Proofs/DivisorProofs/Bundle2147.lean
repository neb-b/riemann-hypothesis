module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secIsMul_of_germ_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  intro R _ _ X p hp L s q hq h
  haveI : Flat (X := X) (Y := Sp R) p := hp
  have loc : ∀ j, ∃ g : Γ(X, L.U j), s.f j = constFn p (L.U j) q * g := fun j =>
    exists_div p hq (L.U j) (s.f j) (fun x hx => h x j hx)
  choose t ht using loc
  have hg : ∀ j (x : X), x ∈ L.U j → gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * gs (𝟙 X) x (L.U j) (t j) := by
    intro j x hx
    rw [ht j, gs_mul _ _ _ hx, gs_constFn p (L.U j) (𝟙 X) x hx, Category.id_comp]
  refine ⟨⟨t, fun i j => ?_⟩, fun j => ?_⟩
  · refine fn_ext fun x hx => ?_
    have e := congrArg (gs (𝟙 X) x (L.U i ⊓ L.U j)) (s.compat i j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e ⊢
    rw [hg i x hx.1, hg j x hx.2, mul_left_comm] at e
    exact cst_regular p x hq e
  · exact ht j

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_away_cover_sm :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a,
          Sm (X := X) W (D := Localization.Away (s a))
            (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) := by
  intro R _ X K W hW D _ _ x
  let f : Sp D ⟶ X.left := x.left
  let S : Set D := {s | ∃ i, ∀ q : PrimeSpectrum D, q ∈ PrimeSpectrum.basicOpen s → f q ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    by_contra h'
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h'
    let p : PrimeSpectrum D := ⟨m, hm.isPrime⟩
    have hp : f p ∈ (⨆ i, W i) := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := f ⁻¹' (W i : Set X.left)) hi ((W i).isOpen.preimage f.continuous)
    have hsS : s ∈ S := ⟨i, fun q hq ↦ hsub hq⟩
    exact hs (hle (Ideal.subset_span hsS))
  have h1 : (1 : D) ∈ Submodule.span D S := by
    change (1 : D) ∈ Ideal.span S; rw [hS]; trivial
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun a ↦ (T.equivFin.symm a : D), ?_, ?_⟩
  · have hr : Set.range (fun a ↦ (T.equivFin.symm a : D)) = (T : Set D) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact (T.equivFin.symm a).2
      · intro hy; exact ⟨T.equivFin ⟨y, hy⟩, by simp⟩
    rw [hr, Ideal.eq_top_iff_one]; exact hT
  · intro a
    obtain ⟨i, hi⟩ := hTS (T.equivFin.symm a).2
    refine ⟨i, fun q _ ↦ ?_⟩
    have hq : (spMap (algebraMap D (Localization.Away ((T.equivFin.symm a : D)))) q : PrimeSpectrum D) ∈
        PrimeSpectrum.basicOpen ((T.equivFin.symm a : D)) :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away ((T.equivFin.symm a : D))) _).le ⟨q, rfl⟩
    exact hi _ hq

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellOfLeadingMinors
section
set_option autoImplicit false

namespace GlobalTheory.ShFam.Cell

open Matrix

variable {R : Type} [CommRing R]

theorem exists_lowInv_mul_upperUni_of_leadingMinors :
    ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (N.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, IsLowInv L ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧ N = L * U := by
  intro n
  induction n with
  | zero =>
    intro N _
    exact ⟨1, 1, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      by ext i; exact Fin.elim0 i⟩
  | succ n ih =>
    intro N hN
    set P : Matrix (Fin n) (Fin n) R := N.submatrix Fin.castSucc Fin.castSucc with hP
    have hPm : ∀ (k : ℕ) (hk : k ≤ n), IsUnit (P.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have e : P.submatrix (Fin.castLE hk) (Fin.castLE hk)
          = N.submatrix (Fin.castLE (hk.trans (Nat.le_succ n))) (Fin.castLE (hk.trans (Nat.le_succ n))) := by
        ext i j; rfl
      rw [e]; exact hN k _
    obtain ⟨L₀, U₀, ⟨hL₀z, hL₀d⟩, hU₀z, hU₀d, hPLU⟩ := ih P hPm
    have hdL₀ : IsUnit L₀.det := by
      rw [Matrix.det_of_isLowerTriangular L₀ (fun i j h => hL₀z i j h)]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hL₀d i)
    have hdU₀ : IsUnit U₀.det := by
      rw [Matrix.det_of_isUpperTriangular (M := U₀) (fun i j h => hU₀z i j h)]
      simp [hU₀d]
    set q : Fin n → R := fun i => N (Fin.castSucc i) (Fin.last n)
    set r : Fin n → R := fun j => N (Fin.last n) (Fin.castSucc j)
    set u : Fin n → R := L₀⁻¹ *ᵥ q with hu
    set l : Fin n → R := r ᵥ* U₀⁻¹ with hl
    set d : R := N (Fin.last n) (Fin.last n) - l ⬝ᵥ u with hd
    have hq : L₀ *ᵥ u = q := by rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdL₀, Matrix.one_mulVec]
    have hr : l ᵥ* U₀ = r := by rw [hl, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdU₀, Matrix.vecMul_one]
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases d l j) (fun i' => Fin.lastCases 0 (fun j' => L₀ i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases (u i') (fun j' => U₀ i' j') j) i
    have hLz : ∀ i j, i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i' =>
        induction j using Fin.lastCases with
        | last => simp [L]
        | cast j' => simpa [L] using hL₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hLdiag : ∀ i, L i i = Fin.lastCases d (fun i' => L₀ i' i') i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [L]
      | cast i' => simp [L]
    have hUz : ∀ i j, j < i → U i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j' => simp [U]
      | cast i' =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j' => simpa [U] using hU₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hUd : ∀ i, U i i = 1 := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [U]
      | cast i' => simpa [U] using hU₀d i'
    have hNLU : N = L * U := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one]
          rw [hd]; simp [dotProduct]
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]
          have := congrFun hr j'
          simpa [vecMul, dotProduct, r] using this.symm
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one, add_zero]
          have := congrFun hq i'
          simpa [mulVec, dotProduct, q] using this.symm
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul, add_zero]
          have := congrFun (congrFun hPLU i') j'
          simpa [hP, Matrix.mul_apply] using this
    have hdet : IsUnit L.det := by
      have h1 : N.det = L.det * U.det := by rw [hNLU, Matrix.det_mul]
      have h2 : U.det = 1 := by
        rw [Matrix.det_of_isUpperTriangular (M := U) (fun i j h => hUz i j h)]; simp [hUd]
      have h3 : N = N.submatrix (Fin.castLE (le_refl (n+1))) (Fin.castLE (le_refl (n+1))) := by
        ext i j; rfl
      have := hN (n+1) le_rfl
      rw [← h3, h1, h2, mul_one] at this
      exact this
    have hdu : IsUnit d := by
      rw [Matrix.det_of_isLowerTriangular L (fun i j h => hLz i j h), Fin.prod_univ_castSucc] at hdet
      have := isUnit_of_mul_isUnit_right hdet
      simpa [hLdiag] using this
    refine ⟨L, U, ⟨hLz, fun i => ?_⟩, hUz, hUd, hNLU⟩
    rw [hLdiag i]
    induction i using Fin.lastCases with
    | last => simpa using hdu
    | cast i' => simpa using hL₀d i'

end GlobalTheory.ShFam.Cell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentreOfValuationSubringProperDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProperCentre

theorem exists_regAt_centre : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsProper s]
    (V : ValuationSubring Y.functionField) (x : X), (∀ f, RegAt x f → functionFieldMap s f ∈ V) →
    ∃ y : Y, s y ⤳ x ∧ ∀ f, RegAt y f → f ∈ V := by
  intro X Y _ _ s _ _ V x h
  let ψ : X.presheaf.stalk x →+* V :=
    ((GlobalTheory.functionFieldMap s).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict
      V.toSubring (fun a => h _ ⟨a, rfl⟩)
  let r : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x
  have hc : GlobalTheory.genericFieldPoint Y ≫ s = GlobalTheory.specAlgebraMap V Y.functionField ≫ r := by
    rw [← GlobalTheory.specMap_functionFieldMap, ← GlobalTheory.specAlgebraMap_fromSpecStalk x]
    simp only [r, GlobalTheory.specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc, ?_, ?_⟩
  · rw [GlobalTheory.apply_valCentre_base]
    have := (IsLocalRing.specializes_closedPoint (R := X.presheaf.stalk x)
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk x).continuous
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact this
  · have hd : GlobalTheory.DominatesStalk V (GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc) :=
      GlobalTheory.dominatesStalk_iff_exists_hom.mpr
        ⟨_, GlobalTheory.specAlgebraMap_valExt s r (GlobalTheory.genericFieldPoint Y) hc, rfl⟩
    rintro f ⟨a, rfl⟩
    exact hd.1 a

end GlobalTheory.ProperCentre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.AbCl

theorem exists_te {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] (v : epsR R ⟶ D.P.A) :
    ∃ bb : TE R ℂ ⟶ D.P.A, bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left := by
  refine ⟨Over.homMk (spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ v.left) ?_, rfl⟩
  rw [Category.assoc, Over.w v]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isD_unique {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {ν : NumOf D ℂ N} {g : ℕ} {d : AB N.toNumB g} {b₀ b : TE R ℂ ⟶ D.P.A} {W₀ W₁ W₂ : Fin g → ℂ}
    (h₀ : ∀ W', IsD ν d W' b₀ ↔ W' = W₀) (h₁ : IsD ν d W₁ b) (h₂ : IsD ν d W₂ b) : W₁ = W₂ := by
  have key : IsD ν d (W₀ + (W₁ - W₂)) b₀ := by
    intro U f hU
    rw [(h₀ W₀).2 rfl U f hU]
    have e := congrArg TrivSqZeroExt.snd ((h₁ U f hU).symm.trans (h₂ U f hU))
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at e
    rw [map_add (f := _), map_sub, e, sub_self, add_zero]
  have := (h₀ _).1 key
  have h3 : W₁ - W₂ = 0 := by simpa using this
  exact sub_eq_zero.1 h3

theorem exists_ab_keyOK : ∀ κ : Rule, Rule4 κ → AllC fun {R} _ _ {D} _ {N} ν => 1 ≤ D.P.g → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ hκ R _ _ _ _ D hψ hτ _ N ν hg
  obtain ⟨th, hth, hcomp⟩ := _root_.GlobalTheory.DegTheta.exists_sec_nonvanishing R D ℂ N ν
  obtain ⟨vB₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.P.A D.P.smoothDim
  let y₀ : KeyIn R := ⟨D.P, hg, D.rig, D.rig_gen, th, hth, vB₀, hv₀⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB y₀ ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))
  have hg₀ : x₀.P.g = D.P.g := by obtain ⟨_, _, _, hgg, _⟩ := hx₀; exact hgg
  obtain ⟨u, τ, a, b, c, W, hNF⟩ := _root_.GlobalTheory.MBLow.Cl.exists_NF D.P.g x₀ hg₀
  obtain ⟨d, G, hdc, huniq⟩ := _root_.GlobalTheory.MBLow.Cl.exists_ab_geo_of_nf R D hψ hτ N ν y₀ rfl HEq.rfl ⟨th, HEq.rfl, hcomp⟩ x₀ hg₀ rfl u τ a b c W hx₀ hNF
  refine ⟨d, G, ?_⟩
  intro vB bs MB k₀ hv hbs hIsD hBK
  have hM : ∀ i, ∃ c : Fin D.P.g → R, IsLieComb c vB₀ (vB i) := fun i => (hv₀.2 (vB i) (hv.1 i)).exists
  choose M' hMc using hM
  let M : Matrix (Fin D.P.g) (Fin D.P.g) R := Matrix.of M'
  obtain ⟨x, hKx, hκx⟩ := _root_.GlobalTheory.KeyLieChg.exists_keyPB_det κ hκ.1 R y₀ x₀ _ hx₀ vB hv M hMc
  have hk : (κ ℂ x : ℂ) = k₀ := hBK.2 hg D.rig_gen th hth hv x hcomp hKx
  choose b₀ hb₀ using fun j => exists_te (D := D) (vB₀ j)
  have hW : ∀ j, ∀ W', IsD ν d W' (b₀ j) ↔ W' = W j := fun j => huniq vB₀ (fun i => HEq.rfl) j (b₀ j) (hb₀ j)
  have hlin : ∀ i, IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j) (bs i) :=
    fun i => GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb R D N ν D.P.g d D.P.g (M i) vB₀ (vB i) W b₀ (bs i) hv₀.1 (hMc i) hb₀ (hbs i) (fun j => (hW j _).2 rfl)
  have hrow : ∀ i, (2 * Real.pi * Complex.I : ℂ)⁻¹ • MB i =
      ∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (M i j)) • W j :=
    fun i => isD_unique (hW ⟨0, hg⟩) (hIsD i) (hlin i)
  have h2π : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let Mx : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := Matrix.of fun j k => (2 * Real.pi * Complex.I : ℂ) * W j k
  have hNF' : NF x₀ hg₀ u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
    have e : (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) = W := by
      funext j k
      show (2 * Real.pi * Complex.I : ℂ)⁻¹ * ((2 * Real.pi * Complex.I : ℂ) * W j k) = W j k
      rw [← _root_.mul_assoc, inv_mul_cancel₀ h2π, _root_.one_mul]
    rw [e]; exact hNF
  obtain ⟨hdet, hval⟩ := _root_.GlobalTheory.MBLow.Cl.key_value_of_nf κ hκ.1 hκ.2.2.1 D.P.g x₀ hg₀ u τ a b c Mx hNF'
  have hMB : MB = (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) * Mx := by
    ext i k
    have e := congrFun (hrow i) k
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at e
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Mx, Matrix.of_apply, RingHom.comp_apply]
    calc MB i k = (2 * Real.pi * Complex.I : ℂ) * ((2 * Real.pi * Complex.I : ℂ)⁻¹ * MB i k) := by field_simp
      _ = _ := by rw [e, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by simp [M]; ring
  have hne : (κ ℂ x : ℂ) ≠ 0 := Units.ne_zero _
  rw [hMB, Matrix.det_mul]
  rw [hκx] at hk hne
  have hf : (M.map ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))).det ≠ 0 := by
    intro h0; apply hne; rw [h0]; ring
  refine ⟨mul_ne_zero hf hdet, ?_⟩
  rw [← hk, hdc, _root_.mul_assoc, hval]
  ring

end GlobalTheory.MBLow.AbCl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedNullSetCharts
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Points (PtsOver)

namespace GlobalTheory.Mean4O.CoverExc

section Model

variable {F : Type} [Field F] [NumberField F] {X G : Scheme.{0}} {p : X ⟶ Sp (𝓞 F)} {q : G ⟶ Sp F} {j : G ⟶ X}


end Model

section Fibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q)


include hπ in
theorem app_algX (U : X.Opens) (a : k) : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := by
  have hw : π ≫ p = q ≫ spMap (RingHom.id k) := by
    rw [hπ, show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := q) (φ := π)
    (σ := RingHom.id k) hw (V := U) (W := π ⁻¹ᵁ U) le_rfl) a
  simpa [Scheme.Hom.app_eq_appLE] using this.symm


include hπ in
theorem etale_app {U : X.Opens} {e : ℕ} {x : Fin e → Γ(X, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale)
    (het : (π.app U).hom.Etale) :
    (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)).Etale := by
  have hcx : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)) =
      (π.app U).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simp [app_algX π hπ]
    · simp
  rw [hcx]
  exact RingHom.Etale.stableUnderComposition _ _ hx het

end Fibre

end GlobalTheory.Mean4O.CoverExc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffwiseDerivationMvPowerSeries
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

theorem mvPowerSeries_derivation_coeffwise (σ R : Type) [CommRing R] (D : Derivation ℤ R R) :
    ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R),
      ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  classical
  let L : MvPowerSeries σ R →ₗ[ℤ] MvPowerSeries σ R :=
    { toFun := fun F => fun α => D (MvPowerSeries.coeff α F)
      map_add' := by
        intro F G
        funext α
        show D (MvPowerSeries.coeff α (F + G)) = D (MvPowerSeries.coeff α F) + D (MvPowerSeries.coeff α G)
        rw [map_add (f := _), map_add (f := _)]
      map_smul' := by
        intro n F
        funext α
        show D (MvPowerSeries.coeff α (n • F)) = n • D (MvPowerSeries.coeff α F)
        rw [map_zsmul, map_zsmul] }
  have hL : ∀ F α, MvPowerSeries.coeff α (L F) = D (MvPowerSeries.coeff α F) := fun _ _ => rfl
  refine ⟨Derivation.mk' L ?_, ?_⟩
  · intro F G
    ext α
    rw [smul_eq_mul, smul_eq_mul, map_add (f := _)]
    erw [hL]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPowerSeries.coeff_mul, map_sum,
      MvPowerSeries.coeff_mul, mul_comm G, MvPowerSeries.coeff_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    erw [hL, hL]
    exact congrArg (_ + ·) (mul_comm _ _)
  · intro F α
    rfl

end GlobalTheory
end

