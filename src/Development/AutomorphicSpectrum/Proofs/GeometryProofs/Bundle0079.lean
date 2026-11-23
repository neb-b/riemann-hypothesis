module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeTwo
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasesChangeByBlockMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem det_eq_det_mul_det_of_block {K : Type} [Field K] {p q : ℕ} (M : Matrix (Fin (p + q)) (Fin (p + q)) K)
    (P : Matrix (Fin p) (Fin p) K) (D : Matrix (Fin q) (Fin q) K)
    (h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k)
    (h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0)
    (h22 : ∀ j l, M (Fin.natAdd p j) (Fin.natAdd p l) = D j l) : M.det = P.det * D.det := by
  have hM : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks P (Matrix.of fun i l => M (Fin.castAdd q i) (Fin.natAdd p l)) 0 D := by
    ext a b
    rcases a with i | j <;> rcases b with k | l
    · simp [h11]
    · simp
    · simp [h21]
    · simp [h22]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, hM, Matrix.det_fromBlocks_zero₂₁]

theorem exists_det_mul_eq_of_isAdapted
    (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v v' : Fin p → W) (w w' : Fin q → W)
    (u u' : Fin (p + q) → W × Module.Dual K W) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K) :
    IsAdapted ρH σ v w u → IsAdapted ρH σ v' w' u' → LinearIndependent K v →
    Submodule.span K (Set.range u) = HT.eigSp ρH σ →
    (∀ i, v' i = ∑ k, P i k • v k) → (∀ i, w' i = ∑ k, Q i k • w k) →
    ∃ B : Matrix (Fin (p + q)) (Fin (p + q)) K, (∀ i, u' i = ∑ k, B i k • u k) ∧ B.det * Q.det = P.det := by
  intro h h' hv hspan hP hQ
  obtain ⟨-, h1, h2⟩ := h
  obtain ⟨he', h1', h2'⟩ := h'
  have hex : ∀ i, ∃ c : Fin (p + q) → K, ∑ k, c k • u k = u' i := fun i => by
    rw [← Submodule.mem_span_range_iff_exists_fun, hspan]
    exact he' i
  choose B hB using hex
  let M : Matrix (Fin (p + q)) (Fin (p + q)) K := Matrix.of B
  have hMB : ∀ i k, M i k = B i k := fun _ _ => rfl
  refine ⟨M, fun i => (hB i).symm, ?_⟩
  have hfst : ∀ i, (u' i).1 = ∑ k : Fin p, M i (Fin.castAdd q k) • v k := fun i => by
    rw [← hB i, Prod.fst_sum, Fin.sum_univ_add]
    simp [h1, (h2 _).1, hMB]
  have h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k := fun i k => by
    have e := (hfst (Fin.castAdd q i)).symm.trans ((h1' i).trans (hP i))
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    simp only [← sub_smul] at e
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ e k)
  have h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0 := fun j k => by
    have e := (hfst (Fin.natAdd p j)).symm.trans (h2' j).1
    exact Fintype.linearIndependent_iff.1 hv _ e k
  have hsnd : ∀ j, (u' (Fin.natAdd p j)).2 =
      ∑ l : Fin q, M (Fin.natAdd p j) (Fin.natAdd p l) • (u (Fin.natAdd p l)).2 := fun j => by
    rw [← hB (Fin.natAdd p j), Prod.snd_sum, Fin.sum_univ_add]
    simp only [← hMB, Prod.smul_snd, h21, zero_smul, Prod.snd_zero, Finset.sum_const_zero, _root_.zero_add]
  let D : Matrix (Fin q) (Fin q) K := fun j l => M (Fin.natAdd p j) (Fin.natAdd p l)
  have hDQ : D * Q.transpose = 1 := by
    ext j j'
    have e := (h2' j).2 j'
    rw [hsnd j, hQ j'] at e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, (h2 _).2, smul_eq_mul] at e
    simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
  have hdet : M.det = P.det * D.det := det_eq_det_mul_det_of_block M P D h11 h21 fun _ _ => rfl
  have hDQd : D.det * Q.det = 1 := by
    rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hDQ, Matrix.det_one]
  rw [hdet, _root_.mul_assoc, hDQd, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasisSpansEigenspace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem adaptedFamily_isBasis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W)
    (u : Fin (p + q) → W × Module.Dual K W),
    IsAdapted ρH σ v w u → LinearIndependent K v → Module.finrank K (HT.eigSp ρH σ) = p + q →
    FiniteDimensional K (HT.eigSp ρH σ) →
    LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ ρH σ p q v w u hA hv hrank hfd
  obtain ⟨hmem, hfst, hsnd⟩ := hA
  have hz : ∀ j : Fin q, (u (Fin.natAdd p j)).1 = 0 := fun j => (hsnd j).1
  have hli : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∑ i, g i • (u i).1 = 0 := by
      have := congrArg Prod.fst hg
      simpa [Prod.fst_sum] using this
    have h2 : ∑ i, g i • (u i).2 = 0 := by
      have := congrArg Prod.snd hg
      simpa [Prod.snd_sum] using this
    rw [Fin.sum_univ_add] at h1 h2
    have h1' : ∑ i : Fin p, g (Fin.castAdd q i) • v i = 0 := by
      simpa [hfst, hz] using h1
    have hcast : ∀ i : Fin p, g (Fin.castAdd q i) = 0 :=
      (Fintype.linearIndependent_iff.mp hv) _ h1'
    have h2' : ∑ j : Fin q, g (Fin.natAdd p j) • (u (Fin.natAdd p j)).2 = 0 := by
      simpa [hcast] using h2
    have hnat : ∀ j' : Fin q, g (Fin.natAdd p j') = 0 := by
      intro j'
      have h3 := congrArg (fun f : Module.Dual K W => f (w j')) h2'
      simpa [LinearMap.sum_apply, (hsnd _).2 j'] using h3
    intro i
    induction i using Fin.addCases with
    | left i => exact hcast i
    | right j => exact hnat j
  refine ⟨hli, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · rw [finrank_span_eq_card hli, Fintype.card_fin, hrank]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyDedekindConstants
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.CoordRead

noncomputable section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem map_flagStep {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] {r : ℕ}
    (f : E →ₗ[Ω] E') (v : Fin r → E) (i : ℕ) : (flagStep Ω v i).map f = flagStep Ω (f ∘ v) i := by
  simp only [flagStep, Submodule.map_span, Set.image_comp]

theorem lc_comp_basisFun {r : ℕ} (b : Fin r → V) :
    Fintype.linearCombination Ω b ∘ ⇑(Pi.basisFun Ω (Fin r)) = b := by
  classical
  funext i
  simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]

theorem flagStep_le_span {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b : Fin r → E) (i : ℕ) :
    flagStep Ω b i ≤ Submodule.span Ω (Set.range b) :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem exists_coords {r : ℕ} (b b' : Fin r → V) (h : ∀ i, flagStep Ω b' i = flagStep Ω b i) :
    ∃ b'c : Fin r → (Fin r → Ω), Fintype.linearCombination Ω b ∘ b'c = b' := by
  have hmem : ∀ k, b' k ∈ LinearMap.range (Fintype.linearCombination Ω b) := by
    intro k
    rw [Fintype.range_linearCombination]
    apply flagStep_le_span b r
    rw [← h r]
    exact Submodule.subset_span ⟨k, k.2, rfl⟩
  choose b'c hb'c using hmem
  exact ⟨b'c, funext hb'c⟩

theorem gr_comap {r : ℕ} (b : Fin r → V) (hb : LinearIndependent Ω b) (L : Lat ξ V) (i : Fin r) :
    (L.comap (Fintype.linearCombination Ω b)).gr (⇑(Pi.basisFun Ω (Fin r))) i = L.gr b i := by
  have hinj : Function.Injective (Fintype.linearCombination Ω b) := hb.fintypeLinearCombination_injective
  have hlc := lc_comp_basisFun (Ω := Ω) b
  have hfl : ∀ j, (flagStep Ω (⇑(Pi.basisFun Ω (Fin r))) j).map (Fintype.linearCombination Ω b) = flagStep Ω b j := by
    intro j; rw [map_flagStep, hlc]
  have he : ∀ j, Fintype.linearCombination Ω b (Pi.basisFun Ω (Fin r) j) = b j := fun j => congrFun hlc j
  funext q
  unfold Lat.gr
  congr 1
  ext t
  constructor
  · rintro ⟨z, hz, hzt⟩
    refine ⟨Fintype.linearCombination Ω b z, hz, ?_⟩
    have := Submodule.mem_map_of_mem (f := Fintype.linearCombination Ω b) hzt
    rwa [map_sub, map_smul, he, hfl] at this
  · rintro ⟨v, hv, hvt⟩
    have hvs : v ∈ LinearMap.range (Fintype.linearCombination Ω b) := by
      rw [Fintype.range_linearCombination]
      have h1 := flagStep_le_span b i hvt
      have h2 : t • b i ∈ Submodule.span Ω (Set.range b) :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      simpa using add_mem h1 h2
    obtain ⟨z, rfl⟩ := hvs
    refine ⟨z, hv, ?_⟩
    have : Fintype.linearCombination Ω b (z - t • Pi.basisFun Ω (Fin r) i) ∈
        (flagStep Ω (⇑(Pi.basisFun Ω (Fin r))) i).map (Fintype.linearCombination Ω b) := by
      rw [map_sub, map_smul, he, hfl]; exact hvt
    obtain ⟨w, hw, hwz⟩ := this
    rwa [← hinj hwz]

theorem isFlagVBOn_comap {r : ℕ} (b : Fin r → V) (hb : LinearIndependent Ω b) (L : Lat ξ V) (T : Set (Cpt ξ))
    (h : L.IsFlagVBOn T b) :
    (L.comap (Fintype.linearCombination Ω b)).IsFlagVBOn T (⇑(Pi.basisFun Ω (Fin r))) := by
  have hinj : Function.Injective (Fintype.linearCombination Ω b) := hb.fintypeLinearCombination_injective
  have hlc := lc_comp_basisFun (Ω := Ω) b
  intro p hp
  obtain ⟨U, hU, b', hfl, hfr⟩ := h p hp
  obtain ⟨b'c, hb'c⟩ := exists_coords b b' hfl
  refine ⟨U, hU, b'c, ?_, ?_⟩
  · intro i
    apply Submodule.map_injective_of_injective hinj
    rw [map_flagStep, map_flagStep, hb'c, hlc, hfl]
  · intro q hq hqU
    obtain ⟨hli, hsp⟩ := hfr q hq hqU
    refine ⟨LinearIndependent.of_comp (Fintype.linearCombination Ω b) (by rw [hb'c]; exact hli), ?_⟩
    show (L q).comap ((Fintype.linearCombination Ω b).restrictScalars (regAt ξ q)) = _
    have hinj' : Function.Injective ((Fintype.linearCombination Ω b).restrictScalars (regAt ξ q)) := hinj
    rw [hsp, ← hb'c, Set.range_comp]
    have : Submodule.span (regAt ξ q) (⇑(Fintype.linearCombination Ω b) '' Set.range b'c) =
        (Submodule.span (regAt ξ q) (Set.range b'c)).map ((Fintype.linearCombination Ω b).restrictScalars (regAt ξ q)) := by
      rw [Submodule.map_span]; rfl
    rw [this, Submodule.comap_map_eq_of_injective hinj']

end

end GlobalTheory.CompanionTheory.Ar.CoordRead

namespace GlobalTheory.CompanionTheory.Ar.CoordRead

theorem flagPair_coord : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) →
    HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m]
      [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ →
    ∀ (V : Type) [AddCommGroup V] [Module Ω V] (r : ℕ) (b : Fin r → V), LinearIndependent Ω b →
    ∀ (L L' : Lat ξ V) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' b Q →
      (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) →
      ∃ (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
        (∀ c, segreVec y c ≠ 0 → B.lat c = coordLat O y L b c ∧ B'.lat c = coordLat O y L' b c) ∧
        IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  intro X Ω _ ξ K _ _ J _ y hT d hd A _ _ _ _ hA hC p hp m _ hm O _ _ _ _ _ _ _ ϖ hϖ V _ _ r b hb L L' Q hP hoff
  have hpair : IsLatFlagPair y (overPrime ξ p) (L.comap (Fintype.linearCombination Ω b))
      (L'.comap (Fintype.linearCombination Ω b)) (⇑(Pi.basisFun Ω (Fin r))) Q := by
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨isFlagVBOn_comap b hb L _ h1, isFlagVBOn_comap b hb L' _ h2, fun i => ?_⟩
    rw [gr_comap b hb L i, gr_comap b hb L' i]
    exact h3 i
  have hoff' : ∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q →
      (L.comap (Fintype.linearCombination Ω b)) q = (L'.comap (Fintype.linearCombination Ω b)) q := by
    intro q h1 h2
    show (L q).comap _ = (L' q).comap _
    rw [hoff q h1 h2]
  obtain ⟨B, B', v, v', hlat, -, -, hfp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatFlag.flag_pair_of_lat X Ω ξ K J y hT d hd A hA hC p hp m hm O ϖ hϖ
    (Fin r → Ω) r (Pi.basisFun Ω (Fin r)) (L.comap (Fintype.linearCombination Ω b))
    (L'.comap (Fintype.linearCombination Ω b)) Q hpair hoff'
  refine ⟨B, B', v, v', fun c hc => ⟨AddSubgroup.ext fun z => ?_, AddSubgroup.ext fun z => ?_⟩, hfp⟩
  · rw [(hlat c hc z).1]
    simp only [coordLat, AddSubgroup.mem_iInf]
    rfl
  · rw [(hlat c hc z).2]
    simp only [coordLat, AddSubgroup.mem_iInf]
    rfl

end GlobalTheory.CompanionTheory.Ar.CoordRead
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseConstantsRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase

theorem algebraMap_mem_regAt_of_base : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (s : X ⟶ Sp O), ξ ≫ s = spMap (algebraMap O Ω) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p := by
  intro X Ω _ ξ O _ _ s hs p o
  exact ⟨_, ConstReg.genMap_germ_const ξ s hs p o⟩

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.RegBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BasisOfSubmoduleIffUniqueCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem basis_iff_unique_combinations : ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] (S : Submodule K W) (n : ℕ) (b : Fin n → W),
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = S) ↔
      (∀ i, b i ∈ S) ∧ ∀ e ∈ S, ∃! x : Fin n → K, e = ∑ i, x i • b i := by
  intro K W _ _ _ S n b
  constructor
  · rintro ⟨hli, hspan⟩
    refine ⟨fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩, fun e he => ?_⟩
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at he
    obtain ⟨x, hx⟩ := he
    refine ⟨x, hx.symm, fun y hy => ?_⟩
    have h0 : ∑ i, (y - x) i • b i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, hx, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  · rintro ⟨hb, huniq⟩
    refine ⟨Fintype.linearIndependent_iff.mpr fun g hg i => ?_, le_antisymm ?_ fun e he => ?_⟩
    · obtain ⟨x, _, hx⟩ := huniq 0 S.zero_mem
      have hg0 : g = x := hx g hg.symm
      have h00 : (0 : Fin n → K) = x := hx 0 (by simp)
      rw [hg0, ← h00]
      rfl
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)
    · obtain ⟨x, hx, _⟩ := huniq e he
      rw [hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TieArith

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar ReciprocityTheory.ChartRestriction.G.AI.I4

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem aeval_eq_ratioPt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    MvPolynomial.aeval y g = MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have h1 := mConeMap_eq_scale y c hc g
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hg, ConeTrdeg.mConeMap_of_isMultiHomog (ratioPt y c) hg] at h1
  have h2 : scaleT (fun k ↦ y ⟨k, c k⟩)
      (MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g) * ∏ k, MvPolynomial.X k ^ d k) =
      MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k) *
        ∏ k, MvPolynomial.X k ^ d k := by
    simp only [scaleT, map_mul, map_prod, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, mul_pow, Finset.prod_mul_distrib]
    ring
  rw [h2] at h1
  have h3 : (∏ k, MvPolynomial.X k ^ d k : MvPolynomial K Ω) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k)
  exact MvPolynomial.C_injective _ _ (mul_right_cancel₀ h3 h1)

theorem birational_of_ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) : Birational y := by
  intro s
  obtain ⟨d, g, h, hg, hh, n, e⟩ := rep_of_mem y c hc (x := s) (by rw [htop]; trivial)
  have hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · rw [aeval_eq_ratioPt y c hc hh]
    exact mul_ne_zero n hU
  · rw [aeval_eq_ratioPt y c hc hg, aeval_eq_ratioPt y c hc hh, e, _root_.mul_assoc]

theorem isArithVar_of_ratioField_eq_top [Nonempty K] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hd : Algebra.trdeg ℤ Ω = d) : IsArithVar (mCoordIdeal y) (d + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = d := by
    rw [hb, ← hd]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr]
  have h4 : (((d : Cardinal) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    rw [map_add (f := _), Cardinal.toENat_nat, Cardinal.toENat_nat]
    push_cast
    ring
  rw [h4]
  rfl

end Forms

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

def genCpt : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
    Scheme.stalkClosedPointTo ξ).hom s = a
  rw [e]
  exact hs

variable {K : Type} [Fintype K] {J : K → Type} [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)

theorem adjoin_le_ratioField {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) : a ∈ ratioField y c := by
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ (ratioField y c).toSubalgebra.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show _ ∈ ratioField y c
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, j k⟩, rfl⟩
  exact hle ha

end Chart

end GlobalTheory.CompanionTheory.Ar.TieArith

namespace GlobalTheory.CompanionTheory.Ar


open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar TieArith in
theorem coordTie_birational_isArithVar (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [Nonempty K] [CharZero Ω] (d : ℕ)
    (h : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hd : Algebra.trdeg ℤ Ω = d) : Birational y ∧ IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨c, hchart⟩ := h.cover (TieArith.genCpt ξ)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦
    (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)
  have htop : GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨s, hs, hu, hsa⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ _ _ h c (TieArith.genCpt ξ) hchart a).mp
      (TieArith.mem_regAt_genCpt ξ h.gen a)
    have h1 := TieArith.adjoin_le_ratioField y c hs
    have h2 := TieArith.adjoin_le_ratioField y c hsa
    have h3 := div_mem h2 h1
    rwa [mul_div_cancel_left₀ _ hu.1] at h3
  exact ⟨TieArith.birational_of_ratioField_eq_top y c hc htop,
    TieArith.isArithVar_of_ratioField_eq_top y c hc htop d hd⟩

end GlobalTheory.CompanionTheory.Ar
end
end

