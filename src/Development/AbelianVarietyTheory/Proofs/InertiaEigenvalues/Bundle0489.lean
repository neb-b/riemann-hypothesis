module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.CrysCoef

open Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {L L' : Type} [Field L] [Algebra Qp L] [Field L'] [Algebra Qp L']

theorem isCrys_mapM [Algebra L L'] [IsScalarTower Qp L L'] [FiniteDimensional L L']
    {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) L) (h : IsCrys PD (matRep M)) :
    IsCrys PD (matRep (mapM (algebraMap L L') M)) := by
  let e := Module.finBasis L L'
  let E : (Fin k → L') ≃ₗ[L] (Fin (finrank L L') → Fin k → L) :=
    { toFun := fun v j i => e.repr (v i) j
      invFun := fun w i => e.equivFun.symm fun j => w j i
      map_add' := fun x y => by funext j i; simp
      map_smul' := fun c x => by funext j i; simp
      left_inv := fun v => by
        funext i
        exact e.equivFun.symm_apply_apply (v i)
      right_inv := fun w => by
        funext j i
        exact congrFun (e.equivFun.apply_symm_apply fun j => w j i) j }
  have : Nonempty (Fin (finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine GlobalTheory.CoeffExt.isCrys_ext PD (E := E) (fun g x j => ?_) (Fintype.card_fin _).symm h
  funext i
  change e.repr (∑ a, algebraMap L L' (M g i a) * x a) j = ∑ a, M g i a * e.repr (x a) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← Algebra.smul_def, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]

end Generic

theorem isCrys_inclusion (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L L' : FinExt l) (h : L.1 ≤ L'.1) (k : ℕ)
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥L.1) (hM : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep (mapM (IntermediateField.inclusion h).toRingHom M)) := by
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 ↥L'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion h).commutes x).symm
  haveI := L'.2
  haveI : FiniteDimensional ↥L.1 ↥L'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  exact isCrys_mapM (P.PD K) M hM

end GlobalTheory.CrysCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomPowerSeriesOfRankOneImage
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TruncationDivisibility

theorem deltaS_X (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] : (deltaS l a).δ (X : (Wq l a)⟦X⟧) = 0 := by
  have h := (deltaS l a).φ_eq X
  have h2 : (deltaS l a).φ X = X ^ l := by
    change (Delta.ofLift l (frobS l a) _ _).φ X = _
    rw [Delta.ofLift_φ, frobS_X]
  rw [h2] at h
  have h3 : (l : (Wq l a)⟦X⟧) * (deltaS l a).δ X = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h3).resolve_left (l_ne_zero l a)

theorem X_pow_dvd_sub_trunc' {R : Type} [CommRing R] (x : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ x - (trunc n x : R⟦X⟧) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self]

end GlobalTheory.TruncationDivisibility

open GlobalTheory.TruncationDivisibility in
theorem GlobalTheory.sdelta_of_rank_one : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ (σ : (Wq l a)⟦X⟧ →+* C) (e : ℕ), σ X ^ e ∈ J → DC.δ (σ X) = 0 → IsδMap (deltaS l a) DC σ := by
  intro l _ a _ C _ DC J hl hH σ e he hX
  set S := δLocus (deltaS l a) DC σ with hS
  have hXS : (X : (Wq l a)⟦X⟧) ∈ S := by
    rw [mem_δLocus, deltaS_X, map_zero, hX]
  have hCS : ∀ w : Wq l a, PowerSeries.C w ∈ S := GlobalTheory.T.C_mem_deltaCommuteLocusSubring_of_isHausdorff l a C DC J hl hH σ
  have hpoly : ∀ p : Polynomial (Wq l a), ((p : (Wq l a)⟦X⟧)) ∈ S := by
    intro p
    induction p using Polynomial.induction_on with
    | C w => rw [Polynomial.coe_C]; exact hCS w
    | add p q hp hq => rw [Polynomial.coe_add]; exact S.add_mem hp hq
    | monomial n w _ =>
      rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
      exact S.mul_mem (hCS w) (S.pow_mem hXS _)
  refine GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l ((Wq l a)⟦X⟧) C (deltaS l a) DC (J.comap σ) J σ ?_ Ideal.map_comap_le hH ?_
  · rw [Ideal.mem_comap, map_natCast]; exact hl
  · intro x n
    refine ⟨_, hpoly (trunc (e * n) x), ?_⟩
    obtain ⟨c, hc⟩ := X_pow_dvd_sub_trunc' x (e * n)
    rw [hc, pow_mul]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ n)
    rw [Ideal.mem_comap, map_pow]; exact he
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDual1Dot
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.JumpDual

def matG {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

theorem isDual1_dot {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {k : ℕ} (T U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (T g⁻¹).transpose) :
    IsDual1 PD (matRep T) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (T g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

theorem loc_cont (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    hM.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact h1.matrix_map hfc

theorem loc_dual (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw (rDuO D.nd i r x) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
        (Br.loc D.nbr i w hw (rTwO D.nd i r x) g⁻¹).transpose := by
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  rw [← GlobalTheory.CycBridge.locChi_epsU D i w hw g]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

theorem jump_dual : ∀ D : D7, DualJumpL D.loc → PotDRL D.loc → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ (x : ↥Xs) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) τ a ↔ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ (-a - 1) := by
  intro D hJ hP i r hr Xs w hw n hF x τ a
  obtain ⟨K', h, hN, hI, hS, Sig, Fr, -, -, -, -, hx⟩ := hF
  have hc := _root_.GlobalTheory.Pass.FamCont.stepCont D i r hr x
  have cT := loc_cont D i w hw _ hc.1
  have cU := loc_cont D i w hw _ hc.2
  have hcr := (_root_.GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hI hS _
    (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))).2.1 (hx x).1
  have hdR := hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) hcr
  exact hJ (D.nd.l i) (D.nbr i w hw).Kw (D.nbr i w hw).LL
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cU)
    (dotProductBilin _ _) (isDual1_dot _ _ _ (loc_dual D i w hw r x)) hdR τ a

end GlobalTheory.JumpDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalHomOfNatCast
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.SelmerSameChar

theorem isLocalHom_of_natCast {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B]
    (f : O →+* B) (l : ℕ) (h0 : (l : O) ≠ 0) (h : ¬ IsUnit (l : B)) : IsLocalHom f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hu : ¬ IsUnit (f ϖ) := fun hu => h (by
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [← map_natCast f, hn, map_mul, map_pow]
    exact (u.isUnit.map f).mul (hu.pow n))
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ IsLocalRing.maximalIdeal O := hn
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [map_mul] at hx
  exact hu (isUnit_of_mul_isUnit_right hx)

theorem isIntegral_of_finite {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂) {O₀ O : Type}
    [CommRing O₀] [Algebra ℤ_[l₁] O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O]
    [Module.Finite ℤ_[l₂] O] (f : O₀ →+* O) : f.IsIntegral := by
  subst h
  cases Subsingleton.elim i₁ i₂
  refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l₁] O₀) f ?_
  rw [padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O)]
  exact algebraMap_isIntegral_iff.2 inferInstance

variable (D : D7)

theorem sT_congr (i : D.ntw.Tw) (s : D.ntw.Sig i) (Q : Finset (PlE D.host)) {O : Type} [CommRing O] [IsDomain O]
    {f f' : D.ntw.O0 i →+* O} (hf : Function.Injective f) (hf' : Function.Injective f')
    {ψ ψ' : Formalism.MainNotions.N.GE D.nd →* Oˣ} (h1 : f = f') (h2 : ψ = ψ') :
    sT D.loc D.ntwbr i s Q f hf ψ = sT D.loc D.ntwbr i s Q f' hf' ψ' := by
  subst h1 h2
  rfl

theorem toOk_local (i : D.ntw.Tw) (k : ℕ) : IsLocalHom (toOk D.ntw i k) := by
  have : CharZero (FractionRing (D.ntw.O0 i)) :=
    ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
  have : CharZero (D.ntw.O0 i) := (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero
  refine isLocalHom_of_natCast _ (D.ntw.l i) (Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero) fun hu => ?_
  have := D.ntw.Ok_fin i k
  have := RingHom.IsIntegral.isLocalHom (f := algebraMap (D.ntw.O i) (D.ntw.Ok i k))
    (algebraMap_isIntegral_iff.2 inferInstance) (D.ntw.Ok_inj i k)
  rw [← map_natCast (algebraMap (D.ntw.O i) (D.ntw.Ok i k))] at hu
  exact D.ntw.O_l i (isUnit_of_map_unit _ _ hu)

theorem sTLoc_eq : ∀ (D : D7) (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok (D.ntw.twOf a) k)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar (D.ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (D.ntw.psiL a) ψ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sTLoc D a s = GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw (D.ntw.twOf a) k) ψ := by
  intro D a s k ψ h
  obtain ⟨O₁, _, _, _, f, gA, gB, χ, iA, iB, lA, lB, cA, cB, eA, eB⟩ :=
    GlobalTheory.Proof.dvr_of_reflects_facts.common _ _ _ _ (D.ntw.twist₂ a) (toOk D.ntw _ k) (twO_inj D.ntw a)
      (isIntegral_of_finite (D.ntw.twOf_l a) _) (toOk_inj D.ntw _ k) (toOk_local D _ k) _ _ h
  have hf : Function.Injective f := Function.Injective.of_comp (f := gA) (by
    rw [← RingHom.coe_comp, cA]; exact twO_inj D.ntw a)
  exact (sT_congr D _ s _ _ (iA.comp hf) cA.symm eA.symm).trans
    ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gA iA χ).trans
      ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gB iB χ).symm.trans
        (sT_congr D _ s _ (iB.comp hf) _ cB eB)))

end GlobalTheory.SelmerSameChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtens
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Algebra Qp LL] [Field LL'] [Algebra Qp LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem isCrys_transport {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have key := PI.CoefExt.finrank_iInf_ker_equiv
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)) (actVB PD ρ) (actVB PD ρ') (fun g x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul v c => simp [actVB, he])
  unfold IsCrys at h ⊢
  rw [← e.finrank_eq, ← h]
  exact key

theorem isCrys_matrix_ext (f : LL →ₐ[Qp] LL') {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (h : IsCrys PD ρ) :
    IsCrys PD (CJ.rep ((f.mapMatrix : Matrix (Fin k) (Fin k) LL →ₐ[Qp]
      Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ))) := by
  letI : TopologicalSpace G := ⊥
  have h1 : IsCrys PD (CJ.rep ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)) := by
    refine isCrys_transport PD b.equivFun (fun g v => ?_) h
    change _ = (LinearMap.toMatrix b b (ρ g)).mulVec (b.repr v)
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  exact PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange PD f _ h1

end Gen

theorem isPotCrys_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb hT
  exact isCrys_matrix_ext (pc Pl h hN hF hS).PD' (incl hL) b ((pc Pl h hN hF hS).resH T.ρ) hT

end GlobalTheory.BaseCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtension
section
noncomputable section

namespace GlobalTheory.NT

open NumberField IsDedekindDomain

theorem isUnramifiedAt_of_unramIn {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (h : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver 𝔭.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) P := by
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have := 𝔭.isMaximal
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := (Ideal.over_def P 𝔭.asIdeal).symm
  have : (P.under (𝓞 K)).IsMaximal := by rw [hu]; infer_instance
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => h τ ⟨P, inferInstance, inferInstance, hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2.symm

end GlobalTheory.NT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDivisibleCoboundariesLeLocConstCocyclesAl
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BDLocConst

theorem lattice_divisible_coboundaries_le_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA c hc
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  obtain ⟨y, rfl⟩ := hc
  induction y using Submodule.Quotient.induction_on with
  | H x =>
  have hval : ∀ g, (LinearMap.pi (fun g => actD LA g - LinearMap.id) (Submodule.Quotient.mk x : A.V ⧸ LA.T)) g
      = Submodule.Quotient.mk (A.ρ g x - x) := by
    intro g
    rfl
  refine ⟨?_, ?_⟩
  · have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
    have := Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA.T hT (fun g => A.ρ g x - x) ((A.cont x).sub continuous_const)
    convert this using 1
    funext g
    exact hval g
  · intro g h
    rw [hval, hval, hval]
    show _ = Submodule.Quotient.mk (A.ρ g x - x) + Submodule.Quotient.mk (A.ρ g (A.ρ h x - x))
    rw [← Submodule.Quotient.mk_add, map_mul]
    congr 1
    simp only [Module.End.mul_apply, map_sub]
    abel

end GlobalTheory.BDLocConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOnto
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem extHom_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  intro l _ G _ _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hF
  choose x hx hfx using fun i => hF (b₂ i) (hb₂.1 i)
  have key : ∀ i j, ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m =
      (1 : Matrix (Fin k₂) (Fin k₂) ↥LL.1) i j := by
    intro i j
    have h1 := congrFun (LinearMap.toMatrix_mulVec_repr b₁ b₂ F.f (x j)) i
    rw [hfx j, Module.Basis.repr_self] at h1
    rw [Matrix.one_apply, ← show _ = ∑ m, LinearMap.toMatrix b₁ b₂ F.f i m * b₁.repr (x j) m from rfl.symm]
    refine Eq.trans h1 ?_
    rw [Finsupp.single_apply]
    simp only [eq_comm]
  let X : Matrix (Fin k₁) (Fin k₂) ↥LL'.1 := fun m j => incl hL (b₁.repr (x j) m)
  have hX : extMat hL b₁ b₂ F * X = 1 := by
    refine Matrix.ext fun i j => ?_
    have := congrArg (incl hL) (key i j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_mul] at this
    rw [Matrix.mul_apply]
    refine Eq.trans this ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  intro y hy
  refine ⟨X.mulVec y, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (incl_integral hL (hb₁.2 _ (hx j) i)) (hy j)
  · change (extMat hL b₁ b₂ F).mulVec (X.mulVec y) = y
    rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]

end GlobalTheory.BaseCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CycBridge

theorem locChi_epsU_eq_cycLL : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.locChi D.nbr i w hw (epsU D.nd i) = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) :=
  fun D i w hw => MonoidHom.ext (GlobalTheory.CycBridge.locChi_epsU D i w hw)

end GlobalTheory.CycBridge
end

