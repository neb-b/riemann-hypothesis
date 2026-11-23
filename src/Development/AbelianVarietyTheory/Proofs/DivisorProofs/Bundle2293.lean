module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisResidueFieldUniformiserCons
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTrBasis

open IsLocalRing

theorem trdeg_le_of_residue {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (S : Place cL) (ψ : S.ring →+* K) (hψ : Function.Surjective ψ)
    (hc : ∀ a, ψ (S.const a) = cK a) (m : ℕ) (x : Fin (m + 2) → L) (hx : TrBasis cL x) :
    letI := cK.toAlgebra
    Algebra.trdeg ℂ K ≤ (m + 1 : ℕ) := by
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hL : Algebra.trdeg ℂ L = (m + 2 : ℕ) := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hR : Algebra.trdeg ℂ (ResidueField S.ring) = (m + 1 : ℕ) :=
    trdeg_residueField_of_trdeg ℂ S.ring L hL
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ K
  let res := IsLocalRing.residue S.ring
  let lift : s → S.ring := fun i => Function.surjInv hψ (i : K)
  have hlift : ψ ∘ lift = Subtype.val := funext fun i => Function.surjInv_eq hψ _
  have hg : AlgebraicIndependent ℂ (fun i => res (lift i)) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    have h0 : res (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) = 0 := by
      rw [MvPolynomial.eval₂_comp_left]
      exact hP
    rw [IsLocalRing.residue_eq_zero_iff, ← hker, RingHom.mem_ker, MvPolynomial.hom_eval₂,
      hcomp, show (fun i => ψ (lift i)) = Subtype.val from hlift] at h0
    exact algebraicIndependent_iff.1 hs.1 P h0
  have h1 := hg.cardinalMk_le_trdeg
  rw [hs.cardinalMk_eq_trdeg, hR] at h1
  exact h1

theorem trBasis_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  intro L K _ _ cL cK S ψ hψ hc F m π y ⟨x, hx⟩ hπ hy hP
  have htr := trdeg_le_of_residue cL cK S ψ hψ hc m x hx
  letI : Algebra ℂ F.ring := F.const.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by omega)
  let f : F.ring := ⟨π, hπm⟩
  have hf0 : f ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
  have hfm : f ∈ maximalIdeal F.ring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := F.ord_eq_zero hu
    change F.ord π = 0 at this
    omega
  let w : Fin m → F.ring := fun i => ⟨y i, hy i⟩
  have hev : ∀ P : MvPolynomial (Fin m) ℂ,
      ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) = MvPolynomial.eval₂ cK y P := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype w
    rw [ValuationSubring.subtype_apply] at h
    rw [h]
    rfl
  have hwu : ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P) := by
    intro P hP0
    obtain ⟨h1, h2⟩ := hP P hP0
    refine IsUnit.of_mul_eq_one (⟨_, h2⟩ : F.ring) (Subtype.ext ?_)
    change ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) * _ = 1
    rw [hev]
    exact mul_inv_cancel₀ h1
  have hsplit : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)
          (MvPolynomial.finSuccEquiv ℂ m P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ m : MvPolynomial (Fin (m + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons π y : Fin (m + 1) → K) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P :
          F.ring) : K) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype
      (Fin.cons f w : Fin (m + 1) → F.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hind : AlgebraicIndependent ℂ (Fin.cons π y : Fin (m + 1) → K) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ m P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf0 hfm _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hQ, hQ0, map_zero])
  unfold TrBasis
  refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
  rw [Cardinal.mk_fin]
  exact htr

end GlobalTheory.FieldPair.ResidueTrBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberUpperWeight
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.JetsUb

open GlobalTheory.AllWt GlobalTheory.CompHS

theorem floorGaps_sub_le {N : ℕ} (a : ℕ) (m : ℤ) (v : Fin N → ℤ) (hv : Antitone v) {i j : Fin N} (hij : i ≤ j) :
    floorGaps a m v i - floorGaps a m v j ≤ v i - v j := by
  have hij' : (i : ℕ) ≤ j := hij
  have e1 : floorGaps a m v i - floorGaps a m v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k / m := by
    simp only [floorGaps, ofGaps]
    rw [← Finset.sum_range_add_sum_Ico _ hij']
    ring
  have e2 : v i - v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k := by
    have h1 := ofGaps_gap v i i
    have h2 := ofGaps_gap v i j
    simp only [ofGaps] at h1 h2
    rw [← Finset.sum_range_add_sum_Ico _ hij'] at h2
    linarith
  rw [e1, e2]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_Ico.1 hk
  have hN : k + 1 < N := by have := j.2; omega
  have h0 : 0 ≤ gap v k := by
    rw [gap, dite_eq_left hN]
    have := hv (show (⟨k, by omega⟩ : Fin N) ≤ ⟨k + 1, hN⟩ from Fin.mk_le_mk.2 (by omega))
    omega
  exact Int.ediv_le_self _ h0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem thA_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) (x : (E →+* ℂ) × ℕ) :
    thA Dw P.ub n x ≤ thA Dw P.u₁ n x := by
  have hd : ∀ τ (i j : Fin (Dw.p + Dw.q)), i ≤ j → P.ub τ i - P.ub τ j ≤ P.u₁ τ i - P.u₁ τ j :=
    fun τ i j h => floorGaps_sub_le _ _ _ (hu τ) h
  show (thExpZ Dw P.ub n x).toNat ≤ (thExpZ Dw P.u₁ n x).toNat
  apply Int.toNat_le_toNat
  obtain ⟨σ, i⟩ := x
  rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · by_cases hi : i < Dw.p
    · rw [thExpZ_big _ n τ i hi, thExpZ_big _ n τ i hi]
      have := hd τ ⟨i, by omega⟩ ⟨Dw.p - 1, by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_big_ge _ n τ i (by omega), thExpZ_big_ge _ n τ i (by omega)]
  · by_cases hi : i < Dw.q
    · rw [thExpZ_small _ n hp τ i hi, thExpZ_small _ n hp τ i hi]
      have := hd τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_small_ge _ n τ i (by omega), thExpZ_small_ge _ n τ i (by omega)]

theorem DF_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) :
    Formalism.L2.Pj.DF Dw (thA Dw P.ub n) ≤ Formalism.L2.Pj.DF Dw (thA Dw P.u₁ n) := by
  unfold Formalism.L2.Pj.DF
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => thA_ub_le P n hp hu (τ, i)

end GlobalTheory.RefSum.JetsUb

theorem GlobalTheory.RefSum.JetNum.of_le {D : Formalism.BasicNotions.D7} {d d' : ℕ} {c : ℝ} (h : GlobalTheory.RefSum.JetNum D d c) (hd : d' ≤ d) :
    GlobalTheory.RefSum.JetNum D d' c := fun k => by
  obtain ⟨h1, h2, h3⟩ := h k
  have hd' : (d' : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 ≤ GlobalTheory.PtTie.rr0 D := by unfold GlobalTheory.PtTie.rr0; positivity
  refine ⟨by omega, ?_, le_trans ?_ h3⟩
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hd' (by positivity)) h2
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (d' : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd' 2
    linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivFlatDescent

theorem trivAlong_of_flat_surjective : ∀ {S S' S'' : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (g : S' ⟶ S) (f : S'' ⟶ S') [Flat f] [Surjective f], L.IsLB → GlobalTheory.KTrivSpread.TrivAlong G L (f ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S S' S'' G _ L g f _ _ _ h T a ha x hx
  let u := pullback.fst a f
  have hu : Epi u := Flat.epi_of_flat_of_surjective _
  let T' : Over S := Over.mk (u ≫ T.hom)
  let U : T' ⟶ T := Over.homMk u rfl
  have hs : pullback.snd a f ≫ f ≫ g = T'.hom := by
    show pullback.snd a f ≫ f ≫ g = u ≫ T.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, ha]
  have e₁ : U ≫ x = 1 := h T' (pullback.snd a f) hs (U ≫ x) (hx.comp U)
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ G) := by rw [e₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi u).1 (congrArg (fun q => q.left) e₂))

end GlobalTheory.KTrivFlatDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UU
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KTrivDvrSpread

theorem symGen_of_local {V : Type} [CommRing V] [IsLocalRing V] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (L : LB G.left) (hs : Out.Sym G L) (g : Sp V ⟶ S) :
    ∃ t : LB.Gen (LB.LinComb (L.pull (pullback.fst G.hom g)) (K := Fin 2)
      ![(ι[(Over.pullback g).obj G]).left, 𝟙 ((Over.pullback g).obj G).left] ![1, -1]), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := hs (g (IsLocalRing.closedPoint V))
  have hU' : ⊤ ≤ g ⁻¹ᵁ U := (top_le_iff_cpt g U).2 hU
  have hr : Set.range (pullback.fst G.hom g) ⊆ Set.range (G.hom ⁻¹ᵁ U).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show G.hom (pullback.fst G.hom g y) ∈ U
    have e : G.hom (pullback.fst G.hom g y) = g (pullback.snd G.hom g y) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [e]
    exact hU' trivial
  have hψ : IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι =
      pullback.fst G.hom g := IsOpenImmersion.lift_fac _ _ _
  refine gen_chartPull (chartPullLinComb L (pullback.fst G.hom g) _ _ _
    (IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr) fun k => ?_) t ht
  fin_cases k
  · show (ι[(Over.pullback g).obj G]).left ≫ pullback.fst G.hom g =
      IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
    rw [← Category.assoc, hψ]
    exact GlobalTheory.PolBaseChange.inv_comm (isGrpPullback_pullback G g)
  · show 𝟙 _ ≫ pullback.fst G.hom g = IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι
    rw [hψ, Category.id_comp]

theorem trivAlong_of_generic : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), IsAbelianScheme G → L.IsLB → Out.RelAmple G L → Out.Rigidified G L → Out.Sym G L → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (g : Sp V ⟶ S), GlobalTheory.KTrivSpread.TrivAlong G L (spMap (algebraMap V (FractionRing V)) ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S G _ _ L hG hL ha hR hS V _ _ _ g h
  have hl := GlobalTheory.abelianSchemeLaws_all.1
  have hp := isGrpPullback_pullback G g
  have hLB : (L.pull (pullback.fst G.hom g)).IsLB := pull_isLB hL _
  have hB : IsAbelianScheme ((Over.pullback g).obj G) := TLinPf.isAb_pullback g G hG
  have := hG.proper
  have haB : Out.RelAmple ((Over.pullback g).obj G) (L.pull (pullback.fst G.hom g)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL ha (IsPullback.of_hasPullback G.hom g)
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V ((Over.pullback g).obj G) _ hLB).1 haB
  have hP : GlobalTheory.AbLaw.IsProjBy ((Over.pullback g).obj G).hom := ⟨_, GlobalTheory.AbLaw.isLB_pw hLB _, n, s, hs⟩
  obtain ⟨t, ht⟩ := GlobalTheory.AbLaw.CubeProj.exists_gen_theta_of_isProjBy hl.globalFns V _ hB hP _ hLB
  obtain ⟨r, hr⟩ := GlobalTheory.PolBaseChange.rigidified_pull hp hR
  obtain ⟨u, hu⟩ := symGen_of_local G L hS g
  obtain ⟨M, hM⟩ := GlobalTheory.AbPackage.exists_cp hl.globalFns hB ⟨L.pull (pullback.fst G.hom g), r, hLB, hr⟩
    ⟨t, ht⟩ ⟨u, hu⟩
  have hML : M.L.L = L.pull (pullback.fst G.hom g) := by rw [hM]
  let j := spMap (algebraMap V (FractionRing V))
  let B := (Over.pullback g).obj G
  have hq := isGrpPullback_pullback B j
  have hA : IsAbelianScheme ((Over.pullback j).obj B) := TLinPf.isAb_pullback j B hB
  have := hA.smooth
  have := hA.geomConnected
  have := hB.proper
  have : ConnectedSpace ((Over.pullback j).obj B).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback j).obj B).hom
  obtain ⟨dim, hdim⟩ := exists_dim_of_preconnected ((Over.pullback j).obj B).hom
    (eSec ((Over.pullback j).obj B) (IsLocalRing.closedPoint (FractionRing V)))
  have hLA := pull_isLB hLB (pullback.fst B.hom j)
  have hK : GlobalTheory.KTrivSpread.TrivAlong ((Over.pullback j).obj B)
      ((L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)) (𝟙 _) :=
    GlobalTheory.KTrivSpread.TrivAlong.pull hq hLB ((GlobalTheory.KTrivSpread.TrivAlong.pull hp hL h).comp (𝟙 _))
  let P : Out.PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback j).obj B
      isAb := hA
      g := dim
      smoothDim := hdim
      L := (L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)
      isLB := hLA
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hq ⟨r, hr⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hq (GlobalTheory.PolBaseChange.sym_pull hp hS)
      ample := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hLB haB (IsPullback.of_hasPullback B.hom j)
      ktriv := kTriv_iff_forall.2 fun T x hx => hK T T.hom (Category.comp_id _) x hx }
  have hw : LBIso P.L (M.L.L.pull (pullback.fst B.hom j)) := by
    rw [hML]
    exact GlobalTheory.PolBaseChange.lbIso_refl hLA
  have hK' : Out.KTriv B M.L.L :=
    GlobalTheory.KTrivSpread.kTriv_of_generic_fibre hl V (FractionRing V) P B M (pullback.fst B.hom j) hB hq hw
      (by rw [hML]; exact haB)
  rw [hML] at hK'
  exact GlobalTheory.KTrivSpread.trivAlong_of_kTriv hp hL hK'

end GlobalTheory.KTrivDvrSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueHomogOfFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyValue_homog_of_fibres : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (K : Type) [Field K] [CharZero K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (g : ℕ) (y y' : Fin g → (epsR K ⟶ G)) (x x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g) (a : K) (M : Matrix (Fin g) (Fin g) K), KeyOn (RingHom.id K) x G L σ (fun i => y (i.cast hg)) → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → (∀ i, IsLieComb (M i) y (y' i)) → a ^ 8 * (κ K x' : K) = M.det ^ 4 * κ K x := by
  intro κ hH hF K _ _ G _ _ L σ σ' g y y' x x' hg hg' a M hx hx' hσ hM
  subst hg
  have ha : a ≠ 0 := by
    rintro rfl
    exact _root_.GlobalTheory.KeyEven.not_keyOn_of_sec_zero K G L σ' x' (fun i => y' (i.cast hg')) hx' (fun i => by rw [hσ i]; simp [constFn])
  obtain ⟨v, hv, hvM, hx1⟩ := _root_.GlobalTheory.LieLift.main K G L σ σ' x x' hg' y y' M hx hx' hM
  have hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus (KeyOnPol.scale x.P.A.hom a x.th) :=
    fun s => (x.th_ne s).imp fun z hz => ⟨hz.1, KeyOnPol.mem_nonzeroLocus_of_unit x.P.A.hom (Units.mk0 a ha) (fun _ => rfl) hz.2⟩
  have hx2 := GlobalTheory.T.keyDatum_scale_sections_by_constant K G L σ σ' ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ y' a
    (KeyOnPol.scale x.P.A.hom a x.th) hth (fun _ => rfl) hσ hx1
  have hx'' : KeyOn ((RingHom.id K).comp (RingHom.id K)) x' G L σ' (fun i => y' (i.cast hg')) := by
    rwa [RingHom.id_comp]
  have hpb := _root_.GlobalTheory.KeyEven.keyPB_of_keyOn_comp K K K (RingHom.id K) (RingHom.id K) G L σ' x.P.g y'
    ⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyOnPol.scale x.P.A.hom a x.th, hth, v, hv⟩ x' rfl hg' hx2 hx''
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have e2 := hH K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (KeyOnPol.scale x.P.A.hom a x.th) hth v hv a M
    (fun _ => rfl) hvM
  simp only [Nat.mul_one] at e2
  rw [e1, RingHom.id_apply]
  exact e2

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionInjectiveAtGeometricPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelSection_injective_at_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (c c' : LevelMod Dw l)
    (h : x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c'), c = c' := by
  first | exact @GlobalTheory.TorsSpec.etaSecL_injective_at | exact GlobalTheory.TorsSpec.etaSecL_injective_at | (intros; apply GlobalTheory.TorsSpec.etaSecL_injective_at <;> assumption)
end

