module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0558
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueCoordinatesOfLocalModelBelowPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair


open IsLocalRing in
theorem exists_residue_coords_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro N r V hC u hx hm hunitP hloc
  classical
  let φ : Q →+* V.ring := Q.subtype.codRestrict V.ring fun q => hC _ q.2
  letI : Algebra ℂ V.ring := V.const.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  letI : Algebra ℂ Q := (c.codRestrict Q hQ.const_mem).toAlgebra
  letI : Algebra Q V.ring := φ.toAlgebra
  haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ Q V.ring := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  haveI : IsLocalHom (algebraMap Q V.ring) := ⟨fun q hq => by
    by_contra hq'
    have hqm : q ∈ maximalIdeal Q := (mem_maximalIdeal _).2 hq'
    exact (mem_maximalIdeal _).1 (hm q hqm) hq⟩
  haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
  obtain ⟨x, hx⟩ := hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [Cardinal.mk_fin] at h2
  have h3 := trdeg_residueField_of_trdeg ℂ V.ring L h2.symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V.ring
  obtain ⟨hN, -⟩ := exists_basis_kaehler_of_trdeg ℂ L h2.symm ht
  let ub : Fin r → ResidueField V.ring := fun i => residue V.ring (u i)
  have key : ∀ P : MvPolynomial (Fin r) Q, residue V.ring (MvPolynomial.eval₂ φ u P) =
      MvPolynomial.aeval ub (P.map (residue Q)) := by
    intro P
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  have hmem : ∀ Pb : MvPolynomial (Fin r) (ResidueField Q),
      MvPolynomial.aeval ub Pb ∈ Algebra.adjoin (ResidueField Q) (Set.range ub) := fun Pb => by
    rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Pb, rfl⟩
  have hind : AlgebraicIndependent (ResidueField Q) ub := by
    rw [algebraicIndependent_iff]
    intro Pb hPb
    by_contra hne
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (residue Q) residue_surjective Pb
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.1 hne
    rw [MvPolynomial.coeff_map] at hα
    have hu := hunitP P ⟨α, fun h => hα ((residue_eq_zero_iff _).2 h)⟩
    rw [← residue_ne_zero_iff_isUnit] at hu
    exact hu ((key P).trans hPb)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin (ResidueField Q) (Set.range ub))
      (ResidueField V.ring) := by
    constructor
    intro y
    obtain ⟨f, rfl⟩ := residue_surjective y
    obtain ⟨P, R, hR, hf⟩ := hloc f
    let a : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (P.map (residue Q))⟩
    let b : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (R.map (residue Q))⟩
    have hb : (b : ResidueField V.ring) ≠ 0 := by
      change MvPolynomial.aeval ub (R.map (residue Q)) ≠ 0
      rw [← key]; exact (residue_ne_zero_iff_isUnit _).2 hR
    have hb0 : b ≠ 0 := fun h => hb (by rw [h]; rfl)
    refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h => hb0 ?_, ?_⟩
    · simpa using congrArg (fun p => p.coeff 1) h
    · have e := congrArg (residue V.ring) hf
      rw [map_mul, key, key] at e
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change (b : ResidueField V.ring) * residue V.ring f - (a : ResidueField V.ring) = 0
      change residue V.ring f * (b : ResidueField V.ring) = (a : ResidueField V.ring) at e
      rw [mul_comm, e, sub_self]
  have hub : IsTranscendenceBasis (ResidueField Q) ub := hind.isTranscendenceBasis_iff_isAlgebraic.2 halg
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  have hB := hT.sumElim_comp hub
  have hc : (r : Cardinal) + Cardinal.mk T = ((N - 1 : ℕ) : Cardinal) := by
    rw [← h3, ← hB.cardinalMk_eq_trdeg, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.mk_fin]
  haveI hfin : Finite T := Cardinal.lt_aleph0_iff_finite.1
    (lt_of_le_of_lt le_add_self (by rw [hc]; exact Cardinal.natCast_lt_aleph0))
  have hcard : r + Nat.card T = N - 1 := by
    rw [← Nat.cast_card (α := T)] at hc
    exact_mod_cast hc
  set j := Nat.card T with hj
  let e : Fin j ≃ T := (Finite.equivFin T).symm
  let s : Fin j → Q := fun i => Function.surjInv residue_surjective ((e i : ResidueField Q))
  have hs : ∀ i, residue Q (s i) = (e i : ResidueField Q) := fun i =>
    Function.surjInv_eq residue_surjective _
  let g : Fin (r + j) → Fin r ⊕ T := fun i => Sum.map id e (finSumFinEquiv.symm i)
  have hg : Function.Injective g :=
    (Sum.map_injective.2 ⟨Function.injective_id, e.injective⟩).comp finSumFinEquiv.symm.injective
  have hind2 := hB.1.comp g hg
  have hv : residue V.ring ∘ (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) =
      Sum.elim ub (algebraMap (ResidueField Q) (ResidueField V.ring) ∘ Subtype.val) ∘ g := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [g, ub, Fin.append_left]
    · simp only [Function.comp_apply, Fin.append_right, g, finSumFinEquiv_symm_apply_natAdd,
        Sum.map_inr, Sum.elim_inr]
      rw [← hs, ResidueField.algebraMap_residue]
      rfl
  refine ⟨j, s, by omega, fun P hP => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
  change MvPolynomial.aeval (residue V.ring ∘ _) P ≠ 0
  rw [hv]
  exact fun h0 => hP (algebraicIndependent_iff.1 hind2 P h0)

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResiduePlaceOfTwoDimLocalModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem residuePlace_of_locModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  intro L K _ _ cL cK Q hQ t u hm hdim S ψ hS ht hψ hc
  letI := hQ.isLocalRing
  have hSQ : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let φ₀ : Q →+* S.ring := Q.subtype.codRestrict S.ring hSQ
  let φ : Q →+* K := ψ.comp φ₀
  have hker : ∀ s : S.ring, ψ s = 0 ↔ ¬ IsUnit s := by
    intro s
    have hmax := RingHom.ker_isMaximal_of_surjective ψ hψ
    have h := IsLocalRing.eq_maximalIdeal hmax
    rw [← RingHom.mem_ker, h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hunit : ∀ s : S.ring, (s : L) ≠ 0 → S.ord s = 0 → IsUnit s := by
    intro s hs h0
    have hinv : (s : L)⁻¹ ∈ S.ring :=
      (S.ord_nonneg_iff (inv_ne_zero hs)).1 (by rw [S.ord_inv, h0, neg_zero])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hs))
  have hφt : φ t = 0 := by
    show ψ (φ₀ t) = 0
    rw [hker]
    intro hu
    have h := S.ord_eq_zero hu
    change S.ord (t : L) = 0 at h
    rw [ht] at h
    exact one_ne_zero h
  have hφu : φ u ≠ 0 := by
    intro hu0
    have hsp : Ideal.span {t, u} ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact hφt
      · exact hu0
    have hle : ∀ f ∈ S.ring, f ∈ Q := by
      intro f hf
      obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f hf
      have hbu : IsUnit (⟨b, hb⟩ : Q) := by
        by_contra hnu
        have h1 : φ ⟨b, hb⟩ = 0 := hsp (hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu)
        exact (hker _).1 h1 (hunit (φ₀ ⟨b, hb⟩) hb0 hbo)
      obtain ⟨v, hv⟩ := hbu.exists_right_inv
      have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
      have hf' : f = a * (v : L) := by
        calc f = f * (b * v) := by rw [hv', mul_one]
          _ = a * v := by rw [← mul_assoc, e]
      rw [hf']
      exact Q.mul_mem ha v.2
    let e : Q ≃+* S.ring := RingEquiv.ofBijective φ₀
      ⟨fun x y h => Subtype.ext (congrArg (fun s : S.ring => (s : L)) h), fun s => ⟨⟨s, hle s s.2⟩, rfl⟩⟩
    have h := ringKrullDim_eq_of_ringEquiv e
    rw [hdim, IsDiscreteValuationRing.ringKrullDim_eq_one] at h
    norm_num at h
  have hmemR : ∀ a : K, a ∈ φ.range ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a := by
    intro a
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨φ₀ q, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  have hfrac : ∀ a : K, ∃ x y : Q, φ y ≠ 0 ∧ a * φ y = φ x := by
    intro a
    obtain ⟨s, rfl⟩ := hψ a
    obtain ⟨x, hx, y, hy, hy0, hyo, e⟩ := hS.2 s s.2
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => (hker _).1 h (hunit (φ₀ ⟨y, hy⟩) hy0 hyo), ?_⟩
    show ψ s * ψ (φ₀ ⟨y, hy⟩) = ψ (φ₀ ⟨x, hx⟩)
    rw [← map_mul]
    exact congrArg ψ (Subtype.ext e)
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  let R := φ.range
  let φR : Q →+* R := φ.rangeRestrict
  haveI : IsNoetherianRing R := isNoetherianRing_range φ
  haveI : IsLocalRing R := IsLocalRing.of_surjective' φR φ.rangeRestrict_surjective
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {φR u} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective φR φ.rangeRestrict_surjective, ← hm,
      Ideal.map_span, Set.image_pair]
    have h0 : φR t = 0 := Subtype.ext hφt
    rw [h0, Ideal.span_insert_zero]
  have hu0R : φR u ≠ 0 := fun h => hφu (congrArg Subtype.val h)
  have hnf : ¬ IsField R := by
    intro hf
    obtain ⟨w, hw⟩ := hf.mul_inv_cancel hu0R
    have hmem : φR u ∈ IsLocalRing.maximalIdeal R := hmR ▸ Ideal.subset_span rfl
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_mul_eq_one w hw)
  haveI hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 1 5).2
      (show (IsLocalRing.maximalIdeal R).IsPrincipal from ⟨_, hmR⟩)
  let V : ValuationSubring K :=
    { R with
      mem_or_inv_mem' := by
        intro a
        obtain ⟨x, y, hy, e⟩ := hfrac a
        obtain ⟨c, hc | hc⟩ := ValuationRing.cond (φR x) (φR y)
        · right
          have hc' : φ x * (c : K) = φ y := congrArg Subtype.val hc
          have h1 : a * c = 1 := by
            refine mul_right_cancel₀ hy ?_
            linear_combination (c : K) * e + hc'
          rw [inv_eq_of_mul_eq_one_right h1]
          exact c.2
        · left
          have hc' : φ y * (c : K) = φ x := congrArg Subtype.val hc
          have h1 : a = c := by
            refine mul_right_cancel₀ hy ?_
            linear_combination e - hc'
          rw [h1]
          exact c.2 }
  have hconst : ∀ a, cK a ∈ V := fun a => (hmemR (cK a)).2 ⟨S.const a, hQ.const_mem a, hc a⟩
  have hφV : ∀ q : Q, φ q ∈ V := fun q => ⟨q, rfl⟩
  let φV : Q →+* V := φ.codRestrict V hφV
  have hφVs : Function.Surjective φV := by
    rintro ⟨v, q, rfl⟩
    exact ⟨q, rfl⟩
  haveI hdvrV : IsDiscreteValuationRing V := hdvr
  have hcomp : cK.codRestrict V hconst = φV.comp (cL.codRestrict Q hQ.const_mem) :=
    RingHom.ext fun a => Subtype.ext (hc a).symm
  let F : Place cK :=
    ⟨V, hconst, hdvrV, hcomp ▸ hQ.essFiniteType.comp (RingHom.FiniteType.of_surjective φV hφVs).essFiniteType⟩
  refine ⟨F, hmemR, fun us hus => ?_⟩
  have h1 : ψ us = ((φV u : V) : K) := by
    show ψ us = ψ (φ₀ u)
    exact congrArg ψ (Subtype.ext hus)
  have hmV : IsLocalRing.maximalIdeal V = Ideal.span {φV u} := hmR
  have hirr : Irreducible (φV u) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmV
  rw [h1]
  exact F.ord_irreducible hirr

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledEmbeddingNormBoundHostField
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.GNorm

theorem entry_bound {ι κ E : Type} [Fintype κ] [DecidableEq κ] [Ring E] {m n : ℕ}
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) (s : κ → ℝ) (hs : ∀ k, 0 < s k)
    (B : ι → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ))
    (ξ : Matrix (Fin m) (Fin n) E) (τ : ι) (k : κ) (j : Fin n) :
    ‖σ τ ((T * ξ) k j)‖ / s k ≤ ∑ i, ‖T.map (σ τ) k i‖ * ‖(B τ * ξ.map (σ τ)) i j‖ := by
  have hmap : σ τ ((T * ξ) k j) = (T.map (σ τ) * ξ.map (σ τ)) k j := by
    rw [← Matrix.map_mul]; rfl
  have key : ((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j) = (T.map (σ τ) * (B τ * ξ.map (σ τ))) k j := by
    rw [hmap, ← Matrix.mul_assoc, hB τ, Matrix.mul_assoc, Matrix.diagonal_mul]
  have hnorm : ‖σ τ ((T * ξ) k j)‖ / s k = ‖((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hs k).le, div_eq_inv_mul]
  rw [hnorm, key, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ => norm_mul _ _)

theorem gnorm_gen {ι κ E : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Ring E] (m n : ℕ)
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : ι → Matrix (Fin m) (Fin m) ℂ,
      (∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ)) →
      ∀ ξ : Matrix (Fin m) (Fin n) E,
        ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤
          C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (σ τ)) i j‖ := by
  set c : ℝ := ∑ τ, ∑ k, ∑ i, ‖T.map (σ τ) k i‖ with hc
  have hc0 : 0 ≤ c := by positivity
  have hac : ∀ τ k i, ‖T.map (σ τ) k i‖ ≤ c := by
    intro τ k i
    have h1 : ‖T.map (σ τ) k i‖ ≤ ∑ i', ‖T.map (σ τ) k i'‖ :=
      Finset.single_le_sum (f := fun i' => ‖T.map (σ τ) k i'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i', ‖T.map (σ τ) k i'‖ ≤ ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ :=
      Finset.single_le_sum (f := fun k' => ∑ i', ‖T.map (σ τ) k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ k)
    have h3 : ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ ≤ c :=
      Finset.single_le_sum (f := fun τ' => ∑ k', ∑ i', ‖T.map (σ τ') k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ τ)
    linarith
  refine ⟨1 + Fintype.card κ * c, by nlinarith [hc0, (Nat.cast_nonneg (Fintype.card κ) : (0:ℝ) ≤ _)], ?_⟩
  intro s hs B hB ξ
  set b : ι → Fin m → Fin n → ℝ := fun τ i j => ‖(B τ * ξ.map (σ τ)) i j‖ with hb
  have hb0 : ∀ τ i j, 0 ≤ b τ i j := fun _ _ _ => norm_nonneg _
  have S0 : 0 ≤ ∑ τ, ∑ i, ∑ j, b τ i j := by positivity
  calc ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1
      = ∑ p : κ × Fin n, ∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖ / s p.1 := by
        simp_rw [Finset.sum_div]
    _ ≤ ∑ p : κ × Fin n, ∑ τ, ∑ i, c * b τ i p.2 := by
        gcongr with p _ τ _
        refine (entry_bound σ T s hs B hB ξ τ p.1 p.2).trans ?_
        gcongr with i _
        exact hac τ p.1 i
    _ = ∑ _k : κ, ∑ j : Fin n, ∑ τ, ∑ i, c * b τ i j := by
        rw [Fintype.sum_prod_type]
    _ = Fintype.card κ * (c * ∑ j, ∑ τ, ∑ i, b τ i j) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Finset.mul_sum]
    _ = Fintype.card κ * c * ∑ τ, ∑ i, ∑ j, b τ i j := by
        rw [mul_assoc]
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_comm]
    _ ≤ (1 + Fintype.card κ * c) * ∑ τ, ∑ i, ∑ j, b τ i j := by nlinarith

end GlobalTheory.Proof.GNorm

namespace GlobalTheory

theorem tGnorm : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E), ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤ C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ := by
  intro D κ _ _ m n T
  exact GlobalTheory.Proof.GNorm.gnorm_gen m n (tauE D) T

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondKindCoordinatesUnitaryArchimedeanPla
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.UAut

theorem exists_coordSecondKind_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ),
      (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧
        ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  intro F E _ _ _ _ _ σ h n J hJ w
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1 with hA
  obtain ⟨d, Z, s₀, hZ, hs, hev⟩ := _root_.GlobalTheory.ClosedMatGroup.coords_second_kind_unitary n A
  have hd : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _

  have hy : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w, GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z i) := by
    intro i t
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd (by
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ i, smul_zero])
    refine ⟨(archEquiv J h τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy

  have hS : ∀ g : GArch σ J w, GlobalTheory.Orb.archMat σ J τ g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A} := by
    intro g
    have := (archEquiv J h τ g).2
    rw [Set.mem_ofPred_eq, GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact this
  have hc : Tendsto (GlobalTheory.Orb.archMat σ J τ) (𝓝 1) (𝓝[{X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A}] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hS⟩
    simpa using (GlobalTheory.Orb.continuous_archMat σ J τ).tendsto 1
  have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ) := fun a b e =>
    (GlobalTheory.Orb.isEmbedding_archMat J h τ).injective (by
      show (fun i j => GlobalTheory.Orb.archMat σ J τ a i j) = fun i j => GlobalTheory.Orb.archMat σ J τ b i j
      rw [e])
  refine ⟨d, fun i t => embArch σ J w (y i t), fun g => s₀ (GlobalTheory.Orb.archMat σ J τ g),
    fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨y i t, rfl, hy i t⟩⟩, hs.comp hc, ?_⟩
  filter_upwards [hc.eventually hev] with g hg
  have e1 : (List.ofFn fun i => embArch σ J w (y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i))).prod =
      embArch σ J w (List.ofFn fun i => y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i)).prod := by
    rw [map_list_prod, List.map_ofFn]; rfl
  rw [e1]
  congr 1
  apply hinj
  rw [map_list_prod, List.map_ofFn]
  refine hg.trans ?_
  congr 1
  exact List.ofFn_inj.2 (funext fun i => (hy i _).symm)

end GlobalTheory.UAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSet
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M A : HermLB p), IsAmpleLB A.B → ∀ S : Set X, S.Finite → ∃ b : ℕ, 0 < b ∧ ∃ u : (M.tens (A.pow b)).B.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX M A hA S hS
  have := hX.isLocallyNoetherian
  have hEv : ∀ᶠ b : ℕ in atTop, ∀ (N : LB X) (hN : N.IsLB),
      CechPic.cls N hN = CechPic.cls M.B M.isLB + (b : ℤ) • CechPic.cls A.B hA.isLB →
        ∃ u : N.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u :=
    tendsto_natCast_atTop_atTop.eventually
      (hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS)
  obtain ⟨b, h₁, hb⟩ := (hEv.and (eventually_gt_atTop 0)).exists
  refine ⟨b, hb, ?_⟩
  have eA : CechPic.cls _ (A.pow b).isLB = (b : ℤ) • CechPic.cls A.B hA.isLB :=
    (CechPic.cls_lbPow hA.isLB b (A.pow b).isLB).trans (natCast_zsmul _ _).symm
  obtain ⟨u, hu⟩ := h₁ _ (M.tens (A.pow b)).isLB
    ((CechPic.cls_tens M.isLB (A.pow b).isLB (M.tens (A.pow b)).isLB).trans (congrArg _ eA))
  exact ⟨u, hu⟩

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMuStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  first | exact @GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | exact GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | (intros; apply GlobalTheory.BCT.HintInv.hint_intMat_mul_mul <;> assumption)
end

