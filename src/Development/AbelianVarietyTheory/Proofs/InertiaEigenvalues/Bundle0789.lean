module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetMatrixUnitCompactTotalDegreeLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.LowestKType.DegBound

theorem deg_X_mul_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.X a * MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

theorem deg_pderiv_X_mul {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b (MvPolynomial.X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (deg_X_mul_pderiv _ _ _) ?_)
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (MvPolynomial.totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (MvPolynomial.totalDegree_smul_le _ _).trans (h P)

theorem one_mem_nonRaising (σ : Type) : (1 : Module.End ℂ (MvPolynomial σ ℂ)) ∈ nonRaising σ :=
  fun _ => le_rfl

end GlobalTheory.LowestKType.DegBound

namespace GlobalTheory.LowestKType

open GlobalTheory.LowestKType.DegBound

theorem kop_totalDegree_le (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m)
    (hab : Cpt w τ a b) (d : ℕ) (P : PolF D m n) (hP : P.totalDegree ≤ d) :
    (kop w τ a b P).totalDegree ≤ d := by
  classical
  refine le_trans ?_ hP
  suffices h : kop w τ a b ∈ nonRaising (FVar D m n) from h P
  unfold kop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => ?_
  by_cases hil : i = a ∧ l = b
  · obtain ⟨rfl, rfl⟩ := hil
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_)
    · intro Q
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, if_true, one_smul]
      unfold Cpt at hab
      by_cases hi : (i : ℕ) < w.p τ
      · have hl : (l : ℕ) < w.p τ := hab.1 hi
        simp only [hi, hl, decide_true, if_true, Module.End.mul_apply, LinearMap.mulLeft_apply]
        exact deg_X_mul_pderiv _ _ _
      · have hl : ¬ (l : ℕ) < w.p τ := fun h => hi (hab.2 h)
        simp only [hi, hl, decide_false, Bool.false_eq_true, if_false, Module.End.mul_apply,
          LinearMap.mulLeft_apply, LinearMap.neg_apply,
          MvPolynomial.totalDegree_neg]
        exact deg_pderiv_X_mul _ _ _
    · split_ifs
      · exact Submodule.smul_mem _ _ (one_mem_nonRaising _)
      · exact Submodule.zero_mem _
  · have : Matrix.single a b (1 : ℂ) i l = 0 := by
      rw [Matrix.single_apply]
      split_ifs with h
      · exact absurd ⟨h.1.symm, h.2.symm⟩ hil
      · rfl
    rw [this, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.LowestKType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolume
section
set_option autoImplicit false

namespace GlobalTheory.ConjScalar

section Ideals

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.HeckeIdealValue
open scoped nonZeroDivisors

variable {L : Type} [Field L] [NumberField L]

theorem conj_of_primes (χ χ' : HChar L) (τ : ℂ ≃+* ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      τ (((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ)) =
        ((χ'.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ))
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    τ (((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)) =
      ((χ'.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have key : ∀ ψ : HChar L,
        ((ψ.onId ((p * a : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) *
          ((Real.sqrt (Ideal.absNorm (p * a) : ℝ) : ℝ) : ℂ) =
        (((ψ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ)) *
          (((ψ.onId (a : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm a : ℝ) : ℝ) : ℂ)) := fun ψ => by
      rw [FractionalIdeal.coeIdeal_mul, onId_mul ψ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
        (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
        show ψ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = ψ.val v from onId_prime ψ v]
      push_cast
      ring
    rw [key, key, map_mul, h v hb, ih ha ha1]

end Ideals

section Lattice

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_numerator_coprime (H : Host E) {n bad : ℕ} (Λ : GenLat E n) (hU : Λ.Unimod) (hT : Λ.TrivAt bad) :
    ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ ∧ cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      Submodule.span (𝓞 E) (detSet Λ.La) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  obtain ⟨h0, cc, c1, c2, c3⟩ := GlobalTheory.ScalarUnit.exists_numerator H Λ hU
  have hN : Nat.Coprime (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index bad := by
    refine Nat.coprime_of_dvd fun p hp h1 h2 => ?_
    obtain ⟨k, hk, hk'⟩ := hT
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (GlobalTheory.ScalarUnit.index_coprime hp Λ ⟨k, hk.coprime_dvd_right h2, hk'⟩ h0).symm h1
  generalize (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index = N at *
  refine ⟨cc, fun e => h0 ?_, ?_, c1, c2⟩
  · rw [e, Ideal.mem_bot] at c3
    exact_mod_cast c3
  · obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 E))
    simp only [map_natCast] at e
    rw [Ideal.eq_top_iff_one, ← e]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ c3))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem ep_conj {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n bad : ℕ} (ta : c.F ≃+* c.F)
    {B B' : Ideal (𝓞 E) → c.F} {epF epF' : Submodule (𝓞 E) (Fin n → E) → c.F}
    (he : EpIs (Dw := Dw) c bad B epF) (he' : EpIs (Dw := Dw) c bad B' epF')
    (hB : ∀ cc, cc ≠ ⊥ → cc ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ → ta (B cc) = B' cc)
    {L : Submodule (𝓞 E) (Fin n → E)} (g : GlobalTheory.ClassScalarCompare.Guard H bad L) : ta (epF L) = epF' L := by
  obtain ⟨cc, c0, c1, c2, c3⟩ := exists_numerator_coprime H ⟨L⟩ g.1 g.2.1
  obtain ⟨q, q0, q1, q2⟩ := he L cc g.1 g.2.1 g.2.2 c2 c3
  obtain ⟨q', q0', q1', q2'⟩ := he' L cc g.1 g.2.1 g.2.2 c2 c3
  have hN : (Ideal.absNorm cc : ℚ) ≠ 0 := by exact_mod_cast fun h => c0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hq : q = q' := by
    have h1 := q1.trans q1'.symm
    rw [← q1] at hN
    exact (pow_left_inj₀ q0.le q0'.le two_ne_zero).1 (mul_right_cancel₀ (right_ne_zero_of_mul hN) h1)
  rw [q2, q2', map_mul, map_inv₀, hB cc c0 c1, map_ratCast, hq]

end Lattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 1000000 in
theorem conj_vol_ep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ta (M.vol a) = M.vol b ∧ ∀ k, ta (M.ep a k) = M.ep b (e k) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hO τ ta hta hF a b e hS hab
  obtain ⟨-, -, -, hbad, hvol, hk⟩ := hS
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨h, J', hR, -⟩ := (hO.tuple a).reps
    rw [hvol, hR.2.2.2.2.1, map_inv₀, map_natCast]
  · have hxi := (_root_.GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hC τ (tup a) (tup b) hab).2.2.1
    obtain ⟨r1, r2, -, -, -, r6⟩ := (hO.reps a).1 k
    have hcj := (GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps a).2 k
    have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (M.La a k).La) ⟨r1, r2, r6⟩
    rw [hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat] at g
    have heb := (hO.ep b).2
    have hBb := (hO.tuple b).B
    rw [hbad] at heb hBb
    rw [(hO.ep a).1 k, (hO.ep b).1 (e k), (hk k).1]
    refine ep_conj M.c' ta (hO.ep a).2 heb (fun cc c0 c1 => Subtype.ext ?_) g
    have h1 : ((M.B a cc : M.c'.F) : ℂ) = _ := (hO.tuple a).B cc c0 c1
    have h2 : ((M.B b cc : M.c'.F) : ℂ) = _ := hBb cc c0 c1
    rw [hta, h1, h2]
    refine conj_of_primes _ _ τ _ (fun P hP => ?_) cc c0 c1
    have hs := hF.split P fun hj => hP (by
      obtain ⟨u, hu⟩ := (hO.bad a).2.2.2.2
      rw [hu, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hj)
    have key : ∀ t, (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val P : ℂˣ) : ℂ) *
        ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) = (((R.xiH t).val P : ℂˣ) : ℂ) *
        ((((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)) := fun t => by
      simp only [Formalism.L2.Host.HChar.val_mul, Units.val_mul]
      ring
    rw [key, key, map_mul, hs, hxi]

end GlobalTheory.ConjScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorTargetLieOneParam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.FockDerivP

def frONB {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : GlobalTheory.ChainFr.Fr V where
  ε _ _ := true
  fr τ := (B τ)⁻¹
  fr_unit τ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _
    ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))))
  fr_gram τ := by
    have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
    obtain ⟨ε, hε, hG, -⟩ := hB τ
    have h1 : (fun a => (ε a : ℂ)) = fun _ => 1 := by
      funext a
      rcases hε a with h | h
      · rw [h.1]; simp
      · exact absurd h.2 (not_le.2 a.2)
    rw [h1, Matrix.diagonal_one] at hG
    have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
      simp [Formalism.REAL.Jm]
    have h2 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B τ)⁻¹)ᴴ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹
        = ((B τ)⁻¹)ᴴ * ((B τ)ᴴ * gramAt D V τ * B τ) * (B τ)⁻¹ := by rw [hJ, hG]
      _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [h2, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

theorem frONB_cart {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).cart = fun _ => 1 := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
    simp [Formalism.REAL.Jm]
  show ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹ = 1
  rw [hJ, Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_nonsing_inv _ hu]

theorem frONB_onb {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).onb = B := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  show ((B τ)⁻¹)⁻¹ = B τ
  rw [Matrix.nonsing_inv_nonsing_inv _ hu]

theorem hasDerivAt_ptP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∃ a : ℂ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + a • P) z) 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t τ Y hY
  have hC := hG.core
  have hB := hC.models.BV i
  set AV := frONB (R.BV i) hB with hAV
  set BW := GlobalTheory.ChainFr.Fr.ofModel (R.MW i (sg0 D A)) with hBW
  have hcA := frONB_cart (R.BV i) hB
  have hoA := frONB_onb (R.BV i) hB
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hvac : GlobalTheory.ChainFr.IsVacF R.ψ R.θ AV BW (R.vP i t) := by
    refine ⟨hf, fun ρ => ?_⟩
    rw [hcA]
    exact hv ρ
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hC.lev i t τ
  have hAll := GlobalTheory.LieScalar.lieFockAll D (Vc D i) (Wc D i) AV BW R.θ R.ψ _ _ (R.ωP i t) (R.vP i t) τ _ _
    hC.models.inf (hC.thP.ωP i t) hI.chiV hI.chiW hvac
  refine ⟨((-eS D i τ : ℚ) : ℂ) * Y.trace, fun P z => ?_⟩
  have hpt : GlobalTheory.ChainFr.ptF R.ψ R.θ AV BW (R.vP i t) = R.ptP i t := by
    unfold GlobalTheory.ChainFr.ptF RealDat.ptP
    rw [hcA, hoA]
    rfl
  have hε : BW.ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ) := by
    funext j
    exact hC.models.order i τ j
  have h := hAll.2 Y hY P z
  rw [hpt, hε] at h
  exact h

end GlobalTheory.FockDerivP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsResOfChrEq
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistResidue

open Formalism.IndefR.Datum

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem isRes_of_chrEq : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P ∈ δ.Q, IsRes χ P (δ.resC P) := by
  intro D δ hδ χ hχ P hP a k u hka hu
  have h := hδ.split.isIdemAt hP
  have he : GlobalTheory.ExportSeries.idemAt P * GlobalTheory.ExportSeries.idemAt P = GlobalTheory.ExportSeries.idemAt P := h.1.1
  have e1 := hχ.2 P _ (by obtain ⟨⟨g1, g2, v, ε, hv, hs⟩, g3⟩ := h; exact ⟨g1, ⟨v, ε, hv, Or.inl ⟨g2, hs⟩⟩, g3⟩) k (locU he k) (locU_val he k)
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ P h
  have hb : toEAf D (incA D (k : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hka]; rfl
  have hx0 : ((locU he k : (AE D)ˣ) : AE D) = 1 + GlobalTheory.ExportSeries.idemAt P * (incA D (k : D.host.E) - 1) := rfl
  have hv : toEAf D ((locU he k : (AE D)ˣ) : AE D) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hx0, GlobalTheory.ConjTwist.map_loc, hb]
    rfl
  have hx : toEAf D ((locU he k : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  have hoff : (1 - GlobalTheory.ExportSeries.idemAt P) * ((locU he k : (AE D)ˣ) : AE D) = 1 - GlobalTheory.ExportSeries.idemAt P := by
    rw [hx0]
    linear_combination (1 - incA D (k : D.host.E)) * he
  have hres : resS D.host.F P ⟨_, hx⟩ = u := by
    have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F P) e2).trans ?_
    rw [GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hu]
    ring
  have e3 := hδ.res P hP _ hoff hx u hres
  refine Units.ext ?_
  rw [← e1, e3]
  rfl

end GlobalTheory.TwistResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOne
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivCover.OpenKerChar


set_option maxHeartbeats 400000 in
theorem map_eq_one_of_finPart_eq_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A),
    IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  intro D A _ χ hχ x hx
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hfam : GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace D.host.E => w.embedding) := by
    unfold GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  choose θ hθ using fun w : InfinitePlace D.host.E =>
    (GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm w.embedding).exists
  obtain ⟨e2, -, hc2, hc2', -⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig (InfinitePlace D.host.E) _ θ hcm hfam hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h2 : (e1 (x : AE D)).2 = 1 := (he1 _).2.trans hx
  set c : InfinitePlace D.host.E → ℂ := e2 (e1 (x : AE D)).1 with hcdef
  have hcu : IsUnit c := by
    have hu : IsUnit (e1 (x : AE D)) := x.isUnit.map e1
    exact (Prod.isUnit_iff.1 hu).1.map e2
  have hc0 : ∀ w, c w ≠ 0 := fun w => (Pi.isUnit_iff.1 hcu w).ne_zero
  let p : ℝ → (InfinitePlace D.host.E → ℂ) := fun t w => Complex.exp (t * Complex.log (c w))
  let γ : ℝ → AE D := fun t => e1.symm (e2.symm (p t), 1)
  have hpc : Continuous p := continuous_pi fun w =>
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hγc : Continuous γ := hc1'.comp ((hc2'.comp hpc).prodMk continuous_const)
  have hpmul : ∀ s t, p s * p t = p (s + t) := fun s t => by
    funext w
    simp only [p, Pi.mul_apply, ← Complex.exp_add, Complex.ofReal_add, add_mul]
  have hγmul : ∀ s t, γ s * γ t = γ (s + t) := fun s t => by
    simp only [γ, ← map_mul, Prod.mk_mul_mk, mul_one, hpmul]
  have hp0 : p 0 = 1 := by funext w; simp [p]
  have hγ0 : γ 0 = 1 := by simp only [γ, hp0, map_one, Prod.mk_one_one]
  have hp1 : p 1 = c := by funext w; simp [p, Complex.exp_log (hc0 w)]
  have hγ1 : γ 1 = x := by
    simp only [γ, hp1, hcdef, RingEquiv.symm_apply_apply]
    rw [← h2, Prod.mk.eta, RingEquiv.symm_apply_apply]
  have hr : ∀ t, γ t * γ (-t) = 1 := fun t =>
    (hγmul t (-t)).trans ((congrArg γ (add_neg_cancel t)).trans hγ0)
  have hl : ∀ t, γ (-t) * γ t = 1 := fun t =>
    (hγmul (-t) t).trans ((congrArg γ (neg_add_cancel t)).trans hγ0)
  let f : ℝ → (AE D)ˣ := fun t => Units.mk (γ t) (γ (-t)) (hr t) (hl t)
  have hf : Continuous f := Units.continuous_iff.2 ⟨hγc, hγc.comp continuous_neg⟩
  have hcl : IsClosed (χ.ker : Set (AE D)ˣ) := Subgroup.isClosed_of_isOpen _ hχ
  have hS : IsClopen (f ⁻¹' (χ.ker : Set (AE D)ˣ)) := ⟨hcl.preimage hf, hχ.preimage hf⟩
  have h0 : (0 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := by
    have : f 0 = 1 := Units.ext hγ0
    simp [this]
  rcases isClopen_iff.1 hS with h | h
  · rw [h] at h0; exact absurd h0 (Set.notMem_empty _)
  · have h1 : (1 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := h ▸ Set.mem_univ _
    have hf1 : f 1 = x := Units.ext hγ1
    rw [Set.mem_preimage, hf1] at h1
    exact h1

end GlobalTheory.UnivCover.OpenKerChar
end

