module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0910
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedDenomRationalMatrixOfFinitePart
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem isIntegral_of_finAdele_valuation_le_one {E : Type} [Field E] [NumberField E] (x : E)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) x) Q) ≤ 1) :
    IsIntegral ℤ x := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E x fun Q => by
    have := h Q
    rwa [show (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) Q = (x : Q.adicCompletion E) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem map_fin_eq_of_isRat (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (V : HSp D) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E) (hR : GlobalTheory.Member.IsRat V γ γ') :
    Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1 =
      Matrix.GeneralLinearGroup.map (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) γ' := by
  have hf : (fin V γ).1 = finHom V γ := rfl
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  rw [hf]
  simp only [finHom, MonoidHom.comp_apply]
  rw [show matHom V γ = _ from hR]
  simp only [Formalism.UG.bc, Matrix.GeneralLinearGroup.map, incA, inclR, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe, Matrix.GeneralLinearGroup.map_apply]
  change ι ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (Algebra.TensorProduct.includeRight ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b))) = algebraMap D.host.E _ ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b)
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  exact h1 _

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem exists_coprime_isIntegral_of_bnd {E : Type} [Field E] [NumberField E] {n : ℕ} (l c : ℕ)
    (A : Matrix (Fin n) (Fin n) E)
    (h : GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 E) E)) •
      A.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)))) :
    ∃ m : ℕ, m.Coprime l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * A a b) := by
  obtain ⟨m, hm, hv⟩ := h
  refine ⟨m, hm, fun a b => isIntegral_of_finAdele_valuation_le_one _ fun Q => ?_⟩
  have := hv a b Q
  simpa [Matrix.smul_apply, Matrix.map_apply, map_mul, mul_assoc] using this

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem denomAt_of_isRat_of_bnd : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → ∀ (V : HSp D) (l c : ℕ) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E), GlobalTheory.Member.IsRat V γ γ' → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1).1) → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1)⁻¹.1) → DenomAt l c γ' := by
  intro D ι h1 V l c γ γ' hR hb1 hb2
  have hM := map_fin_eq_of_isRat D ι h1 V γ γ' hR
  rw [hM] at hb1 hb2
  rw [← map_inv] at hb2
  obtain ⟨m₁, hm₁, hi₁⟩ := exists_coprime_isIntegral_of_bnd l c (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) hb1
  obtain ⟨m₂, hm₂, hi₂⟩ := exists_coprime_isIntegral_of_bnd l c ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) hb2
  have hn : ∀ k : ℕ, IsIntegral ℤ (k : D.host.E) := fun k => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (k : ℤ)))
  refine ⟨m₁ * m₂, Nat.Coprime.mul_left hm₁ hm₂, fun a b => ⟨?_, ?_⟩⟩
  · have e : (((m₁ * m₂ * l ^ c : ℕ) : D.host.E)) * (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b =
        (m₂ : D.host.E) * ((((m₁ * l ^ c : ℕ) : D.host.E)) * (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := by
      push_cast; ring
    rw [e]; exact (hn m₂).mul (hi₁ a b)
  · have e : (((m₁ * m₂ * l ^ c : ℕ) : D.host.E)) * ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b =
        (m₁ : D.host.E) * ((((m₂ * l ^ c : ℕ) : D.host.E)) * ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := by
      push_cast; ring
    rw [e]; exact (hn m₁).mul (hi₂ a b)

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsSplitPlaceLocalMatricesStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisionPoints_splitPlace_local_matrices : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) (ι 1) N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  first | exact @GlobalTheory.DivPtLocalCard.card_DQ_eq | exact GlobalTheory.DivPtLocalCard.card_DQ_eq | (intros; apply GlobalTheory.DivPtLocalCard.card_DQ_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRefTup

section IdempotentCombination
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ)

theorem conj_sum_eq (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ : GA D (Wc D i) → ℂ} {n m : ℕ} {a : Fin n → ℂ}
    {b : Fin m → ℂ} {f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n} {g : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n}
    (ha : Expands O κ Φ a f) (hb : Expands O κ Φ b g) (x : GA D (Wc D i)) :
    ∑ k, τ (a k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) x) =
    ∑ k, τ (b k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (g k : T.toCore.R ((i : ℕ) + 1)) x) := by
  have h0 : Expands O κ (fun _ => 0) (Fin.append a (fun k => -b k)) (Fin.append f g) := by
    intro y
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    rw [← ha y, ← hb y, add_neg_cancel]
  have h1 := hZ.2 _ _ _ h0 x
  rw [Fin.sum_univ_add] at h1
  simp only [Fin.append_left, Fin.append_right, map_neg, one_mul, neg_mul, Finset.sum_neg_distrib] at h1
  linear_combination (-1 : ℂ) * h1

theorem conjFun_lin (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ Φ' Ψ Ψ' : GA D (Wc D i) → ℂ}
    (h1 : ConjFun O κ τ 1 Φ Φ') (h2 : ConjFun O κ τ 1 Ψ Ψ') (c d : ℂ) :
    ConjFun O κ τ 1 (fun x => c * Φ x + d * Ψ x) (fun x => τ c * Φ' x + τ d * Ψ' x) := by
  obtain ⟨n, a, f, ha⟩ := h1.1
  obtain ⟨m, b, g, hb⟩ := h2.1
  have hs : Expands O κ (fun x => c * Φ x + d * Ψ x) (Fin.append (fun k => c * a k) (fun k => d * b k)) (Fin.append f g) := by
    intro x
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [ha x, hb x, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_assoc]
  refine ⟨⟨_, _, _, hs⟩, fun N e h he x => ?_⟩
  simp only [one_mul]
  rw [conj_sum_eq O κ τ hZ he hs x, Fin.sum_univ_add, h1.2 _ _ _ ha x, h2.2 _ _ _ hb x]
  simp only [Fin.append_left, Fin.append_right, one_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem conjFun_sum (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) : ∀ (n : ℕ) (α : Fin n → ℂ)
    (Φ Φ' : Fin n → GA D (Wc D i) → ℂ), (∀ k, ConjFun O κ τ 1 (Φ k) (Φ' k)) →
    ConjFun O κ τ 1 (fun g => ∑ k, α k * Φ k g) (fun g => ∑ k, τ (α k) * Φ' k g) := by
  intro n
  induction n with
  | zero => intro α Φ Φ' _; simpa using hZ
  | succ n ih =>
    intro α Φ Φ' hk
    have h := conjFun_lin O κ τ hZ (hk 0) (ih (fun k => α k.succ) (fun k => Φ k.succ) (fun k => Φ' k.succ)
      (fun k => hk k.succ)) (α 0) 1
    simp only [map_one, one_mul] at h
    simpa only [Fin.sum_univ_succ] using h

end IdempotentCombination


set_option maxHeartbeats 1000000 in
theorem conjFun_base_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∀ y y' : (R.HV i A.μ0).H, ConjForm R i τ c A.μ0 A.μ0 y y' → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase c hc
  have h2 := GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hcore hfin hfw hQ i hpins
  obtain ⟨M, hMp, hMl, hMe, hMn, hMc, hMx, hMs⟩ := h2
  have h3 := _root_.GlobalTheory.GalRef.exists_root_galRul_isSum hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs
  have h4 := _root_.GlobalTheory.ConjRefLift.conjFun_lifts_root hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs h3.choose h3.choose_spec.1 h3.choose_spec.2
  refine ⟨h4.choose, h4.choose_spec.1, fun τ hB y y' hyy => ?_⟩
  have hP := h4.choose_spec.2
  let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  haveI := hMn
  let ta : M.c'.F ≃+* M.c'.F := (τa.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => AlgEquiv.restrictNormal_commutes τa M.c'.F a
  have hct : ConjTup R τ A.μ0 A.μ0 := by
    refine ⟨rfl, fun x => ?_⟩
    have h1 := hcore.lev.xi A.μ0
    rw [hcore.lev.xi_base] at h1
    rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x]
    simp
  have h5 := _root_.GlobalTheory.ConjDesc.conj_desc D G Pl0 T0 A T R F κ v₀ hcore hfw i T0 id M hMp τ ta hta hB c ((hMe c).1 hc) hMx A.μ0 A.μ0 hct y y' hyy
  obtain ⟨n, α, ys, ys', hy, hy', hk⟩ := h5
  have hZ : ConjFun (O i) (κ i) τ 1 (fun _ => 0) (fun _ => 0) := by
    have := hP τ ta hta hB 0 0 (fun h => ⟨0, 0, by simp, by rw [map_zero, map_zero]; rfl, by rw [map_zero, map_zero]; rfl⟩)
    simpa using this
  have hL := conjFun_sum (O i) (κ i) τ hZ n α
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys k) (v₀ i (sg0 D A)) g)
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys' k) (v₀ i (sg0 D A)) g) (fun k => hP τ ta hta hB (ys k) (ys' k) (hk k))
  subst hy hy'
  convert hL using 2 with g g
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.ConjRefTup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjClassSum.conj_lifts | exact GlobalTheory.ConjClassSum.conj_lifts | (intros; apply GlobalTheory.ConjClassSum.conj_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantBilinearFormsVanishOfIoGenerationReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GenByIo

theorem forms_vanish_of_io : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ι : Type) (B : ι → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ), (∀ (j : ι) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → ∀ l, B j P' l = B j P (l ∘ₗ (R.cV i).ρ u)) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → (∀ j, B j P = 0) → ∀ j, B j P' = 0) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (j : ι), B j (R.ioP i x w) = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (j : ι), B j P = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t ι B heq hlie hio P j
  let U : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank) := ⨅ j, LinearMap.ker (B j)
  have hU : ∀ P, P ∈ U ↔ ∀ j, B j P = 0 := fun P => by simp [U, Submodule.mem_iInf]
  have hstab : ∀ u ∈ GinfC (Vc D i), ∀ P ∈ U, ∀ P' : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → P' ∈ U := by
    intro u hu P hP P' h
    rw [hU] at hP ⊢
    intro j
    ext l
    rw [heq j u hu P P' h l, hP j]
    rfl
  have hlie' : ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → P ∈ U → P' ∈ U := by
    intro τ Y hY P P' hd hP
    rw [hU] at hP ⊢
    exact hlie τ Y hY P P' hd hP
  have hio' : ∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W), R.ioP i x w ∈ U := fun x w => (hU _).2 (hio x w)
  obtain ⟨Q, hQ, E, -, -, hNo, hPQ⟩ := _root_.GlobalTheory.FockIsotypic.decomp D G Pl0 T A Ks R F hG hF i t P
  have hQU : Q ∈ U := by
    refine Submodule.span_le.2 ?_ hQ
    rintro _ ⟨φ, w, hφ, rfl⟩
    exact _root_.GlobalTheory.HoweGen.cvType_mem_of_stable D G Pl0 T A Ks R F hG hF i t U hstab hlie' hio' φ hφ w
  have hN : B j (P - Q) = 0 :=
    hNo (B j) (fun u hu P₁ _ P₂ h l => heq j u hu P₁ P₂ h l) _ hPQ
  have := (hU Q).1 hQU j
  rw [map_sub, this, sub_zero] at hN
  exact hN

end GlobalTheory.GenByIo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupFixVacuumTranslates
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.VacTransFix

theorem nsmul_cancel {D : D7} {V W : HSp D} {M : ℕ} (hM : M ≠ 0) {x x' : WO V W} (h : M • x = M • x') : x = x' := by
  set a : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) ((M : D.host.F)⁻¹)) with ha_def
  have ha : a * (M : AE D) = 1 := by
    have e : (M : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (M : D.host.F)) := by
      simp [map_natCast]
    rw [e, ha_def, ← map_mul, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, map_one]
  have key : ∀ z : WO V W, a • (M • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, ha, one_smul]
  rw [← key x, h, key]

theorem fix_trans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ M : ℕ, M ≠ 0 → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ k ∈ GfC V, fin V k ∈ J → ∀ y : WO V W, M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → om (k, 1) (heisO ψ V W y f₀) = heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  obtain ⟨hpair, -, -, -, hsdV, hsdW, -, hcart, hvac⟩ := hP
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.VacFixOpen.exists_open_fix_vacO D ψ θ V W χV χW om hpair.weil hpair.sigV hpair.sigW
    (fun _ => 1) sW (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hpair.std τ) hcart ΛV ΛW hsdV hsdW f₀ hvac
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.LatFixMod.exists_open_keep_cong D V W ΛV ΛW hsdV hsdW (2 * M * M)
    (Nat.mul_pos (Nat.mul_pos two_pos (Nat.pos_of_ne_zero hM)) (Nat.pos_of_ne_zero hM))
  refine ⟨J₁ ⊓ J₂, by rw [Subgroup.coe_inf]; exact hJ₁o.inter hJ₂o, fun k hk hkJ y hy => ?_⟩
  have hθ : IsThetaFunO ψ V W f₀ := hvac.2.theta
  rw [hpair.weil.om_heis k 1 y f₀ hθ, hJ₁ k hk hkJ.1]
  obtain ⟨l, hl, e⟩ := (hJ₂ k hk hkJ.2).2 (M • y) hy
  have hlin : actO V W k 1 (M • y) = M • actO V W k 1 y :=
    (AddMonoidHom.mk' (actO V W k 1) (GlobalTheory.LatNhds.actO_add k 1)).map_nsmul M y
  have e2 : M • actO V W k 1 y = M • (y + 2 • (M • l)) := by
    rw [← hlin, e, smul_add, smul_smul, smul_smul, show 2 * M * M = M * 2 * M by ring]
  rw [nsmul_cancel hM e2]
  refine GlobalTheory.AdForm.SplitGen.heisO_add_two ψ (hvac.2.lat.1 _ (AddSubgroup.nsmul_mem _ hl M)) ?_
  rw [GlobalTheory.RatSelfDual.symplO_nsmul]
  exact GlobalTheory.LatVac.char_sympl_eq_one hvac.1 hsdV hsdW hy hl

end GlobalTheory.VacTransFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandard
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LatOpen.exists_open_hLat_std : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ x ∈ J, Bridge.hLat V x = Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V h1
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup V 1).map (finHom V).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup V one_pos, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  rw [← h1]
  have hk' := GlobalTheory.Member.PrincLevel.finCong_inv hk.2
  have hm := GlobalTheory.Member.PrincLevel.finCong_map hk.2
  have hm' := GlobalTheory.Member.PrincLevel.finCong_map hk'
  have hL := GlobalTheory.StdFrameCong.pj_latHat_eq V
  have e1 : ((((finHom V).rangeRestrict k)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = finHom V k⁻¹ := by
    rw [← map_inv]; rfl
  have e0 : (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = 1 := by
    rw [inv_one]; rfl
  unfold Bridge.hLat
  refine congrArg (Submodule.span _) (Set.ext fun v => ?_)
  show _ ∈ latHat D.host.F D.host.E (L0c D V) ↔ _ ∈ latHat D.host.F D.host.E (L0c D V)
  rw [e1, e0, Units.val_one, Matrix.one_mulVec, ← hL]
  constructor
  · intro h
    have := hm _ h
    have ekk : (finHom V k).1 * (finHom V k⁻¹).1 = 1 := by
      rw [← Units.val_mul, ← map_mul (finHom V) k k⁻¹, mul_inv_cancel k, map_one, Units.val_one]
    rwa [Matrix.mulVec_mulVec, ekk, Matrix.one_mulVec] at this
  · exact hm' _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanks
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_all : ∀ r, UnitMatch r :=
  _root_.GlobalTheory.JR.unitMatch_of_weilField _root_.GlobalTheory.JR.WeilQuad.weilField_main

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypothesesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_of_admittedHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  first | exact @GlobalTheory.TheoremB.theoremB_of_admitted | exact GlobalTheory.TheoremB.theoremB_of_admitted | (intros; apply GlobalTheory.TheoremB.theoremB_of_admitted <;> assumption)
end

