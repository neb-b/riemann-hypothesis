module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CdpGaloisLeOneOfAlgebraicRatFunc
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Brauer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUniqueStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (M : Matrix ι ι (Ainf p O)), IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) M → (∀ c : ι → Ainf p O, ∃ v : ι → Ainf p O, ∀ i, v i - M.mulVec (fun j => WittVector.frobenius (v j)) i = c i) ∧ ∀ v : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ v i - M.mulVec (fun j => WittVector.frobenius (v j)) i) → ∀ i, Sandwich.mu ε ∣ v i := by
  first | exact @GlobalTheory.WSolve.main | exact GlobalTheory.WSolve.main | (intros; apply GlobalTheory.WSolve.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssocEval
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.Assoc

theorem isEval_comp (p : ℕ) {O A B σ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] B) (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨c, hc⟩ := hN f hf
  exact ⟨φ c, by simp [hc, map_mul, map_pow, map_natCast]⟩

theorem constantCoeff_op {O : Type} [CommRing O] {d : ℕ} {τ : Type}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ O) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (j : Fin d) : constantCoeff (op μ u v j) = 0 := by
  have h : ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    rintro (k | k) <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ j)

theorem dvd_pow_map (p : ℕ) {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (φ : A →ₐ[O] B) {a : A} (h : ∃ N : ℕ, (p : A) ∣ a ^ N) :
    ∃ N : ℕ, (p : B) ∣ φ a ^ N := by
  obtain ⟨N, c, hc⟩ := h
  exact ⟨N, φ c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

end GlobalTheory.Chart.Assoc

namespace GlobalTheory.Chart.Assoc

theorem assoc_eval (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ}
    (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A)
    (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hx : ∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (h2 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂)
    (h3 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃)
    (hc : ∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) :
    ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  let Φ₁ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Algebra.TensorProduct.includeLeft (S := O))
  let Φ₃ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) := Algebra.TensorProduct.includeRight
  let Φ₂ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    (Algebra.TensorProduct.assoc O O O A A A).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom O A) (AlgHom.id O A))
  let Φ₄ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Bialgebra.comulAlgHom O A)
  have hnil : ∀ k, ∃ N : ℕ, (p : A ⊗[O] (A ⊗[O] A)) ∣ (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) k ^ N := by
    rintro (k | k | k)
    · exact dvd_pow_map p (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A ⊗[O] A)) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A))) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A))) (hx k)
  have sub := ((_root_.GlobalTheory.CEval.continuous_eval p O _ _ _ hnil).2 E₃ h3).1
  have c1 : ∀ j, constantCoeff (x1 (R := O) (d := d) j) = 0 := fun j => by simp [x1]
  have c2 : ∀ j, constantCoeff (x2 (R := O) (d := d) j) = 0 := fun j => by simp [x2]
  have c3 : ∀ j, constantCoeff (x3 (R := O) (d := d) j) = 0 := fun j => by simp [x3]
  have ce : ∀ {u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O},
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) →
      ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    intro u v hu hv k; rcases k with k | k <;> simp [hu, hv]
  have L1 : ∀ j, E₃ (op μ x1 x2 j) = Φ₁ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₁ h2
    have := sub _ (Sum.elim x1 x2) (Φ₁.comp E₂) (ce c1 c2) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x1, x2, h3.1, Φ₁, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  have L3 : ∀ j, E₃ (op μ x2 x3 j) = Φ₃ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₃ h2
    have := sub _ (Sum.elim x2 x3) (Φ₃.comp E₂) (ce c2 c3) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x2, x3, h3.1, Φ₃, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  intro i
  have LL : E₃ (op μ (op μ x1 x2) x3 i) = Φ₂ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₂ h2
    have := sub _ (Sum.elim (op μ x1 x2) x3) (Φ₂.comp E₂)
      (ce (constantCoeff_op μ hμ _ _ c1 c2) c3) (by
      convert e using 2 with k
      rcases k with k | k
      · simp only [Sum.elim_inl]
        rw [L1]
        have key : ∀ c : A ⊗[O] A, Φ₁ c = (Algebra.TensorProduct.assoc O O O A A A) (c ⊗ₜ[O] 1) := by
          intro c
          induction c using TensorProduct.induction_on with
          | zero => simp
          | tmul a b => simp [Φ₁, Algebra.TensorProduct.one_def]
          | add a b ha hb => rw [map_add (f := _), ha, hb, TensorProduct.add_tmul, map_add (f := _)]
        rw [key]
        simp [Φ₂]
      · simp [x3, h3.1, Φ₂, Algebra.TensorProduct.one_def]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  have RR : E₃ (op μ x1 (op μ x2 x3) i) = Φ₄ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₄ h2
    have := sub _ (Sum.elim x1 (op μ x2 x3)) (Φ₄.comp E₂)
      (ce c1 (constantCoeff_op μ hμ _ _ c2 c3)) (by
      convert e using 2 with k
      rcases k with k | k
      · simp [x1, h3.1, Φ₄, Algebra.TensorProduct.one_def]
      · simp only [Sum.elim_inr]
        rw [L3]
        simp [Φ₃, Φ₄]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  rw [LL, RR]
  have ka : ∀ w : (A ⊗[O] A) ⊗[O] A,
      (Algebra.TensorProduct.assoc O O O A A A) w = TensorProduct.assoc O A A A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul a a' => simp
      | add c c' hc hc' => rw [TensorProduct.add_tmul, map_add (f := _), hc, hc', map_add (f := _)]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]
  have k2 : ∀ c : A ⊗[O] A, Φ₂ c = TensorProduct.assoc O A A A (LinearMap.rTensor A (Coalgebra.comul (R := O) (A := A)) c) := by
    intro c
    rw [← ka]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₂]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have k4 : ∀ c : A ⊗[O] A, Φ₄ c = LinearMap.lTensor A (Coalgebra.comul (R := O) (A := A)) c := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₄]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]
  rw [k2, k4, Coalgebra.coassoc_apply]

end GlobalTheory.Chart.Assoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIntegralClosureEtaleHeightOne
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC


set_option maxHeartbeats 800000 in
theorem etale_bc : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA
    hFits ρ hρ hpt a ha0 ha A₁ _ _ _ _ _ _ f i₁ hf hi₁ hloc₁ hcomp hK
  obtain ⟨-, -, hqA, -, hj, hψ, htor⟩ := hFits
  obtain ⟨hρA, hρker, hρmod⟩ := hρ
  have hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0 := by
    rw [← RingHom.mem_ker, hρker]; exact Ideal.subset_span rfl
  have hmax := comap_maximalIdeal_eq_origin P φ hφ hsh hP
  set β := fibBC f i i₁ EA QA jA hcomp hj hf with hβ
  have hcong := reduce_sub_glue_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hρmod
  have hunit := isUnit_reduce f i i₁ EA QA jA hcomp hj ρ hρA hρX hmax hloc₁ hcong
  refine ⟨Ext f EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ideal₁ f i i₁ EA QA jA hcomp hj, inferInstance, locMap f i i₁ EA QA jA hcomp hj,
    fibMap f i i₁ EA QA jA hcomp hj hi₁, BC β DA, inferInstance, inferInstance, bcAct β DA q actA,
    ⟨hi₁, hloc₁, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, β, inclD β DA, ?_,
    inclD_algebraMap β DA⟩
  · simpa using hqA.map f
  · exact comap_ideal₁_eq_origin f i i₁ EA QA jA hcomp hj hmax hloc₁
  · apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj),
      locMap_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [glue_tmul]
    change algebraMap T[X] O (Polynomial.map i₁ p) * _ = _
    simp
  · exact IsLocalization.lift_comp (S := LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) (M := Algebra.algebraMapSubmonoid (Loc₁ f i i₁ EA QA jA hcomp hj) (nonZeroDivisors A₁)) _
  · exact isZTorsor_bc β DA q hq actA htor
  · apply RingHom.ext; intro x
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁ (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)]
    simp only [reduceLoc, IsLocalization.lift_eq, algebraMap_ext, reduce_tmul]
    change Polynomial.eval 0 (Polynomial.C x) * _ = _
    simp
  · exact GlobalTheory.T.ker_baseChangedReduction_eq_span_X T O A A₁ f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hρker
  · exact reduceLoc_sub_locMap_mem f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit hcong
  · exact GlobalTheory.T.localization_at_prime_etale_compat T O A A₁ f i i₁ hf EA QA jA hcomp hj ρ hρA hρX hunit DA q actA hq htor hpt
  · intro P₁ _ hP₁
    by_cases h : algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁
    · exact GlobalTheory.T.integralClosure_torsor_etale_height_one_abhyankar T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 hK P₁ hP₁ h
    · exact GlobalTheory.T.normal_local_ring_etale_base_change T O A A₁ f i i₁ hf EA QA jA hcomp hj DA q actA hq hqA htor a ha0 ha P₁ h
  · have hloc : (locMap f i i₁ EA QA jA hcomp hj).comp (locBC f i i₁ EA QA jA hcomp hj) = jA := by
      apply IsLocalization.ringHom_ext QA.primeCompl
      apply RingHom.ext; intro x
      simp [locBC_algebraMap, locMap_algebraMap, glue_inclE]
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    rw [RingHom.comp_apply, RingHom.comp_apply, hβ, fibBC_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply ψA, hψ]
    simp only [fibMap, IsLocalization.lift_eq, RingHom.comp_apply]
    rw [← RingHom.comp_apply (locMap f i i₁ EA QA jA hcomp hj), hloc]

end GlobalTheory.KeyOriginBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditive
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

private theorem dualDistrib_eq_mul'_map {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : Module.Dual O M) (ψ : Module.Dual O N) (t : M ⊗[O] N) :
    dualDistrib O M N (φ ⊗ₜ ψ) t = LinearMap.mul' O O (TensorProduct.map φ ψ t) := by
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul m n => simp [dualDistrib_apply]

theorem cartierDual_tangent_mod :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  intro O A _ _ _ _ _ _ a u
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.dual_quotient_form_eq_eval O A (Ideal.span {a})
    (u ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (CartierDual O A)) ∘ₗ
      (CartierDual.toDual O A).symm.toLinearMap)
  have hb' : ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := fun φ => hb φ.ofConv
  obtain ⟨y, hy⟩ := _root_.GlobalTheory.tensor_projective_dvd_of_coord_dvd O A A a (cobOne O A b) (fun φ ψ => by
    have hm := hb' (WithConv.toConv φ * WithConv.toConv ψ)
    rw [dUnit, AugCot.d_mul, map_add (f := _), map_smul, map_smul, ← dUnit, ← dUnit, hb', hb'] at hm
    simp only [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply] at hm
    have hc : (WithConv.toConv φ * WithConv.toConv ψ).ofConv b =
        LinearMap.mul' O O (TensorProduct.map φ ψ (CoalgebraStruct.comul b)) := rfl
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, dualDistrib_eq_mul'_map,
      cobOne_apply]
    simp only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [← hc, ← hm]
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    ring)
  exact ⟨b, y, hy, hb'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CdpGaloisLeOneOfAlgebraicRatFuncStatement
section
open GroundTheory.ProfCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  first | (exact @GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (exact GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (intros; apply GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  first | exact @GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | exact GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero | (intros; apply GlobalTheory.coeff_at2_x1_x2_eq_zero_of_third_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  first | exact @GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | exact GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | (intros; apply GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffProdPowFirstAddSecondThreeGroupsStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  first | exact @GlobalTheory.BinomLeft.coeff_prod_pow_add | exact GlobalTheory.BinomLeft.coeff_prod_pow_add | (intros; apply GlobalTheory.BinomLeft.coeff_prod_pow_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComulChartSubSubstMemPSmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory

theorem comul_ev_sub_ev₂_subst_mem :
    ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ)
      (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n,
        Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  intro p O _ G d c n F
  have hμ : HasSubst c.μ := hasSubst_of_constantCoeff_zero c.isLaw.const
  let φ₁ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n :=
    (Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n)
  let φ₂ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n := (c.ev₂ n).comp (substAlgHom hμ)
  have h1 : ∀ f, φ₁ f = Coalgebra.comul (R := O) (c.ev n f) := fun f => rfl
  have h2 : ∀ f, φ₂ f = c.ev₂ n (subst c.μ f) := fun f => by
    simp only [φ₂, AlgHom.comp_apply, coe_substAlgHom]
  have hpoly : φ₁.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      φ₂.comp (MvPolynomial.coeToMvPowerSeries.algHom O) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X,
      Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply]
    rw [h1, h2, (c.isEval n).1 i, subst_X hμ, c.comul]
  obtain ⟨N₁, hN₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, hN₂⟩ := (c.isEval₂ n).2 1
  set N := max N₁ N₂
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F
  set T := F - (P : MvPowerSeries (Fin d) O)
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α T = 0 := by
    intro α hα
    simp only [T, P, map_sub, MvPolynomial.coeff_coe, coeff_trunc']
    rw [if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_of_lt (lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  have hPe : φ₁ (P : MvPowerSeries (Fin d) O) = φ₂ (P : MvPowerSeries (Fin d) O) := by
    have := congrArg (fun ψ => ψ P) hpoly
    simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this
  obtain ⟨a, ha⟩ := hN₁ T fun α hα => hT α (lt_of_lt_of_le hα (le_max_left _ _))
  obtain ⟨b, hb⟩ := hN₂ (subst c.μ T) fun β hβ =>
    coeff_subst_eq_zero_of_degree_lt O (Fin d) (Fin d ⊕ Fin d) c.μ T N c.isLaw.const hT β
      (lt_of_lt_of_le hβ (le_max_right _ _))
  rw [pow_one] at ha hb
  refine ⟨Coalgebra.comul (R := O) a - b, ?_⟩
  have hF : F = (P : MvPowerSeries (Fin d) O) + T := by simp [T]
  rw [← h1, ← h2, hF, map_add (f := _), map_add (f := _), hPe, add_sub_add_left_eq_sub, h1, h2, ha, hb,
    ← Bialgebra.comulAlgHom_apply, map_mul, map_natCast, Bialgebra.comulAlgHom_apply,
    ← mul_sub, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefect
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

theorem constantCoeff_defect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ f hf n
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ.const n j, map_zero]
  unfold defect
  rw [map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU) hU hf.1, sub_zero]
  simp [hf.1]

end GlobalTheory.QLogDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHold
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.a6ring_holds : GlobalTheory.EtC.DivisorRingCompatibility := by
  intro q _ E
  exact ⟨fun hE _ _ a => (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a,
    fun a b c => GlobalTheory.T.tateTwistCupProduct_assoc q E a b c,
    fun a b => GlobalTheory.T.tateTwistCupProduct_graded_comm q E a b⟩

end GlobalTheory
end

