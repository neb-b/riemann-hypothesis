module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0011
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.FinalC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualSumPairingMapEqPi
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.SelfDualProduct

theorem exists_test (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, HasCompactSupport Φ ∧ Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), h1, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem integral_prod_exp {T V : Type} [Fintype T] [MeasurableSpace V] (ε : ℝ) (β : V → V → ℝ)
    (μ₀ : Measure V) [SigmaFinite μ₀] (f : V → ℂ) (y : T → V) :
    ∫ x : T → V, (∏ ρ, f (x ρ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (x ρ) (y ρ) : ℝ) : ℂ))
        ∂(Measure.pi fun _ : T => μ₀) = ∏ ρ, ActionCoordinates.fourierT ε β μ₀ f (y ρ) := by
  unfold ActionCoordinates.fourierT
  rw [← integral_fintype_prod_eq_prod (fun ρ (x : V) => f x *
    Complex.exp (2 * Real.pi * Complex.I * ((ε * β x (y ρ) : ℝ) : ℂ)))]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  rw [Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

theorem map_eq_pi : ∀ (T V W : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : W ≃ₜ+ (T → V)) (ε : ℝ) (β : V → V → ℝ) (μ₀ : Measure V), μ₀.IsAddHaarMeasure → ActionCoordinates.IsSelfDualFor ε β μ₀ → ∀ (μ : Measure W) (χ : W → W → ℂ), (∀ x y, χ x y = Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (e x ρ) (e y ρ) : ℝ) : ℂ))) → SelfDual μ χ → μ.map e = Measure.pi fun _ : T => μ₀ := by
  intro T V W _ _ _ _ _ _ _ _ _ _ e ε β μ₀ hμ₀ hsd μ χ hχ hμ
  haveI : IsTopologicalAddGroup W :=
    Topology.IsInducing.topologicalAddGroup (e : W →+ (T → V)) e.toHomeomorph.isInducing
  haveI := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set ν : Measure (T → V) := Measure.pi fun _ : T => μ₀ with hν
  haveI : ν.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h0 : μ.map e = Measure.addHaarScalarFactor (μ.map e) ν • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set c : NNReal := Measure.addHaarScalarFactor (μ.map e) ν
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hint : ∀ F : (T → V) → ℂ, ∫ x, F (e x) ∂μ = (c : ℂ) * ∫ x, F x ∂ν := fun F => by
    rw [← hemb.integral_map, h0, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hF : ∀ (f : V → ℂ) (y : W), ∫ x, (∏ ρ, f (e x ρ)) * χ x y ∂μ =
      (c : ℂ) * ∏ ρ, ActionCoordinates.fourierT ε β μ₀ f (e y ρ) := fun f y => by
    rw [← integral_prod_exp, ← hint]
    simp only [hχ]
  obtain ⟨φ, hφs, hφ0⟩ := exists_test V
  obtain ⟨-, hI, hinv⟩ := hsd φ
  have hc1 : Continuous fun x : T → V => ∏ ρ, φ (x ρ) :=
    by fun_prop
  have hs1 : HasCompactSupport fun x : T → V => ∏ ρ, φ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun _ : T => hφs.isCompact) fun x hx => ?_
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  have hI1 : Integrable (fun y : T → V => (c : ℂ) * ∏ ρ, ActionCoordinates.fourierT ε β μ₀ φ (y ρ))
      (μ.map e) := by
    rw [h0]
    exact ((Integrable.fintype_prod (f := fun _ : T => ActionCoordinates.fourierT ε β μ₀ φ)
      fun _ => hI).const_mul _).smul_measure_nnreal
  have key := hμ.2 (fun x => ∏ ρ, φ (e x ρ)) (hc1.comp e.continuous)
    (hs1.comp_homeomorph e.toHomeomorph) (by
      simp only [hF]
      exact (hemb.integrable_map_iff).1 hI1) 0
  simp only [hF, mul_assoc] at key
  rw [integral_const_mul, hF] at key
  simp only [hinv, map_zero, neg_zero, Pi.zero_apply, hφ0, Finset.prod_const_one, mul_one] at key
  have h5 : c * c = 1 := by exact_mod_cast key
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [h0, h6, one_smul]

end GlobalTheory.SelfDualProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabilizerGroupMap
section
noncomputable section

namespace GlobalTheory.Proof.StabilizerGroupMap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

theorem bc_inclE_injective (D : D7) :
    Function.Injective
      (bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
        GL (Fin D.R.k) D.host.E →*
          GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) := inferInstance
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => ?_)
  apply (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).injective
  have h2 := congrArg (fun g : GL (Fin D.R.k) _ => g.val i j) hab
  simpa [bc] using h2

theorem stabGroup_eq_map (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y =
      (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y).map
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.map_colStab D Lv u y).symm

theorem stabGroup_eq_bot_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥ ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y = ⊥ := by
  rw [stabGroup_eq_map, Subgroup.map_eq_bot_iff_of_injective _ (bc_inclE_injective D)]

theorem at_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    (GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D, GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥) ↔
      GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivialAt D Lv u := by
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact ⟨fun h y => (stabGroup_eq_bot_iff D Lv u y).1 (h y.1 y.2),
    fun h y hy => (stabGroup_eq_bot_iff D Lv u ⟨y, hy⟩).2 (h ⟨y, hy⟩)⟩

theorem columnStabilisersTrivial_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.ColumnStabilisersTrivial ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivial :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => at_iff D Lv u

end GlobalTheory.Proof.StabilizerGroupMap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabilizerIndex
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Proof.StabilizerIndex

lemma index_field (F : Type) [Field F] [Finite F] (k : ℕ) (φ : Fin k → F) (hφ : φ ≠ 0) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = Nat.card F ^ k - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := Formalism.LogVandermondeBounds.StandardLattice.cardStabilizerVector F k φ hφ
  have hcm := (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).card_mul_index
  have hc : Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ) =
      Nat.card {A : GL (Fin k) F // Matrix.vecMul φ (A : Matrix (Fin k) (Fin k) F) = φ} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun A => Iff.rfl))
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← hc, ← hcm] at h
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h).symm

theorem index_stabRow : ∀ (κ : Type) [CommRing κ] (T k : ℕ), T.Prime → Nat.card κ = T →
    ∀ φ : Fin k → κ, φ ≠ 0 →
      (((GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index : ℕ) : ℝ) = (T : ℝ) ^ k - 1 := by
  intro κ _ T k hT hcard φ hφ
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : Finite κ := Nat.finite_of_card_ne_zero (hcard ▸ hT.ne_zero)
  letI : Fintype κ := Fintype.ofFinite κ
  have e : ZMod T ≃+* κ := ZMod.ringEquivOfPrime κ hT (by rw [← Nat.card_eq_fintype_card, hcard])
  have hF : IsField κ := MulEquiv.isField (Field.toIsField (ZMod T)) e.symm.toMulEquiv
  have h := @index_field κ hF.toField _ k φ hφ
  have h' : (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = T ^ k - 1 := by
    rw [← hcard]; exact h
  rw [h', Nat.cast_sub (Nat.one_le_pow _ _ hT.pos)]
  push_cast
  rfl

end GlobalTheory.Proof.StabilizerIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
section
open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.Proof.TensorMapDescent

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

section BaseChange

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem fockB_map {σ : Type} (f g : MvPolynomial σ K) : fockB (map φ f) (map φ g) = φ (fockB f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockB_eq_sum _ _ f.support (support_map_subset _ _), fockB, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem map_ten {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) :
    map φ (ten f) = ten fun τ => map φ (f τ) := by
  unfold ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => fk_map_blockEmb φ τ _

theorem ten_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ nablaSq K n (lam τ)) : ten f ∈ VV K lam :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem ten_ne_zero {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) (hf : ∀ τ, f τ ≠ 0) :
    ten f ≠ 0 := by
  unfold ten
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ) :=
    MvPolynomial.rename_injective _ (fun a b h => (Prod.mk.inj h).2)
  exact (map_ne_zero_iff _ hinj).mpr (hf τ)

theorem map_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K ι n) (hF : F ∈ VV K lam) :
    map φ F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h := map_ten φ f
    unfold ten at h
    rw [h]
    exact ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.dualWeylMap K K' φ n n _ _ (hf τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem ssB_desc {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n ν, ssB K' ν m = map φ f := by
  obtain ⟨k, sz, hsz, I, hsh, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis K' n n ν).choose_spec.2 m).2.2
  refine ⟨Formalism.GradedWeylDivisibility.bideterminant K sz hsz I, ?_, by rw [fk_map_bidet]; exact h⟩
  rw [← hsh]
  exact Formalism.GradedWeylDivisibility.bidetMem K n n k sz hsz I

theorem bVVfun_desc {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ F ∈ VV K lam, bVVfun K' lam i = map φ F := by
  choose f hf hf' using fun τ => ssB_desc φ (lam τ).natW (i τ)
  refine ⟨ten f, ten_mem lam f hf, ?_⟩
  rw [map_ten]
  exact congrArg ten (funext hf')

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem eq_zero_of_fockB [CharZero K] (sg : ι → DomWeight n) (x : VV K sg)
    (h : ∀ i, fockB (bVVfun K sg i) (x : Pol K ι n) = 0) : x = 0 := by
  refine (pairingBNondegenerate_holds K ι n sg).2 x fun y => ?_
  have : (pairBK sg).flip x = 0 := by
    refine (bVV K sg).ext fun i => ?_
    rw [LinearMap.flip_apply, pairBK_apply, pairB_apply, bVV_coe, h i, mul_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun this y

open Classical in
theorem gramB_det_ne_zero [CharZero K] (sg : ι → DomWeight n) : (Br.gramB (K := K) sg).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 : ∑ j, v j • bVV K sg j = 0 := by
    refine eq_zero_of_fockB sg _ fun i => ?_
    have := congrFun hv0 i
    simp only [Matrix.mulVec, dotProduct, Br.gramB, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← fockBL_apply, Submodule.coe_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, map_smul, bVV_coe, fockBL_apply, smul_eq_mul, mul_comm]
  exact hv (funext (Fintype.linearIndependent_iff.mp (bVV K sg).linearIndependent v h1))

theorem fockB_projVV_basis [CharZero K] (sg : ι → DomWeight n) (F : Pol K ι n) (k : VVIdx sg) :
    fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) = fockB (bVVfun K sg k) F := by
  classical
  have hG := Matrix.mul_nonsing_inv (Br.gramB (K := K) sg) (Ne.isUnit (gramB_det_ne_zero sg))
  have h1 : fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) =
      ∑ i, ∑ j, Br.gramB (K := K) sg k i * (Br.gramB (K := K) sg)⁻¹ i j * fockB (bVVfun K sg j) F := by
    rw [← fockBL_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Br.projVV, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, Submodule.coe_sum,
      Submodule.coe_smul, map_sum, map_smul, bVV_coe, fockBL_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Br.gramB (K := K) sg k i = fockB (bVVfun K sg k) (bVVfun K sg i) from rfl]
    ring
  rw [h1, Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Matrix.mul_apply, hG, Matrix.one_apply]
  simp

theorem fockB_projVV [CharZero K] (sg : ι → DomWeight n) (F y : Pol K ι n) (hy : y ∈ VV K sg) :
    fockB y (Br.projVV sg F : Pol K ι n) = fockB y F := by
  rw [← (bVVfun_spec K sg).2] at hy
  simp only [← fockBL_apply]
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact fockB_projVV_basis sg F k
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
  | smul c x _ hx => simp only [map_smul, LinearMap.smul_apply, hx]

theorem projVV_map [CharZero K] [CharZero K'] (sg : ι → DomWeight n) (F : Pol K ι n) :
    (Br.projVV sg (map φ F) : Pol K' ι n) = map φ (Br.projVV sg F : Pol K ι n) := by
  have h := eq_zero_of_fockB sg
    (Br.projVV sg (map φ F) - ⟨map φ (Br.projVV sg F : Pol K ι n), map_mem_VV φ sg _ (Br.projVV sg F).2⟩) fun i => by
      rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply, fockB_projVV_basis]
      obtain ⟨Y, hY, hY'⟩ := bVVfun_desc φ sg i
      rw [hY', fockB_map, fockB_map, fockB_projVV sg F Y hY, sub_self]
  exact congrArg Subtype.val (sub_eq_zero.mp h)

variable {N : ℕ} (hN : N = n + 1)

omit [Fintype ι] in
theorem coefLast_map (b : ι → Fin n → ℕ) (F : Pol K ι N) :
    Br.coefLast hN b (map φ F) = map φ (Br.coefLast hN b F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have h1 : (monomial m a : Pol K ι N) = a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    have h2 : (monomial m (φ a) : Pol K' ι N) = φ a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [map_monomial, h2, h1, map_smul, map_smul, Br.coefLast_monomial, Br.coefLast_monomial]
    split_ifs
    · simp [smul_monomial, map_monomial]
    · simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem xiBr_map (lam : DomWeight N) (sg : DomWeight n) : map φ (Br.xiBr K hN lam sg) = Br.xiBr K' hN lam sg := by
  simp only [Br.xiBr, Br.zMinor, map_prod, map_mul, map_pow, fk_map_initMinor, Formalism.GradedWeylDivisibility.lclosedeq_lpMinor_map]

theorem brConst_map (lam : ι → DomWeight N) (sg : ι → DomWeight n) :
    φ (Br.brConst hN K lam sg) = Br.brConst hN K' lam sg := by
  simp only [Br.brConst, Br.kapBr, map_prod, map_mul, map_div₀, map_intCast, ← fockB_map, xiBr_map, extremal,
    Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

theorem branchingProjection_map [CharZero K] [CharZero K'] (lam : ι → DomWeight N) (sg : ι → DomWeight n) (F : Pol K ι N) :
    (Br.brStdP hN lam sg (map φ F) : Pol K' ι n) = map φ (Br.brStdP hN lam sg F : Pol K ι n) := by
  simp only [Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [coefLast_map, projVV_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C, brConst_map]

theorem brOne_map [CharZero K] [CharZero K'] (lam : DomWeight N) (sg : DomWeight n) (f : MvPolynomial (Fin N × Fin N) K) :
    GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K' hN lam sg (map φ f) = map φ (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K hN lam sg f) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply]
  rw [← map_rename, branchingProjection_map, map_rename]

end BaseChange

end GlobalTheory.Proof.TensorMapDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylFieldSmul
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

theorem hcVal_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ} (μ : Fin N → R) (k : ℕ) :
    hcVal S (fun i => φ (μ i)) k = φ (hcVal R μ k) := by
  have hM : hcMat S (fun i => φ (μ i)) = (hcMat R μ).map φ := by
    ext i l
    simp only [hcMat, shift, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hP : (hcMat S (fun i => φ (μ i))) ^ k = ((hcMat R μ) ^ k).map φ := by
    rw [hM]
    exact (map_pow (RingHom.mapMatrix φ) (hcMat R μ) k).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hcVal, hP, Matrix.map_apply, map_sum]

theorem gel_dualWeyl_int (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (j : ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) : gel ℤ N N j f = hcVal ℤ (fun i => (ν i : ℤ)) j • f := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [(_root_.GlobalTheory.Alc.rowOperators_main ℤ N N).2.2 ℚ (Int.castRingHom ℚ) j f,
    GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight N ν hν j _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) N N ν f hf),
    smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  congr 2
  rw [← hcVal_map]
  simp

theorem gel_dualWeyl_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ j : ℕ,
    ∀ f ∈ dualWeyl k N N ν, gel k N N j f = hcVal k (fun i => (ν i : k)) j • f := by
  intro k _ N ν hν j f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hg
    have hb : bideterminant k sz hsz I = map (Int.castRingHom k) (bideterminant ℤ sz hsz I) := by
      simp only [bideterminant, initMinor, map_prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [RingHom.map_det]
      congr 1
      ext p q
      simp
    have hmem : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ N N ν := hsh ▸ bidetMem ℤ N N K sz hsz I
    rw [hb, ← (_root_.GlobalTheory.Alc.rowOperators_main ℤ N N).2.2 k (Int.castRingHom k) j, gel_dualWeyl_int N ν hν j _ hmem,
      smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
    congr 2
    rw [← hcVal_map]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory.Alc
end
end

