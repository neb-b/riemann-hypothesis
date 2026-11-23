module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCompactSecondCountable
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG Matrix GlobalTheory.BorelUMod
open scoped NNReal Pointwise

noncomputable section
namespace GlobalTheory.LineUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem locCompact_secondCountable [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    LocallyCompactSpace L ∧ SecondCountableTopology L := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := L)).2 ⟨inferInstance, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  constructor
  · open scoped Valued in exact inferInstance
  · open scoped Valued in exact inferInstance


open UpLatIndex in
theorem distribHaarChar_eq [CompleteSpace L] [LocallyCompactSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : IsUnramInv ϖ σ q) (u : Lˣ) : (distribHaarChar L u : ℝ) = (q : ℝ) ^ (-2 * ordL (u : L)) := by
  have hq : q ≠ 0 := by have := h.2.2.2.2.2.1; omega
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  haveI := (locCompact_secondCountable h).2
  borelize L
  let μ : Measure L := Measure.addHaar
  have key : ∀ k K : ℤ, k ≤ K → μ.real (ordBall L k) = (q : ℝ) ^ (2 * (K - k)) * μ.real (ordBall L K) := by
    intro k K hk
    have e := relIndex_ordBall h hk
    haveI : ((ordBall L K).addSubgroupOf (ordBall L k)).FiniteIndex :=
      ⟨ne_of_eq_of_ne e (pow_ne_zero _ (pow_ne_zero _ hq))⟩
    have := GlobalTheory.BaseModule.addRelIndex_mul_measure (ordBall L K) (ordBall L k) (ordBall_mono hk)
      (isOpen_vball h.2.2.2.1 K).measurableSet μ
    rw [Measure.real, ← this, e, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← pow_mul, Nat.cast_pow, ← zpow_natCast,
      Measure.real]
    congr 2
    omega
  have hs : u • (ordBall L 0 : Set L) = ordBall L (ordL (u : L)) := by
    ext x
    obtain ⟨y, rfl⟩ := MulAction.surjective u x
    beta_reduce
    rw [Set.smul_mem_smul_set_iff, SetLike.mem_coe, SetLike.mem_coe, mem_ordBall, mem_ordBall, Units.smul_def,
      smul_eq_mul, map_mul, v_eq_exp u.ne_zero, neg_zero, WithZero.exp_zero]
    exact (mul_le_iff_le_one_right WithZero.exp_pos).symm
  have h1 := congrArg ENNReal.toReal (distribHaarChar_mul μ u (ordBall L 0 : Set L))
  rw [hs, ENNReal.toReal_mul, ENNReal.coe_toReal, ← Measure.real, ← Measure.real,
    key 0 |ordL (u : L)| (abs_nonneg _), key (ordL (u : L)) _ (le_abs_self _), ← mul_assoc] at h1
  have hpos : μ.real (ordBall L |ordL (u : L)|) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(isOpen_vball h.2.2.2.1 _).measure_ne_zero μ ⟨0, zero_mem (ordBall L _)⟩,
      (isCompact_vball h _).measure_ne_top⟩
  have h2 := mul_right_cancel₀ hpos h1
  rw [eq_comm, ← mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq'), ← _root_.zpow_neg, ← zpow_add₀ hq'] at h2
  rw [← h2]
  congr 1
  ring

section Mat
omit [Valued L (WithZero (Multiplicative ℤ))]

variable (x y : Fin n → L) (z : L)

end Mat

variable {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)



variable {θ d : L} (hθ : θ + σ θ = 1) (hd : σ d = -d) (hd0 : d ≠ 0)



end GlobalTheory.LineUMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LocalLatStab

open GlobalTheory.AdelicLatMove

variable {D : D7}

def swp (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E : _ →+* _)

theorem map_toEAf (V : HSp D) (g : GA D V) :
    (mt V g).map (toEAf D) = (finMat D.sp.cm.sig V.gram g).map (swp D) := rfl

def swpVec (D : D7) (n : ℕ) (α : Af D.host.F) :
    (Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin n → EAf D) :=
  AddMonoidHom.mk' (fun y i => ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y i))
    (fun y z => by funext i; simp only [Pi.add_apply, map_add (f := _), mul_add])

theorem swpVec_pure {n : ℕ} (α β : Af D.host.F) (x : Fin n → D.host.E) :
    swpVec D n α (fun i => β ⊗ₜ[D.host.F] x i) = fun i => x i ⊗ₜ[D.host.F] (α * β) := by
  funext i
  change ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * (x i ⊗ₜ[D.host.F] β) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mulVec_swpVec (V : HSp D) (g : GA D V) (α : Af D.host.F)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (mt V g).map (toEAf D) *ᵥ swpVec D _ α y = swpVec D _ α (finMat D.sp.cm.sig V.gram g *ᵥ y) := by
  rw [map_toEAf]
  funext i
  change ∑ j, swp D (finMat D.sp.cm.sig V.gram g i j) * (((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y j)) =
    ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (∑ j, finMat D.sp.cm.sig V.gram g i j * y j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_left_comm]

theorem rankOne_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (a : D.host.E) (ha : a ∈ D.host.AA)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hs : s ∈ latHat D.host.F D.host.E LS)
    (t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E) (ht : t ∈ latHat D.host.F D.host.E LT) :
    rankOne S T a (swpVec D _ 1 s) (swpVec D _ α t) ∈ latO S T LS LT P := by
  change rankOneHom S T a _ _ ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨β, hβ, x, hx, rfl⟩ := hs
      obtain ⟨γ, hγ, y, hy, rfl⟩ := ht
      rw [swpVec_pure, swpVec_pure, one_mul]
      apply AddSubgroup.subset_closure
      refine ⟨α * γ * β, (mul_mem (mul_mem hα hγ : α * γ ∈ Formalism.UG.intAd D.host.F) hβ :
        α * γ * β ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_, a, ha, x, hx, y, hy,
        rankOne_pure S T a x y β (α * γ)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : GA D S) (h : GA D T)
    (hg : ∀ y ∈ latHat D.host.F D.host.E LS, finMat D.sp.cm.sig S.gram g *ᵥ y ∈ latHat D.host.F D.host.E LS)
    (hh : ∀ y ∈ latHat D.host.F D.host.E LT, finMat D.sp.cm.sig T.gram h *ᵥ y ∈ latHat D.host.F D.host.E LT)
    (u : WO S T) (hu : u ∈ latO S T LS LT P) : actO S T g h u ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := (one_mem _ : (1 : Af D.host.F) ∈ Formalism.UG.intAd D.host.F)
    have e := rankOne_pure S T a s t (1 * 1) (α * 1)
    rw [← swpVec_pure, ← swpVec_pure, mul_one, mul_one, mul_one] at e
    rw [← e, actO_rankOne, mulVec_swpVec, mulVec_swpVec]
    exact rankOne_mem S T LS LT P a ha α hα hP _
      (hg _ (AddSubgroup.subset_closure ⟨1, h1, s, hs, rfl⟩)) _
      (hh _ (AddSubgroup.subset_closure ⟨1, h1, t, ht, rfl⟩))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem finMat_mul_inv (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
  let f := Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
  change (mt V g).map f * (mt V g⁻¹).map f = 1
  rw [← Matrix.map_mul (f := f), ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inv_keeps (V : HSp D) (L : Set (Fin V.rank → D.host.E)) (g : GA D V)
    (hg : ∀ y, y ∈ latHat D.host.F D.host.E L ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y ∈ latHat D.host.F D.host.E L, finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y ∈ latHat D.host.F D.host.E L := by
  intro y hy
  rw [hg, Matrix.mulVec_mulVec, finMat_mul_inv, Matrix.one_mulVec]
  exact hy

theorem mem_latO_place_iff_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, IsPlaceIdem D v ε → ∀ (g : GA D S) (h : GA D T), (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔ (finMat D.sp.cm.sig S.gram g).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) → (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔ (finMat D.sp.cm.sig T.gram h).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) → ∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v) := by
  intro D S T ΛS ΛT _ _ v _ _ g h hg hh u
  refine ⟨actO_mem S T _ _ _ g h (fun y hy => (hg y).1 hy) (fun y hy => (hh y).1 hy) u, fun hu => ?_⟩
  have h1 := actO_mem S T _ _ _ g⁻¹ h⁻¹ (inv_keeps S _ g hg) (inv_keeps T _ h hh) _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LocalLatStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupported
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSAStep

theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

variable {R : Type*} [CommRing R] {a b : R}

theorem nrm_split (x y : ℍ[R, a, b]) (e : R) (he : e * e = e) :
    nrm ((1 - e) • x + e • y) = (1 - e) * nrm x + e * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  linear_combination ((x.re - y.re) ^ 2 - a * (x.imI - y.imI) ^ 2 - b * (x.imJ - y.imJ) ^ 2 +
    a * b * (x.imK - y.imK) ^ 2) * he

theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

theorem nrm_one : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

theorem pure_sq (u : ℍ[R, a, b]) (t : R) (hn : nrm u = 1) (hr : u.re = t) :
    (u - algebraMap R ℍ[R, a, b] t).re = 0 ∧
      (u - algebraMap R ℍ[R, a, b] t) * (u - algebraMap R ℍ[R, a, b] t) = algebraMap R ℍ[R, a, b] (t ^ 2 - 1) := by
  unfold nrm at hn
  refine ⟨by simp [hr], ?_⟩
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hr]
  · linear_combination (-1 : R) * hn + (u.re + t) * hr
  all_goals ring

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by
  ext <;> simp [rat]

theorem rat_algebraMap (c : F) :
    rat (algebraMap F ℍ[F, a, b] c) = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) := by
  ext <;> simp [rat, QuaternionAlgebra.algebraMap_eq]

theorem continuous_affine (ε : AF F) :
    Continuous fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b) := by
  apply continuous_induced_rng.2
  have e : (coords ∘ fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b)) =
      fun x => (1 - ε) • coords x + coords (ε • (1 : DA F a b)) := by
    funext x i
    fin_cases i <;> simp [coords]
  rw [e]
  have hc : Continuous (coords : DA F a b → Fin 4 → AF F) := continuous_induced_dom
  exact ((continuous_const (y := (1 - ε : AF F))).smul hc).add continuous_const

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

theorem key_step : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  classical
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hsplit g hg hg1 W hW
  have hee : ε * ε = ε := idem_of_isPlacesIdem hε
  have h11 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
  have h10 : (1 - ε) * ε = 0 := by linear_combination -hee
  have h01 : ε * (1 - ε) = 0 := by linear_combination -hee
  set ι := algebraMap F (AF F) with hι
  set φ : DA F a b → DA F a b := fun x => (1 - ε) • x + ε • (1 : DA F a b) with hφ
  have hφg : φ g = g := by
    have : φ g = g - ε • (g - 1) := by
      simp only [hφ, sub_smul, one_smul, smul_sub]; abel
    rw [this, hg1, sub_zero]
  have hW' : φ ⁻¹' W ∈ 𝓝 g :=
    (continuous_affine ε).continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (φ g); rw [hφg]; exact hW)
  obtain ⟨O, hO, ⟨x, hx⟩, hOu⟩ := _root_.GlobalTheory.QSA.traceOpen_adele F a b ha hb g hg _ hW'
  obtain ⟨t, htZ, s, hts⟩ := _root_.GlobalTheory.AddApproxPlaces.exists_approx_notMem F S₁ S₂ ε hε hS x O (hO.mem_nhds hx) {1, -1}
  obtain ⟨u₀, hu₀W, hu₀n, hu₀r⟩ := hOu _ hts
  obtain ⟨h₁, hh₁n, hh₁r⟩ := hsplit (ι t)
  have hc : t ^ 2 - 1 ≠ 0 := by
    have h1 : t ≠ 1 := fun h => htZ (by simp [h])
    have h2 : t ≠ -1 := fun h => htZ (by simp [h])
    have : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
    rw [this]
    exact mul_ne_zero (sub_ne_zero.2 h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))
  obtain ⟨u, hu⟩ : ∃ u : DA F a b, u = (1 - ε) • u₀ + ε • h₁ := ⟨_, rfl⟩
  have hun : nrm u = 1 := by
    rw [hu, nrm_split _ _ _ hee, hu₀n, hh₁n]; ring
  have hur : u.re = ι t := by
    rw [hu]
    simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, hu₀r]
    linear_combination hh₁r - s * hee
  obtain ⟨hq0, hqq⟩ := pure_sq u (ι t) hun hur
  set q := u - algebraMap (AF F) (DA F a b) (ι t) with hq
  have hqq' : q * q = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [hqq]; simp [hι]
  obtain ⟨p, hp0, hpp⟩ := _root_.GlobalTheory.QSA.PureSq.exists_rat_of_adelic F a b ha hb _ hc q hq0 hqq'
  have hrp0 : (rat p).re = 0 := by simp [rat, hp0]
  have hrpp : rat p * rat p = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [← rat_mul, hpp, rat_algebraMap]
  obtain ⟨y, hy, hyq⟩ := _root_.GlobalTheory.QSA.exists_unit_intertwiner F a b ha hb _ hc (rat p) q hrp0 hq0 hrpp hqq'
  set γ : ℍ[F, a, b] := algebraMap F ℍ[F, a, b] t + p with hγ
  have hγn : nrm γ = 1 := by
    have hre := congrArg QuaternionAlgebra.re hpp
    simp [QuaternionAlgebra.algebraMap_eq, hp0] at hre
    simp [hγ, nrm, QuaternionAlgebra.algebraMap_eq, hp0]
    linear_combination -hre
  have hyu : y * u = rat γ * y := by
    have : u = q + algebraMap (AF F) (DA F a b) (ι t) := by rw [hq]; abel
    rw [this, mul_add, hyq, hγ, rat_add, rat_algebraMap, add_mul, ← Algebra.commutes, add_comm]
  set h' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • h₁ with hh'
  set h'' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • star h₁ with hh''
  have hwh : φ u₀ * h' = u := by
    simp only [hφ, hh', hu, add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add]
  have hhh : h' * h'' = 1 := by
    simp only [hh', hh'', add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add, mul_star_eq, hh₁n, map_one]
    rw [← add_smul, sub_add_cancel, one_smul]
  refine ⟨φ u₀, hu₀W, y, hy, γ, hγn, h'', ?_, ?_, ?_⟩
  · rw [hh'', nrm_split _ _ _ hee, nrm_one, nrm_star, hh₁n]; ring
  · have e1 : h'' - 1 = ε • (star h₁ - 1) := by
      simp only [hh'', sub_smul, one_smul, smul_sub]; abel
    rw [e1, smul_smul, hee]
  · calc y * φ u₀ = y * φ u₀ * (h' * h'') := by rw [hhh, mul_one]
      _ = y * (φ u₀ * h') * h'' := by simp only [mul_assoc]
      _ = rat γ * y * h'' := by rw [hwh, hyu]

end GlobalTheory.QSAStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresPowEightMul
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqProd_pow_eight_mul (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) (hD : Datum p F L t) :
    sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  obtain ⟨hmul, -, hrep⟩ := _root_.GlobalTheory.CMModel.ker_sqrtNegNat_cyclic p F L t hp h4 h3 hD
  have ht0 : t ≠ 0 := by
    rintro rfl; exact hD.notMem (zero_mem _)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hα2 : sqrtNegNat p ^ 2 = -(p : ℂ) := by
    simp only [sqrtNegNat, mul_pow, Complex.I_sq]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    push_cast; ring
  have hα0 : sqrtNegNat p ≠ 0 := by
    intro h; apply hp0; have := hα2; rw [h] at this; simp at this; exact_mod_cast this
  have hα12 : sqrtNegNat p ^ 12 = (p : ℂ) ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, hα2]; ring
  have hinj : Set.InjOn (fun k : ℕ => (k : ℂ) * t) (Finset.Ico 1 p : Set ℕ) := by
    intro a _ b _ hab
    exact_mod_cast mul_right_cancel₀ ht0 hab
  set S := (Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t with hS
  have hcard : S.card = p - 1 := by
    rw [hS, Finset.card_image_of_injOn hinj, Nat.card_Ico]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : Even S.card := by
    rw [hcard]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have hpf := _root_.GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul L (sqrtNegNat p) S hα0 hD.mul hrep heven
  rw [hcard, hα12] at hpf
  rw [← hpf]
  congr 1

  have hprod : ∏ x ∈ S, L.derivWeierstrassP x
      = ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t) := by
    rw [hS, Finset.prod_image hinj]
  obtain ⟨e, he⟩ := _root_.GlobalTheory.sq_sum_equiv_Ico p hp h4
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have := (hmul (p : ℤ)).2 dvd_rfl
    simpa using this
  have hsplit : ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t)
      = ∏ s : Sq p ⊕ Sq p, L.derivWeierstrassP (((e s : ℕ) : ℂ) * t) := by
    rw [← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hneg : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inr k) : ℕ) : ℂ) * t)
      = -L.derivWeierstrassP (sqPt p t k) := by
    intro k
    rw [(he k).2, Nat.cast_sub (le_of_lt k.1.2), sub_mul, sqPt]
    have := L.derivWeierstrassP_add_coe (-((k.1 : ℕ) : ℂ) * t) ⟨_, hpt⟩
    simp only at this
    rw [show (p : ℂ) * t - ((k.1 : ℕ) : ℂ) * t = -((k.1 : ℕ) : ℂ) * t + (p : ℂ) * t by ring, this,
      neg_mul, L.derivWeierstrassP_neg]
  have hpos : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inl k) : ℕ) : ℂ) * t)
      = L.derivWeierstrassP (sqPt p t k) := by
    intro k; rw [(he k).1, sqPt]
  rw [hprod, hsplit, Fintype.prod_sum_type]
  simp only [hneg, hpos, Finset.prod_neg]
  have h1 : ((-1 : ℂ) ^ (Finset.univ : Finset (Sq p)).card) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [sqProd, mul_pow, mul_pow, h1]
  ring

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodular
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory

theorem coverUnitary_unimodular :
    ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧
      LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G :=
  fun p q T => ⟨(GlobalTheory.HolDS.haar_unimodular p q T).1, (GlobalTheory.HolDS.haar_unimodular p q T).2,
    GlobalTheory.HolDS.instLocallyCompact T, GlobalTheory.HolDS.instSecondCountable T, GlobalTheory.HolDS.t2Space_cuspAdeles T⟩

end GlobalTheory
end

