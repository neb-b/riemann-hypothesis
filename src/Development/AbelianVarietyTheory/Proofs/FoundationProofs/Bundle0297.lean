module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerTaylorDefectEqZero
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

def entireRing : Subring (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F}
  mul_mem' := fun {F G} hF hG => by
    exact (hF.mul hG : Differentiable ℂ (fun z => F z * G z))
  one_mem' := by simpa using (differentiable_const (1 : ℂ) : Differentiable ℂ fun _ : ℂ => (1 : ℂ))
  add_mem' := fun {F G} hF hG => by
    exact (hF.add hG : Differentiable ℂ (fun z => F z + G z))
  zero_mem' := by simpa using (differentiable_const (0 : ℂ) : Differentiable ℂ fun _ : ℂ => (0 : ℂ))
  neg_mem' := fun {F} hF => by
    exact (hF.neg : Differentiable ℂ (fun z => -F z))

theorem tay_coeff (F : ℂ → ℂ) (n : ℕ) : PowerSeries.coeff n (tay F) = coef1 F n := by
  simp [tay, PowerSeries.coeff_mk]

def tayHom : entireRing →+* PowerSeries ℂ where
  toFun F := tay F
  map_one' := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_one]
    exact GlobalTheory.SerTransport.taylorCoeff_const_function 1 n
  map_mul' F G := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_mul]
    have := GlobalTheory.SerTransport.taylorCoeff_mul_entire F.2 G.2 n
    simp only [tay_coeff]
    exact this
  map_zero' := by
    ext n
    rw [tay_coeff, map_zero]
    have := GlobalTheory.SerTransport.taylorCoeff_const_function 0 n
    simp only [ite_self] at this
    exact this
  map_add' F G := by
    ext n
    rw [map_add (f := _), tay_coeff, tay_coeff, tay_coeff]
    exact GlobalTheory.SerTransport.taylorCoeff_add_entire F.2 G.2 n

def scaleE (β : ℂ) (F : entireRing) : entireRing :=
  ⟨fun z => F.1 (β * z), F.2.comp (differentiable_id.const_mul β)⟩

theorem rescale_tayHom (β : ℂ) (F : entireRing) :
    PowerSeries.rescale β (tayHom F) = tayHom (scaleE β F) := by
  ext n
  rw [PowerSeries.coeff_rescale]
  show β ^ n * PowerSeries.coeff n (tay F.1) = PowerSeries.coeff n (tay (fun z => F.1 (β * z)))
  rw [tay_coeff, tay_coeff, GlobalTheory.SerTransport.taylorCoeff_scale_entire F.2]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem tay_defect_eq_zero : (∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0) → (∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s) → (∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0)) → ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j)) (GlobalTheory.FrobStick.tay (sgStar Λ)) = 0 := by
  intro hLine hRestr hId Λ hL v hv
  have hS : Differentiable ℂ (sgStar Λ) := hL.differentiable
  have hQ : Differentiable ℂ (sqTh Λ v) := hL.differentiable_sqTh v
  have hdS : Differentiable ℂ (deriv (sgStar Λ)) := fun z => ((hS.analyticAt z).deriv).differentiableAt
  have hdQ : Differentiable ℂ (deriv (sqTh Λ v)) := fun z => ((hQ.analyticAt z).deriv).differentiableAt
  have hA : Differentiable ℂ (colA Λ) :=
    (hS.pow 3 : Differentiable ℂ (fun z => sgStar Λ z ^ 3))
  have hB : Differentiable ℂ (colB Λ v) :=
    (hS.mul (hQ.add ((hS.pow 2).const_mul (wpF Λ v))) :
      Differentiable ℂ (fun z => sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)))
  have hC : Differentiable ℂ (colC Λ v) :=
    ((hS.mul hdQ).sub ((hdS.const_mul 2).mul hQ) :
      Differentiable ℂ (fun z => sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z))
  let a : Fin 3 → entireRing := ![⟨colA Λ, hA⟩, ⟨colB Λ v, hB⟩, ⟨colC Λ v, hC⟩]
  let s : entireRing := ⟨sgStar Λ, hS⟩
  have ha : ∀ j, tay (![colA Λ, colB Λ v, colC Λ v] j) = tayHom (a j) := by
    intro j; fin_cases j <;> rfl
  apply hLine ℂ
  intro t
  rw [hRestr]
  have e1 : (Matrix.of fun i j => PowerSeries.rescale (t i) (tay (![colA Λ, colB Λ v, colC Λ v] j))) =
      tayHom.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ha, rescale_tayHom]
  have es : tay (sgStar Λ) = tayHom s := rfl
  rw [e1, ← RingHom.map_det, es, rescale_tayHom, rescale_tayHom, rescale_tayHom, rescale_tayHom,
    show (2 : PowerSeries ℂ) = tayHom 2 from (map_ofNat tayHom 2).symm,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub]
  convert map_zero tayHom
  refine Subtype.ext (funext fun z => ?_)
  let φ : entireRing →+* ℂ := (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp entireRing.subtype
  rw [ZeroMemClass.coe_zero, Pi.zero_apply]
  have hφ : ∀ x : entireRing, (x : ℂ → ℂ) z = φ x := fun x => rfl
  rw [hφ]
  rw [map_sub, RingHom.map_det, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  have hm : φ.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) =
      Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j ((fun i => t i * z) i) := by
    ext i j; fin_cases j <;> rfl
  rw [hm, hId Λ hL v hv (fun i => t i * z)]
  change _ - 2 * sgStar Λ ((t 0 + t 1 + t 2) * z) * sgStar Λ ((t 0 - t 1) * z) * sgStar Λ ((t 1 - t 2) * z) *
    sgStar Λ ((t 2 - t 0) * z) = 0
  simp only [add_mul, sub_mul, sub_self]

end GlobalTheory.FrobStick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseIdeleTriv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem adele_algebraMap_apply (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k := rfl

theorem adele_mul_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a * b) v = a v * b v := rfl

theorem adele_sub_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a - b) v = a v - b v := rfl

theorem adele_one_apply (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl

theorem close_scaled (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : FiniteAdeleRing (𝓞 F) F) (k m : F) (hm : m ≠ 0) (n : ℕ)
    (h : Valued.v (a v - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) * v.valuation F m) :
    Valued.v (f a P - algebraMap E _ (algebraMap F E k)) ≤
      WithZero.exp (-(n : ℤ)) * P.valuation E (algebraMap F E m) := by
  have hm1 : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm
  have hm2 : P.valuation E (algebraMap F E m) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simpa using hm)
  have h1 := h0 ((a - algebraMap F _ k) * algebraMap F _ m⁻¹) n (by
    rw [adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply, map_mul, val_algebraMap,
      map_inv₀]
    exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm1)).2 h)
  rw [map_mul, map_sub, hf, hf, adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply,
    map_mul, val_algebraMap, map_inv₀, map_inv₀] at h1
  exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm2)).1 h1

theorem val_eq_one (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (h : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    Valued.v (f a P) = 1 := by
  have e1 : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← adele_mul_apply, Units.mul_inv, adele_one_apply, map_one]
  have e2 : Valued.v (f a P) * Valued.v (f (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) P) = 1 := by
    rw [← map_mul, ← adele_mul_apply, ← map_mul, Units.mul_inv, map_one, adele_one_apply, map_one]
  rw [h, one_mul] at e1
  have l1 := h0 a 0 (by simp [h])
  have l2 := h0 (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) 0 (by simp [e1])
  simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero] at l1 l2
  refine le_antisymm l1 ?_
  rw [← e2]
  exact mul_le_of_le_one_right' l2

theorem mem_aboveF (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

theorem algebraMap_tmul_one {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (k : R) : (algebraMap R A k) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B k) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_approx (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (b : FiniteAdeleRing (𝓞 F) F) (n : ℕ),
      Valued.v (b (P.under (𝓞 F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)))
    (χ : HChar E) (hχ : χ.TrivOn F) (N : ℕ) (hN : 0 < N) (α : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ),
      (∀ P ∈ S, Valued.v (f α P) = P.valuation E (k P : E) ∧
        Valued.v (f α P - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E)) ∧
      (∀ P, P ∉ S → Valued.v (f α P) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) ∧
      ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) = 1 := by
  classical
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx F N hN α
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨S.biUnion (aboveF (L := E) F), fun P => upF F (k (P.under (𝓞 F))), ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨v, hv, hPv⟩ := Finset.mem_biUnion.1 hP
    obtain rfl := (mem_aboveF v P).1 hPv
    obtain ⟨-, b1, b2⟩ := hS _ hv
    beta_reduce
    set kk := k (P.under (𝓞 F)) with hkk
    have hk : ((upF F kk : Eˣ) : E) = algebraMap F E kk := rfl
    rw [hk]
    have c1 := close_scaled f hf P _ (h0 P) α kk (N * kk) (mul_ne_zero hNF kk.ne_zero) 0 (by simpa using b1)
    have c2 := close_scaled f hf P _ (h0 P) α kk kk kk.ne_zero 1 (by simpa using b2)
    refine ⟨?_, by simpa using c1⟩
    rw [← val_algebraMap]
    apply Valuation.map_eq_of_sub_lt
    rw [val_algebraMap]
    refine c2.trans_lt ?_
    have hm2 : P.valuation E (algebraMap F E kk) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (by simp)
    refine mul_lt_of_lt_one_left (zero_lt_iff.2 hm2) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro P hP
    have hv : P.under (𝓞 F) ∉ S := fun h =>
      hP (Finset.mem_biUnion.2 ⟨_, h, (mem_aboveF _ P).2 rfl⟩)
    obtain ⟨b1, b2⟩ := hS' _ hv
    refine ⟨val_eq_one f P _ (h0 P) α b1, fun h => b2 ?_⟩
    change algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    simpa using h
  · rw [Finset.prod_biUnion]
    · refine Finset.prod_eq_one fun v _ => ?_
      have := hχ.1 v (k v)
      rw [HChar.resFin, MonoidHom.finsetProd_apply] at this
      rw [← Units.coe_prod, Units.val_eq_one, ← this]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [← (mem_aboveF v P).1 hP]; rfl
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (mem_aboveF v P).1 hv, ← (mem_aboveF w P).1 hw]

end General

theorem finite_idele_base_trivial : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F → ∀ a : (AF D.host.F)ˣ, infPart D (idF D a : AE D) = 1 → c (idF D a) = 1 := by
  intro D c χ hc hχ a ha
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  let α : (Af D.host.F)ˣ := Units.map (sndA D.host.F).toRingHom.toMonoidHom a
  let f : Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    ι.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E))
  have hfa : ∀ b, f b = ι (b ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ => rfl
  have hf : ∀ k : D.host.F, f (algebraMap D.host.F _ k) = algebraMap D.host.E _ (algebraMap D.host.F D.host.E k) := by
    intro k
    rw [hfa, ← h1, algebraMap_tmul_one]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (b : Af D.host.F) (n : ℕ),
      Valued.v (b (P.under (𝓞 D.host.F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)) := by
    intro P b n h
    have := h3 b 0 P n (by rwa [map_zero, sub_zero])
    rwa [map_zero, map_zero, sub_zero] at this
  have hfin : ι (finPart D (idF D a : AE D)) = f α := rfl
  obtain ⟨S, k, hS, hS', hp⟩ := exists_approx f hf h0 χ hχ N hN α
  rw [← hfin] at hS hS'
  exact Circle.ext ((hprod (idF D a) ha S k hS hS').trans hp)

end GlobalTheory.BaseIdeleTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfMemSuppSpan
section
noncomputable section

namespace GlobalTheory.SeriesSupport

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.MainNotions.ArithmeticCylinders Formalism.BasicNotions Formalism.CyclotomicNorms
open scoped Classical

section Dual

variable {g : ℕ} [Fact g.Prime]

theorem phi_conj (L : LabelDatum g) (x : Fbar g) : GalSer.phi L (starRingAut : ℂ ≃+* ℂ) x = x⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, GalSer.phi_zero, inv_zero]
  apply GalSer.teich_injective L
  rw [GalSer.teich_phi]
  have h1 : ‖L.teich x‖ = 1 := (L.teich.isOfFinOrder (GalSer.finOrder hx)).norm_eq_one
  have h2 : L.teich x⁻¹ = (L.teich x)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])
  rw [h2, Complex.inv_eq_conj h1]
  rfl

theorem roots_reverse {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    have ha : a ≠ 0 := fun h => hs.1 h.symm
    have hX : (X : K[X]).reverse = 1 := by simp [reverse]
    have e : (X - C a : K[X]).reverse = C (-a) * (X - C a⁻¹) := by
      rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, hX, mul_sub, ← C_mul, neg_mul,
        mul_inv_cancel₀ ha]
      simp [add_comm]
    have hm : (s.map fun x => X - C x).prod ≠ 0 :=
      (monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x).ne_zero
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, e, roots_mul, roots_C_mul _ (neg_ne_zero.2 ha),
      roots_X_sub_C, ih hs.2, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 ha)) (X_sub_C_ne_zero _))
      (by rwa [Ne, reverse_eq_zero])

theorem rel_dual (L : LabelDatum g) {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    GalSer.Rel L (starRingAut : ℂ ≃+* ℂ) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  refine ⟨?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
      inv_mul_cancel₀ h0]
  · have hz : (0 : Fbar g) ∉ rootsBar f := fun h => by
      rw [GalSer.mem_rootsBar hm.ne_zero, ← coeff_zero_eq_aeval_zero'] at h
      exact h0 ((map_eq_zero _).1 h)
    have e : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, reflect_map, natDegree_map]
    have hf := (IsAlgClosed.splits (f.map (algebraMap (ZMod g) (Fbar g)))).eq_prod_roots_of_monic (hm.map _)
    rw [rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
    simp only [phi_conj]
    exact roots_reverse _ hz

end Dual

local instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

abbrev LocRep (D : D7) (k : Fin 2) (n : ℕ) : Type 1 := Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])

variable (D : D7)
  (σ : D.ntypes.Par → ∀ k, D.nd.PlG k → LocRep D k D.R.r)
  (ΩV : D.what₂.Tup → ℕ → ∀ k, D.nd.PlG k → LocRep D k D.R.nV)
  (ιV : ∀ μ j k v, D.what₂.Mt μ j →ₗ[ℂ] ΩV μ j k v)
  (ΩX : D.what₂.Tup → ∀ k, D.nd.PlG k → LocRep D k D.R.rankX')
  (ιX : ∀ μ k v, D.what₂.Amb μ →ₛₗ[starRingEnd ℂ] ΩX μ k v)

end GlobalTheory.SeriesSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

namespace GlobalTheory.AutomorphicL2Local

theorem tsum_indicator_le {G : Type*} [Group G] (Γ : Subgroup G) (C : Set G) (x : G) (a : ℝ≥0∞) :
    ∑' γ : Γ, C.indicator (fun _ => a) (γ * x) ≤ ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) * a := by
  classical
  set T : Set Γ := {γ | (γ : G) * x ∈ C} with hT
  have h1 : (fun γ : Γ => C.indicator (fun _ => a) ((γ : G) * x)) = T.indicator (fun _ => a) := by
    ext γ
    simp [T, Set.indicator_apply]
  rw [h1, ← tsum_subtype T (fun _ => a), ENNReal.tsum_set_const]
  have hle : T.encard ≤ {γ : Γ | (γ : G) ∈ C * C⁻¹}.encard := by
    rcases T.eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
    · simp [h]
    calc T.encard = ((fun γ => γ * γ₀⁻¹) '' T).encard :=
          (Set.InjOn.encard_image (s := T) (f := fun γ : Γ => γ * γ₀⁻¹)
            (fun _ _ _ _ h => mul_right_cancel h)).symm
      _ ≤ _ := by
          refine Set.encard_le_encard ?_
          rintro _ ⟨γ, hγ, rfl⟩
          refine Set.mem_mul.mpr ⟨(γ : G) * x, hγ, ((γ₀ : G) * x)⁻¹, by simpa [hT] using hγ₀, ?_⟩
          simp [mul_assoc]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) bot_le

theorem memLp_restrict_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F C hC
  classical
  have hmeas : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  set N : ℝ≥0∞ := (({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℕ∞) : ℝ≥0∞) with hNdef
  have hN : N ≠ ⊤ := by
    have hfin : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    simpa [N] using hfin.encard_lt_top.ne
  have hF2 : ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ < ∞ := by
    have := (Lp.memLp F).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable F)] at this
    simpa using this
  have key : ∫⁻ g, ‖lift Γ F g‖ₑ ^ (2 : ℝ) ∂μ.restrict C < ∞ := by
    rw [← lintegral_indicator hCm,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeas.enorm.pow_const (2 : ℝ)).indicator hCm)]
    calc ∫⁻ q, ∑' γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out) ∂quotMeasure Γ μ
        ≤ ∫⁻ q, N * ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ := by
          refine lintegral_mono fun q => ?_
          have e : ∀ γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out)
              = C.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) (γ * q.out) := by
            intro γ
            simp only [Set.indicator_apply]
            split_ifs
            · simp [lift, mk_mul, Quotient.out_eq]
            · rfl
          simp_rw [e]
          exact tsum_indicator_le Γ C q.out _
      _ = N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ := lintegral_const_mul' _ _ hN
      _ < ∞ := ENNReal.mul_lt_top hN.lt_top hF2
  have hLp : MemLp (lift Γ F) 2 (μ.restrict C) := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmeas.restrict]
    simpa using key
  refine ⟨hLp, ?_⟩
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  exact hLp.integrable one_le_two

end GlobalTheory.AutomorphicL2Local
end

