module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Product
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralDualOfIndependentModUniformizer
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isUnit_valuationSubring_iff (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := congrArg (fun y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring =>
      Valued.v (y : L)) u.mul_inv
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h1
    have hu : Valued.v ((u : _) : L) ≤ 1 := ((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)).2
    have hw : Valued.v ((u⁻¹ : _) : L) ≤ 1 := ((u⁻¹ : _) : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).2
    refine le_antisymm hu ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
      _ ≤ Valued.v ((u : _) : L) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    let y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring :=
      ⟨(x : L)⁻¹, by
        show Valued.v (x : L)⁻¹ ≤ 1
        rw [map_inv₀, h, inv_one]⟩
    have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

theorem residue_eq_zero_iff_dvdPow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsLocalRing.residue _ x = 0 ↔ DvdPow ϖ 1 (x : L) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_valuationSubring_iff]
  have hx : Valued.v (x : L) ≤ 1 := x.2
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  constructor
  · intro hne
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx hne
    have hle := le_exp_neg_one_of_lt_one' hlt
    refine ⟨(x : L) / ϖ, ?_, by field_simp⟩
    show Valued.v ((x : L) / ϖ) ≤ 1
    rw [map_div₀, hϖ]
    have hpos : (0 : WithZero (Multiplicative ℤ)) < ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
      WithZero.zero_lt_coe _
    exact (div_le_one₀ hpos).2 hle
  · rintro ⟨b, hb, hxb⟩ h1
    have hb' : Valued.v b ≤ 1 := hb
    rw [hxb, pow_one, map_mul, hϖ] at h1
    have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * Valued.v b ≤
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * 1 := by gcongr
    rw [h1, mul_one] at this
    exact absurd this (by decide)

theorem exists_dual_of_indepMod : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → Fin m → L), (∀ i r, z i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    ∃ a : ι → Fin m → L, (∀ i r, a i r ∈ Formalism.UG.intL L) ∧ ∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0 := by
  intro L _ _ ϖ hϖ m ι _ _ z hz hind
  classical
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  let k := IsLocalRing.ResidueField O
  let res : O →+* k := IsLocalRing.residue O
  have hres : Function.Surjective res := IsLocalRing.residue_surjective
  let Z : Matrix ι (Fin m) O := fun i r => ⟨z i r, hz i r⟩
  let Zb : Matrix ι (Fin m) k := Z.map res

  have hinj : LinearMap.ker (Matrix.mulVecLin Zbᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    let d : ι → O := fun i => (hres (w i)).choose
    have hd : ∀ i, res (d i) = w i := fun i => (hres (w i)).choose_spec
    have hsum : ∀ r, DvdPow ϖ 1 (∑ i, ((d i : O) : L) * z i r) := by
      intro r
      have h1 : res (∑ i, d i * Z i r) = 0 := by
        have := congrFun hw r
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simpa [Zb, hd, mul_comm] using this
      have h2 := (residue_eq_zero_iff_dvdPow hϖ _).1 h1
      simpa [Z] using h2
    have hdi := hind (fun i => (d i : L)) (fun i => (d i).2) hsum
    funext i
    rw [← hd i]
    exact (residue_eq_zero_iff_dvdPow hϖ _).2 (hdi i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  let B : Matrix ι (Fin m) k := LinearMap.toMatrix' g
  have hB : B * Zbᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  let Bo : Matrix ι (Fin m) O := fun i r => (hres (B i r)).choose
  have hBo : Bo.map res = B := by
    ext i r; exact (hres (B i r)).choose_spec
  let M : Matrix ι ι O := Bo * Zᵀ
  have hM : M.map res = 1 := by
    simp only [M, Matrix.map_mul, Matrix.transpose_map, hBo]
    exact hB
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : res M.det = 1 := by
      rw [RingHom.map_det]
      change (M.map res).det = 1
      rw [hM, Matrix.det_one]
    rw [show IsLocalRing.residue O M.det = res M.det from rfl, this]
    exact one_ne_zero
  let A : Matrix ι (Fin m) O := M⁻¹ * Bo
  have hA : A * Zᵀ = 1 := by
    simp only [A, Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul M hdet
  refine ⟨fun i r => (A i r : L), fun i r => (A i r).2, fun i j => ?_⟩
  have h := congrArg (fun x : O => (x : L)) (congrFun (congrFun hA i) j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  have h2 : ((∑ r, A i r * Z j r : O) : L) = ∑ r, (A i r : L) * z j r := by
    simp [Z, O]
  rw [h2] at h
  rw [h]
  split_ifs <;> simp

end GlobalTheory.Hk3.IntWitt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HopfOrderScalarExtension
section
open NumberField GlobalTheory.LKTrip
open scoped TensorProduct Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

def extZero (s : Fin n → Prop) [DecidablePred s] : ({i // s i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun w i := if hi : s i then w ⟨i, hi⟩ else 0
  map_add' a b := by funext i; by_cases hi : s i <;> simp [hi]
  map_smul' r a := by funext i; by_cases hi : s i <;> simp [hi]

theorem extZero_apply_mem (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) (i : {i // s i}) :
    extZero s w i = w i := by simp [extZero, i.2]

theorem extZero_apply_not (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) {i : Fin n} (hi : ¬ s i) :
    extZero s w i = 0 := by simp [extZero, hi]

theorem quad_mulVec (h X : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    star (X *ᵥ u) ⬝ᵥ h *ᵥ (X *ᵥ u) = star u ⬝ᵥ (Xᴴ * h * X) *ᵥ u := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem re_quad_ext (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (s : Fin n → Prop) [DecidablePred s]
    (w : {i // s i} → ℂ) :
    (star ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w) ⬝ᵥ
        h *ᵥ ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w)).re =
      ∑ i, hh.eigenvalues i * Complex.normSq (extZero s w i) := by
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp hh.eigenvectorUnitary.2, Matrix.one_mulVec]

theorem finrank_le_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (S : Submodule ℂ (Fin n → ℂ))
    (hS : ∀ u ∈ S, u ≠ 0 → 0 < (star u ⬝ᵥ h *ᵥ u).re) :
    Module.finrank ℂ S ≤ Fintype.card {i : Fin n // 0 < hh.eigenvalues i} := by
  refine GlobalTheory.SylvesterInertia.finrank_le_card_of_vanish
    (star (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) S _ fun u hu hv => ?_
  by_contra hne
  have hpos := hS u hu hne
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh u] at hpos
  refine absurd hpos (not_lt.mpr (Finset.sum_nonpos fun i _ => ?_))
  by_cases hi : 0 < hh.eigenvalues i
  · rw [hv i hi, map_zero, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (Complex.normSq_nonneg _)

end GlobalTheory.SimSign

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

theorem sum_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (w : {i // 0 < hh.eigenvalues i} → ℂ)
    (hw : w ≠ 0) : 0 < ∑ i, hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i ≤ hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    intro i _
    by_cases hi : 0 < hh.eigenvalues i
    · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
    · rw [extZero_apply_not _ w hi]; simp
  have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i < hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    refine ⟨j.1, Finset.mem_univ _, ?_⟩
    rw [extZero_apply_mem]
    exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
  simpa using Finset.sum_lt_sum hle hlt

end GlobalTheory.SimSign

namespace GlobalTheory.HTBetti

end GlobalTheory.HTBetti

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeRowsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

theorem repr_map {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis A b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem coord_eq_zero {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (h : Algebra.TensorProduct.map φ (AlgHom.id F E) z = 0) (i : ι) :
    φ ((Algebra.TensorProduct.basis A b).repr z i) = 0 := by
  rw [← repr_map, h, map_zero, Finsupp.zero_apply]

theorem coord_eq_zero₂ {F E A B C ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [CommRing C] [Algebra F A]
    [Algebra F B] [Algebra F C] (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (ψ : B →ₐ[F] C) (z : A ⊗[F] E)
    (h : Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = 0) (i : ι) :
    ψ (φ ((Algebra.TensorProduct.basis A b).repr z i)) = 0 := by
  rw [← repr_map, coord_eq_zero b ψ _ h]

theorem mul_eq_of_coord {F E A ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    (b : Module.Basis ι F E) (ε : A) (z : A ⊗[F] E)
    (h : ∀ i, ε * (Algebra.TensorProduct.basis A b).repr z i = (Algebra.TensorProduct.basis A b).repr z i) :
    algebraMap A (A ⊗[F] E) ε * z = z := by
  rw [← Algebra.smul_def]
  refine (Algebra.TensorProduct.basis A b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h]

theorem pair_mul_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (a1 : evalV F v α = 1)
    (a : AF F) (e0 : fstA F a = 0) (e1 : ∀ v', v' ≠ v → evalV F v' (sndA F a) = 0) : pairA F 0 α * a = a := by
  refine Prod.ext ((zero_mul (fstA F a)).trans e0.symm) (FiniteAdeleRing.ext _ fun w => ?_)
  change evalV F w (α * sndA F a) = evalV F w (sndA F a)
  rw [map_mul]
  by_cases hw : w = v
  · subst hw
    rw [a1, one_mul]
  · rw [e1 w hw, mul_zero]

theorem map_eq_one_iff {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) {n : ℕ} (m : Matrix (Fin n) (Fin n) R) :
    m.map π = 1 ↔ ∀ i j, π ((m - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Generic

variable {D : D7}

section Inert

variable {v : HeightOneSpectrum (𝓞 D.host.F)} {P : Pl D.host.E}

theorem under_eq (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) : P.under (𝓞 D.host.F) = v :=
  HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 (le_of_eq h))).symm

theorem eq_of_under (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v) : Q = P := by
  refine (GlobalTheory.IdemSupport.eq_of_le ?_).symm
  rw [← (h : _ = P.asIdeal), Ideal.map_le_iff_le_comap, ← hQ]
  exact le_rfl

theorem isPrimeIdem_of_inert (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    IsPrimeIdem P (algebraMap _ (Formalism.L2.Theta.AE D) ε) (algebraMap _ _ ε) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.IdemSupport.place_comp hΦ hε
  exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, (GlobalTheory.IdemSupport.tie_iff hΦ (GlobalTheory.IdemSupport.place_idem hΦ hε) h0 P).2
    ⟨h0, h1 P (under_eq h), fun Q hQ => h2 Q fun e => hQ (eq_of_under h e)⟩⟩

end Inert

section Local

variable (V : HSp D)

theorem locAt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) :
    IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := Iff.rfl

def cmp (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom

def locGrp (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Bridge.Gf V) :=
  ⨅ (v') (_ : v' ≠ v), ((Formalism.UG.bc (cmp D v')).comp (finHom V).range.subtype).ker

theorem mem_locGrp {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Bridge.Gf V} : x ∈ locGrp V v ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := by
  simp only [locGrp, Subgroup.mem_iInf]
  exact forall₂_congr fun v' _ => ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

abbrev fin : GA D V →* Bridge.Gf V := (finHom V).rangeRestrict

theorem idem_mul_eq {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (z : Formalism.L2.Theta.AE D)
    (h0 : infPart D z = 0) (h1 : ∀ v', v' ≠ v → cmp D v' (finPart D z) = 0) : algebraMap _ (Formalism.L2.Theta.AE D) ε * z = z := by
  obtain ⟨α, rfl, a1, -⟩ := hε
  exact mul_eq_of_coord (Module.finBasis D.host.F D.host.E) _ z fun i => pair_mul_eq a1 _
    (coord_eq_zero _ (fstA D.host.F) z h0 i) fun v' hv => coord_eq_zero₂ _ (sndA D.host.F) (evalV D.host.F v') z (h1 v' hv) i

theorem suppF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {g : GA D V}
    (hg : g ∈ GfC V) : SuppF V (algebraMap _ _ ε) g ↔ fin V g ∈ locGrp V v := by
  have key : ∀ v', (Units.val (finHom V g)).map (cmp D v') = (Formalism.L2.Theta.mt V g).map ((cmp D v').comp (finPart D)) :=
    fun _ => rfl
  rw [mem_locGrp]
  constructor
  · intro h v' hv
    refine (key v').trans ((map_eq_one_iff _ _).2 fun i j => ?_)
    obtain ⟨α, rfl, -, a0⟩ := hε
    have h2 : (cmp D v').comp (finPart D) (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α)) = 0 := by
      change evalV D.host.F v' α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [a0 v' hv, TensorProduct.zero_tmul]
    rw [← h i j, RingHom.map_mul, h2, zero_mul]
  · intro h i j
    have h0 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
    exact idem_mul_eq hε _ ((map_eq_one_iff _ _).1 h0 i j)
      fun v' hv => (map_eq_one_iff _ _).1 ((key v').symm.trans (h v' hv)) i j

theorem fin_lift (x : Bridge.Gf V) : ∃ g ∈ GfC V, fin V g = x := by
  obtain ⟨x, g, rfl⟩ := x
  let f : Formalism.L2.Theta.AE D := algebraMap _ _ (pairA D.host.F 0 1)
  have hp : pairA D.host.F 0 1 * pairA D.host.F 0 1 = pairA D.host.F 0 1 :=
    Prod.ext (mul_zero (0 : Ainf D.host.F)) (mul_one (1 : Af D.host.F))
  have hff : f * f = f := by rw [← RingHom.map_mul, hp]
  obtain ⟨g₁, g₂, h₁, h₂, rfl⟩ := GlobalTheory.IdemSupport.exists_split V hff (GlobalTheory.IdemSupport.cA_algebraMap _) g
  have b : finHom V g₂ = 1 := by
    refine Units.ext ((map_eq_one_iff (finPart D) _).2 fun i j => ?_)
    have h3 : finPart D (1 - f) = 0 := by
      rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero]
      rfl
    refine (congrArg (finPart D) (h₂ i j)).symm.trans ?_
    rw [RingHom.map_mul, h3, zero_mul]
  refine ⟨g₁, GlobalTheory.IdemSupport.mem_GfC_of_suppF V (TensorProduct.zero_tmul _ _) h₁, Subtype.ext ?_⟩
  show finHom V g₁ = finHom V (g₁ * g₂)
  rw [map_mul, b, mul_one]


end Local

section Compare

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

end Compare

end GlobalTheory.HeckeRowsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KapGEqCharInf
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_qbar {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (q : TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (algebraMap TaylorLogMetric.Qbar ℂ q) = lam q := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left (show algebraMap TaylorLogMetric.Qbar ℂ q ∈ TaylorLogMetric.Qbar from q.2)]
  rfl

theorem kapG_eq_char_inf : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (a : D.host.E), a * D.host.conj a = 1 → (∀ v, (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det = ρ v a) → letI := wittFractionAlgebraCp p; letI := algKfC E; kapG X ℂ_[p] j c γ = E.iK (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) * TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) * (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
  intro D p _ X E pos lam ρ hLP j c γ a ha hdet
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact zero_ne_one ha
  have hconj : D.host.conj a = a⁻¹ := eq_inv_of_mul_eq_one_right ha

  have hcA : cA X ℂ_[p] j (gamAt X j c γ) =
      TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) := by
    let q : ∀ v : X.Pl, Fin (X.G.P.n' v) → TaylorLogMetric.Qbar := fun v s => ⟨TaylorLogMetric.embT D (pos ⟨v, s⟩) a, embT_mem_qbar D _ a⟩
    have h1 : (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) =
        algebraMap TaylorLogMetric.Qbar ℂ (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), q v s ^ X.w v (j + 1) s) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_zpow₀]
      rfl
    rw [h1, lamC_qbar, map_prod]
    unfold cA
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_zpow₀, hdet v]
    have h2 : lam (q v s) = twG X E v s (ρ v (if IsOddPos s then D.host.conj a else a)) := by
      rw [← hLP v s a, ← lamC_qbar lam (q v s)]
      rfl
    rw [h2, twG_eq_tw]
    by_cases hs : IsOddPos s
    · rw [if_pos hs, if_pos hs, hconj, map_inv₀, map_inv₀, inv_zpow', neg_one_mul]
    · rw [if_neg hs, if_neg hs, one_mul]
  have hP : (∏ v : X.Pl, (p : ℂ_[p]) ^ (-(X.vm v (j + 1) * ordP (X.G.P.W v) p
      (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))) =
      (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
    simp_rw [hdet]
    rw [← Finset.sum_neg_distrib]
    induction (Finset.univ : Finset X.Pl) using Finset.cons_induction with
    | empty => simp
    | cons b s hb ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hp, ih]
  unfold kapG
  rw [hcA, hP]
  rfl

end GlobalTheory.TwV.Xc

end
end

