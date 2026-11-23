module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.DetEqZeroOfMulVecEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

noncomputable section

def analyticAtSubring {σ : Type} [Fintype σ] (p : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g p}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

theorem mem_analyticAtSubring {σ : Type} [Fintype σ] {p : σ → ℂ} {g : (σ → ℂ) → ℂ} :
    g ∈ analyticAtSubring p ↔ AnalyticAt ℂ g p :=
  Iff.rfl

def analyticAtComp {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    analyticAtSubring (L x) →+* analyticAtSubring x where
  toFun g := ⟨fun z => (g : (τ → ℂ) → ℂ) (L z), AnalyticAt.comp g.2 (L.analyticAt x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def analyticAtEval {σ : Type} [Fintype σ] (p y : σ → ℂ) : analyticAtSubring p →+* ℂ :=
  (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) y).comp (analyticAtSubring p).subtype

@[simp] theorem analyticAtEval_apply {σ : Type} [Fintype σ] (p y : σ → ℂ) (g : analyticAtSubring p) :
    analyticAtEval p y g = (g : (σ → ℂ) → ℂ) y :=
  rfl

def analyticAtGerm {σ : Type} [Fintype σ] (p : σ → ℂ) : analyticAtSubring p →+* holGerms p :=
  ((Germ.coeRingHom (𝓝 p)).comp (analyticAtSubring p).subtype).codRestrict (holGerms p)
    fun g => ⟨g, g.2, rfl⟩

theorem analyticAtGerm_eq_iff {σ : Type} [Fintype σ] {p : σ → ℂ} (a b : analyticAtSubring p) :
    analyticAtGerm p a = analyticAtGerm p b ↔ (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 p] b := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem analyticAtGerm_surjective {σ : Type} [Fintype σ] (p : σ → ℂ) :
    Function.Surjective (analyticAtGerm p) := by
  rintro ⟨φ, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem det_eq_zero_of_mulVec_eq_zero {Q : Type*} [CommRing Q] {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (e β : Fin n → Q) (hA : A *ᵥ e = 0) (h1 : ∑ m, β m * e m = 1) : A.det = 0 := by
  have he : (A.adjugate * A) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at he
  calc A.det = A.det * ∑ m, β m * e m := by rw [h1, mul_one]
    _ = ∑ m, β m * (A.det * e m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by
      have := congrFun he m
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this, mul_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreNormalOfRegularDepth.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → SerreR A 1 → SerreS A 2 → NormalRing A

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCauchyBinetMinors
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset

namespace CauchyBinetMinorsAlt

end CauchyBinetMinorsAlt


end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscrAdjoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial

theorem DiscrAdjoin.proof : DiscrAdjoin.Statement := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ ℓ hℓ hadj
  have hK : IsIntegral K ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hFK : minpoly K ℓ = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hℓ
  have hFm : (minpoly R ℓ).Monic := minpoly.monic hℓ
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdegK : (minpoly K ℓ).natDegree = (minpoly R ℓ).natDegree := by
    rw [hFK, natDegree_map_eq_of_injective hinj]
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    have h1 := IntermediateField.adjoin.finrank hK
    rw [hadj, IntermediateField.finrank_top', hdegK] at h1
    exact h1.symm
  have hpos : 0 < (minpoly R ℓ).natDegree := minpoly.natDegree_pos hℓ
  have hF'deg : (derivative (minpoly R ℓ)).natDegree ≤ (minpoly R ℓ).natDegree - 1 :=
    natDegree_derivative_le _
  have hres := resultant_deriv (f := minpoly R ℓ) (natDegree_pos_iff_degree_pos.mp hpos)
  rw [hFm.leadingCoeff, mul_one] at hres
  have hdisc : (minpoly R ℓ).discr = (-1) ^ ((minpoly R ℓ).natDegree *
      ((minpoly R ℓ).natDegree - 1) / 2) * resultant (minpoly R ℓ) (derivative (minpoly R ℓ))
        (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1) := by
    rw [hres, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  refine ⟨hdeg, ?_, ?_⟩
  · intro h0
    have hR : resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree
        ((minpoly R ℓ).natDegree - 1) = 0 := by rw [hres, h0, mul_zero]
    have hRK := congrArg (algebraMap R K) hR
    rw [← resultant_map_map, map_zero, ← derivative_map, ← hFK, ← hdegK] at hRK
    have hsep : (minpoly K ℓ).Separable := Algebra.IsSeparable.isSeparable K ℓ
    have hle : (derivative (minpoly K ℓ)).natDegree ≤ (minpoly K ℓ).natDegree - 1 :=
      natDegree_derivative_le _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree, (minpoly.monic hK).leadingCoeff,
      one_pow, one_mul] at hRK
    exact resultant_ne_zero _ _ hsep hRK
  · intro z hz
    obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant (minpoly R ℓ)
      (derivative (minpoly R ℓ)) le_rfl hF'deg (Or.inl hpos.ne')
    have hev := congrArg (aeval ℓ) hpq
    simp only [map_add (f := _), map_mul, minpoly.aeval, zero_mul, zero_add, aeval_C] at hev
    have hadjK : Algebra.adjoin K {ℓ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hK.isAlgebraic, hadj,
        IntermediateField.top_toSubalgebra]
    have hzmem : z ∈ (Algebra.traceForm K L).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin R {ℓ})) := by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      rw [Submodule.mem_one]
      have hyint : IsIntegral R y := adjoin_le_integralClosure hℓ hy
      have htr : IsIntegral R (Algebra.trace K L (z * y)) := Algebra.isIntegral_trace (hz.mul hyint)
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
      exact ⟨r, by simpa [Algebra.traceForm_apply] using hr⟩
    rw [traceForm_dualSubmodule_adjoin R K hadjK hℓ] at hzmem
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzmem
    have hd : aeval ℓ (derivative (minpoly K ℓ)) = aeval ℓ (derivative (minpoly R ℓ)) := by
      rw [hFK, derivative_map, aeval_map_algebraMap]
    rw [hd]
    have hq : aeval ℓ q ∈ Algebra.adjoin R {ℓ} := aeval_mem_adjoin_singleton R ℓ
    have hw' : w ∈ Algebra.adjoin R {ℓ} := hw
    have key : (minpoly R ℓ).discr • ((aeval ℓ (derivative (minpoly R ℓ)))⁻¹ • w) =
        ((-1 : L) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * aeval ℓ q * w) *
          (aeval ℓ (derivative (minpoly R ℓ)) * (aeval ℓ (derivative (minpoly R ℓ)))⁻¹) := by
      rw [hdisc, Algebra.smul_def, smul_eq_mul, map_mul, ← hev, map_pow, map_neg, map_one]
      ring
    rw [key]
    by_cases hd0 : aeval ℓ (derivative (minpoly R ℓ)) = 0
    · rw [hd0, zero_mul, mul_zero]
      exact zero_mem _
    · rw [mul_inv_cancel₀ hd0, mul_one]
      exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hq) hw'

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem DiscriminantCover.proof (hP : PrimitiveElementFibres.Statement) :
    DiscriminantCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨c, m, Δ, Q, hmon, hdeg, hΔ, hgood⟩ := hP n d J A hJ hdim hA
  set ℓ : (Fin n → ℂ) → ℂ := fun x => ∑ j, c j * x j with hℓ

  have hdet : ∀ w, eval w Δ ≠ 0 → ∀ x ∈ fibre J A w,
      x = fun j => ((Q j).map (eval w)).eval (ℓ x) / eval w Δ := by
    intro w hw x hx
    funext j
    rw [eq_div_iff hw, mul_comm]
    exact ((hgood w hw).2.1 x hx).2 j
  refine ⟨Δ, hΔ, fun y hy => ?_⟩
  obtain ⟨hsep, hfib, hsurj⟩ := hgood y hy
  have hm0 : m.map (eval y) ≠ 0 := (hmon.map _).ne_zero
  have hinj : Set.InjOn ℓ (fibre J A y) := fun x hx x' hx' h => by
    rw [hdet y hy x hx, hdet y hy x' hx', h]
  have himg : ℓ '' fibre J A y = ↑(m.map (eval y)).roots.toFinset := by
    ext τ
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hm0]
    exact ⟨fun ⟨x, hx, hτ⟩ => hτ ▸ (hfib x hx).1, fun h => hsurj τ h⟩
  have hfin : (fibre J A y).Finite :=
    Set.Finite.of_finite_image (by rw [himg]; exact Finset.finite_toSet _) hinj
  refine ⟨hfin, ?_, fun x hx => ?_⟩
  · rw [← hinj.ncard_image, himg, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hmon.natDegree_map, hdeg]

  have hroot : (m.map (eval y)).IsRoot (ℓ x) := (hfib x hx).1
  have hder : (m.map (eval y)).derivative.eval (ℓ x) ≠ 0 := by
    have := hsep.aeval_derivative_ne_zero (x := ℓ x) (by simpa [Polynomial.aeval_def] using hroot)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨U₀, B, ψ, hU₀o, hyU₀, hBo, hτB, hψd, hψy, hψ⟩ := SimpleRootBranch.proof d m y (ℓ x) hroot hder
  set U : Set (Fin d → ℂ) := U₀ ∩ {w | eval w Δ ≠ 0} with hU
  have hUo : IsOpen U := hU₀o.inter (isOpen_ne_fun (MvPolynomial.continuous_eval Δ) continuous_const)
  set g : (Fin d → ℂ) → (Fin n → ℂ) :=
    fun w j => ((Q j).map (eval w)).eval (ψ w) / eval w Δ with hg

  have hkey : ∀ w ∈ U, g w ∈ fibre J A w ∧ ℓ (g w) = ψ w := by
    intro w hw
    have hr : (m.map (eval w)).IsRoot (ψ w) := ((hψ w hw.1).2 (ψ w) (hψ w hw.1).1).mpr rfl
    obtain ⟨x', hx', hℓx'⟩ := (hgood w hw.2).2.2 (ψ w) hr
    have hℓx'' : ℓ x' = ψ w := hℓx'
    have he : x' = g w := by rw [hdet w hw.2 x' hx']; simp only [hg]; rw [hℓx'']
    exact ⟨he ▸ hx', he ▸ hℓx'⟩
  have hℓc : Continuous ℓ := by simp only [hℓ]; fun_prop
  have hAc : Continuous fun z : Fin n → ℂ => A.mulVec z := continuous_const.matrix_mulVec continuous_id
  refine ⟨U, {z | A.mulVec z ∈ U ∧ ℓ z ∈ B}, g, hUo, ⟨hyU₀, hy⟩,
    (hUo.preimage hAc).inter (hBo.preimage hℓc), ⟨by rw [hx.2]; exact ⟨hyU₀, hy⟩, hτB⟩,
    fun w hw => ?_, ?_, fun w hw => (hkey w hw).1.2, ?_⟩
  ·
    have hψw : DifferentiableAt ℂ ψ w := (hψd w hw.1).differentiableAt (hU₀o.mem_nhds hw.1)
    refine DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun j => ?_)
    have hΔd : DifferentiableAt ℂ (fun w => eval w Δ) w :=
      (AnalyticOnNhd.eval_mvPolynomial Δ w trivial).differentiableAt
    have hF : DifferentiableAt ℂ (fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2) (w, ψ w) :=
      (analyticAt_eval_map (Q j) (w, ψ w)).differentiableAt
    have hQd : DifferentiableAt ℂ (fun w => ((Q j).map (eval w)).eval (ψ w)) w :=
      DifferentiableAt.comp (g := fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2)
        (f := fun v => (v, ψ v)) w hF (differentiableAt_fun_id.prodMk hψw)
    have hfun : (fun w => g w j) = fun w => ((Q j).map (eval w)).eval (ψ w) * (eval w Δ)⁻¹ := by
      funext v; simp only [hg, div_eq_mul_inv]
    rw [hfun]
    exact hQd.mul (hΔd.inv hw.2)
  · funext j
    rw [congrFun (hdet y hy x hx) j]
    simp only [hg, hψy]
  · ext z
    constructor
    · rintro ⟨hz, hzU, hzB⟩
      have hzf : z ∈ fibre J A (A.mulVec z) := ⟨hz, rfl⟩
      have hr := ((hgood _ hzU.2).2.1 z hzf).1
      have hℓz : ℓ z = ψ (A.mulVec z) := ((hψ _ hzU.1).2 (ℓ z) hzB).mp hr
      refine ⟨A.mulVec z, hzU, ?_⟩
      funext j
      rw [congrFun (hdet _ hzU.2 z hzf) j]
      simp only [hg]
      rw [hℓz]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hf, hℓg⟩ := hkey w hw
      exact ⟨hf.1, by rw [hf.2]; exact hw, by rw [hℓg]; exact (hψ w hw.1).1⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem DominantFibreBound.trdeg_le {n d : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection P A) :
    Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) ≤ Cardinal.mk (Fin d) := by
  set a : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (linPoly A i) with ha_def
  have hproj : projHom P A = aeval a := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hind : AlgebraicIndependent ℂ a := by
    rw [algebraicIndependent_iff_injective_aeval, ← hproj]
    exact hA.injective
  have hint : Algebra.IsIntegral (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) := by
    constructor
    intro b
    obtain ⟨f, hfm, hfb⟩ := hA.finite.to_isIntegral b
    refine ⟨f.map (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)),
      hfm.map _, ?_⟩
    have hcomp : (algebraMap (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P)).comp
        (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)) =
        (projHom P A).toRingHom := by
      apply RingHom.ext
      intro y
      rw [RingHom.comp_apply]
      change ((hind.aevalEquiv y : Algebra.adjoin ℂ (Set.range a)) : MvPolynomial (Fin n) ℂ ⧸ P) = projHom P A y
      rw [hproj]
      exact hind.algebraMap_aevalEquiv y
    rw [Polynomial.eval₂_map, hcomp]
    exact hfb
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    Algebra.IsIntegral.isAlgebraic
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := ℂ) (s := Set.range a)).trans Cardinal.mk_range_le

theorem DominantFibreBound.exists_poly (hG : ComplexSets.GenericProjectionFinite.Statement) {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (hP : P.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)))
    (b : MvPolynomial (Fin n) ℂ ⧸ P) :
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧
      (g.map (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom).eval b = 0 := by
  obtain ⟨A, hA⟩ := (hG n d P hP hdim).2.1
  set q : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (p i) with hq_def
  have hind : AlgebraicIndependent ℂ q := by
    rw [algebraicIndependent_iff_injective_aeval]
    rw [comp_aeval] at hinj
    exact hinj
  have hbasis : IsTranscendenceBasis ℂ q :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (DominantFibreBound.trdeg_le P A hA)
  obtain ⟨f, hf0, hfb⟩ := hbasis.isAlgebraic.isAlgebraic b
  refine ⟨f.map (hind.aevalEquiv.symm : Algebra.adjoin ℂ (Set.range q) →+* MvPolynomial (Fin d) ℂ),
    (Polynomial.map_ne_zero_iff hind.aevalEquiv.symm.injective).2 hf0, ?_⟩
  rw [Polynomial.map_map, ← hfb, Polynomial.aeval_def, Polynomial.eval_map]
  congr 1
  ext y
  simp [← hind.algebraMap_aevalEquiv]

theorem DominantFibreBound.proof (hG : ComplexSets.GenericProjectionFinite.Statement) :
    DominantFibreBound.Statement := by
  intro n d P p hP hdim hinj
  choose g hg0 hgb using fun j : Fin n =>
    DominantFibreBound.exists_poly hG P p hP hdim hinj (Ideal.Quotient.mk P (X j))
  refine ⟨∏ j, (g j).natDegree, ∏ j, (g j).leadingCoeff, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun j _ => Polynomial.leadingCoeff_ne_zero.2 (hg0 j)
  intro w hw
  rw [map_prod] at hw
  have hlc : ∀ j, eval w (g j).leadingCoeff ≠ 0 := fun j =>
    (Finset.prod_ne_zero_iff.1 hw) j (Finset.mem_univ j)
  have hne : ∀ j, (g j).map (eval w) ≠ 0 := fun j h => by
    have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (eval w) (hlc j)
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact hlc j this.symm
  let R : Fin n → Finset ℂ := fun j => ((g j).map (eval w)).roots.toFinset
  have hsub : {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i} ⊆
      (Fintype.piFinset R : Set (Fin n → ℂ)) := by
    rintro x ⟨hx, hxw⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    let ψ : MvPolynomial (Fin n) ℂ ⧸ P →+* ℂ := Ideal.Quotient.lift P (eval x) hx
    have hψx : ∀ q, ψ (Ideal.Quotient.mk P q) = eval x q := fun q => Ideal.Quotient.lift_mk P _ _
    have hψ : ψ.comp (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom = eval w := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algHom_C]
        rw [← Ideal.Quotient.mk_algebraMap, hψx, MvPolynomial.algebraMap_eq, eval_C, eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rw [hψx, hxw i, eval_X]
    have h0 := congrArg ψ (hgb j)
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hψ, map_zero, ← Polynomial.eval_map] at h0
    have hxj : ψ (Ideal.Quotient.mk P (X j)) = x j := by
      rw [hψx, eval_X]
    rw [hxj] at h0
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hne j)).2 h0)
  calc _ ≤ (Fintype.piFinset R : Set (Fin n → ℂ)).encard := Set.encard_le_encard hsub
    _ = ((Fintype.piFinset R).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ _ := by
      rw [Fintype.card_piFinset]
      exact_mod_cast Finset.prod_le_prod' fun j _ => (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteFibreGermIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteFibreGermIntegral.proof (hWF : WeierstrassFiniteness.Statement)
    (hR : RueckertNullstellensatz.Statement) : FiniteFibreGermIntegral.Statement := by
  intro σ _ X x d A hX hiso g hg
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hfx : ∀ i, AnalyticAt ℂ (f i) x := fun i => hf i x hxN
  have hAj : ∀ j : Fin d, AnalyticAt ℂ (fun z => A z j - A x j) x := fun j =>
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt x).sub
      analyticAt_const

  let F : Fin (k + d) → (σ → ℂ) → ℂ := Fin.append f (fun j z => A z j - A x j)
  have hFx : ∀ i, AnalyticAt ℂ (F i) x := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left] using hfx i
    · simpa only [F, Fin.append_right] using hAj j
  have hcoord : ∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j) := by
    intro l
    have hl : AnalyticAt ℂ (fun z : σ → ℂ => z l - x l) x :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) l).analyticAt x).sub analyticAt_const
    have hvan : ∀ᶠ z in 𝓝 x, (∀ i, F i z = 0) → z l - x l = 0 := by
      filter_upwards [hNo.mem_nhds hxN, hW] with z hzN hzW h0
      have hf0 : ∀ i, f i z = 0 := fun i => by simpa only [F, Fin.append_left] using h0 (Fin.castAdd d i)
      have hA0 : A z = A x := funext fun j =>
        sub_eq_zero.1 (by simpa only [F, Fin.append_right] using h0 (Fin.natAdd k j))
      have hzX : z ∈ X := by
        have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hzN, hf0⟩
        exact this.1
      rw [hWiso z ⟨hzX, hzW⟩ hA0, sub_self]
    obtain ⟨m, h, -, hh, hsum⟩ := hR σ x (k + d) F (fun z => z l - x l) hFx hl hvan
    refine ⟨m, fun i => h (Fin.castAdd d i), fun j => h (Fin.natAdd k j), fun i => hh _, fun j => hh _, ?_⟩
    filter_upwards [hsum] with z hz
    rw [hz, Fin.sum_univ_add]
    simp only [F, Fin.append_left, Fin.append_right]
  obtain ⟨n, a, h, ha, -, hrel⟩ := hWF σ x k f d A hfx hcoord g hg
  refine ⟨n, a, ha, ?_⟩
  filter_upwards [hrel, hNo.mem_nhds hxN] with z hz hzN hzX
  have hz0 : z ∈ X ∩ N := ⟨hzX, hzN⟩
  rw [hXN] at hz0
  rw [hz]
  simp [hz0.2]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAdicCompletionRegular
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AdicCompletionRegular.Statement : Prop :=
  ∀ (R : Type) [CommRing R], IsNoetherianRing R → ∀ (M : Ideal R) [M.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime M) → IsRegularLocalRing (AdicCompletion M R)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

