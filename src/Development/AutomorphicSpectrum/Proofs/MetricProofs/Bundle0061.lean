module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEq
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Abstract

variable {R R' : Type*} [CommRing R] [CommRing R']

theorem length_cut_of_flat (φ : R →+* R') (q : R') (J W : Ideal R) [W.IsPrime]
    (W' : Ideal R') [W'.IsPrime] (hW' : W' = W.map φ ⊔ Ideal.span {q}) (hc : W'.comap φ = W)
    (hflat : ((Ideal.Quotient.mk (Ideal.span {q})).comp φ).Flat) :
    Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (R' ⧸ (J.map φ ⊔ Ideal.span {q}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) := by
  let I : Ideal R' := Ideal.span {q}
  let π : R' →+* R' ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let ψ : R →+* R' ⧸ I := π.comp φ
  have hker : RingHom.ker π = I := Ideal.mk_ker
  have hIW : I ≤ W' := hW' ▸ le_sup_right
  let P : Ideal (R' ⧸ I) := W'.map π
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective hπ (by rw [hker]; exact hIW)
  have hPc : W' = P.comap π := by
    show W' = (W'.map π).comap π
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hIW]
  have hPψ : W = P.comap ψ := by
    have h : P.comap ψ = (P.comap π).comap φ := (Ideal.comap_comap φ π).symm
    rw [h, ← hPc, hc]
  have hPmap : W.map ψ = P := by
    show W.map (π.comp φ) = W'.map π
    rw [hW', Ideal.map_sup, ← Ideal.map_map]
    have : (Ideal.span {q} : Ideal R').map π = ⊥ := Ideal.map_quotient_self I
    rw [this, sup_bot_eq]
  let L := Localization.localRingHom W P ψ hPψ
  have hLflat : L.Flat := RingHom.Flat.localRingHom hflat P W hPψ
  have hcomp : L.comp (algebraMap R (Localization.AtPrime W)) =
      (algebraMap (R' ⧸ I) (Localization.AtPrime P)).comp ψ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hPψ z
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map L =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map, hPmap, IsLocalization.AtPrime.map_eq_maximalIdeal P]
  have hJ : (J.map (algebraMap R (Localization.AtPrime W))).map L =
      (J.map ψ).map (algebraMap (R' ⧸ I) (Localization.AtPrime P)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  have hkerE : RingHom.ker ((Ideal.Quotient.mk (J.map ψ)).comp π) = J.map φ ⊔ I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    show ((J.map (π.comp φ))).comap π = _
    rw [← Ideal.map_map, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker]
  let e : (R' ⧸ (J.map φ ⊔ I)) ≃+* ((R' ⧸ I) ⧸ J.map ψ) :=
    (Ideal.quotEquivOfEq hkerE.symm).trans (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (J.map ψ)).comp π) (Ideal.Quotient.mk_surjective.comp hπ))
  have he : ∀ (s : R') (x : R' ⧸ (J.map φ ⊔ I)), e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (J.map ψ) (π (s * y)) =
      Ideal.Quotient.mk (J.map ψ) (π s) * Ideal.Quotient.mk (J.map ψ) (π y)
    rw [map_mul, map_mul]
  rw [GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective π hπ P W' hPc _ _
      e.toAddEquiv he,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ← hJ]
  exact GroundTheory.Heights₂.Heights.Inter.BCMultProof.length_quot_map_of_flat L hLflat hmax _

end Abstract

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def toPoly : MRing (Tb ι) →+* Polynomial (Polynomial (MRing ι)) :=
  (aeval (fun q : Σ o, Tb ι o => match q with
    | ⟨none, j⟩ => (![Polynomial.X, Polynomial.C Polynomial.X] : Fin 2 → _) j
    | ⟨some k, i⟩ => Polynomial.C (Polynomial.C (X ⟨k, i⟩))) :
      MRing (Tb ι) →ₐ[ℤ] Polynomial (Polynomial (MRing ι))).toRingHom

def ofPoly : Polynomial (Polynomial (MRing ι)) →+* MRing (Tb ι) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom inc yN) xN

theorem toPoly_xN : toPoly (xN : MRing (Tb ι)) = Polynomial.X := by
  simp only [toPoly, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_yN : toPoly (yN : MRing (Tb ι)) = Polynomial.C Polynomial.X := by
  simp only [toPoly, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_comp_inc : (toPoly.comp inc : MRing ι →+* _) = Polynomial.C.comp Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [toPoly, inc]
  · intro i; simp [toPoly, inc, oldIdx]

theorem toPoly_inc (f : MRing ι) : toPoly (inc f) = Polynomial.C (Polynomial.C f) :=
  congrArg (fun g => g f) (toPoly_comp_inc (ι := ι))

theorem ofPoly_comp_toPoly : (ofPoly.comp toPoly : MRing (Tb ι) →+* _) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [toPoly, ofPoly]
  · rintro ⟨o, i⟩
    cases o with
    | none =>
      change Fin 2 at i
      fin_cases i
      · have : (X ⟨none, (0 : Fin 2)⟩ : MRing (Tb ι)) = xN := rfl
        simp [this, toPoly_xN, ofPoly]
      · have : (X ⟨none, (1 : Fin 2)⟩ : MRing (Tb ι)) = yN := rfl
        simp [this, toPoly_yN, ofPoly]
    | some k =>
      simp [toPoly, ofPoly, inc, oldIdx]

theorem toPoly_comp_ofPoly :
    (toPoly.comp ofPoly : Polynomial (Polynomial (MRing ι)) →+* _) = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun f => ?_
      simp [ofPoly, toPoly_inc]
    · simp [ofPoly, toPoly_yN]
  · simp [ofPoly, toPoly_xN]

def polyEquiv : MRing (Tb ι) ≃+* Polynomial (Polynomial (MRing ι)) :=
  RingEquiv.ofRingHom toPoly ofPoly toPoly_comp_ofPoly ofPoly_comp_toPoly

theorem toPoly_quad (p : ℕ) : ∃ s : Polynomial (MRing ι),
    toPoly (quad p : MRing (Tb ι)) = Polynomial.X ^ 2 + Polynomial.C s := by
  refine ⟨Polynomial.C (C (p : ℤ)) * Polynomial.X ^ 2, ?_⟩
  have h : toPoly (C (p : ℤ) : MRing (Tb ι)) =
      Polynomial.C (Polynomial.C (C (p : ℤ) : MRing ι)) := by
    simpa [inc] using toPoly_inc (ι := ι) (C (p : ℤ) : MRing ι)
  simp [quad, toPoly_xN, toPoly_yN, h]

theorem flat_quad (p : ℕ) :
    ((Ideal.Quotient.mk (Ideal.span {quad p})).comp inc :
      MRing ι →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat := by
  obtain ⟨s, hs⟩ := toPoly_quad (ι := ι) p
  let g : Polynomial (Polynomial (MRing ι)) := Polynomial.X ^ 2 + Polynomial.C s
  have hg : g.Monic := Polynomial.monic_X_pow_add
    (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))
  have : Module.Free (Polynomial (MRing ι)) (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  have h1 : (Polynomial.C : MRing ι →+* Polynomial (MRing ι)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (MRing ι) (Polynomial (MRing ι)))
  have h2 : (AdjoinRoot.of g).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat (Polynomial (MRing ι)) (AdjoinRoot g))
  let E : (MRing (Tb ι) ⧸ Ideal.span {quad p}) ≃+* AdjoinRoot g :=
    Ideal.quotientEquiv _ _ (polyEquiv (ι := ι)) (by
      rw [Ideal.map_span, Set.image_singleton]
      show Ideal.span {g} = Ideal.span {toPoly (quad p)}
      rw [hs])
  have h3 : (E.symm : AdjoinRoot g →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat :=
    RingHom.Flat.of_bijective E.symm.bijective
  have hcomp : (Ideal.Quotient.mk (Ideal.span {quad p})).comp inc =
      (E.symm : AdjoinRoot g →+* _).comp ((AdjoinRoot.of g).comp Polynomial.C) := by
    refine RingHom.ext fun f => ?_
    show Ideal.Quotient.mk _ (inc f) = E.symm (AdjoinRoot.of g (Polynomial.C f))
    rw [RingEquiv.eq_symm_apply]
    show Ideal.Quotient.mk _ (toPoly (inc f)) = _
    rw [toPoly_inc]
    rfl
  rw [hcomp]
  exact (h1.comp h2).comp h3

theorem multAt_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (J W : Ideal (MRing ι)) (hW : W ∈ J.minimalPrimes) (hT : (twist p W).IsPrime) :
    multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  have hWp : W.IsPrime := hW.1.1
  unfold multAt
  rw [dite_eq_left hT, dite_eq_left hWp]
  exact congrArg ENat.toNat (length_cut_of_flat inc (quad p) J W (twist p W) rfl
    (comap_inc_twist p W) (flat_quad p))

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory

section Hess

variable {D : ℕ}

theorem hess_comp_star (φ : (Fin D → ℂ) → ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => φ (star y))) z u v =
      fderiv ℝ (fderiv ℝ φ) (star z) (star u) (star v) := by
  let σ : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := starL' ℝ
  let T : ((Fin D → ℂ) →L[ℝ] ℝ) ≃L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    σ.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have h1 : fderiv ℝ (fun y => φ (star y)) = T ∘ ((fderiv ℝ φ) ∘ σ) := by
    funext y
    have := σ.comp_right_fderiv (f := φ) (x := y)
    exact this
  rw [h1, T.comp_fderiv, σ.comp_right_fderiv]
  rfl

theorem cxHessian_comp_star (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (star y)) z = (cxHessian φ (star z)).map (starRingEnd ℂ) := by
  ext i j
  have hs : ∀ i : Fin D, star (Pi.single i 1 : Fin D → ℂ) = Pi.single i 1 := fun i => by
    ext l; by_cases h : l = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hI : ∀ i : Fin D, star (Complex.I • (Pi.single i 1 : Fin D → ℂ)) =
      -(Complex.I • (Pi.single i 1 : Fin D → ℂ)) := fun i => by
    rw [star_smul, hs]; simp
  simp only [cxHessian, Matrix.map_apply, hess_comp_star, hs, hI, map_neg,
    ContinuousLinearMap.neg_apply, neg_neg]
  simp only [map_div₀, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  have h4 : starRingEnd ℂ (4 : ℂ) = 4 := map_ofNat _ 4
  simp [h4]
  ring

theorem mixedDisc_map_conj (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mixedDisc, map_mul, map_sum, map_pow, map_neg, map_one, map_div₀, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.sum_apply]

theorem maDensity_comp_star (φ : Fin D → (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    maDensity (fun j y' => φ j (star y')) y = maDensity φ (star y) := by
  simp only [maDensity, cxHessian_comp_star, mixedDisc_map_conj, Complex.conj_re]

theorem star_measurePreserving :
    MeasurePreserving (star : (Fin D → ℂ) → (Fin D → ℂ)) volume volume := by
  have h : MeasurePreserving (starRingEnd ℂ : ℂ → ℂ) volume volume :=
    Complex.conjLIE.measurePreserving
  exact volume_preserving_pi (fun _ => h)

end Hess

section Pts

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_star (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval (star z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact Subsingleton.elim _ _

theorem star_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    star z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · rw [eval_star, hz.2 f hf, map_zero]

theorem segre_star (z : (Σ k, ι k) → ℂ) : segre (star z) = star (segre z) := by
  funext i
  simp [segre, map_prod]

theorem cons_star {e : ℕ} (y : Fin e → ℂ) :
    (Fin.cons 1 (star y) : Fin (e + 1) → ℂ) = star (Fin.cons 1 y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

variable {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem star_mem_fibre (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : star w ∈ fibre P Ψ' (star y) := by
  obtain ⟨z, hz, rfl, h⟩ := hw
  exact ⟨star z, star_mem_mcPts hz, segre_star z, by rw [hΨ, h, cons_star]⟩

theorem differentiableAt_star_star {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StarAddMonoid E] [StarModule ℂ E] [StarModule ℝ E]
    [ContinuousStar E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [StarAddMonoid F] [StarModule ℂ F] [StarModule ℝ F] [ContinuousStar F]
    {γ : E → F} {x : E} (h : DifferentiableAt ℂ γ (star x)) :
    DifferentiableAt ℂ (fun y => star (γ (star y))) x := by
  have hD := h.hasFDerivAt
  set D := fderiv ℂ γ (star x)
  let sE : E →L[ℝ] E := (starL' ℝ : E ≃L[ℝ] E)
  let sF : F →L[ℝ] F := (starL' ℝ : F ≃L[ℝ] F)
  have hs : HasFDerivAt (star : E → E) sE x := sE.hasFDerivAt
  have hr : HasFDerivAt γ (D.restrictScalars ℝ) (star x) := hD.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => star (γ (star y)))
      (sF.comp ((D.restrictScalars ℝ).comp sE)) x :=
    HasFDerivAt.comp x (g := (star : F → F)) sF.hasFDerivAt (hr.comp x hs)
  let cE : E →SL[starRingEnd ℂ] E := ((starL ℂ : E ≃L⋆[ℂ] E) : E →SL[starRingEnd ℂ] E)
  let cF : F →SL[starRingEnd ℂ] F := ((starL ℂ : F ≃L⋆[ℂ] F) : F →SL[starRingEnd ℂ] F)
  let D' : E →L[ℂ] F := cF.comp (D.comp cE)
  have : HasFDerivAt (fun y => star (γ (star y))) D' x :=
    hasFDerivAt_of_restrictScalars ℝ hc (by ext v; rfl)
  exact this.differentiableAt

theorem isSheet_star (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    IsSheet P Ψ' (star y) (star w) (fun y' => star (γ (star y'))) := by
  refine ⟨by simp only [star_star, segre_star, h.1], ?_⟩
  have ht : Tendsto (star : (Fin e → ℂ) → (Fin e → ℂ)) (𝓝 (star y)) (𝓝 y) := by
    have := (continuous_star (R := Fin e → ℂ)).tendsto (star y)
    simpa using this
  filter_upwards [ht.eventually h.2] with y' ⟨h1, h2, h3⟩
  refine ⟨differentiableAt_star_star h1, star_mem_mcPts h2, ?_⟩
  rw [segre_star, hΨ, h3, cons_star, star_star]

theorem sheetDensity_star {L : Fin e → HermLine ι} (hLc : ∀ j, IsConjInvariantH (L j))
    {B B' : HermLine ι} (hBB : ∀ z ∈ mcPts P, B'.h (star z) = B.h z)
    (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) (hΨ' : ∀ w, Ψ (star w) = star (Ψ' w)) {y : Fin e → ℂ}
    (hy : ∀ w γ γ', IsSheet P Ψ y w γ → IsSheet P Ψ y w γ' →
      logNorm B 1 (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
        logNorm B 1 (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (pot L) (logNorm B 1) y w =
      sheetDensity P Ψ' (pot L) (logNorm B' 1) (star y) (star w) := by
  have back : ∀ γ, IsSheet P Ψ' (star y) (star w) γ →
      IsSheet P Ψ y w (fun y' => star (γ (star y'))) := fun γ h => by
    have := isSheet_star hΨ' h
    simpa only [star_star] using this
  unfold sheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hex' : ∃ γ, IsSheet P Ψ' (star y) (star w) γ :=
      ⟨_, isSheet_star hΨ hex.choose_spec⟩
    rw [dite_eq_left hex, dite_eq_left hex', hy w _ _ hex.choose_spec (back _ hex'.choose_spec)]
    set γ := hex'.choose with hγ
    have hspec : IsSheet P Ψ' (star y) (star w) γ := hex'.choose_spec
    have hz : γ (star y) ∈ mcPts P := hspec.2.self_of_nhds.2.1
    have h1 : logNorm B 1 (star (γ (star (y)))) = logNorm B' 1 (γ (star y)) := by
      have h2 : B'.h (γ (star y)) = B.h (star (γ (star y))) := by
        have := hBB _ (star_mem_mcPts hz)
        rwa [star_star] at this
      simp [logNorm, h2]
    have h3 : maDensity (fun j y' => pot L j (star (γ (star y')))) y =
        maDensity (fun j y' => pot L j (γ y')) (star y) := by
      rw [← maDensity_comp_star]
      congr 1
      funext j y'
      simp only [pot]
      congr 1
      exact hLc j _
    rw [h1, h3]
  · have hex' : ¬ ∃ γ, IsSheet P Ψ' (star y) (star w) γ := fun ⟨γ, h⟩ => hex ⟨_, back γ h⟩
    rw [dite_eq_right hex, dite_eq_right hex']

end Pts

theorem ptsIntegralAt_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (B B' : HermLine ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ' (star w) = star (Ψ w)) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → B.a = 0 → IsSmoothHerm B → B'.a = 0 → IsSmoothHerm B' → (∀ z ∈ mcPts P, B'.h (star z) = B.h z) → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot L) (logNorm B' 1) = ptsIntegralAt P Ψ (pot L) (logNorm B 1) := by
  intro K _ ι _ P e Ψ Ψ' L B B' hP hΨ hΨs hLs hLc hBa hBs _ _ hBB
  have hΨ2 : ∀ w, Ψ (star w) = star (Ψ' w) := fun w => by
    have := hΨs (star w)
    rw [star_star] at this
    rw [this, star_star]
  refine ⟨fun z hz h0 => ?_, ?_⟩
  · refine hΨ _ (star_mem_mcPts hz) ?_
    rw [segre_star, hΨ2, h0, star_zero]
  · have hsec : IsSectionOn P B 1 := by
      refine ⟨0, fun k => by simp [hBa], fun m hm k => ?_, ?_⟩
      · have : m = 0 := by
          have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k)
          rw [this] at hm
          simpa using hm
        simp [this]
      · exact fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    have hme : MeasurableEmbedding (star : (Fin e → ℂ) → (Fin e → ℂ)) :=
      (starL' ℝ : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)).toHomeomorph.measurableEmbedding
    unfold ptsIntegralAt
    rw [← star_measurePreserving.integral_comp hme]
    refine integral_congr_ae ?_
    filter_upwards [sheetIndep K ι P e Ψ L B 1 hP hΨ hLs hBs hsec] with y hy
    symm
    refine finsum_mem_eq_of_bijOn star ⟨fun w hw => star_mem_fibre hΨs hw, ?_, ?_⟩ fun w _ =>
      sheetDensity_star hLc hBB hΨs hΨ2 hy w
    · exact star_injective.injOn
    · intro w hw
      refine ⟨star w, ?_, star_star w⟩
      have := star_mem_fibre hΨ2 hw
      rwa [star_star] at this

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_alphaOf : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hab hj hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p
  obtain ⟨hH, hbpc, hchart, hpt, -⟩ := hF
  intro w hw
  have hbw : bp w ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := (hpt w hw).1
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u)) w := by
    refine GlobalTheory.CompanionTheory.Ar.PB.CWeight.contDiffAt_blockPot j p.2 ?_ ?_ ?_ ?_
    · intro r s
      exact (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_comp_basePoint K ι Φ y Ψ N j M n d BM l p.1 Un bp hUn hbpc hchart
        (fun w' hw' => (hpt w' hw').1) r s).contDiffAt (hUn.mem_nhds hw)
    · intro r s
      exact (hH p.1 r s w hw).contDiffAt.restrict_scalars ℝ
    · exact (BM.G_pos l p.1 (bp w) hbw).2
    · exact ((hpt w hw).2 p.1).2
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) w := by
    by_cases hb : M.blk p = none
    · have hreg := ((BM.good l (bp w) hbw.1).2.2 p hb).2.1
      have han := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family _ _ _ M.x ((BM.F l).υ p) d n BM.Rb Un bp w hUn hw hbpc hchart hreg
      have hne : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsVal BM l p (bp w) ≠ 0 :=
        _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe.upsVal_ne_zero K ι Φ y Ψ N j M n d BM l p (bp w) hbw.1 hb
      obtain ⟨Hh, hHh, hev⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt d _ w han hne
      have hre0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Complex.reCLM (Hh z)) w :=
        Complex.reCLM.contDiff.contDiffAt.comp w (hHh.contDiffAt.restrict_scalars ℝ)
      have hre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (Hh z).re) w := by
        simpa using hre0
      refine hre.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      show GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp z) = (Hh z).re
      unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
      rw [if_pos hb]
      exact hz
    · have hz : (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) = fun _ => (0 : ℝ) := by
        funext u
        unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
        rw [if_neg hb]
      rw [hz]
      exact contDiffAt_const
  have he : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.alphaOf BM l H bp p = fun u =>
      GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u) -
        GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u) := rfl
  rw [he]
  exact (hA.sub hB).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

