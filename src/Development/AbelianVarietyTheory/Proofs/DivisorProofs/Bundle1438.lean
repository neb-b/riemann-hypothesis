module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOrthogonalityRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackMapOfFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleInvOfFamMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LineConst

open Polynomial

variable (k : Type) [Field k]

def scaleHom (R : Type) [CommRing R] [Algebra k R] (u : R) : Polynomial k →+* Polynomial R :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap k R)) (Polynomial.C u * Polynomial.X)

theorem scaleHom_algebraMap (R : Type) [CommRing R] [Algebra k R] (u : R) :
    (scaleHom k R u).comp (algebraMap k (Polynomial k)) = algebraMap k (Polynomial R) := by
  ext a
  simp [scaleHom, Polynomial.algebraMap_apply]

def lineOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Polynomial R)))

variable {k}

def scaled (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) :
    lineOver k R ⟶ B :=
  Over.homMk (spMap (scaleHom k R u) ≫ f) (by
    change spMap (scaleHom k R u) ≫ f ≫ B.hom = spMap (algebraMap k (Polynomial R))
    rw [hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_algebraMap])

def famMap (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) : Sp (Polynomial R) ⟶ B.left :=
  (scaled B f hf R u * (scaled B f hf R 1)⁻¹).left

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

theorem scaleHom_comp_map {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') (u : R) :
    (Polynomial.mapRingHom (φ : R →+* R')).comp (scaleHom k R u) = scaleHom k R' (φ u) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [scaleHom]
  · simp [scaleHom]

def lineMap {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') : lineOver k R' ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.mapRingHom (φ : R →+* R'))) (by
    change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (algebraMap k (Polynomial R)) =
      spMap (algebraMap k (Polynomial R'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => (Polynomial.mapAlgHom φ).commutes a)

theorem lineMap_scaled {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    lineMap φ ≫ scaled B f hf R u = scaled B f hf R' (φ u) := by
  ext1
  change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (scaleHom k R u) ≫ f =
    spMap (scaleHom k R' (φ u)) ≫ f
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_comp_map]

theorem famMap_base {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ famMap B f hf R u = famMap B f hf R' (φ u) := by
  have h := congrArg CommaMorphism.left
    (show lineMap φ ≫ (scaled B f hf R u * (scaled B f hf R 1)⁻¹) =
      scaled B f hf R' (φ u) * (scaled B f hf R' 1)⁻¹ by
      rw [MonObj.comp_mul, GrpObj.comp_inv, lineMap_scaled, lineMap_scaled, map_one])
  exact h

theorem famMap_one {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] :
    famMap B f hf R 1 = spMap (algebraMap k (Polynomial R)) ≫ (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left := by
  unfold famMap
  rw [mul_inv_cancel, Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

def linePt {k : Type} [Field k] (a : k) : 𝟙_ (Over (Sp k)) ⟶ lineOver k k :=
  Over.homMk (spMap (Polynomial.evalRingHom a)) (by
    change spMap (Polynomial.evalRingHom a) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom a).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id])

theorem linePt_scaled_left {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (a c : k) :
    (linePt a ≫ scaled B f hf k c).left = spMap (Polynomial.evalRingHom (c * a)) ≫ f := by
  change spMap (Polynomial.evalRingHom a) ≫ spMap (scaleHom k k c) ≫ f = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply Polynomial.ringHom_ext
  · intro z; simp [scaleHom]
  · simp [scaleHom]

theorem scale_inv_of_famMap {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (c : k)
    (h : famMap B f hf k c = spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c)
    (a : k) : spMap (Polynomial.evalRingHom (c * a)) ≫ f = spMap (Polynomial.evalRingHom a) ≫ f := by
  have hpt : ∀ b : k, spMap (Polynomial.evalRingHom b) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
    intro b
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom b).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hleft : spMap (Polynomial.evalRingHom a) ≫ famMap B f hf k c =
      spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c := by
    conv_lhs => rw [h]
    rw [← Category.assoc, hpt, Category.id_comp]
  have hq : ∀ b : k, linePt b ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      (linePt b ≫ scaled B f hf k c) * (linePt b ≫ scaled B f hf k 1)⁻¹ := by
    intro b; rw [MonObj.comp_mul, GrpObj.comp_inv]
  have h0 : linePt 0 ≫ scaled B f hf k c = linePt 0 ≫ scaled B f hf k 1 := by
    ext1
    rw [linePt_scaled_left, linePt_scaled_left, mul_zero, mul_zero]
  have hall : linePt a ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      linePt 0 ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) := by
    ext1
    exact hleft
  rw [hq, hq, h0, mul_inv_cancel] at hall
  have hall' : linePt a ≫ scaled B f hf k c = linePt a ≫ scaled B f hf k 1 :=
    mul_inv_eq_one.mp hall
  have h2 := congrArg CommaMorphism.left hall'
  have e1 := linePt_scaled_left B f hf a c
  have e2 := linePt_scaled_left B f hf a 1
  rw [_root_.one_mul] at e2
  rw [← e1, ← e2]
  exact h2

end GlobalTheory.LineConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerL2Constant
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.RealWeil
open scoped Matrix ENNReal SchwartzMap

namespace GlobalTheory.SvNForm

theorem sympl_neg_self {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) : sympl w (-w) = 0 := by
  have h1 : pPart (-w) = -pPart w := rfl
  have h2 : qPart (-w) = -qPart w := rfl
  simp only [sympl, h1, h2, inner_neg_right, real_inner_comm (pPart w) (qPart w)]
  ring

theorem rhoFun_neg_cancel {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℂ) :
    rhoFun w (rhoFun (-w) u) = u := by
  rw [rhoFun_rhoFun, sympl_neg_self, add_neg_cancel, rhoFun_zero]
  simp

theorem step (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ)
    (hB : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h)
    (f f' g g' : Sch (Fin n)) (G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n)) (hGc : Continuous G)
    (hG : ∀ w, ⇑(G w) = rhoFun w ⇑f)
    (hGb : ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N) :
    (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' =
      ∫ w, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * B (G w) f' := by
  obtain ⟨L, hL⟩ := hB f'
  set ip : ℂ := ∫ x, f x * starRingEnd ℂ (g x) with hip
  set c : (Fin n ⊕ Fin n → ℝ) → ℂ := fun w => starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) with hc
  have hcc : Continuous c := Complex.continuous_conj.comp (_root_.GlobalTheory.matrixCoeff_continuous_rapidDecay n g g').1
  have hint : ∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) := by
    intro k m
    obtain ⟨C, N, hC⟩ := hGb k m
    set d : ℕ := Module.finrank ℝ (Fin n ⊕ Fin n → ℝ)
    obtain ⟨C', hC'⟩ := (_root_.GlobalTheory.matrixCoeff_continuous_rapidDecay n g g').2 (N + (d + 1))
    have hsc : Continuous fun w => SchwartzMap.seminorm ℂ k m (G w) :=
      ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin n)) ℂ).continuous_seminorm (k, m)).comp hGc
    have hI : Integrable (fun w : Fin n ⊕ Fin n → ℝ => (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by push_cast; linarith)
    refine (hI.const_mul (C' * |C|)).mono' ((hcc.norm.mul hsc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖c w‖ = ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ := by simp [hc]
    have h1 := hC' w
    have h2 := hC w
    have hs0 : 0 ≤ SchwartzMap.seminorm ℂ k m (G w) := apply_nonneg _ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hs0, e1]
    have hrp : (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    rw [hrp]
    set M := ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖
    have hM : 0 ≤ M := norm_nonneg _
    have hA : (0:ℝ) < (1 + ‖w‖) ^ N := by positivity
    have hB' : (0:ℝ) < (1 + ‖w‖) ^ (d + 1) := by positivity
    have h3 : SchwartzMap.seminorm ℂ k m (G w) ≤ |C| * (1 + ‖w‖) ^ N :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hA.le)
    rw [pow_add] at h1
    calc M * SchwartzMap.seminorm ℂ k m (G w) ≤ M * (|C| * (1 + ‖w‖) ^ N) := mul_le_mul_of_nonneg_left h3 hM
      _ = |C| * (M * ((1 + ‖w‖) ^ N * (1 + ‖w‖) ^ (d + 1))) * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          field_simp
      _ ≤ |C| * C' * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          gcongr
      _ = C' * |C| * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by ring
  have hpt : ∀ x, (ip • g') x = ∫ w, c w * G w x := by
    intro x
    simp only [SchwartzMap.smul_apply, smul_eq_mul, hc, hG]
    rw [_root_.GlobalTheory.MoyalPointwise.moyal_pointwise n f g g' x]
  have key := _root_.GlobalTheory.SchwartzIntegral.clm_integral_interchange (Fin n ⊕ Fin n → ℝ) volume n L G c (ip • g') hGc hcc hint hpt
  calc ip * B g' f' = B (ip • g') f' := by rw [hL, hL, map_smul, smul_eq_mul]
    _ = ∫ w, c w * L (G w) := by rw [hL]; exact key
    _ = ∫ w, c w * B (G w) f' := by simp only [hL]

theorem core : ∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hB hherm hpos hinv
  refine _root_.GlobalTheory.hermitian_form_eq_smul_l2 n B hherm hpos fun f f' g g' => ?_
  obtain ⟨G, hGc, hG, hGb⟩ := _root_.GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun n f
  obtain ⟨G', hG'c, hG', hG'b⟩ := _root_.GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun n f'
  have s1 := step n B hB f f' g g' G hGc hG hGb
  have s2 := step n B hB f' f g' g G' hG'c hG' hG'b
  set mc : Sch (Fin n) → Sch (Fin n) → (Fin n ⊕ Fin n → ℝ) → ℂ :=
    fun u v w => ∫ t, rhoFun w ⇑u t * starRingEnd ℂ (v t) with hmc
  have pw : ∀ w, starRingEnd ℂ (mc g g' w) * B (G w) f' = mc g' g (-w) * starRingEnd ℂ (B (G' (-w)) f) := by
    intro w
    have e1 : B (G w) f' = B f (G' (-w)) :=
      hinv w f (G' (-w)) (G w) f' (hG w) (by rw [hG' (-w), rhoFun_neg_cancel])
    have e2 : mc g g' w = ∫ t, g t * starRingEnd ℂ (rhoFun (-w) ⇑g' t) := by
      simp only [hmc]
      conv_lhs => rw [← rhoFun_neg_cancel w ⇑g']
      exact _root_.GlobalTheory.RealWeil.integral_rhoFun_mul_conj n w ⇑g (rhoFun (-w) ⇑g')
    rw [e1, hherm, e2, ← integral_conj]
    simp only [hmc, map_mul, Complex.conj_conj]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  rw [s1]
  have e3 : (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g =
      starRingEnd ℂ ((∫ x, f' x * starRingEnd ℂ (g' x)) * B g f) := by
    rw [map_mul, ← integral_conj, hherm g f]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  simp only [hmc] at pw
  rw [e3, s2, ← integral_conj]
  simp only [pw]
  have hneg := integral_neg_eq_self (fun w => (∫ t, rhoFun w ⇑g' t * starRingEnd ℂ (g t)) *
    starRingEnd ℂ (B (G' w) f)) (volume : Measure (Fin n ⊕ Fin n → ℝ))
  rw [hneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [map_mul]

theorem schrodinger_intertwiner_l2_const : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := _root_.GlobalTheory.ArchUniq.FormTransport.const_of_euclidean core

end GlobalTheory.SvNForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzHadamardLemma
section
open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

noncomputable section

namespace GlobalTheory.ArchUniqStd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def bil {P : V → V → ℝ} (h : IsPairing P) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ P h.addL (fun c x y => by simpa [smul_eq_mul] using h.smulL c x y) h.addR
    (fun c x y => by simpa [smul_eq_mul] using h.smulR c x y)

theorem bil_apply {P : V → V → ℝ} (h : IsPairing P) (x y : V) : bil h x y = P x y := rfl

theorem exists_right [FiniteDimensional ℝ V] {P : V → V → ℝ} (h : IsPairing P) (L : V →L[ℝ] ℝ) :
    ∃ b, ∀ y, P y b = L y := by
  have hinj : Function.Injective (bil h).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact h.nondegR b fun x => by simpa [bil_apply] using LinearMap.congr_fun hb x
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  obtain ⟨b, hb⟩ := hsurj (L : V →ₗ[ℝ] ℝ)
  exact ⟨b, fun y => by simpa [bil_apply] using LinearMap.congr_fun hb y⟩

theorem exists_one [FiniteDimensional ℝ V] : ∃ Φ : 𝓢(V, ℂ), Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiNegFieldChange

theorem semiNeg_descends_baseChange : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (k' : Type) [Field k'] [Algebra k k'], ∃ (C' : Scheme.{0}) (_ : Algebra k' Γ(C', ⊤)) (π : C' ⟶ C), IsCurve k' C' ∧
      ∀ F : C.Modules, SemiNeg k' ((Scheme.Modules.pullback π).obj F) → SemiNeg k F := by
  intro k _ C _ hC k' _ _
  obtain ⟨h1, h2, h3⟩ := hC
  let t : Sp k' ⟶ Sp k := spMap (algebraMap k k')
  let f := strHom k C
  letI A' : Algebra k' Γ(pullback f t, ⊤) := algebraΓOfHom (pullback.snd f t)
  have hs : strHom k' (pullback f t) = pullback.snd f t := strHom_eq fun _ => rfl
  refine ⟨pullback f t, A', pullback.fst f t, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hs]; exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback (IsPullback.of_hasPullback f t) h1
  · rw [hs]; exact GlobalTheory.ProjSpace.isProjOver_pullback_snd _ h2
  · rw [hs]; haveI := h3; infer_instance
  · intro F hF W r hW i hi
    have : IsProper f := by
      obtain ⟨N, j, hj, e⟩ := h2
      have := isProper_str k N
      change IsProper (strHom k (X := C))
      rw [← e]
      infer_instance
    have hinst : (‹Algebra k Γ(C, ⊤)›) = algebraΓOfHom f :=
      Algebra.algebra_ext _ _ (algebraMap_eq_strHom k C)
    haveI : Flat (pullback.fst f t) := inferInstance
    have hm := _root_.GlobalTheory.mono_pullback_map_of_flat _ _ (pullback.fst f t) W F i
    have h := hF _ r (hW.pullback _) _ hm
    rw [← interNum_congr_lbIso k' _ (isLB_vecOne (LB.isLB_pull hW.isLB_det _)) (isLB_vecOne (hW.pullback _).isLB_det)
      (fun j => by fin_cases j; exact hW.lbIso_det_pullback _)] at h
    have P := FieldChangeInter.interNum_pull (f := f) (f' := pullback.snd f t) (π := pullback.fst f t)
      (IsPullback.of_hasPullback f t) (L := ![det W r]) (isLB_vecOne hW.isLB_det)
    have e₃ : (fun j => ((![det W r] : Fin 1 → LB C) j).pull (pullback.fst f t)) = ![(det W r).pull (pullback.fst f t)] :=
      funext fun j => by fin_cases j; rfl
    rw [e₃] at P
    rw [hinst]
    exact P ▸ h

end GlobalTheory.SemiNegFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepClosureFiniteExtPowMemRange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem sepClosure_finiteExt_pow_mem_range :
    ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L]
      [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω']
      [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω') (y : Ω'),
      ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m := by
  intro K L Ω Ω' _ _ _ _ _ _ _ _ _ _ _ _ j y
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable L Ω' := IsSepClosure.separable
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : Algebra.IsAlgebraic K Ω' := Algebra.IsAlgebraic.trans K L Ω'
  set S := separableClosure K Ω'
  set q := ringExpChar K
  haveI : ExpChar Ω' q := expChar_of_injective_algebraMap (algebraMap K Ω').injective q
  haveI : ExpChar S q := expChar_of_injective_algebraMap (algebraMap K S).injective q
  obtain ⟨n, ⟨z, hz⟩⟩ := (isPurelyInseparable_iff_pow_mem S q).1 inferInstance y

  have hzsep : IsSeparable K (z : Ω') := mem_separableClosure_iff.1 z.2
  have hsplit : ((minpoly K (z : Ω')).map (algebraMap K Ω)).Splits :=
    IsSepClosed.splits_codomain _ hzsep
  have hroot : (((minpoly K (z : Ω')).map (algebraMap K Ω)).map (j : Ω →+* Ω')).IsRoot (z : Ω') := by
    rw [Polynomial.map_map, AlgHom.comp_algebraMap]
    simp [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  obtain ⟨x, hx⟩ := hsplit.mem_range_of_isRoot
    (Polynomial.map_ne_zero (minpoly.ne_zero hzsep.isIntegral)) hroot
  refine ⟨q ^ n, x, pow_pos (expChar_pos K q) n, ?_, fun a b => sub_pow_expChar_pow a b n⟩
  rw [← hz]
  simpa using hx.symm

end GlobalTheory.Published.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRealPointsWeightRepresentationEqTop
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem span_range_wInf_comp_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n),
    Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := by
  intro E _ _ _ n lam
  exact span_wInf lam

end GlobalTheory.BCT.TrKer
end
end

