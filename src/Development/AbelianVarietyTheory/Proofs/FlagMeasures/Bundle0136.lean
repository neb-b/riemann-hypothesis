module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnitaryHaarTransportDiagonal
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarTransport

theorem isMatGroup_UH_of_sq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) : PI.IsMatGroup (UH H) := by
  refine ⟨?_, ?_, fun a ha b hb => ?_, fun g hg => ?_⟩
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * H * 1 = H
    simp
  · have ha' : aᴴ * H * a = H := ha
    have hb' : bᴴ * H * b = H := hb
    show (a * b)ᴴ * H * (a * b) = H
    calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [ha', hb']
  · have hg' : gᴴ * H * g = H := hg
    have h1 : (H * gᴴ * H) * g = 1 := by
      rw [Matrix.mul_assoc H, Matrix.mul_assoc H, hg', hH]
    have hu : IsUnit g.det := Matrix.isUnit_det_of_left_inverse h1
    refine ⟨?_, Matrix.mul_nonsing_inv _ hu⟩
    show (g⁻¹)ᴴ * H * g⁻¹ = H
    calc (g⁻¹)ᴴ * H * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * H * g) * g⁻¹ := by rw [hg']
      _ = (g * g⁻¹)ᴴ * H * (g * g⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [Matrix.mul_nonsing_inv _ hu]; simp

theorem haar_transport : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r),
    IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  intro k r μG ε P hμ hP hH
  have hce := Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) (P := P) Formalism.REAL.uJEmb hP
  have hm := hce.continuous.measurable
  have hme := hce.measurableEmbedding
  have hG : PI.IsMatGroup (GG k r) := isMatGroup_UH_of_sq _ (hpkFacts k r).2.1
  have hmem : ∀ y, Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∈ GG k r := fun y =>
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH _).1 ⟨y, rfl⟩
  have hν : PI.IsHaarOnM (GG k r) ((Formalism.REAL.muG ε).map (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P)) := by
    refine ⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩
    · exact (Measure.map_ne_zero_iff hm.aemeasurable).2 (NeZero.ne _)
    · have hcl : IsClosed {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r} := hG.1
      show (Measure.map _ _) {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = 0
      rw [Measure.map_apply hm hcl.measurableSet.compl]
      have : Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ⁻¹' {x : PI.MtM (2 * r + k + 1) | Matrix.of x ∈ GG k r}ᶜ = ∅ := by
        ext y; simpa using hmem y
      rw [this, measure_empty]
    · intro a ha
      obtain ⟨u, hu⟩ := (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff Formalism.REAL.uJEmb uHConj hP hH a).2 ha
      subst hu
      have hl : Measurable (PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)) :=
        (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_cont (k := k) (r := r) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u)).measurable
      rw [Measure.map_map hl hm]
      have e : PI.lmulQ (m := 2 * r + k + 1) (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P u) ∘ Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P =
          Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P ∘ (fun v => u * v) := by
        funext v; exact Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.lmul_phi hP u v
      rw [e, ← Measure.map_map hm (measurable_const_mul u), map_mul_left_eq_self]
  have hμ' : PI.IsHaarOnM (GG k r) μG := hμ
  obtain ⟨c, -, hct, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ μG hG hμ').1 _ hν
  refine ⟨c, hct.ne, fun φ hφ => ?_⟩
  have h1 : ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) =
      ∫⁻ y, φ (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε P y) ∂(Formalism.REAL.muG ε) := rfl
  rw [h1, ← lintegral_map hφ hm, hc, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.HaarTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CapelliCoef

variable {n : ℕ} {ε : Fin n → Bool}

lemma eabV_pair {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (L : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    L (EabV ε a b f g) = EabV ε a b (fun x => L (f x)) g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add (f := _), map_smul, (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h1 hg).2,
    (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h2 hg).2]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma dsigC_unitM (ab : Fin n × Fin n) (v : H) :
    PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM ab) v = EabV ε ab.1 ab.2 (fun x => σ x v) 1 := by
  simp only [PI.DSInfCharCap.dsigC, PI.DSInfCharCap.unitM, PI.DSInfCharCap.thetaJ, PI.PhMeasCore.dsig,
    EabV, EcV, RdV, cpart1, cpart2, Matrix.one_mul, sub_neg_eq_add, ← sub_eq_add_neg]

def freeAct (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (smoothVec ε σ) :=
  FreeAlgebra.lift ℂ fun ab => unitAct hσ ab.1 ab.2

lemma dsigCW_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (w : List (Fin n × Fin n)) (v : smoothVec ε σ) :
    PI.DSInfCharCap.dsigCW ε σ (w.map PI.DSInfCharCap.unitM) v =
      ((w.map fun ab => unitAct hσ ab.1 ab.2).prod v : smoothVec ε σ) := by
  induction w with
  | nil => rfl
  | cons ab w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, PI.DSInfCharCap.dsigCW]
    rw [ih, dsigC_unitM, unitAct_coe]

lemma actU_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (p : FreeAlgebra ℂ (Fin n × Fin n))
    (v : smoothVec ε σ) : PI.DSInfCharCap.actU ε σ p v = (freeAct hσ p v : smoothVec ε σ) := by
  have e : freeAct hσ = (MonoidAlgebra.lift ℂ _ _ (FreeMonoid.lift fun ab => unitAct hσ ab.1 ab.2)).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := Fin n × Fin n)).toAlgHom := by
    ext1
    funext ab
    simp [freeAct, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [e]
  simp only [AlgHom.comp_apply, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, dsigCW_eq hσ, Finsupp.sum,
    LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, FreeMonoid.lift_apply]
  rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def IsCoef (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : H →L[ℂ] Wp)
    (B : Wq →ₗ[ℂ] smoothVec ε σ) (f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ g, inUJ ε g → ∀ w, f g w = P (σ g (B w))

lemma IsCoef.smooth {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) : SmoothOnGV ε f :=
  smooth_congr (PI.UnitaryGroupMassFormula.CapelliEig.coef_smoothOnGV ε σ P
    (LinearMap.toContinuousLinearMap ((smoothVec ε σ).subtype ∘ₗ B)) fun w => (B w).2)
    fun g hg => ContinuousLinearMap.ext fun w => h g hg w

lemma IsCoef.eab (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (a b : Fin n) :
    IsCoef ε σ P (unitAct hσ a b ∘ₗ B) (EabV ε a b f) := by
  intro g hg w
  have e1 := eabV_pair (ContinuousLinearMap.apply ℂ Wp w) h.smooth a b hg
  simp only [ContinuousLinearMap.apply_apply] at e1
  rw [e1, eabV_congr (fun x hx => h x hx w) a b hg, ← eabV_pair P (B w).2 a b hg, LinearMap.comp_apply,
    unitAct_coe, rep_eabV hσ (B w).2 a b hg]

lemma IsCoef.top (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (u : ℂ) (a b : Fin n) :
    IsCoef ε σ P (freeAct hσ (Tm (PI.DSInfCharCap.Egl n) u a b) ∘ₗ B) (Top (EabV ε) u a b f) := by
  intro g hg w
  have e := h.eab hσ a b g hg w
  have e' := h g hg w
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, PI.DSInfCharCap.Egl, freeAct, Module.algebraMap_end_apply, e', e]
  · simp [Formalism.QuantumDeterminants.Top, Tm, hab, PI.DSInfCharCap.Egl, freeAct, e]

lemma IsCoef.word (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (l : List (ℂ × Fin n × Fin n)) :
    IsCoef ε σ P (freeAct hσ (l.map fun q => Tm (PI.DSInfCharCap.Egl n) q.1 q.2.1 q.2.2).prod ∘ₗ B)
      ((l.map fun q => Top (EabV ε) q.1 q.2.1 q.2.2).foldr (fun T h => T h) f) := by
  induction l with
  | nil => simpa [Module.End.one_eq_id] using h
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, Module.End.mul_eq_comp,
      LinearMap.comp_assoc]
    exact ih.top hσ _ _ _

theorem capelli_coef : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  intro n ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hds P Q hQ u g hg w
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := hds.2.2.1
  let B : Wq →ₗ[ℂ] smoothVec ε σ := (Q : Wq →ₗ[ℂ] Hs).codRestrict _ hQ
  have h0 : IsCoef ε σ P B (fun x => P.comp ((σ x).comp Q)) := fun _ _ _ => rfl
  have e : Q w = (B w : Hs) := rfl
  rw [e, actU_eq hσ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [capelli, qdetOp, qminorOp, qdet, qminor, map_sum, map_mul, map_intCast, Finset.sum_apply,
    _root_.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Pi.smul_apply,
    _root_.smul_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := h0.word hσ (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), τ k, k)) g hg w
  simp only [List.map_ofFn, Function.comp_def] at h
  simp only [id]
  rw [h]
  simp [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul ℂ]

end GlobalTheory.CapelliCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRankOneHermitianLatticeClassesLe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RankOneClasses

open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [StarRing E] in
theorem ne_bot_of_isLattice {L : Submodule (𝓞 E) E} (h : Submodule.IsFullLattice E L) : L ≠ ⊥ := by
  intro hb
  let : Submodule.IsFullLattice E L := h
  have : Submodule.span E (L : Set E) = ⊤ := Submodule.IsFullLattice.span_eq_top
  rw [hb] at this
  simp at this

noncomputable def latUnit (L : Submodule (𝓞 E) E) (h : Submodule.IsFullLattice E L) :
    (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  Units.mk0 (⟨L, FractionalIdeal.isFractional_of_fg h.fg⟩ : FractionalIdeal (𝓞 E)⁰ E) (by
    intro h0
    exact ne_bot_of_isLattice h (FractionalIdeal.coeToSubmodule_eq_bot.mpr h0))

omit [StarRing E] in
theorem exists_scale {L M : Submodule (𝓞 E) E} (hL : Submodule.IsFullLattice E L)
    (hM : Submodule.IsFullLattice E M)
    (h : (QuotientGroup.mk (latUnit L hL) :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range) =
      QuotientGroup.mk (latUnit M hM)) :
    ∃ a : E, a ≠ 0 ∧ ∀ y, a * y ∈ M ↔ y ∈ L := by
  obtain ⟨a, ha⟩ := QuotientGroup.eq.mp h
  have h1 : latUnit M hM = toPrincipalIdeal (𝓞 E) E a * latUnit L hL := by
    rw [ha, mul_comm, mul_inv_cancel_left]
  have h2 : ((latUnit M hM : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (a : E) * (latUnit L hL : (FractionalIdeal (𝓞 E)⁰ E)ˣ) := by
    rw [h1, Units.val_mul, coe_toPrincipalIdeal]
  refine ⟨a, a.ne_zero, fun y => ?_⟩
  have h3 : (a : E) * y ∈ M ↔ (a : E) * y ∈
      ((latUnit M hM : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) := Iff.rfl
  rw [h3, h2, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, he⟩
    rw [mul_left_cancel₀ a.ne_zero he]
    exact hz
  · intro hy
    exact ⟨y, hy, rfl⟩

def idealOf (β : E) (L : Submodule (𝓞 E) E) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {t | ∃ x ∈ L, ∃ y ∈ L, t = star x * β * y}

theorem idealOf_fg (β : E) {L : Submodule (𝓞 E) E} (h : Submodule.IsFullLattice E L) :
    (idealOf β L).FG := by
  obtain ⟨d, hd, hdL⟩ : IsFractional (𝓞 E)⁰ L := FractionalIdeal.isFractional_of_fg h.fg
  have hd0 : (d : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hd
  have hs0 : star (d : E) ≠ 0 := by simpa using hd0
  have hle : idealOf β L ≤ Submodule.span (𝓞 E) {(star (d : E))⁻¹ * β * (d : E)⁻¹} := by
    refine Submodule.span_le.mpr ?_
    rintro t ⟨x, hx, y, hy, rfl⟩
    obtain ⟨p, hp⟩ := hdL x hx
    obtain ⟨q, hq⟩ := hdL y hy
    have hi : IsIntegral ℤ (star (p : E)) :=
      p.isIntegral_coe.map (starRingEnd E).toIntAlgHom
    let p' : 𝓞 E := ⟨star (p : E), hi⟩
    refine Submodule.mem_span_singleton.mpr ⟨p' * q, ?_⟩
    have hp' : (p : E) = d * x := hp
    have hq' : (q : E) = d * y := hq
    change (star (p : E) * (q : E)) * _ = _
    rw [hp', hq', star_mul']
    field_simp
  exact Submodule.FG.of_le (Submodule.fg_span_singleton _) hle

theorem idealOf_ne_bot {β : E} (hβ : β ≠ 0) {L : Submodule (𝓞 E) E}
    (h : Submodule.IsFullLattice E L) : idealOf β L ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff L).mp (ne_bot_of_isLattice h)
  refine (Submodule.ne_bot_iff _).mpr ⟨star x * β * x, Submodule.subset_span ⟨x, hx, x, hx, rfl⟩, ?_⟩
  simp [hx0, hβ]

theorem mul_mem_idealOf {β γ t a : E} {L M : Submodule (𝓞 E) E}
    (h : ∀ y ∈ L, a * y ∈ M) (ht : star a * γ * a = t * β) :
    ∀ z ∈ idealOf β L, t • z ∈ idealOf γ M := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * x, h x hx, a * y, h y hy, ?_⟩
    rw [smul_eq_mul, star_mul']
    linear_combination (-(star x * y)) * ht
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem exists_unit {β γ a : E} (hβ : β ≠ 0) (hγ : γ ≠ 0) {L M : Submodule (𝓞 E) E}
    (hL : Submodule.IsFullLattice E L) (ha : a ≠ 0) (h : ∀ y, a * y ∈ M ↔ y ∈ L)
    (hN : idealOf β L = idealOf γ M) :
    ∃ u : (𝓞 E)ˣ, star a * γ * a * ((u : 𝓞 E) : E) = β := by
  have hs : star a ≠ 0 := by simpa using ha
  have h1 : ∀ z ∈ idealOf β L, (star a * γ * a / β) • z ∈ idealOf β L := by
    intro z hz
    have := mul_mem_idealOf (γ := γ) (t := star a * γ * a / β) (fun y hy => (h y).mpr hy)
      (by field_simp) z hz
    rwa [← hN] at this
  have h2 : ∀ z ∈ idealOf β L, (β / (star a * γ * a)) • z ∈ idealOf β L := by
    intro z hz
    rw [hN] at hz
    exact mul_mem_idealOf (a := a⁻¹) (fun y hy => (h _).mp (by rwa [mul_inv_cancel_left₀ ha]))
      (by rw [star_inv₀]; field_simp) z hz
  have i1 := isIntegral_trans (R := ℤ) _ (isIntegral_of_smul_mem_submodule _ (idealOf_ne_bot hβ hL)
    (idealOf_fg β hL) _ h1)
  have i2 := isIntegral_trans (R := ℤ) _ (isIntegral_of_smul_mem_submodule _ (idealOf_ne_bot hβ hL)
    (idealOf_fg β hL) _ h2)
  refine ⟨⟨⟨_, i2⟩, ⟨_, i1⟩, ?_, ?_⟩, ?_⟩
  · apply RingOfIntegers.ext
    change β / (star a * γ * a) * (star a * γ * a / β) = 1
    field_simp
  · apply RingOfIntegers.ext
    change (star a * γ * a / β) * (β / (star a * γ * a)) = 1
    field_simp
  · change star a * γ * a * (β / (star a * γ * a)) = β
    field_simp

noncomputable def even_im_hermitian_sub (u : (𝓞 E)ˣ) : Fin (Units.rank E) → ZMod 2 :=
  fun i => (((Units.basisModTorsion E).repr (Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E)) i : ℤ) : ZMod 2)

omit [StarRing E] in
theorem exists_sq_of_parity {u w : (𝓞 E)ˣ} (h : even_im_hermitian_sub u = even_im_hermitian_sub w) :
    ∃ (ζ : (𝓞 E)ˣ) (v : (𝓞 E)ˣ), ζ ∈ Units.torsion E ∧ u = w * ζ * v ^ 2 := by
  have hd : ∀ i, ∃ k : ℤ,
      (Units.basisModTorsion E).repr (Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E)) i -
      (Units.basisModTorsion E).repr (Additive.ofMul (w : (𝓞 E)ˣ ⧸ Units.torsion E)) i = 2 * k := by
    intro i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).mp (congrFun h i).symm
  choose k hk using hd
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective
    (Additive.toMul ((Units.basisModTorsion E).equivFun.symm k))
  have hv' : Additive.ofMul (v : (𝓞 E)ˣ ⧸ Units.torsion E) =
      (Units.basisModTorsion E).equivFun.symm k := by rw [hv]; rfl
  have he : Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E) =
      Additive.ofMul (w : (𝓞 E)ˣ ⧸ Units.torsion E) +
        (2 : ℤ) • Additive.ofMul (v : (𝓞 E)ˣ ⧸ Units.torsion E) := by
    apply (Units.basisModTorsion E).equivFun.injective
    rw [map_add (f := _), map_smul, hv', LinearEquiv.apply_symm_apply]
    funext i
    simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hk i
  have he' : ((w * v ^ 2 : (𝓞 E)ˣ) : (𝓞 E)ˣ ⧸ Units.torsion E) = u := by
    apply Additive.ofMul.injective
    rw [he, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_pow, two_nsmul, two_zsmul]
  refine ⟨(w * v ^ 2)⁻¹ * u, v, QuotientGroup.eq.mp he', ?_⟩
  rw [mul_right_comm, mul_inv_cancel_left]

theorem eq_of_norm_eq (φ : E →+* ℂ) (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) {A B : E}
    (hA : star A = A) (hB : star B = B) (pA : 0 < (φ A).re) (pB : 0 < (φ B).re)
    (h : ‖φ A‖ = ‖φ B‖) : A = B := by
  apply φ.injective
  have a1 : ((φ A).re : ℂ) = φ A := Complex.conj_eq_iff_re.mp (by rw [← hφ, hA])
  have b1 : ((φ B).re : ℂ) = φ B := Complex.conj_eq_iff_re.mp (by rw [← hφ, hB])
  rw [← a1, ← b1, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg pA.le,
    Real.norm_of_nonneg pB.le] at h
  rw [← a1, ← b1, h]

theorem card_classes_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ N : Submodule (𝓞 E) E, ENat.card (Quot (fun X Y : {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsFullLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2)) ≤ ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E : ℕ) : ENat) := by
  intro E _ _ _ hE N
  classical
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hφ := hE.2.1 φ
  set S := {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsFullLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} with hS
  have hne : ∀ X : S, X.1.1 ≠ 0 := by
    intro X h0
    have := X.2.2.1 φ
    rw [h0] at this
    simp at this
  let cls : S → (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range :=
    fun X => QuotientGroup.mk (latUnit X.1.2 X.2.2.2.1)
  let base : S → S := fun X => Classical.choose (⟨X, rfl⟩ : ∃ B, cls B = cls X)
  have hbase : ∀ X, cls (base X) = cls X := fun X =>
    Classical.choose_spec (⟨X, rfl⟩ : ∃ B, cls B = cls X)
  have hbase' : ∀ X Y, cls X = cls Y → base X = base Y := by
    intro X Y h
    simp only [base, h]
  have hex : ∀ X : S, ∃ (a : E) (u : (𝓞 E)ˣ), a ≠ 0 ∧ (∀ y, a * y ∈ (base X).1.2 ↔ y ∈ X.1.2) ∧
      star a * (base X).1.1 * a * ((u : 𝓞 E) : E) = X.1.1 := by
    intro X
    obtain ⟨a, ha, h⟩ := exists_scale X.2.2.2.1 (base X).2.2.2.1 (hbase X).symm
    obtain ⟨u, hu⟩ := exists_unit (hne X) (hne (base X)) X.2.2.2.1 ha h
      (X.2.2.2.2.trans (base X).2.2.2.2.symm)
    exact ⟨a, u, ha, h, hu⟩
  choose a u ha hm hu using hex
  have key : ∀ X Y : S, cls X = cls Y → even_im_hermitian_sub (u X) = even_im_hermitian_sub (u Y) →
      ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2 := by
    intro X Y hc hp
    obtain ⟨ζ, v, hζ, hv⟩ := exists_sq_of_parity hp
    have hb := hbase' X Y hc
    have hv0 : ((v : 𝓞 E) : E) ≠ 0 := by simp
    have haY := ha Y
    have hsY : star (a Y) ≠ 0 := by simpa using haY
    have hc0 : a X * ((v : 𝓞 E) : E) / a Y ≠ 0 := div_ne_zero (mul_ne_zero (ha X) hv0) haY
    refine ⟨a X * ((v : 𝓞 E) : E) / a Y, hc0, ?_, fun y => ?_⟩
    · apply eq_of_norm_eq φ hφ _ X.2.1 _ (X.2.2.1 φ)
      · have e1 : star (a X * ((v : 𝓞 E) : E) / a Y) * Y.1.1 * (a X * ((v : 𝓞 E) : E) / a Y) =
            star (a X) * (base X).1.1 * a X * ((u Y : 𝓞 E) : E) *
              (star ((v : 𝓞 E) : E) * ((v : 𝓞 E) : E)) := by
          rw [← hu Y, hb, star_div₀, star_mul']
          field_simp
        have e2 : X.1.1 = star (a X) * (base X).1.1 * a X * ((u Y : 𝓞 E) : E) *
              (((ζ : 𝓞 E) : E) * (((v : 𝓞 E) : E) * ((v : 𝓞 E) : E))) := by
          rw [← hu X, hv]
          push_cast
          ring
        have e3 : ‖φ ((ζ : 𝓞 E) : E)‖ = 1 := by
          have := (Units.mem_torsion E).mp hζ (InfinitePlace.mk φ)
          rwa [InfinitePlace.apply] at this
        rw [e1, e2]
        simp only [map_mul, norm_mul, hφ, e3, Complex.norm_conj, one_mul]
      · rw [star_mul', star_mul', star_star, Y.2.1]; ring
      · have : φ (star (a X * ((v : 𝓞 E) : E) / a Y) * Y.1.1 * (a X * ((v : 𝓞 E) : E) / a Y)) =
            (Complex.normSq (φ (a X * ((v : 𝓞 E) : E) / a Y)) : ℂ) * φ Y.1.1 := by
          rw [map_mul, map_mul, hφ, Complex.normSq_eq_conj_mul_self]; ring
        rw [this, Complex.re_ofReal_mul]
        exact mul_pos (Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hc0)) (Y.2.2.1 φ)
    · rw [← hm Y, ← hm X, hb]
      have : a Y * (a X * ((v : 𝓞 E) : E) / a Y * y) = v • (a X * y) := by
        change _ = ((v : 𝓞 E) : E) * _
        field_simp
      rw [this]
      exact Submodule.smul_mem_iff_of_isUnit _ v.isUnit
  let g : Quot (fun X Y : S => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧
      ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2) → ClassGroup (𝓞 E) × (Fin (Units.rank E) → ZMod 2) :=
    fun q => ((ClassGroup.equiv E).symm (cls q.out), even_im_hermitian_sub (u q.out))
  have hg : Function.Injective g := by
    intro q r h
    rw [← q.out_eq, ← r.out_eq]
    exact Quot.sound (key _ _ ((ClassGroup.equiv E).symm.injective (congrArg Prod.fst h))
      (congrArg Prod.snd h))
  refine (ENat.card_le_card_of_injective hg).trans ?_
  rw [ENat.card_eq_coe_fintype_card, Nat.cast_le, Fintype.card_prod, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))

end GlobalTheory.RankOneClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselUnitaryHaarUnique
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem hpk_ne_zero (k r : ℕ) : Hpk k r ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨r, by omega⟩) ⟨r, by omega⟩
  simp only [Hpk, Matrix.zero_apply] at this
  split_ifs at this <;> first | omega | norm_num at this | skip
  all_goals simp_all

theorem isMatGroup_of_isClosedSub {k r : ℕ} {S : Set (Mat k r)} (hS : IsClosedSub k r S) :
    PI.IsMatGroup S := by
  obtain ⟨hU, hc, h1, hm, hi⟩ := hS
  refine ⟨hc, h1, hm, fun a ha => ⟨hi a ha, ?_⟩⟩
  by_cases hd : IsUnit a.det
  · exact Matrix.mul_nonsing_inv a hd
  · exfalso
    have h0 : a⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit a hd
    have hmem := hU (hi a ha)
    rw [h0] at hmem
    have : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hmem
    simp at this
    exact hpk_ne_zero k r this.symm

theorem haarOn_unique : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ μ' : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn S μ → IsHaarOn S μ' → ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ μ' = c • μ := by
  intro k r S μ μ' hS hμ hμ'
  exact (GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1) S μ (isMatGroup_of_isClosedSub hS) hμ).1 μ' hμ'

end GlobalTheory.SgInf
end

