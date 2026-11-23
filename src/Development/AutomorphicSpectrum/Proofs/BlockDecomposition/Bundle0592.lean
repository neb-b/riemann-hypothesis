module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerUnitaryIff
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCentNorm

open GlobalTheory.ClassParam (krylov)
open GlobalTheory.MassNorm

section Core

variable {R : Type} [CommRing R] {m : ℕ}

def PhiU (m : ℕ) (R : Type) [CommRing R] : GL (Fin m) R :=
  ⟨GlobalTheory.Tw.Phi m R, (GlobalTheory.Tw.Phi m R)ᵀ, Phi_mul_transpose m R, PhiT_mul_Phi⟩

def DJ (J : GL (Fin m) R) : GL (Fin m) R := J⁻¹ * (PhiU m R)⁻¹

theorem psi_DJ (c : R →+* R) (J : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) :
    psi c (DJ J) x = (J⁻¹).val * cT c x * J.val := by
  have h1 : ((PhiU m R)⁻¹).val = (GlobalTheory.Tw.Phi m R)ᵀ := rfl
  have h2 : (DJ J).val = (J⁻¹).val * (GlobalTheory.Tw.Phi m R)ᵀ := by
    rw [DJ, Units.val_mul, h1]
  have h3 : ((DJ J)⁻¹).val = GlobalTheory.Tw.Phi m R * J.val := by
    rw [DJ, _root_.mul_inv_rev, inv_inv, inv_inv, Units.val_mul]; rfl
  rw [psi, h2, h3]
  have hP := PhiT_mul_Phi (m := m) (R := R)
  calc _ = (J⁻¹).val * ((GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R) * (c.mapMatrix x)ᵀ *
        ((GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R) * J.val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.mul_one, Matrix.mul_one]; rfl

theorem mem_UJ_iff (c : R →+* R) (J g : GL (Fin m) R) :
    g ∈ UJ c J.val ↔ psi c (DJ J) g.val = (g⁻¹).val := by
  rw [psi_DJ]
  have hJ : J.val * (J⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ' : (J⁻¹).val * J.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg' : (g⁻¹).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  change cT c g.val * J.val * g.val = J.val ↔ _
  constructor
  · intro h
    calc (J⁻¹).val * cT c g.val * J.val
        = (J⁻¹).val * (cT c g.val * J.val * g.val) * (g⁻¹).val := by
          simp only [Matrix.mul_assoc]; rw [hg, Matrix.mul_one]
      _ = _ := by rw [h, hJ', Matrix.one_mul]
  · intro h
    calc cT c g.val * J.val * g.val
        = J.val * ((J⁻¹).val * cT c g.val * J.val) * g.val := by
          simp only [← Matrix.mul_assoc]; rw [hJ, Matrix.one_mul]
      _ = _ := by rw [h, Matrix.mul_assoc, hg', Matrix.mul_one]

theorem psi_norm (c : R →+* R) (hc : ∀ x, c (c x) = x) (D : GL (Fin m) R) :
    psi c D (D * thetaGL m c D).val = ((D * thetaGL m c D)⁻¹).val := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  rw [psi_units]
  congr 1
  simp only [_root_.mul_inv_rev, map_mul, map_inv, hθ]
  group

theorem mem_twCent_iff (c : R →+* R) (D g : GL (Fin m) R) :
    g ∈ twCent (thetaGL m c) D ↔ psi c D g.val = (g⁻¹).val := by
  rw [psi_units]
  constructor
  · intro h
    have h' : g⁻¹ * D = D * thetaGL m c g⁻¹ := (twCent (thetaGL m c) D).inv_mem h
    congr 1
    rw [← h']; group
  · intro h
    have h' : D * thetaGL m c g⁻¹ * D⁻¹ = g⁻¹ := Units.ext h
    have : g⁻¹ ∈ twCent (thetaGL m c) D := by
      change g⁻¹ * D = D * thetaGL m c g⁻¹
      calc g⁻¹ * D = (D * thetaGL m c g⁻¹ * D⁻¹) * D := by rw [h']
        _ = _ := by group
    simpa using (twCent (thetaGL m c) D).inv_mem this

theorem commute_of_mem_twCent (c : R →+* R) (hc : ∀ x, c (c x) = x) (D g : GL (Fin m) R)
    (hg : g ∈ twCent (thetaGL m c) D) : g * (D * thetaGL m c D) = (D * thetaGL m c D) * g := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  have h1 : g * D = D * thetaGL m c g := hg
  have h2 : thetaGL m c g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg (thetaGL m c) h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * thetaGL m c D)
      = (D * thetaGL m c D) * ((thetaGL m c D)⁻¹ * (D⁻¹ * g * D) * thetaGL m c D) := by group
    _ = _ := by rw [← h3]

theorem mem_twCent_iff_mem_UJ (c : R →+* R) (hc : ∀ x, c (c x) = x) (D J : GL (Fin m) R)
    (hN : D * thetaGL m c D ∈ UJ c J.val) (v : Fin m → R)
    (hv : IsUnit (krylov (D * thetaGL m c D).val v).det) (g : GL (Fin m) R) :
    g ∈ twCent (thetaGL m c) D ↔
      g ∈ UJ c J.val ∧ g * (D * thetaGL m c D) = (D * thetaGL m c D) * g := by
  have key : g * (D * thetaGL m c D) = (D * thetaGL m c D) * g →
      psi c D g.val = psi c (DJ J) g.val := by
    intro hcomm
    obtain ⟨p, hp⟩ := aeval_of_commute_cyclic v hv (N := g.val) (by
      change g.val * (D * thetaGL m c D).val = (D * thetaGL m c D).val * g.val
      rw [← Units.val_mul, ← Units.val_mul, hcomm])
    rw [hp, psi_aeval, psi_aeval, psi_norm c hc, (mem_UJ_iff c J _).1 hN]
  constructor
  · intro hg
    have hcomm := commute_of_mem_twCent c hc D g hg
    refine ⟨?_, hcomm⟩
    rw [mem_UJ_iff, ← key hcomm]
    exact (mem_twCent_iff c D g).1 hg
  · rintro ⟨hg, hcomm⟩
    rw [mem_twCent_iff, key hcomm]
    exact (mem_UJ_iff c J g).1 hg

end Core

section Global

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem cT_map_algebraMap {m : ℕ} (M : Matrix (Fin m) (Fin m) E) :
    cT (conjFin (IsCMField.complexConj E).toRingEquiv) (M.map (algebraMap E (Af E))) =
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (algebraMap E (Af E)) := by
  ext i j
  simp [cT, conjFin_algebraMap]

theorem mem_twCent_ratF_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable → IsUnit H.det →
  δ * thE E n δ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H →
  ∀ g : GL (Fin n) (Af E), g ∈ twCent (thF E n) (ratF E n δ) ↔
    g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ∧
      g * ratF E n (δ * thE E n δ) = ratF E n (δ * thE E n δ) * g := by
  intro E _ _ _ n δ H hs hH hU g
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hNorm : ratF E n δ * thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) (ratF E n δ) =
      ratF E n (δ * thE E n δ) := by
    change ratF E n δ * thF E n (ratF E n δ) = _
    rw [GlobalTheory.MassNorm.thF_ratF, map_mul]
  have hdet : IsUnit (H.map (algebraMap E (Af E))).det := by
    have h1 := hH.map (algebraMap E (Af E))
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h1
  let J : GL (Fin n) (Af E) := Matrix.nonsingInvUnit _ hdet
  have hJ : J.val = H.map (algebraMap E (Af E)) := rfl
  have hU' : ratF E n (δ * thE E n δ) ∈
      UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) := by
    have h0 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (δ * thE E n δ).val * H * (δ * thE E n δ).val = H := hU
    change cT _ (ratF E n (δ * thE E n δ)).val * _ * (ratF E n (δ * thE E n δ)).val = _
    have hv : (ratF E n (δ * thE E n δ)).val = (δ * thE E n δ).val.map (algebraMap E (Af E)) := rfl
    rw [hv, cT_map_algebraMap]
    conv_rhs => rw [← h0]
    simp only [Matrix.map_mul]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (krylov (ratF E n δ * thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [hNorm]
    exact h1
  have := mem_twCent_iff_mem_UJ _ hc (ratF E n δ) J (by rw [hNorm, hJ]; exact hU') _ hv' g
  rw [hNorm, hJ] at this
  exact this

end Global

end GlobalTheory.CompanionTheory.TwCentNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProduct
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg.RadHaar

theorem isMulLeftInvariant_map_of {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e q * e p) :
    (P.map e).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => g * x) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => g * x) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => g * x) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem measurePreserving_shear {A C : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [AddCommGroup C] [MeasurableSpace C] [MeasurableAdd₂ C] (κ : Measure A) (β : Measure C) [SFinite κ] [SFinite β]
    [κ.IsAddLeftInvariant] [β.IsAddLeftInvariant] {f : C → A} (hf : Measurable f) (b₀ : C) :
    MeasurePreserving (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) (κ.prod β) (κ.prod β) := by
  have h1 : MeasurePreserving (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) (β.prod κ) (β.prod κ) :=
    (measurePreserving_add_left β b₀).skew_product (g := fun c a => f c + a)
      (by exact (hf.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun c => map_add_left_eq_self κ (f c))
  have h2 := (Measure.measurePreserving_swap (μ := β) (ν := κ)).comp
    (h1.comp (Measure.measurePreserving_swap (μ := κ) (ν := β)))
  have hfun : (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) =
      Prod.swap ∘ (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) ∘ Prod.swap := by
    funext p
    exact Prod.ext (add_comm _ _) (add_comm _ _)
  rw [hfun]
  exact h2

private theorem isMulRightInvariant_map_of_exists_measurePreserving {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) :
    (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => x * g) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => x * g) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem haar_of_shear {A C G : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] [LocallyCompactSpace A]
    [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] [LocallyCompactSpace C]
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : A × C ≃ₜ G) (f : C → C → A) (hf : Continuous fun x : C × C => f x.1 x.2)
    (hmul : ∀ c b c' b', e (c, b) * e (c', b') = e (c + (c' + f b b'), b + b'))
    (κ : Measure A) (β : Measure C) [κ.IsAddHaarMeasure] [β.IsAddHaarMeasure] :
    ((κ.prod β).map e).IsHaarMeasure ∧ ((κ.prod β).map e).IsMulRightInvariant := by
  have hfc : IsFiniteMeasureOnCompacts ((κ.prod β).map e) := by
    refine ⟨fun K hK => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv K < ⊤
    rw [MeasurableEquiv.map_apply]
    exact (e.isCompact_preimage.2 hK).measure_lt_top
  have hop : Measure.IsOpenPosMeasure ((κ.prod β).map e) := by
    refine ⟨fun U hU hne => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv U ≠ 0
    rw [MeasurableEquiv.map_apply]
    exact (hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)
  have hl : ((κ.prod β).map e).IsMulLeftInvariant := by
    refine isMulLeftInvariant_map_of (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f b p.2), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_const.prodMk continuous_id)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c, b) * e (c', b')
    rw [hmul]
    congr 1
    exact Prod.ext (add_left_comm _ _ _) (add_comm _ _)
  have hr : ((κ.prod β).map e).IsMulRightInvariant := by
    refine isMulRightInvariant_map_of_exists_measurePreserving (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f p.2 b), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_id.prodMk continuous_const)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c', b') * e (c, b)
    rw [hmul]
  exact ⟨{ toIsFiniteMeasureOnCompacts := hfc, toIsMulLeftInvariant := hl, toIsOpenPosMeasure := hop }, hr⟩

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def coordB (q : GA D B) : Mx D t W.rank := d.pX ⬝ mt B q ⬝ d.j0

def coordC (q : GA D B) : Mx D t t :=
  d.pX ⬝ mt B q ⬝ d.jY + half D • (coordB d q ⬝ plus W (coordB d q))

theorem pX_nn (c : skewA D t) (b : Mx D t W.rank) : d.pX ⬝ mt B (d.nC c * d.nB b) =
    d.pX + b ⬝ d.p0 - (half D • (b ⬝ plus W b)) ⬝ d.pY + c.1 ⬝ d.pY := by
  rw [GlobalTheory.MixModel.mt_mul, ← Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_nC, Matrix.add_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pY_nB, GlobalTheory.MixModel.HypDec.pX_nB]

theorem coordB_nn (c : skewA D t) (b : Mx D t W.rank) : coordB d (d.nC c * d.nB b) = b := by
  rw [coordB, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_j0, GlobalTheory.MixModel.HypDec.p0_j0, GlobalTheory.MixModel.HypDec.pY_j0, Matrix.mul_one,
    Matrix.mul_zero, zero_add, sub_zero, add_zero]

theorem coordC_nn (c : skewA D t) (b : Mx D t W.rank) : coordC d (d.nC c * d.nB b) = c.1 := by
  rw [coordC, coordB_nn, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jY, GlobalTheory.MixModel.HypDec.p0_jY, GlobalTheory.MixModel.HypDec.pY_jY, Matrix.mul_one,
    Matrix.mul_zero]
  abel

section Top

local instance topRingAE : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1

local instance topGrpGA (S : HSp D) : IsTopologicalGroup (GA D S) := (Formalism.IndefR.Eqv.ga_facts D S).1

theorem continuous_coordB : Continuous (coordB d) := by
  show Continuous fun q : GA D B => d.pX * mt B q * d.j0
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const

theorem continuous_coordC : Continuous (coordC d) := by
  have hB := continuous_coordB d
  have hP : Continuous fun q : GA D B => GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q) :=
    continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_adj.comp hB)
  have hS : Continuous fun q : GA D B =>
      GlobalTheory.MixModel.half D • (coordB d q * (GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q))) :=
    (hB.matrix_mul hP).const_smul (GlobalTheory.MixModel.half D)
  have hA : Continuous fun q : GA D B => d.pX * mt B q * d.jY :=
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const
  exact hA.add hS

theorem coordC_mem (n : radN d) : coordC d n.1.1 ∈ skewA D t := by
  obtain ⟨c, b, h⟩ := n.2
  rw [h, coordC_nn]
  exact c.2

def coordHomeo : (skewA D t × Mx D t W.rank) ≃ₜ radN d where
  toFun p := ⟨⟨d.nC p.1 * d.nB p.2, mul_mem (GlobalTheory.GodementSectionReduction.nC_mem d _) (GlobalTheory.GodementSectionReduction.nB_mem d _)⟩, p.1, p.2, rfl⟩
  invFun n := (⟨coordC d n.1.1, coordC_mem d n⟩, coordB d n.1.1)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (coordC_nn d p.1 p.2)
    · exact coordB_nn d p.1 p.2
  right_inv n := by
    obtain ⟨c, b, h⟩ := n.2
    apply Subtype.ext
    apply Subtype.ext
    change d.nC ⟨coordC d n.1.1, coordC_mem d n⟩ * d.nB (coordB d n.1.1) = n.1.1
    have e1 : (⟨coordC d n.1.1, coordC_mem d n⟩ : skewA D t) = c :=
      Subtype.ext (by change coordC d n.1.1 = c.1; rw [h, coordC_nn])
    rw [e1, h, coordB_nn]
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((d.continuous_nC.comp continuous_fst).mul (d.continuous_nB.comp continuous_snd)) _) _
  continuous_invFun :=
    (Continuous.subtype_mk ((continuous_coordC d).comp (continuous_subtype_val.comp continuous_subtype_val)) _).prodMk
      ((continuous_coordB d).comp (continuous_subtype_val.comp continuous_subtype_val))

theorem coordHomeo_coe (p : skewA D t × Mx D t W.rank) :
    (((coordHomeo d p : radN d) : GlobalTheory.RegSW.stab d) : GA D B) = d.nC p.1 * d.nB p.2 := rfl

end Top


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem exists_coord : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  intro D B W t d _ κ β hκ hβ
  have hc := coordHomeo_coe d
  obtain ⟨i1, i2, i3, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  obtain ⟨j1, j2, j3, j4, j5⟩ := Formalism.IndefR.Eqv.ga_facts D B
  have : T2Space (Mx D t t) := inferInstanceAs (T2Space (Fin t → Fin t → AE D))
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t t) := inferInstanceAs (SecondCountableTopology (Fin t → Fin t → AE D))
  have : LocallyCompactSpace (Mx D t t) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin t → AE D))
  have : T2Space (Mx D t W.rank) := inferInstanceAs (T2Space (Fin t → Fin W.rank → AE D))
  have : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t W.rank) := inferInstanceAs (SecondCountableTopology (Fin t → Fin W.rank → AE D))
  have : LocallyCompactSpace (Mx D t W.rank) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin W.rank → AE D))
  have q3 : SecondCountableTopology (skewA D t) :=
    inferInstanceAs (SecondCountableTopology ((skewA D t : Set (Mx D t t))))
  have hcl : IsClosed ((skewA D t : Set (Mx D t t))) := by
    show IsClosed {c : Mx D t t | GlobalTheory.MixModel.adj c = -c}
    exact isClosed_eq GlobalTheory.MixModel.continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D t) := hcl.locallyCompactSpace
  refine ⟨coordHomeo d, hc, ?_⟩
  refine haar_of_shear (coordHomeo d) (fun b b' => cComm W b b') (GlobalTheory.Unf.HaarCoord.continuous_cComm W t) ?_ κ β
  intro c b c' b'
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, hc, hc]
  dsimp only
  rw [GlobalTheory.MixModel.HypDec.nC_add, GlobalTheory.MixModel.HypDec.nC_add]
  simp only [mul_assoc]
  rw [← mul_assoc (d.nB b) (d.nC c'), ← GlobalTheory.MixModel.HypDec.nC_mul_nB d b c', mul_assoc (d.nC c'), GlobalTheory.MixModel.HypDec.nB_mul_nB,
    ← GlobalTheory.MixModel.HypDec.nC_mul_nB d (b + b') (cComm W b b')]

end GlobalTheory.CompanionTheory.QKAvg.RadHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalInfLeviTrivial
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem mt_mul_frame {k : ℕ} (x y : GA D B) (J : Mx D B.rank k) :
    mt B (x * y) ⬝ J = mt B x ⬝ (mt B y ⬝ J) := by
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul]

theorem levi_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    {a : GL (Fin t) (AE D)} (e : d.nC c * d.nB b = d.emb0 g * d.levi a) : a = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.jX = mt B (d.emb0 g * d.levi a) ⬝ d.jX := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_jX, d.nC_jX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX] at h
  apply Units.ext
  have h' : d.pX ⬝ d.jX = d.pX ⬝ (d.jX ⬝ a.1) := congrArg (fun M => d.pX ⬝ M) h
  rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h'
  exact h'.symm

theorem unitary_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    (e : d.nC c * d.nB b = d.emb0 g * d.levi 1) : g = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.j0 = mt B (d.emb0 g * d.levi 1) ⬝ d.j0 := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_j0, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_add, d.nC_j0,
    ← Matrix.mul_assoc, d.nC_jX] at h
  have h' : d.p0 ⬝ (d.j0 + d.jX ⬝ b) = d.p0 ⬝ (d.j0 ⬝ mt W g) := congrArg (fun M => d.p0 ⬝ M) h
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.zero_mul,
    add_zero, Matrix.one_mul] at h'
  apply GlobalTheory.MixModel.mt_injective
  rw [← h', GlobalTheory.MixModel.mt_one]

theorem radN_disj_levM : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  intro D B W t d x hn hm
  obtain ⟨c, b, hx⟩ := (mem_radN d).1 hn
  obtain ⟨g, a, hy⟩ := (mem_levM d).1 hm
  have e : d.nC c * d.nB b = d.emb0 g * d.levi a := hx.symm.trans hy
  have ha := levi_part_eq_one d e
  subst ha
  have hg := unitary_part_eq_one d e
  subst hg
  have h1 : d.emb0 1 * d.levi 1 = 1 := by rw [map_one, map_one, mul_one]
  exact Subtype.ext (hy.trans h1)

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
section
namespace GlobalTheory.CompanionTheory.Gunr

open NumberField IsDedekindDomain Filter

theorem finInt : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  intro F _ _ X
  have hone : ∀ x : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
    intro x
    have hfin : {v : HeightOneSpectrum (𝓞 F) | 1 < v.valuation F x}.Finite :=
      HeightOneSpectrum.Support.finite (𝓞 F) x
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ¬ 1 < v.valuation F x := by
      rw [eventually_cofinite]
      simpa using hfin
    refine hev.mono fun v hv => ?_
    have e : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, e]
    exact not_lt.mp hv
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ x ∈ X, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset X).2 fun x _ => hone x
  exact hall

end GlobalTheory.CompanionTheory.Gunr
end

