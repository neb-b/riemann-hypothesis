module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0686
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0021
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleConjugationInvariant
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct ENNReal NNReal Matrix Classical NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ModConj

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_involution_eq {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (he2 : ∀ x, e (e x) = x) (ν : Measure G) [ν.IsAddHaarMeasure] [SecondCountableTopology G] :
    ν.map e = ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul _ he.aemeasurable, hb, smul_smul]
  have hid : (e ∘ e : G → G) = id := funext he2
  rw [hid, Measure.map_id] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbb : b * b = 1 := by
    have h3 : ((b * b : ℝ≥0) • ν) K = ((1 : ℝ≥0) • ν) K := by rw [← h2, one_smul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  have hb1 : b = 1 := by
    have := (mul_self_eq_one_iff (a := (b : ℝ))).1 (by exact_mod_cast hbb)
    rcases this with h | h
    · exact_mod_cast h
    · have := b.2; simp only [NNReal.val_eq_coe] at this; linarith
  rw [hb, hb1, one_smul]

def conjA (σ : E →ₐ[F] E) : 𝔸[E] →+* 𝔸[E] :=
  (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).toRingEquiv.toRingHom.comp
    ((sigR (AF F) σ).comp (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm.toRingEquiv.toRingHom)

theorem conjA_apply (σ : E →ₐ[F] E) (y : 𝔸[E]) :
    conjA σ y = GroundTheory.BlockD.ThmBHecke.adeleEquiv F E
      (sigR (AF F) σ ((GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm y)) := rfl

theorem sig_sig {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem continuous_sig {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : Continuous (sigR (AF F) σ) :=
  (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)).2.2.2.2.1

theorem sigma_sigma {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

def conjE {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : 𝔸[E] ≃ₜ+ 𝔸[E] where
  toFun := conjA σ
  invFun := conjA σ
  left_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  right_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  map_add' := map_add _
  continuous_toFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)
  continuous_invFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)

end

theorem ideleModule_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : (AF F ⊗[F] E)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E
        (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ) =
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) := by
  intro F E _ _ _ _ _ σ hcm x
  letI : MeasurableSpace 𝔸[E] := measurableSpace_adeleRing E
  set a := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x with ha
  set a' := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x) with ha'
  set e := conjE hcm with he
  set ν := adeleMeasure E with hν
  have hinv : ∀ y, e (e y) = y := fun y => e.left_inv y
  have hcoe : ∀ y, e y = conjA σ y := fun _ => rfl
  have hea : e (a : 𝔸[E]) = (a' : 𝔸[E]) := by
    rw [hcoe, conjA_apply, ha, ha', GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv,
      GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv, AlgEquiv.symm_apply_apply]
    rfl
  have key : ∀ y : 𝔸[E], a' • y = e (a • e y) := fun y => by
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcoe (_ * _), map_mul, ← hcoe, ← hcoe,
      hinv, hea]
  have hmeas : Measurable e := e.continuous.measurable
  have hm : Measurable (fun y : 𝔸[E] => a • y) := (Homeomorph.smul a).continuous.measurable
  have hνe : ν.map e = ν := map_involution_eq e hinv ν
  have hfun : (fun y : 𝔸[E] => a' • y) = e ∘ (fun y => a • y) ∘ e := funext key
  have h1 : ν.map (fun y : 𝔸[E] => a' • y) =
      ENNReal.ofReal ((IdeleGroup.ideleModule E a : ℝ))⁻¹ • ν := by
    rw [hfun, ← Measure.map_map hmeas (hm.comp hmeas), ← Measure.map_map hm hmeas, hνe, hν,
      map_smul_adeleMeasure, Measure.map_smul _ hmeas.aemeasurable, ← hν, hνe]
  have h2 := map_smul_adeleMeasure (K := E) a'
  rw [← hν, h1] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : 𝔸[E])
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have h3 := congrArg (fun m : Measure 𝔸[E] => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule E a).2.le)
    (inv_nonneg.2 (IdeleGroup.ideleModule E a').2.le)).1 h4
  exact (inv_injective h5).symm

end GlobalTheory.CompanionTheory.SW.ModConj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNeg
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusAdj

theorem conj_one_add {R : Type} [Ring R] (U A D Di : R) (h1 : D * Di = 1) (h2 : Di * D = 1) :
    D * (1 + (U - 1) * A) * Di = 1 + (D * U * Di - 1) * (D * A * Di) := by
  have k : D * U * Di * (D * A * Di) = D * (U * A) * Di := by
    calc D * U * Di * (D * A * Di) = D * U * (Di * D) * A * Di := by simp only [mul_assoc]
      _ = D * (U * A) * Di := by rw [h2]; simp only [mul_one, mul_assoc]
  calc D * (1 + (U - 1) * A) * Di = D * Di + (D * (U * A) * Di - D * A * Di) := by noncomm_ring
    _ = 1 + (D * U * Di * (D * A * Di) - D * A * Di) := by rw [h1, k]
    _ = 1 + (D * U * Di - 1) * (D * A * Di) := by noncomm_ring

theorem map_det_adj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (A u t D Di : Matrix (Fin n) (Fin n) R)
    (h1 : D * Di = 1) (h2 : Di * D = 1) (hS : D * (u.map σ)ᵀ * Di = t) :
    σ (1 + A * (u - 1)).det = (1 + (t - 1) * (D * (A.map σ)ᵀ * Di)).det := by
  have e1 : (σ.mapMatrix (1 + A * (u - 1)))ᵀ = 1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ := by
    rw [map_add (f := _), map_mul, map_sub, map_one, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one]
    rfl
  have e2 : (D * (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ) * Di).det = (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm D.det, mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]
  rw [RingHom.map_det, ← Matrix.det_transpose, e1, ← e2, conj_one_add _ _ _ _ h1 h2, hS]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adj_rm (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) :
    rm d.val * ((rm e).map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = rm (sg d e) := by
  have h : ((rm e).map (conjAd E))ᵀ = rm (e.map (conjE E))ᵀ := by
    ext i j
    simp [rm, conjAd_algebraMap]
    rfl
  rw [h, sg, rm_mul, rm_mul]

theorem adj_inv (d : GL (Fin n) E) (t : GA E n) (ht : t ∈ adCent d) :
    rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = t.val := by
  have h : t⁻¹ * ratGL E n d * thetaA E n t = ratGL E n d := ht
  have hv : (t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ = rm d.val :=
    congrArg Units.val h
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  calc rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val
      = t.val * ((t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ) *
          rm (d⁻¹ : GL (Fin n) E).val := by
        simp only [← mul_assoc, Units.mul_inv, one_mul]
    _ = t.val := by rw [hv, mul_assoc, h1, mul_one]

theorem chi_sg (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) (t : GA E n) (ht : t ∈ adCent d)
    (hc : t.val * rm (sg d e) = rm (sg d e) * t.val) : chi (sg d e) t = conjAd E (chi e t⁻¹) := by
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  have h2 : rm (d⁻¹ : GL (Fin n) E).val * rm d.val = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  have hcom : (t.val - 1) * rm (sg d e) = rm (sg d e) * (t.val - 1) := by
    rw [sub_mul, mul_sub, hc, one_mul, mul_one]
  rw [chi, chi, map_det_adj (conjAd E) (rm e) _ t.val _ _ h1 h2 (adj_inv d t ht), adj_rm, hcom]

theorem lam_sg (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E)
    (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t ∈ adCent d)
    (h1 : t.val * rm e = rm e * t.val) (h2 : t.val * rm (sg d e) = rm (sg d e) * t.val) :
    lam (sg d e) t = - lam e t := by
  rw [← lam_inv e he t h1, lam, lam, chi_sg d e t ht h2]
  exact GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces _

end GlobalTheory.CompanionTheory.TorusAdj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePreservedCofinitelyByUnit
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

theorem eventually_cV_mul_mem_latV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (y : (AF F ⊗[F] E)ˣ), ∀ᶠ v in cofinite, ∀ Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E, (fun a i => cV v (y : AF F ⊗[F] E) * Y a i) ∈ latV b v ↔ Y ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b y
  have e1 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => (y : AF F ⊗[F] E)))
  have e2 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)))
  filter_upwards [e1, e2, GlobalTheory.CompanionTheory.SW.LatFix.eventually_mul_closed b] with v h1 h2 h3 Y
  have c1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v (y : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F := fun k => h1 0 0 k
  have c2 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F :=
    fun k => h2 0 0 k
  have hone : cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * cV v (y : AF F ⊗[F] E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  constructor
  · intro hY a i k
    have h := h3 _ _ c2 (hY a i) k
    rwa [← mul_assoc, hone, one_mul] at h
  · intro hY a i k
    exact h3 _ _ c1 (hY a i) k

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingByUnit
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.Haar

theorem nnnorm_eq_distribHaarChar (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : (Fv F v)ˣ) :
    ‖(n : Fv F v)‖₊ = distribHaarChar (Fv F v) n := by
  have hn : (n : Fv F v) ≠ 0 := n.ne_zero
  have hva : Valued.v (n : Fv F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hn
  have h := PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v (n : Fv F v) hn
  rw [PI.NglqJacSplitW.modF, dite_eq_right hn] at h
  have hu : Units.mk0 (n : Fv F v) hn = n := by ext; rfl
  rw [hu] at h
  have habs : PI.LocJacTyp.absV v (n : Fv F v) = ‖(n : Fv F v)‖ := by
    unfold PI.LocJacTyp.absV
    rw [dite_eq_right hva, NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hva]
    push_cast
    rw [WithZero.toAdd_unzero_eq_log]
  rw [habs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal] at h
  exact (ENNReal.coe_injective h).symm

theorem map_mul_left (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hl : lam.IsAddHaarMeasure) (n : (Fv F v)ˣ) :
    lam.map (fun t => (n : Fv F v) * t) = (‖(n : Fv F v)‖₊)⁻¹ • lam := by
  have : SecondCountableTopology (Fv F v) := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  have : lam.Regular := inferInstance
  have hc : Continuous fun t : Fv F v => (n : Fv F v) * t := continuous_const.mul continuous_id
  ext S hS
  rw [Measure.map_apply hc.measurable hS, nnnorm_eq_distribHaarChar, ← map_inv]
  have hset : (fun t : Fv F v => (n : Fv F v) * t) ⁻¹' S = n⁻¹ • S := by
    ext y
    rw [Set.mem_inv_smul_set_iff]
    rfl
  rw [hset, ← distribHaarChar_mul lam n⁻¹ S]
  rfl

end GlobalTheory.CompanionTheory.Haar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingTensorUnits
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale

open GlobalTheory.CompanionTheory.SW.WBox (cK eW)

theorem map_eq_of_conj {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m s : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0) (hs : ∀ x, s (s x) = x)
    (h : ν.map (fun x => s (m (s (m x)))) = (c * c) • ν) : ν.map m = c • ν :=
  _root_.UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj m s ν c hs h

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem cK_tmul_mul' (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

end Coord

theorem pi_map_mul {R ι : Type} [Fintype ι] [CommRing R] [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (f : R → R) (hf : Measurable f) (c : ℝ≥0) (h : lam.map f = c • lam) :
    (Measure.pi fun _ : ι => lam).map (fun t i => f (t i)) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam := by
  haveI : SigmaFinite (lam.map f) := by rw [h]; infer_instance
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  refine Measure.pi_eq fun s hs => ?_
  simp only [h, Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z with
  | add x y hx hy => simp [hx, hy]
  | tmul r e => simp [sigR, hσ]

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

def mulT {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (u : Sˣ) :
    (Fin 1 → Fin 1 → S) ≃ₜ+ (Fin 1 → Fin 1 → S) where
  toFun X a i := (u : S) * X a i
  invFun X a i := ((u⁻¹ : Sˣ) : S) * X a i
  left_inv X := by
    funext a i
    exact Units.inv_mul_cancel_left u _
  right_inv X := by
    funext a i
    exact Units.mul_inv_cancel_left u _
  map_add' X Y := by
    funext a i
    exact mul_add _ _ _
  continuous_toFun := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul (continuous_apply_apply a i)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul (continuous_apply_apply a i)

def sigT {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (f : S →+* S) (hf : Continuous f)
    (hff : ∀ x, f (f x) = x) : (Fin 1 → Fin 1 → S) ≃ₜ+ (Fin 1 → Fin 1 → S) where
  toFun X a i := f (X a i)
  invFun X a i := f (X a i)
  left_inv X := by
    funext a i
    exact hff _
  right_inv X := by
    funext a i
    exact hff _
  map_add' X Y := by
    funext a i
    exact map_add f _ _
  continuous_toFun := continuous_pi fun a => continuous_pi fun i =>
    hf.comp (continuous_apply_apply a i)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    hf.comp (continuous_apply_apply a i)

theorem map_coordW_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ (y : (R ⊗[F] E)ˣ) (n : Rˣ) (c : ℝ≥0), (n : R) ⊗ₜ[F] (1 : E) = sigR R σ y * y → lam.map (fun t => (n : R) * t) = c • lam → (coordW R b lam 1 1).map (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => (y : R ⊗[F] E) * X a i) = c • coordW R b lam 1 1 := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR d b lam hlam y n c hn hc
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨iTR, iLC, iSC, iT2, hsc, -, hK', hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI := hB 1 1
  haveI := hlam
  have hK : IsHomeomorph (cK (F := F) (E := E) R b) := hK' 2 b
  haveI hν : (coordW R b lam 1 1).IsAddHaarMeasure :=
    (_root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R 2 b lam hlam).2.1 1 1
  have hinv := sigR_sigR R σ (conj_conj σ hcm)
  set π : Measure (Fin 1 × Fin 1 × Fin 2 → R) := Measure.pi fun _ => lam with hπ
  have hmp := GlobalTheory.CompanionTheory.SW.WBox.map_coordW R hK lam 1 1
  have hf : Measurable (fun t : R => (n : R) * t) := (continuous_const.mul continuous_id).measurable
  have hTm : Measurable (fun (t : Fin 1 × Fin 1 × Fin 2 → R) i => (n : R) * t i) :=
    Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)
  have hT : π.map (fun t i => (n : R) * t i) = (c * c) • π := by
    have h1 := pi_map_mul (ι := Fin 1 × Fin 1 × Fin 2) lam _ hf c hc
    have e : c ^ Fintype.card (Fin 1 × Fin 1 × Fin 2) = c * c := by
      simp [pow_two]
    rw [e] at h1
    exact h1
  have hνπ : coordW R b lam 1 1 = π.map (eW R hK 1 1).symm := by
    rw [hπ, ← hmp.map_eq, Measure.map_map (eW R hK 1 1).symm.measurable (eW R hK 1 1).measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id]
  have hNc : Continuous (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  have hNm := hNc.measurable
  have hcomm : (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) ∘ (eW R hK 1 1).symm =
      (eW R hK 1 1).symm ∘ (fun t i => (n : R) * t i) := by
    funext t
    apply (eW R hK 1 1).injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    funext p
    have h1 := congrFun ((eW R hK 1 1).apply_symm_apply t) p
    rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply] at h1
    rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply, cK_tmul_mul', h1]
  have hN : (coordW R b lam 1 1).map
      (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) =
      (c * c) • coordW R b lam 1 1 := by
    calc _ = (π.map (eW R hK 1 1).symm).map
            (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) := by rw [← hνπ]
      _ = π.map ((eW R hK 1 1).symm ∘ (fun t i => (n : R) * t i)) := by
          rw [Measure.map_map hNm (eW R hK 1 1).symm.measurable, hcomm]
      _ = (π.map (fun t i => (n : R) * t i)).map (eW R hK 1 1).symm := by
          rw [Measure.map_map (eW R hK 1 1).symm.measurable hTm]
      _ = _ := by
          rw [hT, Measure.map_smul, ← hνπ]
          exact (eW R hK 1 1).symm.measurable.aemeasurable
  refine map_eq_of_conj (mulT y) (sigT (sigR R σ) hsc hinv) _ c (fun X => ?_) ?_
  · funext a i
    exact hinv _
  · have e : (fun X => sigT (sigR R σ) hsc hinv (mulT y (sigT (sigR R σ) hsc hinv (mulT y X)))) =
        (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) := by
      funext X a i
      change sigR R σ ((y : R ⊗[F] E) * sigR R σ ((y : R ⊗[F] E) * X a i)) = _
      rw [map_mul, hinv, hn, mul_assoc]
    rw [e, hN]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedSizeRatGLMul
section
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.Desc
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele diagUnits)
open scoped ENNReal
attribute [local instance] borelH

noncomputable section
namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.CompanionTheory.PiVec
end
end

