module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTransitiveAdelicUnitLengthVectors
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermVolumeRatioSameKindOfVolumeRatioInduction
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.VolRatio

section Congr

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

theorem fDeg_congr (e : K ≃+* L) : Formalism.HermitianLatticesTheory.fDeg K = Formalism.HermitianLatticesTheory.fDeg L := by
  unfold Formalism.HermitianLatticesTheory.fDeg
  refine Fintype.card_congr
    { toFun := fun w => w.comap (e.symm : L →+* K)
      invFun := fun w => w.comap (e : K →+* L)
      left_inv := fun w => ?_
      right_inv := fun w => ?_ }
  · ext x
    simp
  · ext x
    simp

theorem vInv_congr (e : K ≃+* L) : Formalism.HermitianLatticesTheory.vInv K = Formalism.HermitianLatticesTheory.vInv L := by
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [fDeg_congr e, NumberField.discr_eq_discr_of_ringEquiv K e]

variable [StarRing K] [StarRing L]

theorem conjIdeal_comap (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (P : Ideal (𝓞 L)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (P.comap (RingOfIntegers.mapRingEquiv e)) =
      (Formalism.HermitianLatticesTheory.conjIdeal (K := L) P).comap (RingOfIntegers.mapRingEquiv e) := by
  set g := RingOfIntegers.mapRingEquiv e with hg
  have hge : ∀ x : 𝓞 K, algebraMap (𝓞 L) L (g x) = e (algebraMap (𝓞 K) K x) := fun x => rfl
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  conv_rhs => rw [← Ideal.map_symm, Ideal.map_span]
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, hr⟩
    exact ⟨g r, ⟨g s, hs, by rw [hge, hge, hr, he]⟩, g.symm_apply_apply r⟩
  · rintro ⟨t, ⟨s, hs, ht⟩, rfl⟩
    refine ⟨g.symm s, by simpa only [Ideal.mem_comap, RingEquiv.apply_symm_apply] using hs, e.injective ?_⟩
    rw [he, ← hge, ← hge, g.apply_symm_apply, g.apply_symm_apply, ht]

theorem eulerFac_comap (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) (P : Ideal (𝓞 L)) :
    Formalism.HermitianLatticesTheory.eulerFac K M (P.comap (RingOfIntegers.mapRingEquiv e)) = Formalism.HermitianLatticesTheory.eulerFac L M P := by
  have hN : Ideal.absNorm (P.comap (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv _ P (RingOfIntegers.mapRingEquiv e)
      (Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective P).symm).toEquiv
  have hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (P.comap (RingOfIntegers.mapRingEquiv e)) =
      P.comap (RingOfIntegers.mapRingEquiv e) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P := by
    rw [conjIdeal_comap e he]
    exact (Ideal.comap_injective_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective).eq_iff
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [hN]
  by_cases h : Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P
  · rw [if_pos h, if_pos (hc.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.1 h'))]

theorem lValEta_congr (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) :
    Formalism.HermitianLatticesTheory.lValEta K M = Formalism.HermitianLatticesTheory.lValEta L M := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  let g := RingOfIntegers.mapRingEquiv e
  let φ : {P : Ideal (𝓞 L) // P.IsMaximal} ≃ {P : Ideal (𝓞 K) // P.IsMaximal} :=
    { toFun := fun P => ⟨P.1.comap g, by
        haveI := P.2
        exact Ideal.comap_isMaximal_of_surjective g g.surjective⟩
      invFun := fun P => ⟨P.1.comap g.symm, by
        haveI := P.2
        exact Ideal.comap_isMaximal_of_surjective g.symm g.symm.surjective⟩
      left_inv := fun P => by
        ext x
        simp only [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      right_inv := fun P => by
        ext x
        simp only [Ideal.mem_comap, RingEquiv.symm_apply_apply] }
  rw [← φ.tprod_eq]
  exact tprod_congr fun P => eulerFac_comap e he M P.1

theorem rankFac_congr (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) :
    rankFac K M = rankFac L M := by
  unfold rankFac
  rw [fDeg_congr e, vInv_congr e, lValEta_congr e he]

theorem eulerFac_nonneg (M : ℕ) (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    0 ≤ Formalism.HermitianLatticesTheory.eulerFac K M P := by
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs
  · have h2 : (1 : ℝ) ≤ Real.sqrt (Ideal.absNorm P : ℝ) := Real.one_le_sqrt.2 h1
    have h3 : Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ h2 (by omega)
    have h4 : 0 ≤ Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by positivity
    refine inv_nonneg.2 ?_
    rcases neg_one_pow_eq_or ℝ M with h | h <;> rw [h] <;> linarith
  · have h3 : (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ h1 (by omega)
    exact Real.rpow_nonneg (by linarith) _

theorem rankFac_nonneg (M : ℕ) : 0 ≤ rankFac K M := by
  have h : 0 ≤ Formalism.HermitianLatticesTheory.lValEta K M := tprod_nonneg fun P => eulerFac_nonneg M P.1 P.2
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  unfold rankFac
  positivity

end Congr

theorem volU_pos (i : ℕ) : 0 < volU i := by
  have : 0 < sphV i := by
    unfold sphV
    exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity
  unfold volU
  positivity

theorem ennreal_volume_ratio_step_cancel (X Y : ENNReal) (r a b ρ : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hρ : ρ * a = r * b)
    (h : X / ENNReal.ofReal a = Y / ENNReal.ofReal b * ENNReal.ofReal ρ) :
    X = Y * ENNReal.ofReal r := by
  have e2 : ρ = b * (r / a) := by field_simp; linarith
  rw [e2, ENNReal.ofReal_mul hb.le, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_div_of_pos ha, ← mul_div_assoc] at h
  have h0 := (ENNReal.ofReal_pos.2 ha).ne'
  rw [← ENNReal.div_mul_cancel (a := ENNReal.ofReal a) (b := X) h0 ENNReal.ofReal_ne_top, h,
    ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top]

theorem sameField_trans {I I' I'' : AutInst} (h : SameField I I') (h' : SameField I' I'') :
    SameField I I'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e'.trans e, fun x => by simp [he, he']⟩

theorem sameField_symm {I I' : AutInst} (h : SameField I I') : SameField I' I := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun x => e.injective ?_⟩
  simp [he]

theorem step (hstep : VolumeStep) (I : AutInst) (P Q : ℕ) (h : HasSig I P Q) (h3 : 3 ≤ P + Q) (s : Bool)
    (hs : if s then 1 ≤ P else 1 ≤ Q) :
    ∃ I' : AutInst, SameField I I' ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) ∧
      ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
        (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
        IsGaugeAll I c → IsGaugeAll I' c' →
        gaugeVol I c μf = gaugeVol I' c' μf' * ENNReal.ofReal (rankFac I.E (P + Q)) := by
  obtain ⟨hf, -, -, -, -, hpq⟩ := _root_.GlobalTheory.FlagMeas.instance_numbers I
  have hn := hpq P Q h
  obtain ⟨I', e, x, A, he, hn', -, -, -, hsig, hv⟩ := hstep I P Q h (by omega) s hs
  refine ⟨I', ⟨e, he⟩, hsig, ?_⟩
  intro c μf _ _ c' μf' _ _ hc hc'
  have hR := _root_.GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume I.E I.n (by omega)
  rw [hf, show I.n - 1 = I'.n by omega] at hR
  rw [hn]
  exact ennreal_volume_ratio_step_cancel _ _ _ _ _ _ (rankFac_nonneg _) (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hR
    (hv c μf c' μf' hc hc')

theorem volumeRatio_of_volumeStep : VolumeStep → VolumeRatio := by
  intro hstep I p q p₀ q₀ hsig hp hq h2
  induction' hd : (p - p₀) + (q - q₀) with d ih generalizing I p q
  · obtain rfl : p₀ = p := by omega
    obtain rfl : q₀ = q := by omega
    refine ⟨⟨I, ⟨RingEquiv.refl _, fun _ => rfl⟩, hsig⟩, ?_⟩
    intro I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀
    rw [Finset.Ioc_self, Finset.prod_empty, ENNReal.ofReal_one, mul_one]
    exact _root_.GlobalTheory.VolInvariant.volumeInvariant I I₀ _ _ hI hsig hsig₀ c μf c₀ μ₀ hc hc₀
  · obtain ⟨I', p', q', hI', hsig', hp', hq', hsum, hv⟩ : ∃ (I' : AutInst) (p' q' : ℕ), SameField I I' ∧
        HasSig I' p' q' ∧ p₀ ≤ p' ∧ q₀ ≤ q' ∧ p' + q' + 1 = p + q ∧
        ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
          (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
          IsGaugeAll I c → IsGaugeAll I' c' →
          gaugeVol I c μf = gaugeVol I' c' μf' * ENNReal.ofReal (rankFac I.E (p + q)) := by
      by_cases hpp : p₀ < p
      · obtain ⟨I', h1, h2, h3⟩ := step hstep I p q hsig (by omega) true (by simp; omega)
        exact ⟨I', p - 1, q, h1, h2, by omega, hq, by omega, h3⟩
      · obtain ⟨I', h1, h2, h3⟩ := step hstep I p q hsig (by omega) false (by simp; omega)
        exact ⟨I', p, q - 1, h1, h2, hp, by omega, by omega, h3⟩
    obtain ⟨⟨I₁, hI₁, hsig₁⟩, hrat⟩ := ih I' p' q' hsig' hp' hq' (by omega)
    refine ⟨⟨I₁, sameField_trans hI' hI₁, hsig₁⟩, ?_⟩
    intro I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀
    obtain ⟨μ', hH, hS⟩ := GlobalTheory.CongTop.exists_haar_sigmaFinite I'
    choose c' _ hc' _ using fun v : InfinitePlace I'.F => _root_.GlobalTheory.GaugeConst.gauge_exists_pos_unique I'.n (I'.ε v)
    have hg' : IsGaugeAll I' c' := hc'
    rw [hv c μf c' μ' hc hg', hrat I₀ (sameField_trans (sameField_symm hI') hI) hsig₀ c' μ' c₀ μ₀ hg' hc₀,
      ← hsum, Finset.prod_Ioc_succ_top (by omega),
      ENNReal.ofReal_mul (Finset.prod_nonneg fun M _ => rankFac_nonneg M), mul_assoc]
    obtain ⟨e, he⟩ := hI'
    simp only [rankFac_congr e he]

end GlobalTheory.FlagMeas.VolRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryFixingSpanPreservesGluedLattices
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueStable

theorem glueSet_gmap_mem : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M := by
  intro D U M g hg Λ hΛ
  obtain ⟨hgI, hgU⟩ := hg
  obtain ⟨hlat, huni, hcap⟩ := hΛ
  have H := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT g hgI Λ
  refine ⟨H.2.2.2.2.mpr hlat, H.2.2.2.1.mpr huni, ?_⟩
  rw [← hcap]
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e ▸ h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e : g.symm x = x := by
      conv_lhs => rw [← hgU x h2]
      simp
    exact ⟨e.symm ▸ h1, h2⟩

end GlobalTheory.GlueStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentChangedRationalFramesOfUnitrian
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

open Formalism.MainNotions.S.Loc

section General

theorem linInd_of_change {R W ι : Type} [CommRing R] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    {v w : ι → W} (B : Matrix ι ι R) (hB : IsUnit B.det) (hv : LinearIndependent R v)
    (hw : ∀ j, w j = ∑ i, B i j • v i) : LinearIndependent R w := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have h1 : ∑ i, (B.mulVec g) i • v i = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, hw, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 : B.mulVec g = 0 := funext (hv _ h1)
  have h3 : g = B⁻¹.mulVec (B.mulVec g) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  intro i
  rw [h3, h2, Matrix.mulVec_zero, Pi.zero_apply]

theorem isUnit_ringInverse_of_ne {R : Type} [CommRing R] {y : R} (h : Ring.inverse y ≠ 0) :
    IsUnit (Ring.inverse y) := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    rw [Ring.inverse_unit]
    exact Units.isUnit _
  · exact absurd (Ring.inverse_non_unit y hy) h

theorem det_uni_eq_one {K : Type} [CommRing K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Uni A) :
    A.det = 1 := by
  obtain ⟨hlow, hdiag⟩ := hA
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hlow i j hij)]
  simp [hdiag]

end General

section Main

variable {D : D7}

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨P, hne, hP⟩ :=
    Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField D.host.F)
  exact ⟨⟨P, hP, hne⟩⟩

private theorem linearIndependent_frameD_of_T_ne_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : LocNG.FrameD H r) (hT : Fr.T ≠ 0) : LinearIndependent E Fr.f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ y, H.h (∑ i, g i • Fr.f i) y = ∑ i, g i * H.h (Fr.f i) y := by
    intro y
    have hs : ∀ s : Finset (Fin (r + 1)),
        H.h (∑ i ∈ s, g i • Fr.f i) y = ∑ i ∈ s, g i * H.h (Fr.f i) y := by
      intro s
      refine Finset.induction_on s (by simp [H.h_zero_left]) ?_
      intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
    exact hs Finset.univ
  have hlast : g (Fin.last r) = 0 := by
    have hz := key (Fr.f (Fin.last r))
    rw [hg, H.h_zero_left, Fin.sum_univ_castSucc] at hz
    have hoff : ∀ i : Fin r, H.h (Fr.f i.castSucc) (Fr.f (Fin.last r)) = 0 :=
      fun i => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last i))
    simp only [hoff, mul_zero, Finset.sum_const_zero, zero_add, Fr.h_zz] at hz
    have hu : IsUnit (-(algebraMap F E Fr.T)) := ((Ne.isUnit hT).map (algebraMap F E)).neg
    exact hu.mul_left_eq_zero.1 hz.symm
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have he := key (Fr.es j)
  rw [hg, H.h_zero_left, Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at he
  simp only [Fr.h_es, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at he
  exact he.symm

theorem local_pair_linInd (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS)
    (hR : P.RelG (LocNG.theta (Z.M p))) :
    LinearIndependent (D.s.atP p).Ep (Sum.elim P.A.f P.B.f) := by
  obtain ⟨hX, -, -, -, -, -, hN⟩ := hR
  obtain ⟨-, hT, -, hT', -⟩ := hN
  exact LinearIndependent.sum_type (linearIndependent_frameD_of_T_ne_zero P.A hT) (linearIndependent_frameD_of_T_ne_zero P.B hT')
    (disjoint_iff.2 hX)

end Main

section Final

variable {D : D7}

theorem base_frames_linInd (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) :
    LinearIndependent D.host.E (Sum.elim (frame F) (frame F')) := by
  obtain ⟨p⟩ := exists_place D
  have hloc := local_pair_linInd Z p (FP p) (hR p)
  obtain ⟨hA, hA', -, -⟩ := hB p
  have hu : ∀ i, Sum.elim (FP p).A.f (FP p).B.f i =
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i • baseChange₂ D p (Sum.elim (frame F) (frame F') i) := by
    rintro (a | a)
    · simp only [Sum.elim_inl, hA]
    · simp only [Sum.elim_inr, hA']
  have hs : ∀ i, Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) *
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i = 1 := by
    intro i
    have hne : Sum.elim (frFac Z.δ p) (frFac Z.δ p) i ≠ 0 := by
      intro h0
      apply hloc.ne_zero i
      rw [hu i, h0, zero_smul]
    refine Ring.inverse_mul_cancel _ ?_
    rcases i with a | a
    · exact isUnit_ringInverse_of_ne hne
    · exact isUnit_ringInverse_of_ne hne
  rw [Fintype.linearIndependent_iff] at hloc ⊢
  intro g hg
  have h1 : ∑ i, ((D.s.atP p).ιE (g i) * Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i)) •
      Sum.elim (FP p).A.f (FP p).B.f i = 0 := by
    have hmap := congrArg (baseChange₂ D p) hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at hmap
    rw [← hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i, smul_smul, mul_assoc, hs i, mul_one, baseChange_smul₂]
  intro i
  have h2 := hloc _ h1 i
  have h3 : (D.s.atP p).ιE (g i) = 0 := by
    have h4 := congrArg (· * Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) h2
    simpa only [mul_assoc, hs i, mul_one, zero_mul] using h4
  exact (map_eq_zero_iff _ (D.s.atP p).ιE.injective).1 h3

theorem changed_frames_linInd : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  intro D Z FP Tn T'n F G F' G' hB hR hG hG'
  have hbase := base_frames_linInd Z FP Tn T'n F F' hB hR
  obtain ⟨A, hA, hcA⟩ := hG
  obtain ⟨A', hA', hcA'⟩ := hG'
  refine linInd_of_change (Matrix.fromBlocks A 0 0 A') ?_ hbase ?_
  · rw [Matrix.det_fromBlocks_zero₂₁, det_uni_eq_one hA, det_uni_eq_one hA', mul_one]
    exact isUnit_one
  · rintro (b | b)
    · simp only [Sum.elim_inl, Fintype.sum_sum_type, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      exact hcA b
    · simp only [Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
      exact hcA' b

end Final
end GlobalTheory.GenMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchingTranslateSameRowDoubleCoset
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgKey

theorem translate_key : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', ∀ s : TauC Y u u', s.lam = t₀.lam → s.lam' = t₀.lam' → (∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (a * t₀.lin * a'⁻¹) * n') → key s = key t := by
  intro D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  obtain ⟨hl, hl', a, ha, a', ha', K1⟩ := _root_.GlobalTheory.Unfold.CntC.translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  refine ⟨a, ha, a', ha', ?_⟩
  rintro s hs hs' ⟨n, hn, n', hn', hsl⟩
  rw [GlobalTheory.Unfold.KeyIff.key_eq_iff]
  refine ⟨hs.trans hl.symm, hs'.trans hl'.symm, ?_⟩
  rw [hs, hsl]
  have hI : ∀ {x y : GV D}, x ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      x * y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun hx hy => (Formalism.HermitianLatticesTheory.isom _).mul_mem hx hy
  have ht : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have htΛ : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have ha'i : a'⁻¹ ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := (GlobalTheory.KeyGroup.flagLatticeAutomorphismGroup _ _).inv_mem ha'
  have hγ : a * t₀.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI (hI ha.1.1 ht) ha'i.1.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹) t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, GlobalTheory.Unfold.Model.gmap_mul, ha'i.2, htΛ, ha.2]
  have hγn : a * t₀.lin * a'⁻¹ * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI hγ hn'.1.1
  have hγnΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹ * n') t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, hn'.1.2, hγΛ]
  have hs3 : n * (a * t₀.lin * a'⁻¹) * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    rw [mul_assoc]; exact hI hn.1.1 hγn
  have hs3Λ : Formalism.HermitianLatticesTheory.gmap (n * (a * t₀.lin * a'⁻¹) * n') t₀.lam' = t₀.lam := by
    rw [mul_assoc, GlobalTheory.Unfold.Model.gmap_mul, hγnΛ, hn.1.2]
  have K2 := GlobalTheory.KeyGroup.keyEq_right (F := lf D (X.Fu u)) (F0' := X.Fu u') hγ hγΛ hn'
  have K3 := GlobalTheory.KeyGroup.keyEq_left (F0' := X.Fu u') hγn hn
  rw [← mul_assoc] at K3
  have K4 := GlobalTheory.KeyGroup.keyEq_trans hγ hγn hγΛ hγnΛ K2 K3
  have K5 := GlobalTheory.KeyGroup.keyEq_symm hγ hs3 hγΛ hs3Λ K4
  exact GlobalTheory.KeyGroup.keyEq_trans hs3 hγ hs3Λ hγΛ K5 K1

end GlobalTheory.Unfold.TgKey
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTransitiveAdelicUnitLengthVectorsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_transitive_adelic_unit_length_vectors : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E) (xf g : I.Gf), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → x ∈ lamX I (1, xf) → x ∈ lamX I (1, g) → ∃ h : I.Gf, (I.fmat h *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∧ ∃ k ∈ I.Kset, g = h * xf * k := by
  first | exact @GlobalTheory.FinOrbit.exists_stab_mul_level | exact GlobalTheory.FinOrbit.exists_stab_mul_level | (intros; apply GlobalTheory.FinOrbit.exists_stab_mul_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
section
namespace GlobalTheory.St

theorem swxs_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.VolStabS.MassDataS.SWXS :=
  fun h _ X => GlobalTheory.St.siegelWeil_volumes h _ _ _ (MassDataVolumesW.stepCM X) _ _ (MassDataVolumesW.stepHerm X)

end GlobalTheory.St
end

