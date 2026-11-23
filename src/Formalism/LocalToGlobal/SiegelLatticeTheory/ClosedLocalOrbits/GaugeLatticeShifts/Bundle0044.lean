module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0043

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeAR
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut Formalism.L2.SG.Pf.BridgeRat

namespace Formalism.L2.SG.Pf.BridgeAR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_of_coprime {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {c : ℕ}
    (hc : Nat.Coprime c X.B.g) (hZ : ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t)) :
    ZMod' X.B.I X.B.g t := by
  obtain ⟨s, hs, hcs⟩ := hZ
  have hb := Nat.gcd_eq_gcd_ab c X.B.g
  rw [hc.gcd_eq_one, Nat.cast_one] at hb
  have hb' : (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    have h1 := congrArg (Int.cast : ℤ → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hb
    push_cast at h1
    exact h1
  refine ⟨(Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s +
    (Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t, ?_, ?_⟩
  · exact (IntAf X.B.I.F X.B.I.E).add_mem
      ((IntAf X.B.I.F X.B.I.E).mul_mem (intCast_mem _ _) hs)
      ((IntAf X.B.I.F X.B.I.E).mul_mem (intCast_mem _ _) ht)
  · calc t = 1 * t := (one_mul t).symm
      _ = ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) * (Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
            ((Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) := by
        rw [hb']
        ring
      _ = _ := by
        rw [hcs]
        ring

end Formalism.L2.SG.Pf.BridgeAR

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BridgeAR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaBridgeARC_holds : IotaBridgeARC := by
  intro D X Y u Λ hΛ β b hb hK hN hT x hx
  set A : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u with hAdef
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf := fun y => by
    have := (Y.cs u).lat_eq ((Y.cs u).base Λ) y
    rw [hbl] at this
    exact this
  have hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)) := fun a => by
    unfold hat
    exact fixes_inv X (fixes_mul X (((Y.cs u).h ((Y.cs u).base Λ)).2 _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      ((X.xu_fix u a).1))
  have hTF : ∀ a, (X.Fu u).e a = X.eX a := (Formalism.L2.SG.Full.Full.frameTie (X := X) u u).1
  have hFC : IsFixedConv Λ (gS D) (lf D (X.Fu u)) := ((Y.rowsOK u).1 Λ hΛ).2.1.2.2.2
  refine ratFromAd X A hlat hfixE hFC hTF ?_
  rw [hat_sub, hat_ratLink X A hb, show X.B.I.fmat (A⁻¹ * b.2 * A) *ᵥ hat X A x - hat X A x =
    (X.B.I.fmat (A⁻¹ * b.2 * A) - 1) *ᵥ hat X A x by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
  have hxΛ : x ∈ Λ := hx.1
  have hw : hat X A x ∈ X.B.I.Lf := (hlat x).1 hxΛ
  refine Formalism.L2.SG.Pf.BridgeAd.adFull_of_adTriv Y.TR hK hN hT hw (fun a => ?_)

  have hxo : x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := hx.2
  have h0 : (VS D).hT (X.eX a) x = 0 := by
    have hmem : X.eX a ∈ Xsp (lf D (X.Fu u)) := by
      rw [← hTF a]
      exact Submodule.subset_span ⟨a, rfl⟩
    have := (Submodule.mem_iInf _).1 hxo (X.eX a)
    exact (Submodule.mem_iInf _).1 this hmem
  have hE0 : hA X.B.I (incl X.B.I (X.crd (X.eX a))) (hat X A x) = 0 := by
    rw [← hfixE a, hA_hat, h0, map_zero, map_zero]
  obtain ⟨c, hc, hcd⟩ := (X.basisApprox a).1
  have hint : hA X.B.I (X.e0 a) (hat X A x) ∈ IntAf X.B.I.F X.B.I.E := hA_int X.B.I (X.vectorsInLattice.1 a).1 hw
  refine Z_of_coprime X hint hc ?_
  have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 a) (hat X A x) =
      hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.crd (X.eX a)))) (hat X A x) := by
    rw [hA_smul_left, hA_sub_left, hE0, sub_zero, map_natCast]
  rw [e]
  exact Z_hA_mL X hcd hw

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ConjHSymmApply
section
noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

theorem HG_compact {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) :
    IsCompact (HG ε e p z : Set (UJ ε)) := by
  set Q : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε} ∩ ((⋂ a, {g | g *ᵥ e a = e a}) ∩
    ((⋂ a, {g | g *ᵥ p a = p a}) ∩ {g | g *ᵥ z = z})) with hQ
  have e1 : (HG ε e p z : Set (UJ ε)) = (fun g : UJ ε => Formalism.MainNotions.S.uMat g) ⁻¹' Q := by
    ext g
    simp only [coe_HG, HLoc, hQ, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨g.2, h.1, h.2.1, h.2.2⟩, fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩
  have hQc : IsClosed Q := by
    refine (isClosed_eq ((continuous_id.matrix_conjTranspose.mul continuous_const).mul continuous_id)
      continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
        continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
          continuous_const).inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)))
  have hzz : hJ ε z z ≠ 0 := by
    rw [Fw.zz]; exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 Fw.T_ne)
  have hQk : IsCompact Q := Formalism.L2.SG.Pf.frame_compact ε e p z w Fw.ee Fw.pp Fw.ep Fw.ez Fw.pz hzz Fw.ww Fw.ew Fw.pw
    Fw.zw hdim.symm hQc (fun g hg => ⟨hg.1, fun a => Set.mem_iInter.1 hg.2.1 a,
      fun a => Set.mem_iInter.1 hg.2.2.1 a, hg.2.2.2⟩)
  rw [e1]
  exact ((Formalism.REAL.uJEmb n ε).1).isCompact_preimage hQk

def conjH (h : UJ ε) : UJ ε ≃ₜ UJ ε := (Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)

theorem conjH_apply (h x : UJ ε) : conjH h x = h * x * h⁻¹ := rfl

section Conj

theorem map_conj_isHaarS {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε}
    (hh : h ∈ HG ε e p z) : IsHaarS (NLoc ε e z) (μ.map (conjH h)) := by
  obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hμ
  have hmeas : Measurable (conjH h) := (conjH h).continuous.measurable
  set E := (conjH h).toMeasurableEquiv with hE
  have hEe : ⇑E = ⇑(conjH h) := rfl
  refine ⟨⟨?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [← hEe]; exact E.sigmaFinite_map
  · intro h0
    apply hne
    have := congrArg (fun m : Measure (UJ ε) => m Set.univ) h0
    simp only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, FunLike.coe_zero,
      Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.1 this
  · rw [Measure.map_apply hmeas (show MeasurableSet (NLoc ε e z)ᶜ from (NG_closed ε e z).measurableSet.compl)]
    refine measure_mono_null (s := (conjH h) ⁻¹' (NLoc ε e z)ᶜ) (t := (NLoc ε e z)ᶜ)
      (fun x hx hxN => hx ?_) hcompl
    exact conj_mem ε e p z hh hxN
  · have ht' : h⁻¹ * t * h ∈ (NG ε e z) := by
      have := conj_mem ε e p z ((HG ε e p z).inv_mem hh) ht
      simpa using this
    have hcomm : (fun x => t * x) ∘ conjH h = conjH h ∘ (fun x => h⁻¹ * t * h * x) := by
      funext x; simp only [Function.comp_apply, conjH_apply]; group
    rw [Measure.map_map (measurable_const_mul t) hmeas, hcomm,
      ← Measure.map_map hmeas (measurable_const_mul _), hinv _ ht']
  · refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hmeas hK.measurableSet]
    have : (conjH h) ⁻¹' K = (conjH h).symm '' K := (congrFun (conjH h).image_symm K).symm
    rw [this]
    exact (hK.image (conjH h).symm.continuous).measure_lt_top

theorem conj_haar_eq {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k)
    {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε} (hh : h ∈ HG ε e p z) :
    μ.map (conjH h) = μ := by
  have : LocallyCompactSpace (NG ε e z) := (NG_closed ε e z).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (NG ε e z) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hNm : MeasurableSet ((NG ε e z) : Set (UJ ε)) := (NG_closed ε e z).measurableSet
  have memb : MeasurableEmbedding (Subtype.val : (NG ε e z) → UJ ε) := MeasurableEmbedding.subtype_coe hNm
  set m0 : Measure (UJ ε) := (Measure.haar : Measure (NG ε e z)).map Subtype.val with hm0

  have huniq : ∀ ν : Measure (UJ ε), IsHaarS (NLoc ε e z) ν → ∃ c : ℝ≥0, ν = c • m0 := by
    intro ν hν
    obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hν
    set ν' : Measure (NG ε e z) := ν.comap Subtype.val with hν'
    have hrestr : ν.restrict ((NG ε e z) : Set (UJ ε)) = ν := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hcompl
    have hmapν : ν'.map Subtype.val = ν := by
      rw [hν', memb.map_comap, Subtype.range_coe, hrestr]
    have himg : ∀ (t : (NG ε e z)) (A : Set (NG ε e z)), Subtype.val '' ((fun x => t * x) ⁻¹' A) =
        (fun x => (t : UJ ε) * x) ⁻¹' (Subtype.val '' A) := by
      intro t A
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨t * y, hy, rfl⟩
      · rintro ⟨a, ha, hax⟩
        have hxS : x ∈ (NG ε e z) := by
          have : x = ((t⁻¹ * a : (NG ε e z)) : UJ ε) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hax]; group
          rw [this]; exact (t⁻¹ * a).2
        refine ⟨⟨x, hxS⟩, ?_, rfl⟩
        show t * ⟨x, hxS⟩ ∈ A
        have : t * ⟨x, hxS⟩ = a := Subtype.ext (by simpa using hax.symm)
        rw [this]; exact ha
    have hνinv : ν'.IsMulLeftInvariant := by
      refine ⟨fun t => ?_⟩
      ext A hA
      rw [Measure.map_apply (measurable_const_mul t) hA, hν', memb.comap_apply, memb.comap_apply, himg,
        ← Measure.map_apply (measurable_const_mul _) (memb.measurableSet_image.2 hA), hinv _ t.2]
    have hνfin : IsFiniteMeasureOnCompacts ν' := by
      refine ⟨fun K hK => ?_⟩
      rw [hν', memb.comap_apply]
      exact (hK.image continuous_subtype_val).measure_lt_top
    have hνeq : ν' = ν'.haarScalarFactor Measure.haar • Measure.haar :=
      Measure.isMulLeftInvariant_eq_smul ν' Measure.haar
    refine ⟨ν'.haarScalarFactor Measure.haar, ?_⟩
    conv_lhs => rw [← hmapν, hνeq]
    rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable]

  obtain ⟨C', hC'c, hC'n⟩ : ∃ C' : Set (NG ε e z), IsCompact C' ∧ C' ∈ 𝓝 (1 : (NG ε e z)) := by
    obtain ⟨C', h1, h2⟩ := exists_compact_mem_nhds (1 : (NG ε e z))
    exact ⟨C', h1, h2⟩
  have hC'pos : 0 < (Measure.haar : Measure (NG ε e z)) C' := Measure.measure_pos_of_mem_nhds _ hC'n
  set C : Set (UJ ε) := Subtype.val '' C' with hC
  have hHc := HG_compact Fw hdim
  set K : Set (UJ ε) := (fun q : UJ ε × UJ ε => q.1 * q.2 * q.1⁻¹) '' ((HG ε e p z : Set (UJ ε)) ×ˢ C) with hK
  have hKc : IsCompact K :=
    (hHc.prod (hC'c.image continuous_subtype_val)).image (by fun_prop)
  have hKN : K ⊆ ((NG ε e z) : Set (UJ ε)) := by
    rintro _ ⟨⟨h', x⟩, ⟨hh', ⟨x', _, rfl⟩⟩, rfl⟩
    exact conj_mem ε e p z hh' x'.2
  have hCK : C ⊆ K := fun x hx => ⟨(1, x), ⟨(HG ε e p z).one_mem, hx⟩, by simp⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hm0K : m0 K = (Measure.haar : Measure (NG ε e z)) (Subtype.val ⁻¹' K) := by
    rw [hm0, Measure.map_apply measurable_subtype_coe hKm]
  have hm0pos : 0 < m0 K := by
    rw [hm0K]
    refine lt_of_lt_of_le hC'pos (measure_mono ?_)
    intro x hx
    exact hCK ⟨x, hx, rfl⟩
  have hm0fin : m0 K < ⊤ := by
    rw [hm0K]
    exact ((NG_closed ε e z).isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top
  have hinvK : (conjH h) ⁻¹' K = K := by
    ext x
    constructor
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, hxe⟩
      refine ⟨(h⁻¹ * h', x'), ⟨(HG ε e p z).mul_mem ((HG ε e p z).inv_mem hh) hh', hx'⟩, ?_⟩
      have hxe' : h' * x' * h'⁻¹ = h * x * h⁻¹ := hxe
      show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = x
      rw [show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * x' * h'⁻¹) * h by group, hxe']
      group
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, rfl⟩
      refine ⟨(h * h', x'), ⟨(HG ε e p z).mul_mem hh hh', hx'⟩, ?_⟩
      simp only [conjH_apply]
      group

  obtain ⟨c1, h1⟩ := huniq μ hμ
  obtain ⟨c2, h2⟩ := huniq _ (map_conj_isHaarS hμ hh)
  have hK12 : (μ.map (conjH h)) K = μ K := by
    rw [Measure.map_apply (conjH h).continuous.measurable hKm, hinvK]
  have hc : (c2 : ℝ≥0∞) = c1 := by
    have e2 : (μ.map (conjH h)) K = c2 * m0 K := by
      conv_lhs => rw [h2]
      rfl
    have e1 : μ K = c1 * m0 K := by
      conv_lhs => rw [h1]
      rfl
    rw [e2, e1] at hK12
    exact (ENNReal.mul_left_inj hm0pos.ne' hm0fin.ne).1 hK12
  rw [h2, h1]
  congr 1
  exact_mod_cast hc

end Conj

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrameLocX
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem frameLoc_X (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    FrameLoc (X.B.I.ε v) D.R.k (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
      (Tw u) (Tw u') := by
  refine
    { dim := (Formalism.L2.SG.Pf.card_frame X).symm
      k_pos := by have := D.R.m_add_three_le_k; omega
      sig := Formalism.L2.SG.PoincareInHH.Cut.card_eps_false X v
      e_li := ?_
      ee := fun a b => (hJ_X X v _ _).trans (by rw [X.ee]; simp)
      ez := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
      ez' := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u' a).1]; simp)
      zz := (hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
      zz' := (hJ_X X v _ _).trans (by rw [X.zu_norm u']; simp [Tw])
      T_pos := Tw_pos u
      T'_pos := Tw_pos u' }
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_fsum_r] at h
  have hfe : ∀ i, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR i)) = if i = j then 1 else 0 :=
    fun i => (hJ_X X v _ _).trans (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [h]
  unfold hJ
  simp

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolHinfPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem hinfConjC_holds : HinfConjC := by
  intro D X u h hh Ω hΩ
  obtain ⟨h1, hmul, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  let N : Subgroup X.B.I.Ginf :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.subOf (X.NinfU u) h1 (fun x hx y hy => (hmul x hx y hy).1) hinvN
  have hNc : IsClosed (N : Set X.B.I.Ginf) := Formalism.L2.SG.Pf.Vanish2.ninf_closed X.B.I X.eR (X.zR u)
  have hH : IsHaarOnSet X.B.I (N : Set X.B.I.Ginf) (X.muN u) := X.muN_haar u
  have hHa := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I N hNc (X.muN u) hH
  obtain ⟨_, h0, hc, hl⟩ := hH
  have hfin : IsFiniteMeasureOnCompacts (X.muN u) := ⟨hHa.2.1⟩
  have hconj : ∀ g ∈ Hinf X u, ∀ n ∈ X.NinfU u, g * n * g⁻¹ ∈ X.NinfU u := fun g hg n hn => by
    have hi : g⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hg
    have hfix : ∀ v, ∀ x ∈ fixSet X u, (uMat (g⁻¹ v)).mulVec (rv X.B.I v x) = rv X.B.I v x := hi
    have := Formalism.L2.SG.CovariantRepresentation.ninf_conj X u g⁻¹ (fun v a => hfix v _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      (fun v => hfix v _ (Or.inr rfl)) hn
    simpa using this
  have hcont : ∀ g : X.B.I.Ginf, Continuous fun s : X.B.I.Ginf => g * s * g⁻¹ := fun g =>
    (continuous_const.mul continuous_id).mul continuous_const

  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : X.B.I.Ginf)
  have hK0pos : 0 < X.muN u K0 := by
    have hpos := hHa.2.2 (interior K0) isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK0n, h1⟩
    exact lt_of_lt_of_le hpos (measure_mono interior_subset)
  let K : Set X.B.I.Ginf :=
    (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2 * p.1⁻¹) '' ((Hinf X u : Set X.B.I.Ginf) ×ˢ K0)
  have hKc : IsCompact K :=
    ((Formalism.L2.SG.Pf.hinf_compact X u).prod hK0c).image
      ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hK0K : K0 ⊆ K := fun k hk => ⟨(1, k), ⟨(Hinf X u).one_mem, hk⟩, by simp⟩
  have hKpos : 0 < X.muN u K := lt_of_lt_of_le hK0pos (measure_mono hK0K)
  have hKfin : X.muN u K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKinv : ∀ g ∈ Hinf X u, (fun s => g * s * g⁻¹) ⁻¹' K = K := by
    intro g hg
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g⁻¹ * a, k), ⟨(Hinf X u).mul_mem ((Hinf X u).inv_mem hg) ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = g * x * g⁻¹ := hx
      show g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = x
      calc g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = g⁻¹ * (a * k * a⁻¹) * g := by group
        _ = x := by rw [hx']; group
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g * a, k), ⟨(Hinf X u).mul_mem hg ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = x := hx
      show g * a * k * (g * a)⁻¹ = g * x * g⁻¹
      calc g * a * k * (g * a)⁻¹ = g * (a * k * a⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hx']

  have key : ∀ g ∈ Hinf X u, (X.muN u).map (fun s => g * s * g⁻¹) = X.muN u := by
    intro g hg
    have hm : Measurable fun s : X.B.I.Ginf => g * s * g⁻¹ := (hcont g).measurable
    have hpre : ∀ S : Set X.B.I.Ginf, (fun s => g * s * g⁻¹) ⁻¹' S = (fun s => g⁻¹ * s * g⁻¹⁻¹) '' S := by
      intro S
      exact (congrFun (Set.image_eq_preimage_of_inverse (f := fun s => g⁻¹ * s * g⁻¹⁻¹)
        (g := fun s => g * s * g⁻¹) (fun s => by show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s; group)
        (fun s => by show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s; group)) S).symm
    have hν0 : (X.muN u).map (fun s => g * s * g⁻¹) ≠ 0 := by
      intro hz
      apply h0
      have := congrArg (fun m : Measure X.B.I.Ginf => m Set.univ) hz
      simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    have hνc : (X.muN u).map (fun s => g * s * g⁻¹) (N : Set X.B.I.Ginf)ᶜ = 0 := by
      rw [Measure.map_apply hm hNc.measurableSet.compl]
      exact measure_mono_null (t := (N : Set X.B.I.Ginf)ᶜ) (fun ⦃s⦄ hs hsN => hs (hconj g hg s hsN)) hc
    have hνi : ∀ t ∈ N, ((X.muN u).map (fun s => g * s * g⁻¹)).map (fun x => t * x) =
        (X.muN u).map (fun s => g * s * g⁻¹) := by
      intro t ht
      have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ X.NinfU u := hconj g⁻¹ ((Hinf X u).inv_mem hg) t ht
      rw [Measure.map_map (measurable_const_mul t) hm]
      have e : (fun x => t * x) ∘ (fun s => g * s * g⁻¹) =
          (fun s => g * s * g⁻¹) ∘ (fun x => (g⁻¹ * t * g⁻¹⁻¹) * x) := by
        funext s
        show t * (g * s * g⁻¹) = g * (g⁻¹ * t * g⁻¹⁻¹ * s) * g⁻¹
        group
      rw [e, ← Measure.map_map hm (measurable_const_mul _), hl _ ht']
    have hνf : IsFiniteMeasureOnCompacts ((X.muN u).map (fun s => g * s * g⁻¹)) := ⟨fun C hC => by
      rw [Measure.map_apply hm hC.isClosed.measurableSet, hpre]
      exact (hC.image (hcont _)).measure_lt_top⟩
    obtain ⟨c, _, hceq⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique N hNc (X.muN u)
      ((X.muN u).map (fun s => g * s * g⁻¹)) h0 hc hl hfin hνc hνi hνf
    have hK' : (X.muN u).map (fun s => g * s * g⁻¹) K = X.muN u K := by
      rw [Measure.map_apply hm hKc.isClosed.measurableSet, hKinv g hg]
    rw [hceq, Measure.smul_apply, smul_eq_mul] at hK'
    have hc1 : c = 1 := (ENNReal.mul_left_inj hKpos.ne' hKfin).1 (hK'.trans (one_mul _).symm)
    rw [hceq, hc1, one_smul]
  have hinv' : h⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hh
  have e : (fun s => h * s * h⁻¹) '' Ω = (fun s => h⁻¹ * s * h⁻¹⁻¹) ⁻¹' Ω :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun s => h * s * h⁻¹) (g := fun s => h⁻¹ * s * h⁻¹⁻¹)
      (fun s => by show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s; group)
      (fun s => by show h * (h⁻¹ * s * h⁻¹⁻¹) * h⁻¹ = s; group)) Ω
  rw [e, ← Measure.map_apply (hcont _).measurable hΩ, key _ hinv']

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfSratZ
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

theorem rational_z_condition_holds : SratZC := by
  intro D X u' s σ hs hS
  obtain ⟨M, -, -, h2, h3⟩ := hs
  obtain ⟨-, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hS
  obtain ⟨-, hfz⟩ := hsf
  have hG : ∀ y, X.B.I.fmat s.2 *ᵥ Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I y =
      Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
    intro y
    rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply, h2]
    exact Formalism.L2.SG.Pf.Level.incl_mulVec X _ y
  have e := Formalism.L2.SG.Pf.Vanish2.tr_sub (Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I) _ _ hG (X.zR u')
  rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply] at e
  rw [e, ← Set.image_univ] at hfz
  have hd := Formalism.L2.SG.Pf.Level.descend X Set.univ _ hfz
  have hm : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.zR u' =
      X.crd (σ (X.zu u') - X.zu u') :=
    Formalism.L2.SG.Pf.Vanish2.mcrd X h3 (X.zu u')
  rw [hm] at hd
  have ht := Formalism.L2.SG.Pf.RegroupPf.StabFlagPf.toV_span X hd
  rw [Formalism.L2.SG.Pf.Level.toV_crd, Set.image_image] at ht
  have e2 : (fun b => Formalism.L2.SG.Pf.Level.toV X (X.eR b)) = X.eX :=
    funext fun b => Formalism.L2.SG.Pf.Level.toV_crd X (X.eX b)
  rw [e2] at ht
  have hXs : Xsp (lf D (X.Fu u')) = Submodule.span D.host.E (X.eX '' Set.univ) := by
    rw [Set.image_univ]
    show Submodule.span D.host.E (Set.range (X.Fu u').e) = _
    rw [X.Fu_e]
  rw [hXs]
  exact ht

end Formalism.L2.SG.Pf.SlabCount
end
end

