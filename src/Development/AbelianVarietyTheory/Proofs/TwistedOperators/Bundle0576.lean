module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  classical

  have join : ∀ t₁ t₂ : M₀ ⊗[ℂ] (⨂[ℂ] i, M i),
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ + t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
    rintro t₁ t₂ ⟨m₁, f₁, φ₁, rfl⟩ ⟨m₂, f₂, φ₂, rfl⟩
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r g =>
      refine ⟨1, fun _ => r • x, fun _ => g, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add]
      exact join _ _ h₁ h₂
  | add t₁ t₂ h₁ h₂ => exact join _ _ h₁ h₂

theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h

  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Bᵀ * M * B.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [B, Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hdet.symm

theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have hmap : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, hmap, h0, map_zero, mul_zero]

theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · have hc : Continuous fun z => χ z / χ' z := h.1.div' h'.1
    exact hc
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · exact div_one 1
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

end GlobalTheory.HoweGlobalPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CongAssemble

open Matrix

variable {D : D7}

theorem isIntM_of_smul_maps {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (s : Lev.EAf D) (M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (h : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, s • (M *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsIntM (s • ((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1)) := by
  intro i j
  have h1 := (hfr _).1 (h _ (GlobalTheory.FrameIdeal.col_mem_hatL hfr j)) i
  have e1 : (β⁻¹ : GL (Fin n) (Lev.EAf D)).1 *ᵥ (s • (M *ᵥ (β.1 *ᵥ Pi.single j 1))) =
      s • (((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1) *ᵥ Pi.single j 1) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, Matrix.mulVec_single_one] at h1
  simpa [Matrix.smul_apply] using h1


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cong_assemble : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  classical
  intro D V Λ hsd Z e hZe 𝔪 h𝔪 g hg hx
  obtain ⟨β, hfr⟩ := frame_exists_alt D.host.F D.host.E V.rank Λ
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hsd)
  have hUA := GlobalTheory.LevSplit.finE_mem_UA V g
  have hγ : (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * (Lev.finE V g).1 * β.1 := by
    simp only [Units.val_mul]
  have hγi : ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * ((Lev.finE V g)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * β.1 := by
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have h1 : IsIntM (toEAf D e • (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγ]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').1
  have h2 : IsIntM (toEAf D e • ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγi]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').2.1
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ β hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := _root_.GlobalTheory.IdemConjSum.idemSum_add_conj_idem Z e hZe
  obtain ⟨k, -, hmt⟩ := _root_.GlobalTheory.GfCut.exists_cut V (GlobalTheory.LevelNbhd.finPartG V g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC V g) hεε hεc
  have hfk := _root_.GlobalTheory.FineCut.finE_cut V β _ k (e + cA D e) hmt
  rw [GlobalTheory.SuppLevO.finE_finPartG] at hfk
  obtain ⟨hSt, -⟩ := _root_.GlobalTheory.FrameIdem.cut_mem_St_red V.rank β _ _ Z e hZe h1 h2 h3 h4 hfk
  have hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g := fun PP hP => by
    rw [← GlobalTheory.SuppLevO.proj_finPartG V g]
    exact _root_.GlobalTheory.CompIdem.projV_eq_of_idem V _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt
  have hkloc := (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hfr k).1 hSt
  have hgSt : Lev.finE V g ∈ Formalism.L2.DIV.St β := by
    refine (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hfr g).2 fun v => ?_
    by_cases hv : ∃ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
    · obtain ⟨PP, hP, rfl⟩ := hv
      rw [← hcomp PP hP]
      exact hkloc _
    · push_neg at hv
      exact hg v hv
  have hfw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr hgSt
  have hbw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr (inv_mem hgSt)

  have h𝔪0 : 𝔪 ≠ ⊥ := by
    intro h0
    haveI := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.E
    exact Set.infinite_univ (Z.finite_toSet.subset fun PP _ => h𝔪 PP (by rw [h0]; exact bot_le))
  have hrad : (∏ PP ∈ Z, PP.asIdeal) ≤ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪0 (le_bot_iff.1 (h ▸ hJ))
    have hQ := h𝔪 ⟨J, hJp, hJ0⟩ hJ
    calc (∏ PP ∈ Z, PP.asIdeal) = (∏ PP ∈ Z.erase ⟨J, hJp, hJ0⟩, PP.asIdeal) * J := (Finset.prod_erase_mul _ _ hQ).symm
      _ ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right | exact Ideal.mul_le_left'
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg 𝔪 (IsNoetherian.noetherian _)
  have hle : (∏ PP ∈ Z, PP.asIdeal ^ N) ≤ 𝔪 := by
    rw [Finset.prod_pow]
    exact (Ideal.pow_right_mono hrad N).trans hN
  obtain ⟨t, ht, htv⟩ := (GlobalTheory.IdemSumIdeal.isIdemSum_props e Z (fun _ => N) hZe).2.2
  refine GlobalTheory.ChiGrid.mem_congLev.2 ⟨hUA, fun x => ⟨fun hx' => hfw x hx', fun hx' => ?_⟩, fun x hx' => ?_⟩
  · have := hbw _ hx'
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  · have hw : (Lev.finE V g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := Submodule.sub_mem _ (hfw x hx') hx'
    have e1 : (Lev.finE V g).1 *ᵥ x - x = toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) +
        (1 - toEAf D e) • ((Lev.finE V g).1 *ᵥ x - x) := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [e1]
    refine Submodule.add_mem _ (hx x hx').2.2 ?_
    rw [← htv]
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) (GlobalTheory.FrameIdeal.idS_smul_mem_hatL Λ ht hw)

end GlobalTheory.CongAssemble
end
end

