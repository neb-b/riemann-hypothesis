module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DRDual

open GlobalTheory.DRFil

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def twistRep (χ : G →* LLˣ) (ρ : Representation LL G V) : Representation LL G V where
  toFun g := ((χ g : LLˣ) : LL) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem act_zpow (T : Fˣ) (hT : (T : F) = PD.ι PD.t) (n : ℤ) (g : G) :
    PD.actdR g ((T ^ n : Fˣ) : F) = ((PD.χ g ^ n : Qpˣ) : Qp) • ((T ^ n : Fˣ) : F) := by
  have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
    (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
  have h1 : Units.map (PD.actdR g : F →* F) T = Units.map (algebraMap Qp F : Qp →* F) (PD.χ g) * T := by
    ext
    have h2 := PD.ι_comm g PD.t
    rw [PD.t_act, hsm, ← hT, Algebra.smul_def] at h2
    exact h2.symm
  have h3 := congrArg (fun x : Fˣ => ((x ^ n : Fˣ) : F)) h1
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h3
  rw [Algebra.smul_def, ← map_zpow]
  exact h3

theorem twist_unit (ρ ρ' : Representation LL G V) (u : Fˣ) (n : ℤ) (ψ : G → Qpˣ)
    (hu : (u : F) ∈ PD.Fil n) (hu' : ((u⁻¹ : Fˣ) : F) ∈ PD.Fil (-n))
    (ha : ∀ g, PD.actdR g (u : F) = (ψ g : Qp) • (u : F))
    (ha' : ∀ g, PD.actdR g ((u⁻¹ : Fˣ) : F) = (((ψ g)⁻¹ : Qpˣ) : Qp) • ((u⁻¹ : Fˣ) : F))
    (hρ : ∀ g x, (ψ g : Qp) • ρ' g x = ρ g x) :
    (IsDR PD ρ → IsDR PD ρ') ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD ρ' τ (n + a) = multV PD ρ τ a := by
  have hρ' : ∀ g x, (((ψ g)⁻¹ : Qpˣ) : Qp) • ρ g x = ρ' g x := fun g x => by
    rw [← hρ, smul_smul, Units.inv_mul, one_smul]
  let Φ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V u ∘ₗ ext Qp F LinearMap.id
  let Ψ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V (u⁻¹ : Fˣ) ∘ₗ ext Qp F LinearMap.id
  have h1 : ∀ x, Φ (Ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v b => simp [Φ, Ψ]
  have h2 : ∀ x, Ψ (Φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v b => simp [Φ, Ψ]
  let E : V ⊗[Qp] F ≃ₗ[LL] V ⊗[Qp] F := LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2)
  have hD : (DdR PD ρ).map E.toLinearMap = DdR PD ρ' := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_DdR PD ρ ρ' LinearMap.id _ _ ha hρ hx
    · exact ⟨Ψ y, twist_mem_DdR PD ρ' ρ LinearMap.id _ _ ha' hρ' hy, h1 y⟩
  have hF : ∀ τ a, (FildR PD ρ τ a).map E.toLinearMap = FildR PD ρ' τ (n + a) := by
    intro τ a
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_FildR PD ρ ρ' LinearMap.id _ _ ha hρ τ hu hx
    · have := twist_mem_FildR PD ρ' ρ LinearMap.id _ _ ha' hρ' τ hu' hy
      rw [neg_add_cancel_left] at this
      exact ⟨Ψ y, this, h1 y⟩
  refine ⟨fun h => ?_, fun τ a => ?_⟩
  · rw [IsDR, ← hD, LinearEquiv.finrank_map_eq, h]
  · unfold multV
    rw [add_assoc, ← hF, ← hF, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

end Generic

theorem twisted_dual_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ), Function.Bijective m → (∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m j hm hg h
  have := K.2
  have := LL.2
  have := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have h₀ : IsDR (P.PD K) ρ₀ := isDR_of_spans T K LL ρ₀
    (spans_dual_of_spans (P.PD K) ρ ρ₀ m (isField_dR T) hβ hβ' (hs.spans _))
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨h1, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  refine ⟨h1 h₀, fun τ a _ => ?_⟩
  obtain ⟨n, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

end GlobalTheory.DRDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTauPowFrameAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalY

private theorem witt_padicInt_hom_ext (l : ℕ) [Fact l.Prime] {k : Type} [CommRing k] [CharP k l]
    (f g : ℤ_[l] →+* WittVector l k) : f = g := by
  refine RingHom.ext fun x => sub_eq_zero.1 (WittVector.ext fun n => ?_)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) x)
  have hx : x = (x.appr (n + 1) : ℤ_[l]) + y * (l : ℤ_[l]) ^ (n + 1) := by rw [hy]; ring
  have h : f x - g x = (f y - g y) * (l : WittVector l k) ^ (n + 1) := by
    rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.zero_coeff]
  exact WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self n)

theorem inclW_zA (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) : inclW l (Per.zA l z) = algebraMap ℤ_[l] (WCb l) z := by
  exact RingHom.congr_fun
    (witt_padicInt_hom_ext l ((inclW l).comp (Per.zA l)) (algebraMap ℤ_[l] (WCb l))) z

end GlobalTheory.BKLim.GalY


open GlobalTheory.BKLim.GalY in
theorem GlobalTheory.BKLim.gal_tauPow_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  intro l _ K bk τ N d ρ F Y hY g
  apply Matrix.map_injective (f := inclW l) (GlobalTheory.Prism.inclW_injective)
  have hsm : ∀ {m n : Type} (c : Ainf l) (M : Matrix m n (Ainf l)), (c • M).map (inclW l) = inclW l c • M.map (inclW l) :=
    fun c M => Matrix.ext fun i j => by simp
  have hz : ((ρ g).map (Per.zA l)).map (inclW l) = zW (ρ g) :=
    Matrix.ext fun i j => inclW_zA l _
  have hg' : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) :=
    Matrix.ext fun i j => (GlobalTheory.Prism.galW_inclW _ _).symm
  have hgal := F.gal g
  show Matrix.map _ (inclW l) = Matrix.map _ (inclW l)
  have hsg : ∀ (c : WCb l) (M : Matrix (Fin d) (Fin d) (WCb l)),
      (c • M).map (galW l (g : GQ l)) = galW l (g : GQ l) c • M.map (galW l (g : GQ l)) :=
    fun c M => Matrix.ext fun i j => by simp
  rw [hsm, hsm, Matrix.map_mul, Matrix.map_mul, hz, hg', hY, hsg, map_pow, map_pow, map_pow, GlobalTheory.Prism.galW_inclW,
    Matrix.mul_smul, hgal, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigit
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_radius (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := (gC_basic_values l ρ h0 h1).2.1
  have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
  rw [mul_zero, hl] at hm
  have : (1 - ρ) * gC l ρ 0 = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · linarith
  · exact h'

theorem gC_eq_zpow_mul_of_vr (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l) (hx : x ≠ 0) (hy : y ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r x - vr l r y = n * r) (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ x = ρ ^ n * gC l ρ y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  set r := -Real.logb l ρ with hr
  have hρr : (l : ℝ) ^ (-r) = ρ := by
    rw [hr, neg_neg, Real.rpow_logb hl0 hl1.ne' hρ]
  have hr0 : 0 < r := by
    have := Real.logb_neg hl1 hρ h1
    linarith
  have hr1 : r ≤ 1 := by
    have h := (Real.logb_le_logb hl1 (inv_pos.2 hl0) hρ).2 h0
    rw [Real.logb_inv, Real.logb_self_eq_one hl1] at h
    linarith
  have hv := hn r ⟨hr0, hr1⟩
  simp only [vr, hρr] at hv
  have hgx := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx ρ h0 h1
  have hgy := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l y hy ρ h0 h1
  apply Real.logb_injOn_pos hl1 hgx (Set.mem_Ioi.2 (mul_pos (zpow_pos hρ n) hgy))
  have hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ := by
    rw [Real.logb, Real.logb, Real.log_zpow, mul_div_assoc]
  rw [Real.logb_mul (zpow_pos hρ n).ne' hgy.ne', hz]
  rw [hr] at hv
  linarith

end GlobalTheory.PMon.Gauss

theorem GlobalTheory.PMon.Gauss.one_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  intro l _ h s hsh w w' hφh hw' hrat hg
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨ζ, o, ρ₀, ho, hζo, hζ0, hρ₀l, hρ₀1, hlt⟩ := _root_.GlobalTheory.GaussCancel.equal_gauss_cancel l w w' hw' hg
  have hζl : ζ ^ l = ζ := _root_.GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self l h s hsh w w' ζ o ρ₀ hφh hw' hrat hg ho hζo hζ0 hρ₀l.le hρ₀1 hlt
  obtain ⟨c, hcu, hc⟩ := GlobalTheory.PMon.Gauss.teichmuller_root_unity_eq_unit l ζ hζl hζ0
  refine ⟨c, hcu, fun ρ h0 h1 => ?_⟩
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  by_cases hw1 : w - zc l c * w' = 0
  · rw [hw1, gC_zero_of_radius l h0 h1]
    exact mul_nonneg hρ.le (hN.1 w').1
  have hφz : φc l (zc l c) = zc l c := by
    rw [hc, frob_teich, hζl]
  have hrat1 : φc l (w - zc l c * w') * w' = (w - zc l c * w') * φc l w' := by
    rw [map_sub, map_mul, hφz]
    linear_combination hrat
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul l h s hsh (w - zc l c * w') w' hφh hw1 hw' hrat1
  have hmono := gC_eq_zpow_mul_of_vr l _ w' hw1 hw' n hn
  have hρ₀ : 0 < ρ₀ := (inv_pos.2 hl0).trans hρ₀l
  have hn1 : 1 ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hle : n ≤ 0 := by omega
    have e := hmono ρ₀ hρ₀l.le hρ₀1
    rw [← hc] at hlt
    rw [e] at hlt
    have hg0 := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l w' hw' ρ₀ hρ₀l.le hρ₀1
    have : (1 : ℝ) ≤ ρ₀ ^ n := one_le_zpow_of_nonpos₀ hρ₀ hρ₀1.le hle
    nlinarith
  rw [hmono ρ h0 h1]
  have hle : ρ ^ n ≤ ρ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hρ h1.le hn1
  rw [zpow_one] at hle
  exact mul_le_mul_of_nonneg_right hle (hN.1 w').1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevCharacterGLnNormAndReciprocity
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.GGNorm

variable {g : ℕ} [Fact g.Prime]

theorem wh_formula (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) :
    wh ψ χ = ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
      ∑ u : Gn g n, (if IsUniUp (u : Mt g n) then
        (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0) * χ u := by
  unfold wh tr eU eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc]
  congr 2
  rw [Finset.sum_ite_eq']
  simp

theorem gg_term_inv (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (u : Gn g n) :
    (if IsUniUp ((u⁻¹ : Gn g n) : Mt g n) then
        ψ (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) else 0) =
      if IsUniUp (u : Mt g n) then (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0 := by
  by_cases hu : IsUniUp (u : Mt g n)
  · have hi := GlobalTheory.BadCount.Inh.isUniUp_inv u hu
    rw [if_pos hi, if_pos hu]
    have h := GlobalTheory.BadCount.Inh.sd_mul hi hu
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, GlobalTheory.BadCount.Inh.sd_one] at h
    have e : (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) =
        -(∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)) :=
      eq_neg_of_add_eq_zero_left h.symm
    rw [e, AddChar.map_neg_eq_inv]
  · have hi : ¬ IsUniUp ((u⁻¹ : Gn g n) : Mt g n) := fun h =>
      hu (by simpa using GlobalTheory.BadCount.Inh.isUniUp_inv u⁻¹ h)
    rw [if_neg hi, if_neg hu]

theorem ip_gg (ψ : AddChar (ZMod g) ℂ) (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    ip χ (gg ψ n) = wh ψ χ := by
  set c : ℂ := ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ with hc
  set F : Gn g n → ℂ := fun z => if IsUniUp (z : Mt g n) then
    ψ (∑ i ∈ Finset.range (n - 1), entN (z : Mt g n) i (i + 1)) else 0 with hF
  have hgg : ∀ x, gg ψ n x = c * ∑ y : Gn g n, F (y⁻¹ * x * y) := fun x => rfl
  have hinner : ∀ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) = ∑ u : Gn g n, χ u * F u⁻¹ := by
    intro y
    let e : Gn g n ≃ Gn g n :=
      ⟨fun x => y⁻¹ * x * y, fun u => y * u * y⁻¹, fun x => by group, fun u => by group⟩
    refine Fintype.sum_equiv e _ _ fun x => ?_
    have h1 : χ (y⁻¹ * x * y) = χ x := by
      have := hχ x y⁻¹
      rwa [inv_inv] at this
    have h2 : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    change χ x * F (y⁻¹ * x⁻¹ * y) = χ (y⁻¹ * x * y) * F (y⁻¹ * x * y)⁻¹
    rw [h1, h2]
  have hG : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∑ x : Gn g n, χ x * gg ψ n x⁻¹ = c * ∑ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) := by
    simp only [hgg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  have e2 : wh ψ χ = c * ∑ u : Gn g n, χ u * F u⁻¹ := by
    rw [wh_formula]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm]
    congr 1
    exact (gg_term_inv ψ u).symm
  unfold ip
  rw [e1, e2, Finset.sum_congr rfl fun y _ => hinner y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc c, inv_mul_cancel₀ hG, mul_one]

theorem wh_gg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) := by
  have h1 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ n
  have h2 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ (n - 1)
  rw [Nat.sub_add_cancel hn] at h2
  rw [Finset.sum_range_succ, h2] at h1
  linear_combination h1

theorem gg_norm : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) ∧
      ∀ χ : Gn g n → ℂ, IsClass χ → ip χ (gg ψ n) = wh ψ χ :=
  fun _ _ ψ hψ n hn => ⟨wh_gg ψ hψ n hn, fun χ hχ => ip_gg ψ n χ hχ⟩

end GlobalTheory.GLq.GGNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnits
section
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.LocUnitPow

variable {L : Type} [Field L] [NumberField L]

theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {z : v.adicCompletion L} (hz : Valued.v z = 1) (i : ℕ) :
    Valued.v (z ^ i - 1) ≤ Valued.v (z - 1) := by
  induction i with
  | zero => simp
  | succ m ih =>
    have e : z ^ (m + 1) - 1 = z ^ m * (z - 1) + (z ^ m - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ih
    rw [map_mul, map_pow, hz, one_pow, one_mul]

theorem val_pow_sub_one_step {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) {j : ℤ} (hj : Valued.v (z - 1) ≤ WithZero.exp (-j)) (hj1 : 1 ≤ j) :
    Valued.v (z ^ N - 1) ≤ WithZero.exp (-(j + 1)) := by
  have e : z ^ N - 1 = (z - 1) * ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) := by
    rw [← geom_sum_mul, Finset.sum_sub_distrib]
    simp [mul_comm]
  have hS : Valued.v ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
    refine Valuation.map_add_le _ ?_ hN
    refine Valuation.map_sum_le _ fun i _ => ?_
    exact (val_pow_sub_one_le hz i).trans (hj.trans (WithZero.exp_le_exp.mpr (by omega)))
  rw [e, map_mul]
  calc _ ≤ WithZero.exp (-j) * WithZero.exp (-1 : ℤ) := mul_le_mul' hj hS
    _ = _ := by rw [← WithZero.exp_add]; congr 1; ring

theorem val_pow_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) (hz1 : Valued.v (z - 1) ≤ WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (z ^ (N ^ k) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa using hz1
  | succ k ih =>
    rw [pow_succ, pow_mul]
    have hzk : Valued.v (z ^ N ^ k) = 1 := by rw [map_pow, hz, one_pow]
    have := val_pow_sub_one_step hN hzk ih (by omega)
    convert this using 3
    push_cast
    ring

theorem loc_pow_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  intro L _ _ χ v x hx
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hNdef
  have hN2 : 1 < N := Fintype.one_lt_card
  have hNv : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ) := by
    have hr : IsLocalRing.residue (v.adicCompletionIntegers L) (N : v.adicCompletionIntegers L) = 0 := by
      rw [map_natCast]; exact FiniteField.cast_card_eq_zero _
    rw [IsLocalRing.residue_eq_zero_iff] at hr
    have hlt : Valued.v (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hr
    have e : (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) = (N : v.adicCompletion L) := by
      push_cast; rfl
    rw [e] at hlt
    exact le_exp_neg_one' hlt
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  have e : (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) =
      (x : v.adicCompletion L) ^ (N - 1) - 1 := by
    push_cast; rfl
  rw [e] at hlt
  have hx1 := le_exp_neg_one' hlt
  have hz : Valued.v ((x : v.adicCompletion L) ^ (N - 1)) = 1 := by
    rw [map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  have key := val_pow_pow_sub_one_le hNv hz hx1 n
  refine ⟨(N - 1) * N ^ n, Nat.mul_pos (by omega) (pow_pos (by omega) _), ?_⟩
  rw [← map_pow]
  refine hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
  rw [Units.val_pow_eq_pow_val, pow_mul]
  exact key.trans (WithZero.exp_le_exp.mpr (by omega))

end GlobalTheory.LocUnitPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_dual_pairing_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ BD LA' := by
  first | exact @GlobalTheory.TateOrth.mem_BD_of_orthogonal | exact GlobalTheory.TateOrth.mem_BD_of_orthogonal | (intros; apply GlobalTheory.TateOrth.mem_BD_of_orthogonal <;> assumption)
end

