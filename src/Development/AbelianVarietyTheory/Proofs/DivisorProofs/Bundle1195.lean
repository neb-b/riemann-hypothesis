module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsSplitCentreExponentLeOfConjMemCompact
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CentralExponent

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.UnitaryBC

theorem abs_le_of_conj_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a),
      g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  intro E _ _ _ a ha W hW
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have hc : Continuous fun x : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det x)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊, fun γ n g hmem => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have e : GeneralLinearGroup.det (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g) =
      diag E (GeneralLinearGroup.det γ) * eIdele E ^ ((a : ℤ) * n) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm _ (GeneralLinearGroup.det g), mul_inv_cancel_left]
  have key : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g))) =
      ((a : ℤ) * n : ℤ) * Real.log (ideleNorm (E := E) (eIdele E)) := by
    rw [e, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul, map_zpow,
      Real.log_zpow]
  have h1 := hC _ hmem
  rw [key, Real.norm_eq_abs, abs_mul, abs_of_pos hL] at h1
  have h2 : (|n| : ℝ) ≤ |(((a : ℤ) * n : ℤ) : ℝ)| := by
    push_cast
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast ha)
  have h3 : (|n| : ℝ) ≤ ⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊ :=
    (h2.trans ((le_div_iff₀ hL).2 h1)).trans (Nat.le_ceil _)
  exact_mod_cast h3

end GlobalTheory.CentralExponent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAbsDetMulArchimedeanExpScalarCurve
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem expCurve_eq_diagUnits (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ) :
    expCurve E a t = GroundTheory.Automorphic.Reduction.diagUnits a
      (fun _ : Fin a => GroundTheory.Automorphic.Reduction.posIdele (K := E) (Real.exp t) (Real.exp_pos t)) := by
  rw [GlobalTheory.CuspBoundSiegel.posIdele_exp]
  have e : t • (1 : Cinf E) = fun _ => (t : ℂ) := by
    funext w; simp
  unfold expCurve
  rw [e]
  refine Units.ext ?_
  rw [GroundTheory.Automorphic.Reduction.coe_diagUnits]
  rfl

theorem absDetA_mul_expCurve (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g : GA E a) (t : ℝ) :
    absDetA (g * expCurve E a t) = absDetA g * Real.exp (t * (a * Module.finrank ℚ E)) := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E),
    map_mul, map_mul, Positive.val_mul, expCurve_eq_diagUnits, GlobalTheory.CuspBoundSiegel.ideleModule_det_diagUnits_posIdele,
    ← Real.exp_nat_mul]
  congr 2
  push_cast; ring

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.SubPull

theorem app_injective_of_frames {X : Scheme.{0}} {F E : X.Modules} (φ : F ⟶ E) {U V : X.Opens}
    {ι κ : Type} [Fintype ι] [Fintype κ] {e : ι → Γ(F, U)} {b : ι ⊕ κ → Γ(E, U)}
    (he : IsFrame e) (hb : IsFrame b) (hφ : ∀ j, φ.app U (e j) = b (.inl j)) (h : V ≤ U) :
    Function.Injective (φ.app V) := by
  have li : LinearIndependent Γ(X, V) (appLinear φ V ∘ he.basis h) := by
    have := (hb.basis h).linearIndependent.comp Sum.inl Sum.inl_injective
    convert this using 1
    funext j
    simp only [Function.comp_apply, IsFrame.basis_apply, appLinear_apply, app_resM, hφ]
  have : Function.Injective (appLinear φ V) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h0 := Fintype.linearIndependent_iff.1 li ((he.basis h).repr x) (by
      rw [← hx]
      conv_rhs => rw [← (he.basis h).sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Function.comp_apply])
    exact (he.basis h).ext_elem fun j => by simp [h0 j]
  exact this

theorem isSubbundle_pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (F E : X.Modules) (i : F ⟶ E) (r : ℕ), IsVB F r → IsSubbundle i → IsSubbundle ((Scheme.Modules.pullback f).map i) := by
  intro X Y f F E i r hF ⟨hm, s, hs⟩
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  refine ⟨QCoh.mono_of_locally_app_injective _ fun W y hy => ?_, s,
    (hs.pullback f).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback f) i)⟩
  have h₁ : SheafOfModules.IsQuasicoherent
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).X₁ := hF.isQuasicoherent
  have h₂ : SheafOfModules.IsQuasicoherent
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).X₂ :=
    (VBExt.isVB_and_cls_det_of_shortExact X _ r s hS hF hs).1.isQuasicoherent
  obtain ⟨c, hc⟩ := VBExt.exists_adaptedChart hS hF hs (f y)
  refine ⟨W ⊓ f ⁻¹ᵁ c.U, ⟨hy, hc⟩, inf_le_left, ?_⟩
  exact app_injective_of_frames _ (c.he.pullback f)
    ((VBExt.isFrame_sumElim hS c.he c.ht).pullback f)
    (fun j => QCoh.pullback_map_app_pullbackSections f i _ _) inf_le_right

end GlobalTheory.SubPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_tendsto_of_rep : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a b M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a) (m * b) (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + ((D + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS hC k _ X _ p D hX P a b M α t₀ hRep hα hN t ht
  have hNt := _root_.GlobalTheory.NefShift.isNef_shift_mono hC k X p D hX M t₀ t ht hN
  have hSt := hC.arShift k X p D hX M α t hα
  have hT := GlobalTheory.Published.ArithHilbertSamuel.tendsto_of_triv hHS hX hNt hSt
  have hF : ((D + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 := hT.div_const ((D + 1).factorial : ℝ)
  have e (m : ℕ) : P.lc (m * a) (m * b) (Real.exp (t * m)) =
      Real.log ((((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.ncard : ℝ)) := by
    rw [Pair.lc, Set.ncard_def, Set.ncard_def, (_root_.GlobalTheory.VolBr.SmallBall.main k X p P a b M hRep t m).1]
  convert (preTransparency := .reducible) h2 using 1
  · funext m
    rw [e]
    field_simp
  · field_simp

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection
section
namespace GlobalTheory.Published

theorem arCalc_of_form_mix_projection : ArFormExists → ArMix → HeightProjection → ArCalc := fun hF hM hP =>
  have hE : ArExists := _root_.GlobalTheory.Published.arExists_of_form_of_mix hF hM
  have hC : ArChange := arChange_of_arMix hE hM
  ⟨hE, hC, _root_.GlobalTheory.Published.arShift_of_arChange hE hC, hM, GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula hP, arIso_holds, _root_.GlobalTheory.Published.arMetric_of_arMix hE hM⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem encard_mul_le_at_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ),
    (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤
      {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  intro k _ X _ p D hX P b s t hg N m hfin

  have hnu : ∀ (a c : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a c σ y f := by
    intro a c σ y f
    unfold Pair.nu
    positivity
  have hs0 : s ^ m ≠ 0 := pow_ne_zero _ hg.s_ne

  obtain ⟨hsH, hsnu⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P 0 1 s hg.s_mem.1 m
  obtain ⟨htH, htnu⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (-1) b t hg.t_mem.1 N
  have hsle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑m * 0) (↑m * 1) σ y (s ^ m) ≤ 1 := by
    intro σ y
    rw [hsnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.s_mem.2 σ y)
  have htle : ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (↑N * (-1)) (↑N * ↑b) σ y (t ^ N) ≤ 1 := by
    intro σ y
    rw [htnu]
    exact pow_le_one₀ (hnu _ _ _ _ _) (hg.t_mem.2 σ y)

  let Λ₀ : AddSubgroup X.functionField := (P.H N 0).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  let Λ₀' : AddSubgroup X.functionField := (P.H 0 (b * N)).comap (AddMonoidHom.mulRight (s ^ m)⁻¹)
  have key := GlobalTheory.VolBr.encard_mul_le_of_quot_embed X.functionField (P.H N m) (P.H 0 (b * N + m)) Λ₀ Λ₀'
    (P.Bl N m) (P.Bl 0 (b * N + m)) (AddMonoidHom.mulRight (t ^ N))
    (_root_.GlobalTheory.VolBr.Pair.isBallFam k X p P N m) (_root_.GlobalTheory.VolBr.Pair.isBallFam k X p P 0 (b * N + m)) ?_ ?_ hfin
  rotate_left
  ·
    intro u hu
    obtain ⟨hH, hn⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P N m (↑N * (-1)) (↑N * ↑b) u (t ^ N) hu.1 htH
    have e1 : (N : ℤ) + ↑N * (-1) = 0 := by ring
    have e2 : (m : ℤ) + ↑N * ↑b = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    simp only [AddMonoidHom.coe_mulRight]
    rw [hn]
    exact mul_le_one₀ (hu.2 σ y) (hnu _ _ _ _ _) (htle σ y)
  ·
    intro u hu hT
    simp only [Λ₀, Λ₀', AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight] at hT ⊢
    rw [← div_eq_mul_inv] at hT ⊢
    exact _root_.GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow k X p D hX P b s t hg N m u hu hT

  have hE : (P.Bl 0 (b * N) 1).encard ≤ (P.Bl 0 (b * N + m) 1 ∩ (Λ₀' : Set X.functionField)).encard := by
    rw [← (mul_left_injective₀ hs0).injOn.encard_image]
    apply Set.encard_le_encard
    rintro _ ⟨g, hg', rfl⟩
    obtain ⟨hH, hn⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P 0 (↑b * ↑N) (↑m * 0) (↑m * 1) g (s ^ m) hg'.1 hsH
    have e1 : (0 : ℤ) + ↑m * 0 = 0 := by ring
    have e2 : (↑b * ↑N : ℤ) + ↑m * 1 = ↑b * ↑N + ↑m := by ring
    rw [e1, e2] at hH hn
    refine ⟨⟨hH, fun σ y => ?_⟩, ?_⟩
    · rw [hn]
      exact mul_le_one₀ (hg'.2 σ y) (hnu _ _ _ _ _) (hsle σ y)
    · show g * s ^ m * (s ^ m)⁻¹ ∈ P.H 0 (↑b * ↑N)
      rw [mul_inv_cancel_right₀ hs0]
      exact hg'.1

  have hB : (P.Bl N m 2 ∩ (Λ₀ : Set X.functionField)) =
      (fun f => f * s ^ m) '' {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2} := by
    ext u
    constructor
    · rintro ⟨hu, hu0⟩
      refine ⟨u * (s ^ m)⁻¹, ⟨hu0, ?_⟩, ?_⟩
      · rw [inv_mul_cancel_right₀ hs0]
        exact hu
      · exact inv_mul_cancel_right₀ hs0 u
    · rintro ⟨f, ⟨hf, hfs⟩, rfl⟩
      refine ⟨hfs, ?_⟩
      show f * s ^ m * (s ^ m)⁻¹ ∈ P.H N 0
      rw [mul_inv_cancel_right₀ hs0]
      exact hf
  rw [hB, (mul_left_injective₀ hs0).injOn.encard_image] at key
  refine le_trans ?_ key
  gcongr

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherent
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, IsAmpleLB L → ∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (hdim k (twist F (lbPow L m)) 0 : ℤ) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hp d F _ hd L hL
  obtain ⟨C, hC⟩ := GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hp d F hd L hL.isLB
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    (hL.eventually_subsingleton_coh_twist (algebraMap_eq_strHom k X) F)
  refine ⟨C, m₀, fun m hm => ?_⟩
  rw [← chi_eq_hdim_zero k (hm₀ m hm)]
  exact hC m

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
section
namespace GlobalTheory

theorem bernsteinZelevinskyFiniteness_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
section
namespace GlobalTheory.Laid

theorem bzfin_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  intro k _ _ _ _

  exact ⟨CompanionTheory.SmGLBridge.irreducibleAdmissible k, CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    CompanionTheory.BZInd.inductionFiniteLength k, SmGL.IndDual.inductionContragredient k⟩

end GlobalTheory.Laid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLe
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory.IntCount

theorem exists_abs_repr_le_mul_house (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem card_bounded_integers_le (E : Type) [Field E] [NumberField E] :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧
      ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  classical
  obtain ⟨c, hc, hb⟩ := exists_abs_repr_le_mul_house E
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  refine ⟨Fintype.card ι, (2 * c + 3) ^ Fintype.card ι, by positivity, fun T hT => ?_⟩
  set S := {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T} with hS
  let M : ℕ := ⌈c * T⌉₊
  let s : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  let f : 𝓞 E → (ι → ℤ) := fun ξ j => (RingOfIntegers.basis E).repr ξ j
  have hf : Function.Injective f := fun ξ η h =>
    (RingOfIntegers.basis E).ext_elem fun j => congrFun h j
  have hmaps : ∀ ξ ∈ S, f ξ ∈ s := by
    intro ξ hξ
    refine Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2 (abs_le.1 ?_)
    have hh : house (ξ : E) ≤ T := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun φ => ?_
      have := hξ (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h1 := hb ξ j
    have h2 : c * house (ξ : E) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_left hh hc).trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  have hsub : S ⊆ f ⁻¹' (s : Set (ι → ℤ)) := fun ξ hξ => hmaps ξ hξ
  have hfin : S.Finite := ((s.finite_toSet).preimage hf.injOn).subset hsub
  refine ⟨hfin, ?_⟩
  have hcard : S.ncard ≤ s.card := by
    rw [← Set.ncard_coe_finset s]
    exact Set.ncard_le_ncard_of_injOn f (fun ξ hξ => hmaps ξ hξ) hf.injOn s.finite_toSet
  have hs : (s.card : ℝ) = (2 * (M : ℝ) + 1) ^ Fintype.card ι := by
    simp only [s, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    push_cast
    congr 1
    have : (↑M + 1 - -↑M : ℤ).toNat = 2 * M + 1 := by omega
    rw [this]; push_cast; ring
  have hM : (M : ℝ) ≤ c * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hbase : 2 * (M : ℝ) + 1 ≤ (2 * c + 3) * T := by nlinarith
  calc (S.ncard : ℝ) ≤ s.card := by exact_mod_cast hcard
    _ = (2 * (M : ℝ) + 1) ^ Fintype.card ι := hs
    _ ≤ ((2 * c + 3) * T) ^ Fintype.card ι := by gcongr
    _ = (2 * c + 3) ^ Fintype.card ι * T ^ Fintype.card ι := mul_pow _ _ _

end GlobalTheory.IntCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusions
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory Matrix

namespace GlobalTheory.GLProj

theorem continuous_proj_incl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧
    Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧
    Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  intro E _ _ _ a
  have hInf : Continuous (pInf E) :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
  have hFin : Continuous (pFin E) := continuous_snd
  refine ⟨Continuous.units_map _ (continuous_id.matrix_map hInf),
    Continuous.units_map _ (continuous_id.matrix_map hFin), continuous_infGL, ?_⟩
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => 1 - matN a (sFin E) 1 + x.map (sFin E))

end GlobalTheory.GLProj
end
end

