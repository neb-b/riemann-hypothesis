module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsIrrOfEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinIrr

private lemma act_mem_of_forall_upq_act_mem {p q : ℕ} (N : GKMod p q) (W : Submodule ℂ N.V)
    (h : ∀ Z ∈ upq p q, ∀ y ∈ W, N.act Z y ∈ W) : ∀ Z, ∀ y ∈ W, N.act Z y ∈ W := by
  intro Z y hy
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z) y hy
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z) y hy
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add (f := _), map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  exact W.add_mem (W.smul_mem _ hre) (W.smul_mem _ him)

private lemma comm_act_of_comm_act_upq {p q : ℕ} (N : GKMod p q) (T : N.V →ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, T ∘ₗ N.act Z = N.act Z ∘ₗ T) : ∀ Z, T ∘ₗ N.act Z = N.act Z ∘ₗ T := by
  intro Z
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add (f := _), map_smul, map_smul, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, hre, him]

theorem absIrr_of_equiv {p q : ℕ} (N : GKMod p q) (hI : Formalism.MainNotions.SchurIrreducible.IrrGK N) (hA : Formalism.MainNotions.SchurIrreducible.AdmGK N)
    {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) (e : K ≃ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, e (a g x) = N.act Z (e x) + c • e x) : AbsIrr a := by
  have hy : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, N.act Z (e x) = e (a g x - c • x) := by
    intro Z hZ
    obtain ⟨g, c, hg⟩ := h Z hZ
    refine ⟨g, c, fun x => ?_⟩
    rw [map_sub, map_smul, hg, add_sub_cancel_right]
  refine ⟨fun W hW => ?_, fun T hT => ?_⟩
  · have hst : ∀ Z ∈ upq p q, ∀ y ∈ W.map (e : K →ₗ[ℂ] N.V), N.act Z y ∈ W.map (e : K →ₗ[ℂ] N.V) := by
      rintro Z hZ _ ⟨x, hx, rfl⟩
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hmem : a g x - c • x ∈ W := W.sub_mem (hW g x hx) (W.smul_mem c hx)
      have hout := Submodule.mem_map_of_mem (f := (e : K →ₗ[ℂ] N.V)) hmem
      simpa [hg] using hout
    rcases hI.2 _ (act_mem_of_forall_upq_act_mem N _ hst) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := Submodule.mem_map_of_mem hx
      rw [h0, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      simpa using hx'
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := by rw [h1]; trivial
      obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.mp hx'
      have hxy : y = x := e.injective hyx
      exact hxy ▸ hyW
  · have hc : ∀ Z ∈ upq p q, ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) ∘ₗ N.act Z =
        N.act Z ∘ₗ ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) := by
      intro Z hZ
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hTg : ∀ x, T (a g x) = a g (T x) := fun x => LinearMap.congr_fun (hT g) x
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, LinearEquiv.symm_apply_apply, map_sub, map_smul, hTg]
    obtain ⟨c, hc'⟩ := GlobalTheory.IrrTensor.schur N hI hA _ (comm_act_of_comm_act_upq N _ hc)
    refine ⟨c, LinearMap.ext fun x => e.injective ?_⟩
    have hx := LinearMap.congr_fun hc' (e x)
    simpa using hx

theorem absIrr_kFin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ ≃ₗ[ℂ] R.U.H) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → Formalism.MainNotions.SchurIrreducible.IrrGK R.HK → Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → IsKAct M τ a → AbsIrr fun X : lieAt V τ => a X := by
  intro D V S M τ p q T R φ m U a hM hI hA hK
  have hfin : ∀ x : kFin M τ, U x ∈ LinearMap.range R.ι := fun x =>
    LinearMap.mem_range.mpr ((hM.kfin x.1).mp x.2)
  have hequiv : ∃ e : kFin M τ ≃ₗ[ℂ] R.HK.V, ∀ y, R.ι (e y) = U y := by
    let f : kFin M τ →ₗ[ℂ] LinearMap.range R.ι :=
      LinearMap.codRestrict (LinearMap.range R.ι) ((U : M.H τ →ₗ[ℂ] R.U.H) ∘ₗ (kFin M τ).subtype) hfin
    have hf : ∀ y, (f y : R.U.H) = U y := fun y => rfl
    have hbij : Function.Bijective f := by
      constructor
      · intro x y hxy
        have hv : U x = U y := by rw [← hf, ← hf, hxy]
        exact Subtype.ext (U.injective hv)
      · rintro ⟨y, hy⟩
        have hk : U.symm y ∈ kFin M τ := by
          refine (hM.kfin _).mpr ?_
          rw [U.apply_symm_apply]
          exact LinearMap.mem_range.mp hy
        refine ⟨⟨U.symm y, hk⟩, Subtype.ext ?_⟩
        rw [hf]
        exact U.apply_symm_apply y
    let e2 := LinearEquiv.ofInjective R.ι R.ι_inj
    refine ⟨(LinearEquiv.ofBijective f hbij).trans e2.symm, fun y => ?_⟩
    have h3 := congrArg Subtype.val (e2.apply_symm_apply (f y))
    rw [LinearEquiv.ofInjective_apply, hf] at h3
    exact h3
  obtain ⟨e, hιe⟩ := hequiv
  refine absIrr_of_equiv R.HK hI hA (fun X : lieAt V τ => a X) e ?_
  intro Z hZ
  have hX : IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z) ∈ lieAt V τ := by
    rw [← hM.lie]
    exact ⟨Z, hZ, rfl⟩
  have hd : ∀ x : kFin M τ, dRep (M.rep τ) (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) (x : M.H τ) =
      (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x : M.H τ) := fun x =>
    (hK.der _ hX x).deriv
  refine ⟨⟨_, hX⟩, (m : ℂ) / 2 * Z.trace, fun x => R.ι_inj ?_⟩
  show R.ι (e (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x)) = R.ι (R.HK.act Z (e x) + ((m : ℂ) / 2 * Z.trace) • e x)
  rw [hιe, ← hM.der Z hZ (e x) x (hιe x).symm, hd x]

end GlobalTheory.KFinIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCUnitary

variable {n : ℕ} {ε : Fin n → Bool}

theorem maxCpt_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.maxCpt (UJset ε) = Kset ε := by
  ext g
  refine ⟨fun hg => ⟨hg.2, ?_⟩, fun hg => ⟨mem_UJset_of_mem_Kset hg, hg.1⟩⟩
  have h1 : g * gᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hg.2
  have h2 : gᴴ * Jm ε * g = Jm ε := hg.1
  calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [h2]
    _ = Jm ε * g := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, h1, Matrix.one_mul]

theorem isLinRed_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.IsLinRed (UJset ε) := by
  have hW : IsIsoFlag ε (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => (⊥ : Submodule ℂ (Fin n → ℂ))) :=
    ⟨rfl, monotone_const, fun i => i.elim0, fun x hx y _ => by
      rw [(Submodule.mem_bot ℂ).1 hx]; simp⟩
  have h := (_root_.GlobalTheory.LeviPolar.isLinRed_leviOne n ε 0 _ _ hW (fun i => i.elim0)).1
  rwa [leviOne_zero hW, mats_top] at h

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isKStable_iff {S : Submodule ℂ H} : GlobalTheory.LinRed.IsKStable (UJset ε) π S ↔ IsKStableOn ε π S := by
  unfold GlobalTheory.LinRed.IsKStable IsKStableOn
  rw [maxCpt_UJset]

theorem isKTypeOf_map {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε π Λ S) (T : H →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ w ∈ S, T (π k w) = π k (T w)) : S.map T = ⊥ ∨ IsKTypeOf ε π Λ (S.map T) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hv⟩, hdom⟩ := hS
  have hpre : ∀ S' : Submodule ℂ H, IsKStableOn ε π S' → IsKStableOn ε π (S ⊓ S'.comap T) :=
    fun S' h k hk w hw => ⟨hst k hk w hw.1, by
      have : T (π k w) ∈ S' := by rw [hT k hk w hw.1]; exact h k hk _ hw.2
      exact this⟩
  have hbot : IsKStableOn ε π ⊥ := fun k _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _
  rcases hirr _ inf_le_left (hpre ⊥ hbot) with h0 | h1
  · right
    have hinj : ∀ w ∈ S, T w = 0 → w = 0 := fun w hw h => by
      have : w ∈ S ⊓ (⊥ : Submodule ℂ H).comap T := ⟨hw, h⟩
      rwa [h0, Submodule.mem_bot] at this
    refine ⟨inferInstance, ?_, fun S' hle hS' => ?_, ⟨T v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h),
      fun θ hθ => ?_⟩, ?_⟩
    · rintro k hk _ ⟨w, hw, rfl⟩
      exact ⟨π k w, hst k hk w hw, hT k hk w hw⟩
    · rcases hirr _ inf_le_left (hpre S' hS') with h | h
      · left
        refine eq_bot_iff.2 fun x hx => ?_
        obtain ⟨w, hw, rfl⟩ := hle hx
        have : w ∈ S ⊓ S'.comap T := ⟨hw, hx⟩
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]; exact Submodule.zero_mem _
      · exact Or.inr (le_antisymm hle (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h)))
    · rw [← hT _ hθ v hvS, hv θ hθ, map_smul]
    · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
      refine hdom μ w hw (fun h => hw0 (by rw [h, map_zero])) fun θ hθ => ?_
      refine sub_eq_zero.1 (hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw)) ?_)
      rw [map_sub, map_smul, hT _ hθ w hw, hwt θ hθ, sub_self]
  · exact Or.inl (eq_bot_iff.2 (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h1)))

theorem isAdmOn_iff [CompleteSpace H] : GlobalTheory.LinRed.IsAdmOn (UJset ε) π ↔ IsAdmRep ε π := by
  unfold GlobalTheory.LinRed.IsAdmOn IsAdmRep
  simp only [isKStable_iff]
  rw [maxCpt_UJset]
  refine and_congr_right fun h1 => and_congr_right fun h2 => and_congr_right fun h3 => ?_
  obtain ⟨hA, hB⟩ := GlobalTheory.KTypeHighest.ktype_highest_weight n ε H π h1 h2 h3
  refine ⟨fun h Λ => ?_, fun h S hfin hst hirr => ?_⟩
  · by_cases he : ∃ S₀, IsKTypeOf ε π Λ S₀
    · obtain ⟨S₀, hS₀⟩ := he
      haveI := h S₀ hS₀.1 hS₀.2.1 hS₀.2.2.1
      refine Submodule.finiteDimensional_of_le (sSup_le_sSup (t := {S' | ∃ T : H →ₗ[ℂ] H, S' = S₀.map T ∧
        ∀ k ∈ Kset ε, ∀ w ∈ S₀, T (π k w) = π k (T w)}) fun S hS => ?_)
      obtain ⟨B, hB1, hB2⟩ := hB Λ S₀ S hS₀ hS.2
      exact ⟨B, hB2.symm, fun k hk w _ => hB1 k hk w⟩
    · exact Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le fun S hS => absurd ⟨S, hS.2⟩ he)
  · by_cases h0 : S = ⊥
    · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le ?_)
      rintro _ ⟨T, rfl, -⟩
      rw [h0, Submodule.map_bot]
    · obtain ⟨Λ, hΛ⟩ := hA S hfin h0 hst hirr
      haveI := h Λ
      refine Submodule.finiteDimensional_of_le (S₂ := sSup {S | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S}) (sSup_le ?_)
      rintro _ ⟨T, rfl, hT⟩
      rcases isKTypeOf_map hΛ T hT with hb | hk
      · rw [hb]; exact bot_le
      · exact le_sSup ⟨le_top, hk⟩

end GlobalTheory.HCUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactTorusProductRealPlacesSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol

theorem torProd_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (s : D.what₂.Tau → Fin T.rank → ℝ), GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s ∈ GinfC T ∧ ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T (GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s)) = B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ := by
  intro D S T C B hB s
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hu : ∀ ρ, IsAtTau C.θ T ρ (B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹) (torAt C.θ T B ρ (s ρ)) := by
    intro ρ
    have hS : (diagonal fun c => cexp ((s ρ c : ℂ) * I))ᴴ * sgnM C.X * (diagonal fun c => cexp ((s ρ c : ℂ) * I)) = sgnM C.X := by
      unfold sgnM
      exact GlobalTheory.HolRead.AdExt.diag_unitary _ _
    exact GlobalTheory.HolRead.AdExt.atTau_spec R ρ (GlobalTheory.HolRead.AdExt.conj_mem_unitary (isUnit_det_B C hB ρ) (hB ρ) hS)
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod ∈ GinfC T ∧
      ∀ ρ, infMat D.sp.cm.sig T.gram (C.θ ρ) (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod =
        if ρ ∈ l then B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ else 1 by
    obtain ⟨h1, h2⟩ := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    refine ⟨h1, fun ρ => ?_⟩
    have := h2 ρ
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at this
    exact this
  intro l hl
  induction l with
  | nil =>
    refine ⟨one_mem _, fun ρ => ?_⟩
    simpa using R.2.2.2.2.1 1 (one_mem _) ρ
  | cons τ l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨i1, i2⟩ := ih hl.2
    rw [List.map_cons, List.prod_cons]
    refine ⟨mul_mem (hu τ).1 i1, fun ρ => ?_⟩
    rw [R.2.2.2.1, i2 ρ]
    by_cases c : ρ = τ
    · subst c
      rw [(hu ρ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hu τ).2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

end GlobalTheory.AdSpan.ConjHol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFrameToRealLieAlgebraSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol.ToLie

lemma conj_mem_sgn {n : ℕ} (d : Fin n → ℂ) (hd : ∀ a, star (d a) = d a)
    (A : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * diagonal d + diagonal d * A = 0) :
    (A.map (starRingEnd ℂ))ᴴ * diagonal d + diagonal d * A.map (starRingEnd ℂ) = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.zero_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply] at hij ⊢
  have := congrArg star hij
  simp only [star_add, star_mul', star_star, star_zero, hd] at this
  simpa [RCLike.star_def, add_comm, mul_comm] using this

end GlobalTheory.AdSpan.ConjHol.ToLie

open GlobalTheory.AdSpan.ConjHol GlobalTheory.HolRead.AdExt in
theorem GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ Z ∈ GlobalTheory.HolRead.unitLie C.X, (∀ ρ, (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z ρ).1 = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) ∧ GlobalTheory.AdSpan.ConjHol.toLieC C R B (I • Z) = 0 := by
  intro D S T C R B hB Z hZ
  have hfix : ∀ ρ, conjAt T ρ (B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹)
      = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹ := by
    intro ρ
    have hW := GlobalTheory.AdSpan.ConjHol.ToLie.conj_mem_sgn _ ?_ _ (hZ (C.m.e ρ))
    · have hB' : (B ρ)ᴴ * gramAt D T ρ * B ρ = diagonal fun (a : Fin T.rank) => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ) := hB ρ
      have hL := conj_mem_lie (isUnit_det_B C hB ρ) hB' hW
      exact conj_eq_of_mem_lie (R.1 ρ).2 hL
    · intro a; simp
  refine ⟨fun ρ => ?_, ?_⟩
  · show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL Z) ρ).1 = _
    rw [toLie_val, mat_conjL, hfix ρ]
    module
  · funext ρ
    apply Subtype.ext
    show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL (I • Z)) ρ).1 = (0 : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    have hc : conjL (I • Z) = I • (-(conjL Z)) := by
      funext τ a b
      simp [conjL]
    have hm : mat (-(conjL Z)) (C.m.e ρ) = -(mat (conjL Z) (C.m.e ρ)) := rfl
    have hneg : ∀ M : Matrix (Fin T.rank) (Fin T.rank) ℂ,
        conjAt T ρ (B ρ * -M * (B ρ)⁻¹) = -(conjAt T ρ (B ρ * M * (B ρ)⁻¹)) := by
      intro M; simp [conjAt]
    rw [hc, toLie_I, hm, hneg, mat_conjL, hfix ρ]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIdealEqOfConjPl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.InertEigScalar

theorem conjIdeal_eq_of_conjPl {D : D7} (P : Pl D.host.E) (hc : conjPl P = P) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal := by
  have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    show _ = Ideal.span _
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hr⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change _ = (algebraMap (𝓞 D.host.E) D.host.E r)
      rw [hr]
      rfl
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [h1]
  exact congrArg HeightOneSpectrum.asIdeal hc


set_option maxHeartbeats 1000000 in
theorem inert_label_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P = P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC _hEx _hH _hPG j c h hh _hN P hP hc d hd
  have hlab := (_root_.GlobalTheory.LabChar.labels_char (Vc D j) P d).1 hd
  obtain ⟨s', hs2, hsp, hspos, rfl⟩ :=
    (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank d).1 ⟨hlab.1, hlab.2.1, hlab.2.2 hc⟩
  have hPg : P ∉ R.Pg := fun hm => (hP P (Or.inl hm)).1 rfl
  have hPQ : P ∉ R.Q A3.A.fam.μ0 := fun hm => (hP P (Or.inr hm)).1 rfl
  have hfix := conjIdeal_eq_of_conjPl P hc
  have hSb : P ∉ R.Sb := by
    have e : R.Sb = R.Pg := hC.allPl
    rw [e]; exact hPg
  have hoff : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := ⟨hfix, fun hm => hSb (Finset.mem_coe.1 hm)⟩
  have honto : R.in_onto := hC.inert.onto
  have hex : ∃ Q, R.plI Q = P := honto P hoff
  obtain ⟨Q, hQ⟩ := hex
  have hQok : Q ∈ A3.okI A3.A.fam.μ0 := by
    refine (hC.inert.tie.okI A3.A.fam.μ0 Q).2 ⟨?_, ?_⟩
    · rw [hQ]; exact hfix
    · rw [hQ, hC.allPl]
      simp only [Set.mem_union, Finset.mem_coe]
      tauto
  subst hQ
  have hLt : R.in_L := hC.inert.hL
  have hn := hLt j A3.A.fam.μ0
  obtain ⟨Comparison₂⟩ := hn
  let inR' : ↥(A3.okI A3.A.fam.μ0) × List ℕ → Prop :=
    fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 ∧ R.plI k.1 = R.plI Q
  let Tie' : Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j A3.A.fam.μ0).pres (A3.heckeLI j A3.A.fam.μ0) inR'
      (fun k => GlobalTheory.Hk3.IsLabElt (Vc D j) (R.plI k.1) (GlobalTheory.Hk3.labIn (Vc D j).rank k.2))
      (fun k => GlobalTheory.Hk3.IsLocElt (Vc D j) (R.plI k.1)) :=
    { hx := Comparison₂.hx, hA := Comparison₂.hA, hx_ok := fun i hi => Comparison₂.hx_ok i hi.1, hA_loc := fun i hi => Comparison₂.hA_loc i hi.1,
      chi_loc := fun i hi => Comparison₂.chi_loc i hi.1, hDC := fun i hi => Comparison₂.hDC i hi.1, op_eq := fun i hi => Comparison₂.op_eq i hi.1 }
  let k : ↥(A3.okI A3.A.fam.μ0) × List ℕ := (⟨Q, hQok⟩, s')
  have hk : inR' k := ⟨⟨hsp, hspos, hs2⟩, rfl⟩
  have hin : ∀ i, inR' i → GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
      (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    rintro ⟨Q', t'⟩ ⟨hty, hpl⟩
    simp only at hpl ⊢
    rw [hpl]
    exact ⟨hP, hc, ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨t', hty.2.2, hty.1, hty.2.1, rfl⟩).2.1⟩
  have key := (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models j
    A3.A.fam.μ0 _ (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.fam.μ0) inR'
    hin Tie' k hk).2.2.2 h hh
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hC.base.models
  have hop : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s') 1)) := by
    apply LinearMap.ext_on_range (hK j A3.A.fam.μ0).2
    intro b
    rw [← Formalism.IndefR.Cx.CxData.jL_opL (R.toCx3 F) hK]
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j A3.A.fam.μ0 (A3.heckeLI j A3.A.fam.μ0 k _)) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) _ (R.jV j A3.A.fam.μ0 _))
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (key _)
  refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inr k)), fun x hx => ?_⟩
  have hx' : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) x = c (Sum.inr k) • x :=
    (Formalism.IndefR.U2.mem_eigPart.1 hx) (Sum.inr k)
  rw [hop] at hx'
  exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0)) hx'

end GlobalTheory.InertEigScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwinesStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedRep_conj_maxCompact_intertwines : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v → Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  first | exact @GlobalTheory.GKLie.dRep_conj_Kset | exact GlobalTheory.GKLie.dRep_conj_Kset | (intros; apply GlobalTheory.GKLie.dRep_conj_Kset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EnormMixedModelTermLeISup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

theorem enorm_term_le_iSup : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ ≤ ⨆ w, ‖G w‖ₑ := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  have hψ1 : ∀ x, ‖(ψ x : ℂ)‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hψ.1.2.1 x, ENNReal.ofReal_one]
  calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ
      ≤ ∫⁻ z in 𝓨, ‖heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G
          (isoPart V W C z + midPart V V' W B 0)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in 𝓨, (⨆ w, ‖G w‖ₑ) ∂μ := by
        refine lintegral_mono fun z => ?_
        simp only [heisO, enorm_mul, hψ1, one_mul]
        exact le_iSup (fun w => ‖G w‖ₑ) _
    _ = ⨆ w, ‖G w‖ₑ := by rw [setLIntegral_const, hμ.2.2, mul_one]

end GlobalTheory.MixedTerm
end

