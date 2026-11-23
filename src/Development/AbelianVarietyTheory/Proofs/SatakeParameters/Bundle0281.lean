module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0152
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalToGlobal.Divisibility.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEq
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem full_span {n : ℕ} (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsFullLattice E M) : Submodule.span E (M : Set (Fin n → E)) = ⊤ := by
  letI := hM
  exact Submodule.IsFullLattice.span_eq_top

theorem dualL_fg {n : ℕ} (τ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M) : (dualL τ J M).FG := by
  classical
  obtain ⟨S, hS⟩ := hM.fg
  have hSE : Submodule.span E ((S : Set (Fin n → E))) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 E) E, hS]
    exact full_span M hM
  let Θ : (Fin n → E) →ₗ[𝓞 E] (S → E) :=
    { toFun := fun y s => hform τ J s.1 y
      map_add' := fun y y' => by
        funext s
        simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r y => by
        funext s
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [show r • y = (r : E) • y from (algebraMap_smul E r y).symm, GlobalTheory.LevelHecke.DualConj.hform_smul_right,
          Algebra.smul_def] }
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ x ∈ Submodule.span E (S : Set (Fin n → E)), hform τ J x y = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact congrFun hy ⟨x, hx⟩
      | zero => simp [hform]
      | add x x' _ _ hx hx' =>
        have e : hform τ J (x + x') y = hform τ J x y + hform τ J x' y := by
          simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
        rw [e, hx, hx', add_zero]
      | smul c x _ hx => rw [GlobalTheory.LevelHecke.DualConj.hform_smul_left, hx, mul_zero]
    have hJy : J *ᵥ y = 0 := by
      funext i
      have := h0 (Pi.single i 1) (by rw [hSE]; trivial)
      show (J *ᵥ y) i = 0
      rw [← this]
      simp [hform, Pi.single_apply, Matrix.mulVec, dotProduct]
    have : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [this, hJy, Matrix.mulVec_zero]
  let P : Submodule (𝓞 E) (S → E) := LinearMap.range
    (LinearMap.pi fun s : S => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj s) : (S → 𝓞 E) →ₗ[𝓞 E] (S → E))
  have hP : P.FG := by
    show (LinearMap.range _).FG
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  refine Submodule.fg_of_fg_map_injective Θ hΘ (Submodule.FG.of_le_of_isNoetherian (T := P) ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hy' := (GlobalTheory.LevelHecke.DualConj.mem_dualL τ J M y).1 hy
  choose f hf using fun s : S => hy' s.1 (hS ▸ Submodule.subset_span s.2)
  refine ⟨f, ?_⟩
  funext s
  exact hf s

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_sup_smul_iff (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M N : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E)
    (z : Fin n → E ⊗[F] v.adicCompletion F) :
    z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (M ⊔ Ideal.span {a} • N) ↔
      ∃ m ∈ latS (F := F) (v.adicCompletion F) (intV E v) M, ∃ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
        z = m + inclE (F := F) (v.adicCompletion F) (a : E) • w := by
  set c := inclE (F := F) (v.adicCompletion F) (a : E) with hc
  have hincl : ∀ y y' : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((y + y') i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (y i)) + fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    intro y y'; funext i; simp
  have hsm : ∀ y : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((a • y) i)) =
      c • fun i => inclE (F := F) (v.adicCompletion F) (y i) := by
    intro y; funext i
    simp only [Pi.smul_apply, smul_eq_mul, hc, ← map_mul]
    rw [Algebra.smul_def]
  have hcw : ∀ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
      c • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Ideal.span {a} • N) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← hsm]
      exact Submodule.subset_span ⟨a • y, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add w w' _ _ hw hw' => rw [smul_add]; exact add_mem hw hw'
    | smul s w _ hw =>
      rw [Subring.smul_def, smul_comm]
      exact Submodule.smul_mem _ s hw
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Submodule.ideal_span_singleton_smul] at hq
      obtain ⟨q', hq', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
      exact ⟨_, Submodule.subset_span ⟨p, hp, rfl⟩, _, Submodule.subset_span ⟨q', hq', rfl⟩, by
        show (fun i => inclE (F := F) (v.adicCompletion F) ((p + a • q') i)) = _
        rw [hincl, hsm]⟩
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      obtain ⟨m', hm', w', hw', rfl⟩ := hz'
      exact ⟨m + m', add_mem hm hm', w + w', add_mem hw hw', by rw [smul_add]; abel⟩
    | smul s z _ hz =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      refine ⟨s • m, Submodule.smul_mem _ s hm, s • w, Submodule.smul_mem _ s hw, ?_⟩
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rintro ⟨m, hm, w, hw, rfl⟩
    have h1 : (M : Set (Fin n → E)) ⊆ ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_left
    have h2 : ((Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ⊆
        ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_right
    exact add_mem (Submodule.span_mono (Set.image_mono h1) hm) (Submodule.span_mono (Set.image_mono h2) (hcw w hw))

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

theorem isLattice_compan {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (M : Submodule (𝓞 E) (Fin N → E)) (hM : Submodule.IsFullLattice E M) :
    Submodule.IsFullLattice E (compan (sp := sp) J a M) := by
  have hfg : (compan (sp := sp) J a M).FG :=
    hM.fg.sup (Submodule.FG.smul (IsNoetherian.noetherian (Ideal.span {a}))
      (dualL_fg (sp.cm.sig : E →+* E) J hJ M hM))
  refine { toIsLattice := Submodule.IsLattice.of_fg E hfg, span_eq_top := ?_ }
  apply top_unique
  rw [← full_span M hM]
  apply Submodule.span_mono
  exact SetLike.coe_subset_coe.mpr le_sup_left
theorem compan_latAd_eq {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = sp.cm.sig) (J : Matrix (Fin N) (Fin N) E)
    (hJ : IsUnit J.det) (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    compan (sp := sp) J a (latAd x Lb) = latAd x (compan (sp := sp) J a Lb) := by
  have hcomp : ∀ M : Submodule (𝓞 E) (Fin N → E),
      compan (sp := sp) J a M = M ⊔ Ideal.span {a} • dualL (σ : E →+* E) J M := by
    intro M
    unfold compan dualL
    rw [hσ]
  have hLb : Submodule.IsFullLattice E Lb :=
    { toIsLattice := Submodule.IsLattice.of_fg E hfg, span_eq_top := hspan }
  have hfin : Module.Finite (𝓞 E) Lb := Module.Finite.iff_fg.mpr hfg
  have hlatAd : ∀ M : Submodule (𝓞 E) (Fin N → E), Submodule.IsFullLattice E M → Submodule.IsFullLattice E (latAd x M) := by
    intro M hM
    have e : latAd x M = Formalism.UG.CS.globLat x M := Submodule.span_eq (Formalism.UG.CS.globLat x M)
    rw [e]
    exact Formalism.UG.P.csGlob_lattice M (Module.Finite.iff_fg.mpr hM.fg) (full_span M hM) x
  have hΛ := hlatAd Lb hLb
  have hcL := isLattice_compan sp J hJ a Lb hLb
  have hcΛ := isLattice_compan sp J hJ a (latAd x Lb) hΛ
  have hRHS := hlatAd _ hcL
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (compan (sp := sp) J a (latAd x Lb)) ↔
        z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x (compan (sp := sp) J a Lb)) := by
    intro v z
    set g := bc (prV (E := E) v) x with hg
    have hgU : g ∈ UPts σ J (v.adicCompletion F) := GlobalTheory.MemDual.bc_prV_mem_UPts σ J v hx
    have hcar1 := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v
    have hcar2 := GlobalTheory.LocCarry.mem_latS_latAd_iff x (compan (sp := sp) J a Lb)
      (Module.Finite.iff_fg.mpr hcL.fg) (full_span _ hcL) v
    have hdm := GlobalTheory.DualCompletion.dual_move F E σ N J v (latAd x Lb) Lb g hJ hΛ hLb hgU hcar1
    have hgg : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, ((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ
        ((g : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hgg' : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, (g : Matrix (Fin N) (Fin N) _) *ᵥ
        (((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hcar2, hcomp, hcomp, mem_latS_sup_smul_iff, mem_latS_sup_smul_iff]
    constructor
    · rintro ⟨m, hm, w, hw, rfl⟩
      exact ⟨_, (hcar1 m).1 hm, _, (hdm w).1 hw, by rw [Matrix.mulVec_add, Matrix.mulVec_smul]⟩
    · rintro ⟨m, hm, w, hw, he⟩
      refine ⟨(g : Matrix (Fin N) (Fin N) _) *ᵥ m, (hcar1 _).2 (by rw [hgg]; exact hm),
        (g : Matrix (Fin N) (Fin N) _) *ᵥ w, (hdm _).2 (by rw [hgg]; exact hw), ?_⟩
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← he, hgg']
  apply le_antisymm
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hRHS.fg) (full_span _ hRHS) w fun v => ?_
    exact (key v _).1 (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hcΛ.fg) (full_span _ hcΛ) w fun v => ?_
    exact (key v _).2 (Submodule.subset_span ⟨w, hw, rfl⟩)

theorem locP_companion_latAd : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  intro R F E _ _ _ _ _ _ sp N σ hσ J hJ a x hx Lb hfg hspan P
  rw [compan_latAd_eq sp σ hσ J hJ a x hx Lb hfg hspan]

end GlobalTheory.CompanLatAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeVectorLocalMemDualBaseCompletionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionLatticeVector_local_mem_dualBaseCompletion : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) → IsUnit J.det →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E), u ∈ latCo sp J crd a x Lb →
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) := by
  first | exact @GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | exact GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo | (intros; apply GlobalTheory.CompanLocal.mem_latS_dual_of_mem_latCo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  first | exact @GlobalTheory.LocQCoset.coset_agree | exact GlobalTheory.LocQCoset.coset_agree | (intros; apply GlobalTheory.LocQCoset.coset_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalBaseChangeTransTowerStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_baseChange_trans_tower : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), IsLift π P → IsLift P Q → IsLift π Q := by
  first | (exact @GlobalTheory.LiftTrans.isLift_trans) | (exact GlobalTheory.LiftTrans.isLift_trans) | (intros; apply GlobalTheory.LiftTrans.isLift_trans  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.FrobOps
open Polynomial

theorem not_dvd_normV {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) (w : HeightOneSpectrum (𝓞 E))
    (h : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  first
  | exact @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | (apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem ..)

theorem norm_le_one {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (m : ℤ) (q e : ℕ) (hq : ¬ l ∣ q) :
    ‖ι.symm ((m : ℂ) / (q : ℂ) ^ e)‖ ≤ 1 := by
  rw [map_div₀, map_pow, map_intCast, map_natCast, norm_div, norm_pow]
  have h1 : ‖((q : ℕ) : Qbar l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq
  rw [h1, one_pow, div_one]
  exact IsUltrametricDist.norm_intCast_le_one _ m

theorem trace_pow_of_charpoly {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) (B : Multiset ℂ)
    (h : M.charpoly = (B.map fun b => X - C b).prod) (n : ℕ) : (M ^ n).trace = (B.map (· ^ n)).sum := by
  rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, h, Polynomial.roots_multiset_prod_X_sub_C]

theorem iota_trc {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : Γ →* GL (Fin a) (Qbar l))
    (s : Γ) (n : ℕ) :
    ι (trc r (s ^ n)) = ((((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom) ^ n).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.map_pow, trc, map_pow, Units.val_pow_eq_pow_val, Matrix.trace, Matrix.trace, map_sum]
  rfl

end GlobalTheory.FrobOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariantStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledStepDatum_rationalUnitary_equivariant : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i = t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  first | exact @GlobalTheory.CplRat.xiPt_cpl_smul | exact GlobalTheory.CplRat.xiPt_cpl_smul | (intros; apply GlobalTheory.CplRat.xiPt_cpl_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TieUnr


set_option maxHeartbeats 4000000 in
theorem mt_eq_one_of_intUnit : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint hsupp
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  obtain ⟨x', hx'int, hx'h90, hx'supp⟩ := _root_.GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial D.host.F D.host.E (sigD D) (_root_.GlobalTheory.cmData_sig_isConjOf _ _ D.sp.cm)
    (GlobalTheory.HeckeAdjoint.unramified_host D) _ hzU hint
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = x' := by
    ext
    simp [x]
  have hq : A.q x = dtU y := H.q_dt x y (by rw [hxx, hx'h90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hx'int.1
    · simpa [x] using hx'int.2

  have hsub : ∀ {K : Type} [Field K] [NumberField K] (w : FiniteAdeleRing (𝓞 K) K) (P : HeightOneSpectrum (𝓞 K)),
      (w - 1) P = w P - 1 := fun _ _ => rfl
  have hsuppX : ∀ Q : HeightOneSpectrum (𝓞 t.X.E), (∃ P ∈ SB t μ, P.under (𝓞 t.X.F) = Q.under (𝓞 t.X.F)) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q = 1 := by
    rintro Q ⟨P, hP, hPQ⟩
    have hxm1 : (x : AfE t.X.F t.X.E) - 1 ∈ RInt t.X.F t.X.E := sub_mem hxint.1 (one_mem _)
    have key := _root_.GlobalTheory.AfeLocTr.afIso_eq_zero_iff t.X.F t.X.E D.host.F D.host.E t.seam.iE A.iA H.iA_rat H.iA_int _ hxm1 Q
    have e1 : A.iA ((x : AfE t.X.F t.X.E) - 1) = (x' : AfE D.host.F D.host.E) - 1 := by
      rw [map_sub, map_one]
      simp [x]
    rw [e1] at key
    have hA : GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) Q =
        GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q - 1 := by
      rw [map_sub, map_one]; rfl
    have hB : GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) =
        GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (x' : AfE D.host.F D.host.E) (seamP t.seam Q) - 1 := by
      rw [map_sub, map_one]; rfl
    rw [← sub_eq_zero, ← hA]
    refine key.1 ?_
    show GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) = 0
    rw [hB, sub_eq_zero]
    refine hx'supp _ fun R hR => ?_
    have hv : UnderSB t μ ((seamP t.seam Q).under (𝓞 D.host.F)) := by
      refine ⟨P, hP, ?_⟩
      show ((seamP t.seam Q).under (𝓞 D.host.F)).asIdeal = ((seamP t.seam P).under (𝓞 D.host.F)).asIdeal
      rw [_root_.GlobalTheory.TwU.seamP_under_eq D t.X t.seam t.seam_ok H.fields.ok P Q hPQ]
    exact (GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one _ _ _ _).1 (hsupp _ hv) R hR
  have hvG : ∀ P : HeightOneSpectrum (𝓞 t.X.E), (∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) P = 1 := by
    rintro P ⟨k, hk⟩
    obtain ⟨P', hP', hu⟩ := _root_.GlobalTheory.GprimUnder.exists_vG_under t.X t.Pr H.fields.ok t.pr_ok k P hk
    refine hsuppX P ⟨P', Finset.mem_union_left _ ?_, hu⟩
    fin_cases k
    · exact Finset.mem_union_left _ hP'
    · exact Finset.mem_union_right _ hP'
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∀ j : Fin D.R.m, D.muTil (j.1 + 1) (A.q x) = 1 := by
    intro j
    rw [H.muTil _ hiso j (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    refine Units.ext ?_
    have h1 := GlobalTheory.Mem.ReadEx.map_toIdl_eq_one (H.mu0 j).tame hxint (fun P hP => ?_)
    · rw [h1]
    · have hg : ∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
        by_contra hc
        push_neg at hc
        exact hP ((H.mu0 j).unr P hc)
      have h2 := hvG P hg
      show Valued.v (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) P) ≤ _
      rw [map_sub, map_one, hsub, h2, sub_self, map_zero]
      exact zero_le'
  have hxi : (t.tup μ : Chr t.X.F t.X.E t.X.K) x = 1 := by
    have hmem := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at hmem
    refine _root_.GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified t.X.F t.X.E t.X.K t.seam.σ₀ _ hmem.1.1.1.1.2 hmem.1.1.1.1.1 x hxint fun P hP => hsuppX P ?_
    refine ⟨t.sel (P.under (𝓞 t.X.F)), Finset.mem_union_right _ ?_, ?_⟩
    · have hs : (t.sel (P.under (𝓞 t.X.F))).under (𝓞 t.X.F) = P.under (𝓞 t.X.F) :=
        GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
      refine (GlobalTheory.TwistPlaces.mem_QE_iff H.sel (t.tup μ)).2 ⟨?_, ?_⟩
      · rw [hs]; exact hP
      · rw [hs]
    · exact GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
  rw [← hq]
  by_cases hμ : μ = D.what₂.mu0
  · rw [(H.ref hμ).2]
    exact hmu ⟨i, hi⟩
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hmu ⟨i, hi⟩, one_mul, hξ x, hxi, map_one]

end GlobalTheory.TieUnr
end
end

