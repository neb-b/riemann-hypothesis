module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasFr

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isSelfDualC_of_base {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {N : ℕ} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ N) : IsSelfDualC V Λ := by
  obtain ⟨-, hdual, hN, hin, hout⟩ := hB
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hl0 := (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.self_dual_lattice_is_self_dual V).1
  let φ : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := (N : 𝓞 D.host.E) • LinearMap.id
  have hφ : ∀ x, φ x = (N : D.host.E) • x := fun x => by
    simp only [φ, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E) x, map_natCast]
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · have hφinj : Function.Injective φ := fun a b hab => by
      rw [hφ, hφ] at hab
      exact smul_right_injective _ hN0 hab
    have hle : Λ.map φ ≤ Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.mem_self_dual_lattice_set, hφ]
      exact hout x hx
    have : IsNoetherian (𝓞 D.host.E) (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V) := isNoetherian_of_fg_of_noetherian _ hl0.fg
    have h1 : ((Λ.map φ).comap (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces.l0s V).subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Submodule.fg_of_fg_map_injective φ hφinj h2
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [Formalism.IndefR.Eqv.dual_of_dualL hdual y]
    simp only [Formalism.UG.hform, starRingEnd_apply, RingHom.mem_range]

section R

open Formalism.IndefR.Links Formalism.IndefR.Links.RealDat

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


end R

end Formalism.IndefR.Eqv.KerDiag

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem finHom_eq_one_iff (h : GA D V) : finHom V h = 1 ↔ Lev.finE V h = 1 := by
  unfold Lev.finE
  rw [MonoidHom.comp_apply]
  refine ⟨fun h1 => by rw [h1, map_one], fun h1 => ?_⟩
  have hinj : Function.Injective (Formalism.IndefR.Lev.swapAE D) := by
    intro a b hab
    unfold Formalism.IndefR.Lev.swapAE at hab
    simpa using hab
  apply Units.ext
  ext i j
  have h2 := congrArg (fun g => (Units.val g) i j) h1
  simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Units.val_one] at h2
  apply hinj
  refine Eq.trans h2 ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem brg_mem_GinfC (fr : UI.Frames D V) (x : (UI.instV fr).GA) : UI.brg fr x ∈ GinfC V ↔ x.2 = 1 := by
  unfold GinfC
  rw [MonoidHom.mem_ker, finHom_eq_one_iff, ← Units.val_eq_one]
  have hb := (UI.brg_isBridge fr x).2
  have hz : ∀ z, Formalism.IndefR.Lev.swapAE D (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)
      (AlgHom.id D.host.F D.host.E) z) = (Algebra.TensorProduct.lift ((Algebra.TensorProduct.includeRight : Formalism.MainNotions.S.Af D.host.F →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F).comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)) (Algebra.TensorProduct.includeLeft : D.host.E →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F) (fun _ _ => Commute.all _ _)) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).symm
    | tmul a e => simp [Formalism.IndefR.Lev.swapAE, Algebra.TensorProduct.tmul_mul_tmul]
    | add y w hy hw => erw [map_add, map_add, hy, hw, map_add]
  have key : Units.val (Lev.finE V (UI.brg fr x)) =
      Formalism.L2.SG.AdBridge.ofHAFin (UI.instV fr) (UI.brg fr x) := by
    ext i j
    exact hz _
  rw [key]
  constructor
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := hb.trans h1
    simpa [Units.val_eq_one] using h2
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := by simp [h1]
    exact hb.symm.trans h2

theorem ginf_compact (F : MF.FrA V) (hD : V.IsDefinite) : CompactSpace (UI.instV (MF.toFrames F)).Ginf := by
  have hc : ∀ v : InfinitePlace D.host.F, CompactSpace (Formalism.REAL.UJ ((MF.toFrames F).ε v)) := by
    intro v
    haveI : CompactSpace (UpqT (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).1
        (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).2) := by
      rcases hD (tauE D ((Formalism.L2.Host.tauPl D).symm v)) with h | h
      · rw [h]; infer_instance
      · rw [h]; infer_instance
    exact (MF.phiR F v).toHomeomorph.compactSpace
  exact @Pi.compactSpace _ _ (fun _ => inferInstance) hc

theorem isCompact_GinfC (hS : V.SigOK) (hD : V.IsDefinite) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  haveI := ginf_compact F hD
  have e : (GinfC V : Set (GA D V)) = UI.brg (MF.toFrames F) '' (Set.univ ×ˢ {1}) := by
    ext h
    obtain ⟨x, rfl⟩ := (UI.brg (MF.toFrames F)).surjective h
    rw [SetLike.mem_coe, brg_mem_GinfC]
    constructor
    · intro hx
      exact ⟨x, ⟨trivial, hx⟩, rfl⟩
    · rintro ⟨x', ⟨-, hx'⟩, e'⟩
      have := (UI.brg (MF.toFrames F)).injective e'
      subst this
      exact hx'
  rw [e]
  exact (isCompact_univ.prod isCompact_singleton).image (UI.brg (MF.toFrames F)).continuous

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasLev
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem upq_mat_mul {p q : ℕ} (a b : UpqT p q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

theorem upq_mat_one {p q : ℕ} : UpqT.mat (1 : UpqT p q) = 1 := rfl

theorem upq_mat_inv_mul {p q : ℕ} (a : UpqT p q) : UpqT.mat a⁻¹ * UpqT.mat a = 1 := by
  rw [← upq_mat_mul, inv_mul_cancel, upq_mat_one]

variable {D : D7} {V : HSp D}


theorem cond_change {p q : ℕ} (A₀ A : Matrix (Fin p ⊕ Fin q) (Fin V.rank) ℂ) (u : UpqT p q)
    (hu : A = UpqT.mat u * A₀) (B : Set (UpqT p q)) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (∃ b ∈ B, UpqT.mat b * A = A * X) ↔ ∃ c ∈ (fun c => u * c * u⁻¹) ⁻¹' B, UpqT.mat c * A₀ = A₀ * X := by
  subst hu
  constructor
  · rintro ⟨b, hb, hbx⟩
    refine ⟨u⁻¹ * b * u, ?_, ?_⟩
    · show u * (u⁻¹ * b * u) * u⁻¹ ∈ B
      simpa [mul_assoc] using hb
    · calc UpqT.mat (u⁻¹ * b * u) * A₀ = UpqT.mat u⁻¹ * (UpqT.mat b * (UpqT.mat u * A₀)) := by
            simp only [upq_mat_mul, Matrix.mul_assoc]
        _ = UpqT.mat u⁻¹ * (UpqT.mat u * A₀ * X) := by rw [hbx]
        _ = A₀ * X := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, upq_mat_inv_mul, Matrix.one_mul]
  · rintro ⟨c, hc, hcx⟩
    refine ⟨u * c * u⁻¹, hc, ?_⟩
    calc UpqT.mat (u * c * u⁻¹) * (UpqT.mat u * A₀) = UpqT.mat u * (UpqT.mat c * A₀) := by
          simp only [upq_mat_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (UpqT.mat u⁻¹), upq_mat_inv_mul, Matrix.one_mul]
      _ = UpqT.mat u * A₀ * X := by rw [hcx, Matrix.mul_assoc]

theorem isMeasLevW_exists
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgH : ∀ ρ m, good ρ m → m.IsHaarMeasure) (hex : ∀ ρ, ∃ m, good ρ m)
    (huq : ∀ ρ m m', good ρ m → good ρ m' → m' = m) (hS : V.SigOK)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsLevelA V K) : ∃ μ, Lev.IsMeasLevW V K good μ := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  choose m0 hm0 using hex
  haveI : ∀ ρ, (m0 ρ).IsHaarMeasure := fun ρ => hgH ρ _ (hm0 ρ)
  obtain ⟨g1, g2, g3⟩ := gf_facts (MF.toFrames F)
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  obtain ⟨hkc, hko⟩ := kf_isCompact_isOpen_of_levelA (MF.toFrames F) K hK
  set νf : Measure (UI.instV (MF.toFrames F)).Gf := Measure.haar
  have hk0 : νf (kf (MF.toFrames F) K) ≠ 0 := (hko.measure_pos νf ⟨1, K.one_mem⟩).ne'
  have hkt : νf (kf (MF.toFrames F) K) ≠ ⊤ := hkc.measure_lt_top.ne
  set μf := (νf (kf (MF.toFrames F) K))⁻¹ • νf
  haveI hμf : μf.IsHaarMeasure := by
    exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hkt) (ENNReal.inv_ne_top.mpr hk0)
  haveI hmv : ∀ v, ((m0 ((Formalism.L2.Host.tauPl D).symm v)).map (MF.phiR F v)).IsHaarMeasure := fun v =>
    (MF.phiR F v).toMulEquiv.isHaarMeasure_map (m0 ((Formalism.L2.Host.tauPl D).symm v)) (MF.phiR F v).continuous (MF.phiR F v).symm.continuous
  set μi := Measure.pi fun v => (m0 ((Formalism.L2.Host.tauPl D).symm v)).map (MF.phiR F v)
  have hμi : μi.IsHaarMeasure := Measure.pi.isHaarMeasure _
  have hsi : SFinite μi := inferInstance
  have hsf : SFinite μf := inferInstance
  have hmm : MeasurableMul (UI.instV (MF.toFrames F)).Gf := inferInstance
  have hmi : MeasurableMul ((v : InfinitePlace D.host.F) → Formalism.REAL.UJ ((MF.toFrames F).ε v)) := inferInstance
  have hprod : (μi.prod μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure μi μf
  let μA : Measure (UI.instV (MF.toFrames F)).GA := μi.prod μf
  haveI hμA : μA.IsHaarMeasure := hprod
  refine ⟨μA.map (UI.brg (MF.toFrames F)), ?_, ?_⟩
  · exact (UI.brg (MF.toFrames F)).toMulEquiv.isHaarMeasure_map μA (UI.brg (MF.toFrames F)).continuous
      (UI.brg (MF.toFrames F)).symm.continuous
  refine ⟨⟨thetaC D, isInfFam_thetaC D⟩, fun θ hθ => ?_⟩
  rw [eq_thetaC D hθ]
  refine ⟨⟨F.A, F.hA⟩, fun A hA => ?_⟩
  refine ⟨⟨m0, hm0⟩, fun m hm => ?_⟩
  have hmm : m = m0 := funext fun ρ => huq ρ _ _ (hm0 ρ) (hm ρ)
  subst hmm
  intro B hB
  choose u hu using fun ρ => MF.frame_change (F.e ρ) (gramAt D V ρ) (isUnit_iff_ne_zero.mpr (MF.gramAt_det ρ))
    (MF.gramAt_herm ρ) (F.A ρ) (A ρ) (F.hA ρ) (hA ρ)
  set B' := fun ρ => (fun c => u ρ * c * (u ρ)⁻¹) ⁻¹' B ρ
  have hB' : ∀ ρ, m ρ (B' ρ) = m ρ (B ρ) := by
    intro ρ
    have hc : Continuous (fun c => u ρ * c * (u ρ)⁻¹) := (continuous_const.mul continuous_id).mul continuous_const
    show m ρ ((fun c => u ρ * c * (u ρ)⁻¹) ⁻¹' B ρ) = _
    rw [← Measure.map_apply hc.measurable (hB ρ)]
    have := MU.map_conj_upq (m ρ) (u ρ)⁻¹
    simp only [inv_inv] at this
    rw [this]
  have hset : {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ B ρ,
      UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h} =
      {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ c ∈ B' ρ,
      UpqT.mat c * F.A ρ = F.A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h} := by
    ext h
    simp only [Set.mem_setOf_eq]
    refine and_congr Iff.rfl (forall_congr' fun ρ => ?_)
    exact cond_change (F.A ρ) (A ρ) (u ρ) (hu ρ) (B ρ) _
  rw [hset, ← Finset.prod_congr rfl fun ρ _ => hB' ρ]
  have hpre : (UI.brg (MF.toFrames F)) ⁻¹' {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ c ∈ B' ρ,
      UpqT.mat c * F.A ρ = F.A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h} =
      (Set.univ.pi fun v => MF.phiR F v '' B' ((Formalism.L2.Host.tauPl D).symm v)) ×ˢ kf (MF.toFrames F) K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ_pi]
    rw [finE_brg, and_comm]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro h v _
      exact (MF.cond_iff F x v (B' ((Formalism.L2.Host.tauPl D).symm v))).mp (h ((Formalism.L2.Host.tauPl D).symm v))
    · intro h ρ
      have := (MF.cond_iff F x (Formalism.L2.Host.tauPl D ρ) (B' ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)))).mpr
        (h (Formalism.L2.Host.tauPl D ρ) (Set.mem_univ _))
      rw [Equiv.symm_apply_apply] at this
      exact this
  have hmap := (UI.brg (MF.toFrames F)).toHomeomorph.toMeasurableEquiv.map_apply
    (μ := μi.prod μf) {h : GA D V | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ c ∈ B' ρ,
      UpqT.mat c * F.A ρ = F.A ρ * infMat D.sp.cm.sig V.gram (thetaC D ρ) h}
  refine Eq.trans hmap ?_
  refine Eq.trans (congrArg (μi.prod μf) hpre) ?_
  rw [Measure.prod_prod, Measure.pi_pi]
  have hf1 : μf (kf (MF.toFrames F) K) = 1 := by
    show ((νf (kf (MF.toFrames F) K))⁻¹ • νf) (kf (MF.toFrames F) K) = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hk0 hkt]
  rw [hf1, mul_one]
  have hv : ∀ v, ((m ((Formalism.L2.Host.tauPl D).symm v)).map (MF.phiR F v)) (MF.phiR F v '' B' ((Formalism.L2.Host.tauPl D).symm v)) = m ((Formalism.L2.Host.tauPl D).symm v) (B' ((Formalism.L2.Host.tauPl D).symm v)) := by
    intro v
    rw [show ((m ((Formalism.L2.Host.tauPl D).symm v)).map (MF.phiR F v)) = (m ((Formalism.L2.Host.tauPl D).symm v)).map (MF.phiR F v).toHomeomorph.toMeasurableEquiv from rfl,
      MeasurableEquiv.map_apply]
    congr 1
    exact Set.preimage_image_eq _ (MF.phiR F v).injective
  simp only [hv]
  exact Fintype.prod_equiv (Formalism.L2.Host.tauPl D).symm _ _ fun v => rfl

variable (D)

theorem measLevExists_holds : MeasLevExists D := fun V hS K hK =>
  isMeasLevW_exists (V := V) (fun _ m => Lev.IsMinf m) (fun _ _ h => h.1) (fun _ => MU.isMinf_exists _ _)
    (fun _ _ _ h h' => MU.isMinf_unique h h') hS K hK

theorem measLevDefExists_holds : MeasLevDefExists D := fun V hS hD K hK =>
  isMeasLevW_exists (V := V) (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) (fun _ _ h => h.1)
    (fun ρ => by
      rcases hD (tauE D ρ) with h | h
      · haveI : CompactSpace (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := by rw [h]; infer_instance
        exact MU.prob_exists
      · haveI : CompactSpace (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := by rw [h]; infer_instance
        exact MU.prob_exists)
    (fun _ _ _ h h' => MU.prob_unique h h') hS K hK

theorem measFDExists_holds : MeasFDExists D := fun V hS K hK => by
  obtain ⟨μ, hμ⟩ := measLevExists_holds D V hS K hK
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, -, -, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  haveI : DiscreteTopology (GQ V) := G5.hfin_disc D.sp.cm.sig V.gram
  obtain ⟨𝓕, -, h𝓕⟩ := G5.fdom_exists_all (GQ V)
  exact ⟨μ, 𝓕, hμ, h𝓕 μ⟩

end Formalism.IndefR.Eqv

end
end

