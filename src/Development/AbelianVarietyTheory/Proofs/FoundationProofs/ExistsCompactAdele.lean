module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory NumberField Matrix Topology GlobalTheory.Mem.Vol
open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.VolPairExists
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

section Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem infEmb_tmul (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (a : Ainf F) (x : E) : θ (a ⊗ₜ x) = GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) a * τ x :=
  haveI := h.1
  GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 a x

theorem infEmb_unique (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ θ' : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (hθ' : IsInfEmb τ θ') : θ = θ' := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [infEmb_tmul h hθ, infEmb_tmul h hθ']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infEmb_continuous {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) : Continuous θ :=
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  IsModuleTopology.continuous_of_ringHom (R := Ainf F) θ hθ.2

theorem infEmb_sigR (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (z : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ z) = starRingEnd ℂ (θ z) := by
  haveI := h.1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : sigR (Ainf F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
    rw [e, infEmb_tmul h hθ, infEmb_tmul h hθ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, h.2.2.2]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem infEmb_bijective (h : IsCMExt F E σ) {I : Type} {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    Function.Bijective fun (z : Ainf F ⊗[F] E) (ρ : I) => θ ρ z := by
  haveI := h.1
  haveI := h.2.1
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x) := h.2.2.2
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc1 : c ≠ 1 := fun e => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, e, AlgEquiv.one_apply]
  choose θ₀ h1 h2 using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := fun φ => by
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by simp only [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · exact absurd ⟨i, by rw [← e]; ext x; simp⟩ hn
  have hb := GlobalTheory.InfAdeleCM.bijective c h.2.2.1 hc1 hc θ₀
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ₀ φ) (h1 φ) (h2 φ)) _ hΨ
  have hinj : Function.Injective τ := fun i j e => hτ.1 (by simp only [e])
  have e0 : ∀ ρ, θ ρ = θ₀ (τ ρ) := fun ρ => infEmb_unique h (hθ ρ) ⟨h1 _, h2 _⟩
  have := ((Equiv.ofInjective τ hinj).symm.arrowCongr (Equiv.refl ℂ)).bijective.comp hb
  convert this using 1
  funext z ρ
  rw [e0]
  rfl

theorem exists_compact_adele (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) (R : ℝ) (C : Set (Af F ⊗[F] E))
    (hC : IsCompact C) : ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ ∀ z : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z ∈ C →
      (∀ ρ, ‖θ ρ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)‖ ≤ R) → z ∈ K := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology
  have hb := infEmb_bijective h hτ hθ
  let Θ : Ainf F ⊗[F] E →+ (I → ℂ) := (Pi.ringHom θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  let Φ := (Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho
  have hB : IsCompact (Φ ⁻¹' Set.pi Set.univ fun _ : I => Metric.closedBall (0 : ℂ) R) :=
    Φ.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨_, (hB.prod hC).image hc, fun z hz hR => ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩⟩
  · rw [(he z).1]
    exact fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ)
  · rw [(he z).2]
    exact hz

variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_infMat {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    Continuous fun h => infMat σ J θ h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact (h1.matrix_map (GlobalTheory.Member.Arch.continuous_inf F E)).matrix_map (infEmb_continuous hθ)

theorem continuous_finMat : Continuous fun h => finMat σ J h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact h1.matrix_map (GlobalTheory.LevelOpen.continuous_fin F E)

theorem JR_map {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    (JR (F := F) (Ainf F) J).map θ = J.map τ :=
  Matrix.ext fun _ _ => hθ.1 _

theorem infMat_unitary (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (g : HA (AF F) σ J) : (infMat σ J θ g)ᴴ * J.map τ * infMat σ J θ g = J.map τ := by
  have hm := GlobalTheory.Member.Arch.inf_mem σ J (HA.mat (AF F) σ J g) g.2
  have h2 := GlobalTheory.Member.Arch.form_map _ θ (infEmb_sigR h hθ)
    ((HA.mat (AF F) σ J g).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))) (JR (Ainf F) J)
  rw [← JR_map J hθ]
  exact h2.symm.trans (congrArg (fun X => X.map θ) hm)


variable (σ) in
def stab (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | StabHat F L (finMat σ J h)}
  one_mem' := fun y => by rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb y => by
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := fun {a} ha y => by
    refine Iff.trans ?_ (ha _).symm
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]

theorem isOpen_stab (L : Submodule (𝓞 E) (Fin M → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) : IsOpen (stab σ J L : Set (HA (AF F) σ J)) := by
  have := Unfold.topGroupHA σ J
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds F E M L hfg hsp 1 one_pos
  have hc := continuous_finMat (σ := σ) J
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [finMat_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, finMat_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_)
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one,
      Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end Chart

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isCMExt (cm : CMData F E) : IsCMExt F E cm.sig :=
  ⟨cm.totReal, cm.cmUnram.1, cm.deg2, cm.cmUnram.2.1⟩

theorem isHermND (cm : CMData F E) (W : HSpace E) : IsHermND cm.sig W.gram :=
  ⟨fun i j => W.herm.eq (W.frame j) (W.frame i), GlobalTheory.StabCompact.det_gram_ne_zero W⟩

theorem exists_lattice (W : HSpace E) : ∃ L : Submodule (𝓞 E) (Fin W.rank → E), L.FG ∧
    Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ ∧ (L : Set (Fin W.rank → E)) = latC W := by
  let f := W.frame.equivFun.toLinearMap
  refine ⟨W.L0.map (f.restrictScalars (𝓞 E)), W.standardTuple_isLattice.fg.map _, ?_, ?_⟩
  · have : (W.L0.map (f.restrictScalars (𝓞 E)) : Set (Fin W.rank → E)) = f '' W.L0 := rfl
    have hspan : Submodule.span E (W.L0 : Set W.V) = ⊤ := by
      classical
      by_contra hspan
      obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
      obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis W.hT W.nondeg W.frame
      let μ := ∑ j, star (φ (W.frame j)) • bs j
      have hμ : ∀ v, W.hT μ v = φ v := by
        have key : W.hT μ = φ := by
          apply W.frame.ext
          intro i
          dsimp [μ]
          rw [map_sum, LinearMap.sum_apply]
          have hs : ∀ j, W.hT (star (φ (W.frame j)) • bs j) (W.frame i) =
              φ (W.frame j) * (if i = j then 1 else 0) := by
            intro j
            rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
            congr 1
            rw [← W.herm.eq (W.frame i) (bs j), hbs]
            split_ifs <;> simp
          simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        intro v
        rw [key]
      have hμ₀ : μ ≠ 0 := by
        intro h
        apply hφ₀
        ext y
        simpa [h] using (hμ y).symm
      have hline (a : E) : a • μ ∈ W.L0 := by
        rw [← W.baseLattice_isUnimodular]
        change a • μ ∈ Formalism.E.hdual W.hT W.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply]
        intro y hy
        have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
        simp [← W.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
      obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
        (show μ ∉ (⊥ : Submodule E W.V) by simpa using hμ₀)
      let g := ψ.restrictScalars (𝓞 E)
      have hmap (x : E) : x ∈ W.L0.map g := by
        refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
        change ψ ((x / ψ μ) • μ) = x
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
      obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
        (S := nonZeroDivisors (𝓞 E)) (W.standardTuple_isLattice.fg.map g)
      have hinj := IsFractionRing.injective (𝓞 E) E
      have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
        fun h => ha (hinj (h.trans (map_zero _).symm))
      have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
        have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
        rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
          one_mul] at hx
      apply RingOfIntegers.not_isField E
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
      intro a ha
      obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
      refine ⟨b, hinj ?_⟩
      rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  · ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, W.frame.equivFun x i • W.frame i ∈ W.L0
      rwa [W.frame.sum_equivFun]
    · intro hv
      refine ⟨W.frame.equivFun.symm v, ?_, W.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv

end Main

end GlobalTheory.Mem.VolExists
