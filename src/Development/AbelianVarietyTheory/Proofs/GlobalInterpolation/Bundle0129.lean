module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbit
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealOrbitMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_homeomorph (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    ∃ Φ : (Ainf F ⊗[F] E) ≃ₜ (I → ℂ), ∀ z ρ, Φ z ρ = θ ρ z := by
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
  exact ⟨(Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho, fun _ _ => rfl⟩

theorem mat_inv_mul {P Q : ℕ} (t : UpqT P Q) : UpqT.mat t⁻¹ * UpqT.mat t = 1 :=
  Units.inv_mul (show Formalism.UG.Upq P Q from t).1

theorem theta_projInf {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    (fun i => θ (projInf (h • ratTup (F := F) (AF F) x) 0 i)) = infMat σ J θ h *ᵥ fun i => τ (x 0 i) := by
  funext i
  let p : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have e := RingHom.map_mulVec (θ.comp p) (HA.mat (AF F) σ J h).1 (ratTup (F := F) (AF F) x 0) i
  refine e.trans ?_
  have e2 : (θ.comp p) ∘ ratTup (F := F) (AF F) x 0 = fun i => τ (x 0 i) := by
    funext j
    rw [← hθ.1]
    show θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (1 ⊗ₜ x 0 j)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [e2]
  rfl

theorem realOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  intro F E _ _ _ _ _ σ hcm I _ τ hτ θ hθ M P Q J A N hl hr x
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph hcm hτ hθ
  let v : (I → UpqT P Q) → I → Fin P ⊕ Fin Q → ℂ := fun g ρ => UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))
  have key : ∀ (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : I → Fin P ⊕ Fin Q → ℂ),
      (∀ ρ, infCoord (θ ρ) (A ρ) Y = w ρ) ↔ Y = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ w ρ) i := by
    intro Y w
    constructor
    · intro hY
      funext a i
      obtain rfl : a = 0 := Subsingleton.elim _ _
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      funext ρ
      rw [hΦ, ← hY ρ, infCoord, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    · rintro rfl ρ
      have : (fun i => θ ρ (Φ.symm fun ρ => (N ρ *ᵥ w ρ) i)) = N ρ *ᵥ w ρ := by
        funext i
        rw [← hΦ, Φ.apply_symm_apply]
      rw [infCoord, this, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
  refine ⟨⟨fun g _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i, fun g => (key _ (v g)).2 rfl⟩, fun pt hpt => ?_⟩
  have hpt' : ∀ g, pt g = fun _ i => Φ.symm fun ρ => (N ρ *ᵥ v g ρ) i := fun g => (key _ (v g)).1 (hpt g)
  refine ⟨?_, fun g g' hg => ?_, fun h t ht => ?_⟩
  · haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
    haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
    haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    haveI : SecondCountableTopology (UpqT P Q) :=
      (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
    rw [show pt = _ from funext hpt']
    refine Measurable.of_eval fun _ => Measurable.of_eval fun i => Continuous.measurable ?_
    refine Φ.symm.continuous.comp (continuous_pi fun ρ => (continuous_apply i).comp (f := fun a => N ρ *ᵥ v a ρ) ?_)
    exact continuous_const.matrix_mulVec
      ((GlobalTheory.VolPairExists.continuous_mat.comp (continuous_apply ρ).inv).matrix_mulVec continuous_const)
  · rw [hpt', hpt', show v g = v g' from funext hg]
  · rw [hpt']
    refine ((key _ (v t)).1 fun ρ => ?_).symm
    have e : A ρ * infMat σ J (θ ρ) h⁻¹ = UpqT.mat (t ρ)⁻¹ * A ρ := by
      calc A ρ * infMat σ J (θ ρ) h⁻¹
          = UpqT.mat (t ρ)⁻¹ * (UpqT.mat (t ρ) * A ρ) * infMat σ J (θ ρ) h⁻¹ := by
            rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
        _ = UpqT.mat (t ρ)⁻¹ * A ρ := by
            rw [ht, Matrix.mul_assoc, Matrix.mul_assoc, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, mul_inv_cancel,
              Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_one, Matrix.mul_one]
    rw [infCoord, theta_projInf (hθ ρ), Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]

end GlobalTheory.RealOrbitMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinPartInvSmulMemLatHatIffStabMulLevel
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.AdelicOrbit

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem parts_inj (x y : AF F ⊗[F] E)
    (h1 : (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom y)
    (h2 : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem mem_parts (g : GL (Fin M) (AF F ⊗[F] E)) :
    g ∈ HR (AF F) σ J ↔
      Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g ∈ HR (Af F) σ J := by
  have := GlobalTheory.UnitarySplit.mem_iff _ _ (parts_inj (F := F) (E := E)) (sigR _ σ) (sigR _ σ) (sigR _ σ)
    (GlobalTheory.UnitarySplit.map_sig _ _) (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g
  rw [GlobalTheory.UnitarySplit.map_JR, GlobalTheory.UnitarySplit.map_JR] at this
  exact this

theorem exists_fin (h : HA (AF F) σ J) :
    ∃ k : HA (Af F) σ J, (HA.mat (Af F) σ J k).1 = finMat σ J h :=
  ⟨(⟨_, ((mem_parts σ J (HA.mat (AF F) σ J h)).1 h.2).2⟩ : HR (Af F) σ J), rfl⟩

theorem exists_lift (k : HA (Af F) σ J) :
    ∃ h : HA (AF F) σ J, finMat σ J h = (HA.mat (Af F) σ J k).1 ∧
      (HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hs : ∀ a b, ∃ x, (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x = a ∧
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x = b := fun a b => by
    refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp
  obtain ⟨g, g1, g2⟩ := GlobalTheory.UnitarySplit.gl_glue _ _ parts_inj hs 1 (HA.mat (Af F) σ J k)
  have hg : g ∈ HR (AF F) σ J := (mem_parts σ J g).2 ⟨g1 ▸ one_mem _, g2 ▸ k.2⟩
  exact ⟨(⟨g, hg⟩ : HR (AF F) σ J), congrArg Units.val g2, congrArg Units.val g1⟩

omit [NumberField E] in
theorem projFin_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) :
    projFin (h • ratTup (F := F) (AF F) x) 0 = finMat σ J h *ᵥ fun i => inclR (F := F) (Af F) (x 0 i) := by
  funext i
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

omit [NumberField E] in
theorem projInf_smul (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) (i : Fin M) :
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom ((h • ratTup (F := F) (AF F) x) 0 i) =
      ((HA.mat (AF F) σ J h).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom *ᵥ
        fun i => inclR (F := F) (Ainf F) (x 0 i)) i := by
  have := RingHom.map_mulVec (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
    (HA.mat (AF F) σ J h).1 (fun i => inclR (F := F) (AF F) (x 0 i)) i
  refine this.trans ?_
  congr 1

end SlopeTestRemainingChoices

theorem mem_latHat_iff : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → ∀ x : Fin 1 → Fin M → E, x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ h : HA (AF F) σ J, projFin (h⁻¹ • ratTup (F := F) (AF F) x) 0 ∈ latHat F E (L : Set (Fin M → E)) ↔ ∃ a ∈ Hstab (AF F) σ J x, a⁻¹ * h ∈ stab σ J (L : Set (Fin M → E)) := by
  intro hT F E _ _ _ _ _ σ hcm hur M J hJ L hL β hβ x hx hq h
  constructor
  · intro hm
    have hO := (hT F E σ hcm hur M J hJ L hL β hβ (x 0) hx hq).2.1
    obtain ⟨k', hk'⟩ := exists_fin σ J h⁻¹
    have h1 : k'⁻¹ ∈ {h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x 0 i)) ∈
        latHat F E (L : Set (Fin M → E))} := by
      rw [Set.mem_setOf_eq, inv_inv, actV_eq, hk', ← projFin_smul]
      exact hm
    rw [hO] at h1
    obtain ⟨af, haf, kf, hkf, e⟩ := h1
    obtain ⟨a, ha1, ha2⟩ := exists_lift σ J af
    refine ⟨a, ?_, ?_⟩
    · change a • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x
      funext c i
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine parts_inj _ _ ?_ ?_
      · rw [projInf_smul, ha2, Matrix.one_mulVec]
        rfl
      · have h2 := congrFun (projFin_smul σ J a x) i
        rw [ha1] at h2
        refine h2.trans ?_
        have h3 : af • ratTup (F := F) (Af F) (fun _ : Fin 1 => x 0) = ratTup (F := F) (Af F) (fun _ => x 0) := haf
        exact congrFun (congrFun h3 0) i
    · have e' : k' * af = kf⁻¹ := by
        have e2 : af * kf = k'⁻¹ := e
        rw [← inv_inv k', ← e2]
        group
      have h2 : h⁻¹ * a ∈ stab σ J (L : Set (Fin M → E)) := by
        intro y
        rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ha1, ← hk', ← Matrix.mulVec_mulVec, ← actV_eq, ← actV_eq, ← actV_mul, e']
        exact (inv_mem hkf : kf⁻¹ ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E)))) y
      have h3 := inv_mem h2
      rwa [_root_.mul_inv_rev, inv_inv] at h3
  · rintro ⟨a, ha, hk⟩
    have h1 : a⁻¹ • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) x := inv_mem ha
    have h2 : h⁻¹ • ratTup (F := F) (AF F) x = (a⁻¹ * h)⁻¹ • ratTup (F := F) (AF F) x := by
      conv_rhs => rw [← h1, ← mul_smul]
      congr 1
      group
    rw [h2, projFin_smul]
    exact ((inv_mem hk : (a⁻¹ * h)⁻¹ ∈ stab σ J (L : Set (Fin M → E))) _).1
      (AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x 0, hx, rfl⟩)

end GlobalTheory.AdelicOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormAndSelfDualLatticeInFrameCoords
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.FrameDict

theorem form_coords {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W : Formalism.BasicNotions.HSpace E) (x y : Fin W.rank → E) :
    hE cm.sig W.gram x y = W.hT (∑ i, x i • W.frame i) (∑ i, y i • W.frame i) := by
  have hs : ∀ a : E, (cm.sig : E →+* E) a = star a := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, hs,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (z : E) :
    z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem dict : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (W : HSpace E), (∀ a b : W.V, hE cm.sig W.gram (fun i => W.frame.repr a i) (fun i => W.frame.repr b i) = W.hT a b) ∧ ∃ L : Submodule (𝓞 E) (Fin W.rank → E), IsSelfDualLat cm.sig W.gram L ∧ (L : Set (Fin W.rank → E)) = latC W := by
  intro F E _ _ _ _ _ _ cm W
  refine ⟨fun a b => ?_, ?_⟩
  · rw [form_coords, W.frame.sum_repr, W.frame.sum_repr]
  obtain ⟨L, hfg, hsp, hL⟩ := exists_lattice W
  refine ⟨L, ⟨hfg, hsp, fun y => ?_⟩, hL⟩
  have hmem : ∀ x : Fin W.rank → E, x ∈ L ↔ ∑ i, x i • W.frame i ∈ W.L0 := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hu : ∀ v : W.V, (∀ u ∈ W.L0, W.hT u v ∈ (1 : Submodule (𝓞 E) E)) ↔ v ∈ W.L0 := fun v => by
    have h : Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 := W.baseLattice_isUnimodular
    conv_rhs => rw [← h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  rw [hmem, ← hu]
  constructor
  · intro h x hx
    rw [form_coords, ← mem_one_iff]
    exact h _ ((hmem x).1 hx)
  · intro h u hu'
    have := h (fun i => W.frame.repr u i) (by rw [hmem, W.frame.sum_repr]; exact hu')
    rw [form_coords, W.frame.sum_repr, ← mem_one_iff] at this
    exact this

end GlobalTheory.FrameDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpq
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabEmbClosed

theorem isClosedEmbedding_conj_fromBlocks {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m (n ⊕ Unit) ℂ) (N : Matrix (n ⊕ Unit) m ℂ) (hNM : N * M = 1) :
    IsClosedEmbedding
      (fun X : Matrix n n ℂ => M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun Y : Matrix m m ℂ => (N * Y * M).toBlocks₁₁) ?_ ?_ ?_
  · intro X
    have : N * (M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) * M
        = fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) := by
      calc _ = (N * M) * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * (N * M) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hNM, Matrix.one_mul, Matrix.mul_one]
    simp only [this, toBlocks_fromBlocks₁₁]
  · have h : Continuous fun Y : Matrix m m ℂ => N * Y * M :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h.matrix_submatrix Sum.inl Sum.inl
  · exact (continuous_const.matrix_mul
      (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const

theorem isClosedEmbedding_of_isStabEmb : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  intro P Q P' Q' hd x₀ hx j hj
  obtain ⟨C, hC, hCx, hj⟩ := hj
  obtain ⟨N, B, hNM, hMN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hd hx hC hCx
  have key : ∀ g : UpqT P' Q', (j g).mat =
      C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) * N := by
    intro g
    obtain ⟨h1, h2⟩ := hj g
    have h3 : (j g).mat * replicateCol Unit x₀ = replicateCol Unit x₀ := by
      rw [← replicateCol_mulVec, h1]
    have h4 : (j g).mat * C.fromCols (replicateCol Unit x₀) =
        C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) := by
      rw [mul_fromCols, fromCols_mul_fromBlocks, h2, h3]
      simp
    rw [← h4, Matrix.mul_assoc, hMN, Matrix.mul_one]
  refine IsClosedEmbedding.of_comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q)).isEmbedding ?_
  have := (isClosedEmbedding_conj_fromBlocks _ N hNM).comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P') (Q := Q'))
  convert this using 1
  funext g
  exact key g

end GlobalTheory.StabEmbClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDual
section
noncomputable section

namespace GlobalTheory.VolStabImage

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem map_restrict_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), M = P + Q → ∀ (J : Matrix (Fin M) (Fin M) E), J.det ≠ 0 → ∀ (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∀ (L : Set (Fin M → E)), MeasurableSet (stab σ J L : Set (HA (AF F) σ J)) → ∀ (cd : CDHaar) (μ : Measure (HA (AF F) σ J)), (∀ B : I → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) → μ {h | StabHat F L (finMat σ J h) ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat σ J (θ ρ) h} = ∏ ρ, cd.cd P Q (B ρ)) → (∃ N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ, (∀ ρ, N ρ * A ρ = 1) ∧ ∀ ρ, A ρ * N ρ = 1) ∧ ∃ ψ : HA (AF F) σ J →* (I → UpqT P Q), Continuous ψ ∧ (∀ h ρ, UpqT.mat (ψ h ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) ∧ (μ.restrict (stab σ J L)).map ψ = Measure.pi fun _ => cd.cd P Q := by
  intro F E _ _ _ _ _ σ hcm I _ τ θ hθ M P Q hM J hJ A hA L hL cd μ hμ
  have hd : ∀ ρ, IsUnit (J.map (τ ρ)).det := fun ρ => by
    have : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    rw [this]
    exact ((map_ne_zero (τ ρ)).2 hJ).isUnit
  let N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hl : ∀ ρ, N ρ * A ρ = 1 := fun ρ => by
    change (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q) * A ρ = 1
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (hd ρ)]
  have e : Fin M ≃ (Fin P ⊕ Fin Q) := Fintype.equivOfCardEq (by simpa using hM)
  have hr : ∀ ρ, A ρ * N ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv e).1 (hl ρ)
  refine ⟨⟨N, hl, hr⟩, ?_⟩
  choose ψ hψ hψm using fun ρ => GlobalTheory.VolPairExists.exists_hom _ (continuous_infMat J (hθ ρ))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul σ J (θ ρ)) (infMat_unitary J hcm (hθ ρ)) (hA ρ) (hl ρ) (hr ρ)
  have hψA : ∀ h ρ, UpqT.mat (ψ ρ h) * A ρ = A ρ * infMat σ J (θ ρ) h := fun h ρ => by
    rw [hψm, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hc : Continuous (MonoidHom.pi ψ) := continuous_pi hψ
  refine ⟨MonoidHom.pi ψ, hc, hψA, ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (UpqT P Q) :=
    (GlobalTheory.UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := cd.haar P Q
  refine (Measure.pi_eq fun B hB => ?_).symm
  have hm : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  rw [Measure.map_apply hc.measurable hm, Measure.restrict_apply (hc.measurable hm), ← hμ B hB]
  congr 1
  ext h
  refine and_comm.trans (and_congr Iff.rfl ?_)
  rw [Set.mem_preimage, Set.mem_univ_pi]
  refine forall_congr' fun ρ => ⟨fun hb => ⟨_, hb, hψA h ρ⟩, ?_⟩
  rintro ⟨b, hb, hbA⟩
  have : b = ψ ρ h := GlobalTheory.VolPairExists.mat_injective (by
    rw [hψm, ← hbA, Matrix.mul_assoc, hr, Matrix.mul_one])
  subst this
  exact hb

end GlobalTheory.VolStabImage
end
end

