module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabCompact

theorem exists_compact_of_entries {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (C : Set (R ⊗[F] E)) (hC : IsCompact C) :
    ∃ K : Set (HA R σ J), IsCompact K ∧ ∀ h : HA R σ J, (∀ i j, (HA.mat R σ J h).1 i j ∈ C) → h ∈ K := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hc : IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  let S : Set (Matrix (Fin M) (Fin M) (R ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  let f : Matrix (Fin M) (Fin M) (R ⊗[F] E) → (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun A => MulOpposite.op (JR (F := F) R J⁻¹ * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J))
  have hf : Continuous f := MulOpposite.continuous_op.comp (continuous_const.matrix_mul
    ((continuous_id.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const))
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (R ⊗[F] E))).comp
    hc.isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage (hS.prod (hS.image hf)), fun h hh => ?_⟩
  have hm : (HA.mat R σ J h).1 ∈ S := fun i _ j _ => hh i j
  refine ⟨hm, (HA.mat R σ J h).1, hm, ?_⟩
  have hu : Formalism.UG.cT (sigR R σ) (HA.mat R σ J h).1 * JR (F := F) R J * (HA.mat R σ J h).1 = JR (F := F) R J := h.2
  have h1 : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  change MulOpposite.op _ = MulOpposite.op ((HA.mat R σ J h)⁻¹).1
  congr 1
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  rw [Matrix.mul_assoc, hu, h1]

theorem exists_compact_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG) :
    ∃ C : Set (Fin M → Af F ⊗[F] E), IsCompact C ∧ ∀ y ∈ latHat F E (L : Set (Fin M → E)), y ∈ C := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have hZ : (L.restrictScalars ℤ).FG := hL.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  let g : (Fin m → Af F) → Fin M → Af F ⊗[F] E := fun c i => ∑ k, c k ⊗ₜ[F] x k i
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    have : (fun c : Fin m → Af F => c k ⊗ₜ[F] x k i) = fun c => c k • ((1 : Af F) ⊗ₜ[F] x k i) := by
      funext c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    have hk : Continuous fun c : Fin m → Af F => c k := continuous_apply k
    have ho : Continuous fun _ : Fin m → Af F => (1 : Af F) ⊗ₜ[F] x k i := continuous_const
    exact hk.smul ho
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  refine ⟨g '' Set.pi Set.univ fun _ => intAf F, (isCompact_univ_pi fun _ => hI).image hg, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
    refine ⟨fun k => n k • a, fun k _ w => ?_, ?_⟩
    · rw [map_zsmul]
      exact zsmul_mem (ha w) _
    · funext i
      simp only [g, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero =>
    refine ⟨0, fun k _ w => ?_, ?_⟩
    · rw [Pi.zero_apply, map_zero]
      exact zero_mem _
    · funext i
      simp [g]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    refine ⟨c + d, fun k _ w => ?_, ?_⟩
    · rw [Pi.add_apply, map_add (f := _)]
      exact add_mem (hc k trivial w) (hd k trivial w)
    · funext i
      simp only [g, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨-c, fun k _ w => ?_, ?_⟩
    · rw [Pi.neg_apply, map_neg]
      exact neg_mem (hc k trivial w)
    · funext i
      simp only [g, Pi.neg_apply, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

theorem exists_compact_entries (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) :
    ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧ ∀ A : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (∀ y ∈ latHat F E (L : Set (Fin M → E)), A.mulVec y ∈ latHat F E (L : Set (Fin M → E))) →
      ∀ i j, A i j ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨C, hC, hLC⟩ := exists_compact_latHat F E L hL
  choose d hd hdL using fun j => GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  refine ⟨⋃ p : Fin M × Fin M, (fun y : Fin M → Af F ⊗[F] E =>
      y p.1 * ((1 : Af F) ⊗ₜ[F] ((d p.2 : E)⁻¹))) '' C,
    isCompact_iUnion fun p => hC.image ((continuous_apply p.1).mul continuous_const), fun A hA i j => ?_⟩
  have h1 : (1 : Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hy : (fun k => (1 : Af F) ⊗ₜ[F] (d j • (Pi.single j 1 : Fin M → E)) k) ∈
      latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL j, rfl⟩
  refine Set.mem_iUnion.2 ⟨(i, j), _, hLC _ (hA _ hy), ?_⟩
  have hd0 : (d j : E) ≠ 0 := Nat.cast_ne_zero.2 (hd j).ne'
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem exists_compact_adele (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (R : ℝ) (C : Set (Af D.host.F ⊗[D.host.F] D.host.E)) (hC : IsCompact C) :
    ∃ K : Set (AE D), IsCompact K ∧ ∀ z : AE D, finPart D z ∈ C → (∀ ρ, ‖θ ρ (infPart D z)‖ ≤ R) → z ∈ K := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  obtain ⟨s, hs⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let j : Af D.host.F ⊗[D.host.F] D.host.E → AE D := fun w => e.symm (0, w)
  have hj : Continuous j := hc.comp (continuous_const.prodMk continuous_id)
  have hj1 : ∀ w, infPart D (j w) = 0 := fun w =>
    (he (e.symm (0, w))).1.symm.trans (by rw [e.apply_symm_apply])
  have hj2 : ∀ w, finPart D (j w) = w := fun w =>
    (he (e.symm (0, w))).2.symm.trans (by rw [e.apply_symm_apply])
  have hB : IsCompact (Set.pi Set.univ fun _ : D.what₂.Tau => Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨_, (hB.prod hC).image ((hs.cont.comp continuous_fst).add (hj.comp continuous_snd)), fun z hz hR => ?_⟩
  refine ⟨(fun ρ => θ ρ (infPart D z), finPart D z), ⟨fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ), hz⟩, ?_⟩
  refine sub_eq_zero.1 (hs.ext _ ?_ fun τ => ?_)
  · change finPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), hs.fin, hj2, zero_add, sub_self]
  · change θ τ (infPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z)) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), hj1, add_zero, RingHom.map_sub, hs.comp, sub_self]

theorem exists_compact_stab : ∀ (D : D7) (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ R : ℝ, ∃ K : Set (GA D V), IsCompact K ∧ ∀ h : GA D V, (∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) → (∀ ρ i j, ‖infMat D.sp.cm.sig V.gram (θ ρ) h i j‖ ≤ R) → h ∈ K := by
  intro D V θ hθ R
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
        let W := Submodule.span D.host.E (V.L0 : Set V.V)
        change W = ⊤
        by_contra h
        let e : V.V ≃ₗ⋆[D.host.E] V.V :=
          (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
        let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
          (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
        have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
            Module.finrank D.host.E V.V := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt h
        obtain ⟨z, hz, hz₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
        have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
          rw [← V.baseLattice_isUnimodular]
          simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
            Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
          intro y hy
          have hzy : V.hT (e z) y = 0 :=
            congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
              (LinearMap.mem_ker.mp hz)
          have hyz : V.hT y (e z) = 0 := by
            have hh := V.herm.eq (e z) y
            simpa [hzy] using hh.symm
          simp [hyz]
        let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
          ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
        let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
        let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
          smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField D.host.E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries D.host.F D.host.E L (V.standardTuple_isLattice.fg.map _) hsp
  rw [hL] at hCe
  obtain ⟨C', hC', hCe'⟩ := exists_compact_adele D θ hθ R C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) C' hC'
  exact ⟨K, hK, fun h h1 h2 => hKe h fun i j =>
    hCe' _ (hCe _ (fun y hy => (h1 y).1 hy) i j) fun ρ => h2 ρ i j⟩

end GlobalTheory.StabCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsDvdCoprimeMulPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.DCos

section Generic

variable {R : Type} [CommRing R] {k : ℕ}

variable {E : Type} [Field E] [NumberField E]

end Generic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ}

theorem tmul_mem {L : Set (Fin k → E)} {a : Af F} (ha : a ∈ intAf F)
    {x : Fin k → E} (hx : x ∈ L) : (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem map_mem_latHat {L L' : Set (Fin k → E)} (f : (Fin k → Af F ⊗[F] E) →+ (Fin k → Af F ⊗[F] E))
    (h : ∀ a ∈ intAf F, ∀ x ∈ L, f (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L') {u : Fin k → Af F ⊗[F] E}
    (hu : u ∈ latHat F E L) : f u ∈ latHat F E L' := by
  have : latHat F E L ≤ (latHat F E L').comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact h a ha x hx
  exact this hu

theorem mulVec_mem_latHat {L L' : Set (Fin k → E)} {δ : Matrix (Fin k) (Fin k) E}
    (h : ∀ v ∈ L, δ *ᵥ v ∈ L') {u : Fin k → Af F ⊗[F] E} (hu : u ∈ latHat F E L) :
    δ.map (inclR (F := F) (Af F)) *ᵥ u ∈ latHat F E L' := by
  refine map_mem_latHat (Matrix.mulVecLin (δ.map (inclR (F := F) (Af F)))).toAddMonoidHom
    (fun b hb x hx => ?_) hu
  convert tmul_mem hb (h x hx) using 1
  funext i
  change ∑ j, ((1 : Af F) ⊗ₜ[F] δ i j : Af F ⊗[F] E) * b ⊗ₜ[F] x j = b ⊗ₜ[F] ∑ j, δ i j * x j
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Adelic

end GlobalTheory.Ker.DCos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExpansionOfRowHighest
section
section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr

namespace GlobalTheory.Dict.CuspAny

theorem mem_minorSpan_of_rowHighest {T : Type} [Fintype T] {p q n : ℕ} {c : T → Fin p → ℕ}
    {c' : T → Fin q → ℕ} {P : Harm.Poly ℂ T p q (Fin n)} (hP : P ∈ Harm.rowHighest ℂ c c') :
    P ∈ GaussGauge.minorSpan (Fin n) c c' := by
  classical
  have h : p + q ≤ n + (p + q) := Nat.le_add_left _ _
  let A : Matrix (Fin n) (Fin (n + (p + q))) ℂ :=
    (1 : Matrix _ _ ℂ).submatrix (Fin.castAdd (p + q)) id
  have hA : A * Aᵀ = 1 := by
    ext i j
    simp [A, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h1 : Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P ∈ GaussGauge.minorSpan _ c c' :=
    GaussGauge.orbitSpan_le_minorSpan h c c'
      (Harm.rowHighest_eq_orbitSpan h c c' ℂ ▸ Harm.colSubst_mem_rowHighest (fun _ => hA) hP)
  have h2 : Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)
      (Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P) = P := by
    rw [← AlgHom.comp_apply, Harm.colSubst_comp]
    simp only [hA]
    rw [Harm.colSubst_one, AlgHom.id_apply]
  rw [← h2]
  refine (Submodule.span_le (p := (GaussGauge.minorSpan (Fin n) c c').comap
    (Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)).toLinearMap)).2 ?_ h1
  rintro _ ⟨x, rfl⟩
  change Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A) (Harm.minorProd c c' x.1 x.2) ∈
    GaussGauge.minorSpan (Fin n) c c'
  rw [Harm.colSubst_minorProd]
  exact GaussGauge.minorProd_mem_minorSpan _ _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) (mem_minorSpan_of_rowHighest hP) hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

theorem mem_SS_of_eq_sum_thFr {J : Type} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
    {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ} (hs : IsSympl X bas)
    (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr c c' n) ga * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx
    (fun p : s × (Fin n → Fin g → ℤ) => t p.1 * A p.1 p.2)
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1 (fun p => ν p.1 p.2)
    (fun u => ?_) 0 fun p hp => h3 _ _ (right_ne_zero_of_mul hp)
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

end GlobalTheory.Dict.CuspAny

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspAny

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk φ hφ P hP Q hQ hΓ
  obtain ⟨m, a, b, t, h⟩ := (GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 φ hφ
  rcases hk with ⟨τ, hτ⟩ | h0
  · exact CuspAny.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ⟨τ, Or.inl hτ⟩ (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ
  · exact ThFr.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn
      (Or.inr (CuspClass.not_isIso_of_definite X (by omega))) (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ

end GlobalTheory.Dict.CuspAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticBasisOfSelfD
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level

theorem GlobalTheory.Ker.exists_symplectic_basis_of_selfD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r), SelfD X X.Λ →
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (_ : Fin g ≃ X.Ψ × Fin r), IsSympl X bas := by
  intro E _ _ _ r X hL

  obtain ⟨bas, hbas⟩ := GlobalTheory.Dict.Letters.exists_isSympl X hL (Fintype.equivFin (X.Ψ × Fin r)).symm
  exact ⟨_, bas, (Fintype.equivFin _).symm, hbas⟩
end

