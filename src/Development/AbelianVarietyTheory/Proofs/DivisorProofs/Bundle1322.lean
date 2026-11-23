module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay LineDeriv

namespace GlobalTheory.ArchDecay.SchAStab

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem pureA_line (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t : ℝ) :
    pureA F f g (x + fun i => infAd F (t • v i)) = f (arch F x + t • v) * g (fun i => (x i).2) := by
  unfold pureA
  congr 2
  · funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • v i)) = evI F (x i) + t • v i
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
    rfl
  · funext i
    exact add_zero (x i).2

theorem hasDerivAt_line (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t : ℝ => pureA F f g (x + fun i => infAd F (t • v i)))
      (fderiv ℝ f (arch F x) v * g (fun i => (x i).2)) 0 := by
  simp only [pureA_line]
  have h1 : HasDerivAt (fun t : ℝ => arch F x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (arch F x)
  have h2 : HasDerivAt (fun t : ℝ => f (arch F x + t • v)) (fderiv ℝ f (arch F x) v) 0 :=
    (f.differentiableAt (x := arch F x)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  exact h2.mul_const _

theorem dD_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : κ → mixedEmbedding.mixedSpace F) : dD F v (pureA F f g) = pureA F (∂_{v} f : SchwartzMap _ ℂ) g := by
  funext x
  rw [dD, (hasDerivAt_line F f g x v).deriv]
  show _ = (∂_{v} f : SchwartzMap _ ℂ) (arch F x) * _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

def mulL (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (⇑l) f

theorem mulL_apply (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    mulL F l f y = (l y : ℂ) * f y := by
  rw [mulL, SchwartzMap.smulLeftCLM_apply_apply l.hasTemperateGrowth, Complex.real_smul]

theorem mM_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : mM F l (pureA F f g) = pureA F (mulL F l f) g := by
  funext x
  simp only [mM, pureA, mulL_apply, mul_assoc]
  rfl

theorem mem_schA_mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    mM F l Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    rw [mM_pureA]
    exact Submodule.subset_span ⟨mulL F l f, g, hg, rfl⟩
  | zero =>
    have : mM F l (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [mM]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have : mM F l (Φ + Ψ) = mM F l Φ + mM F l Ψ := by funext x; simp [mM, mul_add]
    rw [this]; exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have : mM F l (a • Φ) = a • mM F l Φ := by funext x; simp [mM]; ring
    rw [this]; exact Submodule.smul_mem _ a h

theorem archimedeanDirectionalDerivative_mem_adelicSchwartz (v : κ → mixedEmbedding.mixedSpace F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∀ x : κ → AF F, DifferentiableAt ℝ (fun t : ℝ => Φ (x + fun i => infAd F (t • v i))) 0) ∧
      dD F v Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨fun x => (hasDerivAt_line F f g x v).differentiableAt, ?_⟩
    rw [dD_pureA]
    exact Submodule.subset_span ⟨_, g, hg, rfl⟩
  | zero =>
    refine ⟨fun x => differentiableAt_const _, ?_⟩
    have : dD F v (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [dD]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun x => (h1.1 x).add (h2.1 x), ?_⟩
    have : dD F v (Φ + Ψ) = dD F v Φ + dD F v Ψ := by
      funext x
      simp only [dD, Pi.add_apply]
      exact deriv_add (h1.1 x) (h2.1 x)
    rw [this]; exact Submodule.add_mem _ h1.2 h2.2
  | smul a Φ _ h =>
    refine ⟨fun x => (h.1 x).const_mul a, ?_⟩
    have : dD F v (a • Φ) = a • dD F v Φ := by
      funext x
      simp only [dD, Pi.smul_apply, smul_eq_mul]
      exact deriv_const_mul a (h.1 x)
    rw [this]; exact Submodule.smul_mem _ a h.2

theorem app_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ),
    ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  intro F _ _ κ _ o f hf
  rcases o with v | l
  · exact (archimedeanDirectionalDerivative_mem_adelicSchwartz F v hf).2
  · exact mem_schA_mM F l hf

end GlobalTheory.ArchDecay.SchAStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSmoothFunctionCentreOrbitFiniteDime
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.KilledFinCentre

theorem centre_orbit_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  intro E _ _ _ b q hq
  classical
  obtain ⟨T, hT, hZ⟩ := _root_.GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps E b
  let p : Module.End ℂ (Sm E b) → Polynomial ℂ := fun t =>
    if h : ∃ τ u, t = cap τ u then q h.choose h.choose_spec.choose else 1
  have hp : ∀ t ∈ T, p t ≠ 0 := by
    intro t ht
    simp only [p]
    split_ifs with h
    · exact hq _ _
    · exact one_ne_zero
  have hkill : ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) →
      ∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0 := by
    intro ψ hψ t ht
    have h : ∃ τ u, t = cap τ u := hT t ht
    have key : ∀ τ u, t = cap τ u → Polynomial.aeval t (q τ u) ψ = 0 := by
      rintro τ u rfl; exact hψ τ u
    simp only [p, dif_pos h]
    exact key _ _ h.choose_spec.choose_spec
  have hc : ∀ s ∈ T, ∀ t ∈ T, Commute s t := fun s hs t ht =>
    GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hZ ▸ Algebra.subset_adjoin hs) (hZ ▸ Algebra.subset_adjoin ht)
  obtain ⟨X', hX', hX'e⟩ := _root_.GlobalTheory.eigencharacters_finite_of_commuting_annihilated _ T p hc hp
  refine ⟨X', ∏ t ∈ T, (p t).natDegree, hX', fun ψ hψ => ?_⟩
  rw [hZ]
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.killed_span_adjoin_finrank_le _ T p hc hp ψ (hkill ψ hψ)
  exact ⟨h1, h2, hX'e ψ (hkill ψ hψ)⟩

end GlobalTheory.KilledFinCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.FDim

theorem fromSpecStalk_comp_spec {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem isClosed_origin (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (p : Sp K) :
    IsClosed ({(η[A]).left.base p} : Set A.left) := by
  have hr : Set.range (η[A]).left.base = {(η[A]).left.base p} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hs : Subsingleton (Sp K) := inferInstance
      obtain rfl : q = p := hs.elim q p
      rfl
    · rintro rfl
      exact ⟨p, rfl⟩
  rw [← hr]
  exact (η[A]).left.isClosedEmbedding.isClosed_range

theorem cechLB_triv_finrank_one_two : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  intro K _ _ A _ g hA hsm κ _ _ D hD hcov
  obtain ⟨L, H, _, j, hL, hproj, hgen, hj, hci, hfin, hK⟩ := _root_.GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel K A hA
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hx₀ : (η[A]).left.base p ∈ Set.range (η[A]).left.base := ⟨p, rfl⟩
  obtain ⟨J, C, φ, hJ, hφ, hfree, hbdd, hcok, hfib, hiso⟩ :=
    _root_.GlobalTheory.MumfordLocalComplex.exists_ideal_free_complex_at_origin K A g hA hsm L H j hL hproj hgen hj hci hfin hK _ hx₀
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.FinSubGen.ideal_eq_span_fin K A g hA hsm H j hj hci hfin _ hx₀ J hJ
  obtain ⟨hJt, hart⟩ := _root_.GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing K A H j hj hci hfin _ hx₀ J hJ
  subst hf
  let σ : K →+* A.left.presheaf.stalk ((η[A]).left.base p) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.hom.appTop ≫
      A.left.presheaf.germ ⊤ ((η[A]).left.base p) trivial).hom
  have hσ : A.left.fromSpecStalk ((η[A]).left.base p) ≫ A.hom = Spec.map (CommRingCat.ofHom σ) := by
    rw [fromSpecStalk_comp_spec]
    rfl
  have hloc : IsLocalHom σ := ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩
  obtain ⟨-, -, hreg, hdim⟩ := _root_.GlobalTheory.StabFlat.stalk_of_smooth_local K A.left A.hom g hsm _ (isClosed_origin K A p) σ hσ hloc
  have hbot : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot (A.left.presheaf.stalk ((η[A]).left.base p)))
  haveI : IsRegularLocalRing (A.left.presheaf.stalk ((η[A]).left.base p)) :=
    IsRegularLocalRing.of_ringEquiv e
  have hdim' : ringKrullDim (A.left.presheaf.stalk ((η[A]).left.base p)) = g := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact hdim
  have hex := _root_.GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing _ g hdim' C hfree hbdd hfib
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.finrank_homology_one_two_of_dual_resolution _ g hdim' f hJt hart C hfree hex hcok K φ hφ
  haveI := hA.proper
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K A.left A.hom (LB.triv A.left) κ D
      (LB.isLB_triv _) inferInstance hproj hD hcov i
  · obtain ⟨e1⟩ := hiso κ D hD hcov 1
    rw [← e1.finrank_eq]
    exact h1
  · obtain ⟨e2⟩ := hiso κ D hD hcov 2
    rw [← e2.finrank_eq]
    exact h2

end GlobalTheory.AbCoh.FDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexLineBundleTermTorsionFreeCharZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)

namespace GlobalTheory.CechPic

theorem intCast_mul_eq_zero_of_isIntegral {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X]
    (hc : CharZero Γ(X, ⊤)) (W : X.Opens) {m : ℤ} (hm : m ≠ 0) {c : Γ(X, W)}
    (h : (m : Γ(X, W)) * c = 0) : c = 0 := by
  by_cases hW : Nonempty W
  · have hinj := AlgebraicGeometry.map_injective_of_isIntegral X (homOfLE (le_top : W ≤ ⊤))
    have hm' : (m : Γ(X, W)) ≠ 0 := by
      intro h0
      apply hm
      have : (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (m : Γ(X, ⊤)) =
          (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom 0 := by
        rw [map_intCast, map_zero, h0]
      exact_mod_cast hinj this
    exact (mul_eq_zero.1 h).resolve_left hm'
  · have hb : W = ⊥ := eq_bot_iff.2 fun x hx => (hW ⟨⟨x, hx⟩⟩).elim
    subst hb
    have := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
    exact Subsingleton.elim _ _

theorem cechLB_X_noZSMulDivisors : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) →
    ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 →
    ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  intro X _ hc f M κ _ D n m hm x hx
  have key : ∀ (V : X.Opens) (y : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V), m • y = 0 → y = 0 := by
    intro V y hy
    refine GlobalTheory.AbLaw.SecOnR.ext (R := ℤ) (f := f) fun i => ?_
    let c : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V →+ Γ(X, V ⊓ M.U i) :=
      { toFun := fun z => GlobalTheory.AbLaw.SecOnR.coord z i
        map_zero' := GlobalTheory.AbLaw.SecOnR.coord_zero i
        map_add' := fun z w => GlobalTheory.AbLaw.SecOnR.coord_add z w i }
    have hi : c (m • y) = c 0 := congrArg c hy
    rw [map_zsmul, map_zero, zsmul_eq_mul] at hi
    exact intCast_mul_eq_zero_of_isIntegral hc _ hm hi
  funext s
  refine key _ (x s) ?_
  exact congrFun hx s

end GlobalTheory.CechPic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceQuotientActionTop
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho.CRTSplit

variable {k O C V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup V] [Module k V]

abbrev actC (τ : O →+* Module.End k V) : MonoidAlgebra k C →ₐ[k] Module.End k V :=
  MonoidAlgebra.lift k (Module.End k V) C (τ.comp (algebraMap C O)).toMonoidHom

abbrev chiC (χ : C →+* k) : MonoidAlgebra k C →ₐ[k] k :=
  MonoidAlgebra.lift k k C χ.toMonoidHom

theorem actC_apply (τ : O →+* Module.End k V) (f : MonoidAlgebra k C) (v : V) :
    actC τ f v = ∑ c ∈ f.coeff.support, f.coeff c • τ (algebraMap C O c) v := by
  rw [actC, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem chiC_apply (χ : C →+* k) (f : MonoidAlgebra k C) :
    chiC χ f = ∑ c ∈ f.coeff.support, f.coeff c * χ c := by
  rw [chiC, MonoidAlgebra.lift_apply, Finsupp.sum]
  rfl

theorem actC_of (τ : O →+* Module.End k V) (c : C) :
    actC τ (MonoidAlgebra.of k C c) = τ (algebraMap C O c) := by
  rw [actC, MonoidAlgebra.lift_of]; rfl

theorem chiC_of (χ : C →+* k) (c : C) : chiC χ (MonoidAlgebra.of k C c) = χ c := by
  rw [chiC, MonoidAlgebra.lift_of]; rfl

theorem actC_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (f : MonoidAlgebra k C) (hf : ∀ i, chiC (χ i) f = 0) (v : V) :
    actC τ f v = 0 := by
  have hmem : actC τ f v ∈ jSub τ χ ⊤ := by
    apply Submodule.subset_span
    refine ⟨f.coeff.support.card, fun l => f.coeff (f.coeff.support.equivFin.symm l),
      fun l => (f.coeff.support.equivFin.symm l : C), v, trivial, fun i => ?_, ?_⟩
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x * χ i x)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x * χ i x), ← chiC_apply, hf i]
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x • τ (algebraMap C O x) v)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x • τ (algebraMap C O x) v),
        actC_apply]
  rw [hJ] at hmem
  simpa using hmem

theorem actC_mem_mSub (τ : O →+* Module.End k V) (χ : C →+* k) (f : MonoidAlgebra k C)
    (hf : chiC χ f = 0) (x : V) : actC τ f x ∈ mSub τ χ ⊤ := by
  have h : actC τ f x = ∑ c ∈ f.coeff.support, f.coeff c • (τ (algebraMap C O c) x - χ c • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [actC_apply, ← Finset.sum_smul, ← chiC_apply, hf, zero_smul, sub_zero]
  rw [h]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, x, trivial, rfl⟩)

theorem actC_mSub_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (i : Idx) (e : MonoidAlgebra k C) (he : ∀ l, l ≠ i → chiC (χ l) e = 0)
    (y : V) (hy : y ∈ mSub τ (χ i) ⊤) : actC τ e y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, x, -, rfl⟩ := hz
    have h2 : τ (algebraMap C O c) x - χ i c • x =
        actC τ (MonoidAlgebra.of k C c - algebraMap k _ (χ i c)) x := by
      rw [map_sub, AlgHom.commutes, actC_of, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [h2, ← Module.End.mul_apply, ← map_mul]
    refine actC_eq_zero τ χ hJ _ (fun l => ?_) x
    rw [map_mul]
    by_cases hl : l = i
    · subst hl
      rw [map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply, sub_self,
        mul_zero]
    · rw [he l hl, zero_mul]
  | zero => simp
  | add _ _ _ _ h1 h2 => rw [map_add (f := _), h1, h2, add_zero]
  | smul a _ _ h => rw [map_smul, h, smul_zero]

end GlobalTheory.HTRho.CRTSplit


open GlobalTheory.HTRho.CRTSplit in
theorem GlobalTheory.HTRho.finrank_homO_eq_sum_quot : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k),
    Function.Injective χ → jSub τ χ ⊤ = ⊥ →
    finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  intro k O C Idx W V _ _ _ _ _ _ _ _ _ _ _ σW τ χ hχ hJ
  classical
  have hb : ∀ i j, ∃ b : MonoidAlgebra k C, i ≠ j → chiC (χ i) b = 1 ∧ chiC (χ j) b = 0 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp (hχ.ne hij)
    have hc' : χ i c - χ j c ≠ 0 := sub_ne_zero.mpr hc
    refine ⟨(χ i c - χ j c)⁻¹ • (MonoidAlgebra.of k C c - algebraMap k _ (χ j c)), fun _ => ⟨?_, ?_⟩⟩
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        smul_eq_mul, inv_mul_cancel₀ hc']
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self, smul_zero]
  choose b hb using hb
  let e : Idx → MonoidAlgebra k C := fun i => ∏ j ∈ Finset.univ.erase i, b i j
  have he : ∀ i l, chiC (χ l) (e i) = if l = i then 1 else 0 := by
    intro i l
    simp only [e, map_prod]
    split_ifs with hl
    · subst hl; exact Finset.prod_eq_one fun j hj => (hb l j (Finset.ne_of_mem_erase hj).symm).1
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (hb i l (Ne.symm hl)).2
  have hsum : ∀ v : V, v = ∑ i, actC τ (e i) v := by
    intro v
    have h0 : actC τ (1 - ∑ i, e i) v = 0 :=
      actC_eq_zero τ χ hJ _ (fun l => by simp [map_sub, map_sum, he]) v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, map_sum, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      sub_eq_zero] at h0
    exact h0
  let Φ : V →ₗ[k] ((i : Idx) → V ⧸ mSub τ (χ i) ⊤) := LinearMap.pi fun i => (mSub τ (χ i) ⊤).mkQ
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro v hv
      have hv' : ∀ i, v ∈ mSub τ (χ i) ⊤ := fun i => by
        have := congr_fun hv i
        simpa [Φ, Submodule.Quotient.mk_eq_zero] using this
      rw [hsum v]
      exact Finset.sum_eq_zero fun i _ =>
        actC_mSub_eq_zero τ χ hJ i (e i) (fun l hl => by rw [he, if_neg hl]) v (hv' i)
    · intro q
      choose w hw using fun i => Submodule.Quotient.mk_surjective (mSub τ (χ i) ⊤) (q i)
      refine ⟨∑ j, actC τ (e j) (w j), funext fun i => ?_⟩
      simp only [Φ, LinearMap.pi_apply, Submodule.mkQ_apply]
      rw [← hw i, Submodule.Quotient.eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_right_comm]
      refine add_mem ?_ (Submodule.sum_mem _ fun j hj => actC_mem_mSub τ (χ i) _
        (by rw [he, if_neg (Finset.ne_of_mem_erase hj).symm]) (w j))
      have h3 := actC_mem_mSub τ (χ i) (e i - 1) (by rw [map_sub, he, if_pos rfl, map_one, sub_self]) (w i)
      simpa [map_sub] using h3
  let Φe := LinearEquiv.ofBijective Φ hΦ
  let Ψ : homO σW τ →ₗ[k] ((i : Idx) → homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) :=
    LinearMap.pi fun i =>
      { toFun := fun T => ⟨(mSub τ (χ i) ⊤).mkQ ∘ₗ T.1, (mem_homO _ _ _).mpr fun a x => by
            rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_homO _ _ _).mp T.2 a x, qAct_mk]⟩
        map_add' := fun S T => by ext; simp
        map_smul' := fun c T => by ext; simp }
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro S T h
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply hΦ.1
      funext i
      have := congrArg (fun F => ((F i).1 x)) h
      simpa [Ψ, Φ] using this
    · intro F
      let T : W →ₗ[k] V := Φe.symm.toLinearMap ∘ₗ LinearMap.pi (fun i => (F i).1)
      have hT : ∀ x i, (mSub τ (χ i) ⊤).mkQ (T x) = (F i).1 x := fun x i =>
        congr_fun (Φe.apply_symm_apply (fun i => (F i).1 x)) i
      have hTm : T ∈ homO σW τ := by
        rw [mem_homO]
        intro a x
        apply hΦ.1
        funext i
        change (mSub τ (χ i) ⊤).mkQ (T (σW a x)) = (mSub τ (χ i) ⊤).mkQ (τ a (T x))
        rw [hT, ← qAct_mk τ _ (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)), hT,
          (mem_homO _ _ _).mp (F i).2 a x]
      refine ⟨⟨T, hTm⟩, funext fun i => Subtype.ext (LinearMap.ext fun x => ?_)⟩
      exact hT x i
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective Ψ hΨ), Module.finrank_pi_fintype]
end
end

