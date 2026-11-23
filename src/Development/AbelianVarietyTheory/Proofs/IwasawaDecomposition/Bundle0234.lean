module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySubsingletonCohAmplePsEff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem TwistConeVanishing.of_isZero {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {F : X.Modules} (hF : IsZero F) : TwistConeVanishing A N F :=
  ⟨0, fun j m _ _ p _ => cohOn.subsingleton_of_isZero
    ((isZero_twist_iff (isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m))).2 hF) ⊤ p⟩

theorem TwistConeVanishing.of_shortExact {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : TwistConeVanishing A N S.X₁)
    (h₃ : TwistConeVanishing A N S.X₃) : TwistConeVanishing A N S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨max a b, fun j m hj hm p hp => ?_⟩
  have hT := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  exact cohOn.subsingleton₂ (Twist.shortExact_map hT hS) ⊤ p
    (ha j m (le_of_max_le_left hj) hm p hp) (hb j m (le_of_max_le_right hj) hm p hp)

theorem TwistConeVanishing.of_generic (k : Type) [Field k] {V : Scheme.{0}} [IsIntegral V]
    (f : V ⟶ Sp k) (hf : IsProjOver f) (A N : LB V) (hA : IsAmpleLB A) (hN : IsPsEff N)
    (G : V.Modules) [IsFiniteQC G]
    (h : ∀ E : V.Modules, IsFiniteQC E → genericPoint V ∉ support E → TwistConeVanishing A N E) :
    TwistConeVanishing A N G := by
  have : AlgebraicGeometry.IsNoetherian V := isNoetherian_of_isProjOver hf
  obtain ⟨r, hr, s, hs⟩ := hN.exists_hasNonzeroSec hA (m := 2) (by norm_num)
  have hM : (lbPow (tens (lbPow N 2) A) r).IsLB :=
    isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB 2) hA.isLB) r
  have hgen : genericPoint V ∈ Out.nonzeroLocus s := (sec_ne_zero_iff s).1 hs
  obtain ⟨j₁, hj₁⟩ := _root_.GlobalTheory.exists_subsingleton_coh_twist_tens_lbPow k f hf A N hA hN.isLB G (2 * r)
  have hCf : IsFiniteQC (cokernel (cutHom G hM s)) := ((cut_by_regular_section.{0} G hM).1 s).2.2.1
  have hCs : support (cokernel (cutHom G hM s)) = support G \ ↑(Out.nonzeroLocus s) :=
    ((cut_by_regular_section.{0} G hM).1 s).2.2.2.1
  haveI : IsFiniteQC (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1)) :=
    isFiniteQC_twist (isLB_lbZPow hM (-1))
  refine _root_.GlobalTheory.twistConeVanishing_of_cut A N hA.isLB hN.isLB r hr hM s G ⟨j₁, hj₁⟩ (h _ inferInstance ?_)
    (h _ hCf ?_)
  · exact _root_.GlobalTheory.KernelCut.notMem_support_kernel_cutHom hM s G _ hgen
  · rw [hCs]
    exact fun h' => h'.2 hgen

end GlobalTheory

namespace GlobalTheory

theorem eventually_subsingleton_coh_ample_psEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → ∀ F : X.Modules, IsFiniteQC F → ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p → Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ X f hf A N hA hN hpe F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  refine devissage X (TwistConeVanishing A N) (fun _ h => .of_isZero hA.isLB hN h)
    (fun _ hS _ _ h₁ h₃ => .of_shortExact hA.isLB hN hS h₁ h₃) ?_ F hF
  intro Z hZ hsmall G hG
  haveI := hG
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  refine (_root_.GlobalTheory.twistConeVanishing_pull_iff_pushforward (redι Z) A N hA.isLB hN G).1 ?_
  refine TwistConeVanishing.of_generic k (redι Z ≫ f)
    (ProjSpace.isProjOver_comp_of_isClosedImmersion _ hf) _ _ hAV (hpe Z hZ) G ?_
  intro E hE hη
  haveI := hE
  have hE' : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj E) :=
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV E
  refine (_root_.GlobalTheory.twistConeVanishing_pull_iff_pushforward (redι Z) A N hA.isLB hN E).2 (hsmall _ hE' ?_)
  have hsub := _root_.GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion (redι Z) E
  refine ⟨hsub.trans ((Set.image_subset_range _ _).trans (range_redι Z).le), fun hle => hη ?_⟩
  have hηZ : (redι Z) (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ∈ (Z : Set X) :=
    (range_redι Z).le ⟨_, rfl⟩
  obtain ⟨y, hy, hyη⟩ := hsub (hle hηZ)
  rwa [(redι Z).isClosedEmbedding.injective hyη] at hy

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CoefInv

open GlobalTheory.SplitScalar GlobalTheory.HeisOrtho

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ)
    (w : WO S T) : ℂ := ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ

theorem coef_right (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {f : WO S T → ℂ} {u : WO S T}
    (hu : heisO ψ S T u f = f) (w : WO S T) :
    coef ψ S T μ 𝓕 f w = ψ (symplOH S T w u) * coef ψ S T μ 𝓕 f (w + u) := by
  have h := heisO_heisO ψ S T w u f
  rw [hu] at h
  unfold coef
  rw [h, ← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem coef_left (hψ : IsCharAF D.host.F ψ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : heisO ψ S T u f = f) (w : WO S T) :
    coef ψ S T μ 𝓕 f w = ψ (symplOH S T u w) * coef ψ S T μ 𝓕 f (w + u) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
    (fun x => heisO ψ S T w f x * star (f x)) (by
      intro γ hγ x
      have h0 := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T γ x)))
      have h1 := heisO_quasi hf w γ hγ x
      have h2 := heisO_quasi hf 0 γ hγ x
      rw [heisO_zero] at h2
      show heisO ψ S T w f (γ + x) * (starRingEnd ℂ) (f (γ + x)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]
      rfl) u
  unfold coef
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h0 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T x u))
  have h1 : ψ (symplOH S T x u) * heisO ψ S T w f (x + u) = ψ (symplOH S T u w) * heisO ψ S T (u + w) f x :=
    congrFun (heisO_heisO ψ S T u w f) x
  have h2 : ψ (symplOH S T x u) * f (x + u) = f x := congrFun hu x
  show heisO ψ S T w f (x + u) * (starRingEnd ℂ) (f (x + u)) =
    ψ (symplOH S T u w) * (heisO ψ S T (w + u) f x * (starRingEnd ℂ) (f x))
  rw [← h2, add_comm w u, ← mul_assoc, ← h1, map_mul, mul_mul_mul_comm, h0, one_mul]

theorem char_eq_one (hψ : IsCharAF D.host.F ψ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : heisO ψ S T u f = f) {w : WO S T} (hw : coef ψ S T μ 𝓕 f w ≠ 0) : ψ (symplO S T w u) = 1 := by
  have h1 := coef_right μ 𝓕 hu w
  have h2 := coef_left hψ hμ h𝓕 hf hu w
  have h3 : coef ψ S T μ 𝓕 f (w + u) ≠ 0 := fun h => hw (by rw [h1, h, mul_zero])
  have h4 := mul_right_cancel₀ h3 (h1.symm.trans h2)
  rw [← symplOH_add_self, AddChar.map_add_eq_mul]
  nth_rewrite 2 [h4]
  rw [← AddChar.map_add_eq_mul, symplOH_skew S T w u, add_neg_cancel, AddChar.map_zero_eq_one]

theorem nsmul_cancel {m n : ℕ} {N : ℕ} (hN : 0 < N) {x y : Mx D m n} (h : N • x = N • y) : x = y := by
  have hu : IsUnit (N : AE D) := by
    have h1 : IsUnit (N : D.host.F) := (Nat.cast_ne_zero.2 hN.ne').isUnit
    have h2 := (h1.map (algebraMap D.host.F (AF D.host.F))).map (algebraMap (AF D.host.F) (AE D))
    rwa [map_natCast, map_natCast] at h2
  refine Matrix.ext fun i j => hu.mul_left_cancel ?_
  have h3 : N • x i j = N • y i j := congrFun (congrFun h i) j
  rwa [nsmul_eq_mul, nsmul_eq_mul] at h3

theorem symplO_nsmul (N : ℕ) (x y : WO S T) : symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := symplO_smul S T (N : AE D) x y
  rwa [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h

theorem real_part (w : WO S T) : (realIdem D • w).map (finPart D) = 0 := by
  funext i j
  show finPart D (realIdem D * w i j) = 0
  rw [RingHom.map_mul, finPart_realIdem, zero_mul]

theorem fin_part (w : WO S T) : (w - realIdem D • w).map (infPart D) = 0 := by
  funext i j
  show infPart D (w i j - realIdem D * w i j) = 0
  rw [RingHom.map_sub, RingHom.map_mul, infPart_realIdem, one_mul, sub_self]

theorem actO_real {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T) {u : WO S T}
    (hu : u.map (finPart D) = 0) : actO S T g h u = u := by
  have h1 : (Formalism.L2.Theta.mt T h).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actO S T g h u).map (infPart D) = u.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actO S T g h u).map (finPart D) = u.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  exact Matrix.ext fun i j => adele_ext (congrFun (congrFun h3 i) j) (congrFun (congrFun h4 i) j)

theorem eventually_mod (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ x ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  obtain ⟨G, hG, hGl, hgen⟩ := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  have h := (Filter.eventually_all_finite hG).2 fun u hu =>
    GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u (latO_fin (hGl u hu)) N hN
  filter_upwards [h] with p hp
  intro w hw
  have key := hgen (((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True).map (nsmulAddMonoidHom N)).comap (GlobalTheory.LatLevel.actHom S T p.1 p.2 - AddMonoidHom.id _))
    (fun α hα u hu => ?_) w hw
  · obtain ⟨l, hl, e⟩ := key
    refine ⟨l, hl, ?_⟩
    have e' : N • l = actO S T p.1 p.2 w - w := e
    rw [e', add_sub_cancel]
  · obtain ⟨l, hl, e⟩ := hp u hu
    refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
      GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
    show N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l) =
      actO S T p.1 p.2 (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u) -
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u
    rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, add_sub_cancel_left, smul_comm]

theorem eventually_coef_of_ne (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w,
      coef ψ S T μ 𝓕 f w ≠ 0 → coef ψ S T μ 𝓕 f (actO S T p.1 p.2 w) = coef ψ S T μ 𝓕 f w := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  have hfix := fun u hu => hUf _ (hNU u hu) (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  filter_upwards [eventually_mod _ _ hS hT (N * (2 * N)) (by positivity)] with p hp hg hh w hw
  have hfin : (N • (w - realIdem D • w)).map (infPart D) = 0 := by
    rw [GlobalTheory.LatNhds.fin_iff, smul_comm, GlobalTheory.LatNhds.fin_iff.1 (fin_part w), nsmul_zero]
  have hmem := GlobalTheory.LatVac.mem_of_char hψ hS hT hfin fun u hu => by
    rw [symplO_nsmul, symplO_sub_left, symplO_real_fin S T (real_part w) (latO_fin (AddSubgroup.nsmul_mem _ hu N)),
      sub_zero]
    exact char_eq_one hψ.1 hμ h𝓕 hf (hfix u hu) hw
  obtain ⟨l, hl, e⟩ := hp _ hmem
  have e1 : actO S T p.1 p.2 (w - realIdem D • w) = (w - realIdem D • w) + (2 * N) • l := by
    refine nsmul_cancel hN ?_
    rw [nsmul_add, ← mul_nsmul', ← e]
    exact (map_nsmul (GlobalTheory.LatLevel.actHom S T p.1 p.2) N _).symm
  have e2 : actO S T p.1 p.2 w = w + N • (l + l) := by
    have h := GlobalTheory.LatNhds.actO_add p.1 p.2 (realIdem D • w) (w - realIdem D • w)
    rw [e1, actO_real hg hh (real_part w), ← add_assoc, add_sub_cancel] at h
    rw [h, ← two_nsmul, ← mul_nsmul]
  have h1 := coef_right μ 𝓕 (hfix _ (AddSubgroup.add_mem _ hl hl)) w
  rw [nsmul_add, symplOH_add_right, symplOH_add_self, char_eq_one hψ.1 hμ h𝓕 hf (hfix l hl) hw, one_mul,
    ← nsmul_add] at h1
  rw [e2, ← h1]

theorem eventually_coef_actO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w, ∫ x in 𝓕, heisO ψ S T (actO S T p.1 p.2 w) f x * star (f x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 f hf
  have h1 := eventually_coef_of_ne hψ hμ h𝓕 hf
  haveI : ∀ V : HSp D, IsTopologicalGroup (GA D V) := fun V => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have ht : Filter.Tendsto (fun p : GA D S × GA D T => p⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := GA D S × GA D T)).tendsto 1
    rwa [inv_one] at this
  filter_upwards [h1, ht.eventually h1] with p hp hp' hg hh w
  show coef ψ S T μ 𝓕 f (actO S T p.1 p.2 w) = coef ψ S T μ 𝓕 f w
  by_cases hw : coef ψ S T μ 𝓕 f w = 0
  · by_contra hne
    have h2 := hp' (inv_mem hg) (inv_mem hh) _ (hw ▸ hne)
    have h3 := GlobalTheory.AdelicLatMove.actO_actO_inv S T p.1⁻¹ p.2⁻¹ w
    rw [inv_inv, inv_inv] at h3
    exact hne (h2.symm.trans (congrArg _ h3))
  · exact hp hg hh w hw

end GlobalTheory.Mem.CoefInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLine
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

namespace StepLoc

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K] {O : Subring K} {τ : ι}

abbrev blk (k : ι → ℕ) (τ : ι) (P : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (P τ).submatrix Subtype.val Subtype.val

theorem mul_apply_rest {P : Mat m K} (hP : Par k O P) (g : Mat m K) (a : Fin (m τ)) (j : Rest m k τ) :
    (g * P) τ a j.1 = Matrix.vecMul (fun l : Rest m k τ => g τ a l.1) (blk k τ P) j := by
  rw [Pi.mul_apply, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ))]
  have : ∑ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * P τ l.1 j.1 = 0 :=
    Finset.sum_eq_zero fun l _ => by
      have h1 := l.2
      have h2 := j.2
      rw [(hP τ).2.2.2 l.1 j.1 (by omega) (by show (l.1 : ℕ) < j.1; omega), mul_zero]
  rw [this, add_zero]
  rfl

theorem blk_mul_inv {P : Mat m K} (hP : Par k O P) : blk k τ P * blk k τ P⁻¹ = 1 := by
  ext a j
  have := mul_apply_rest hP.inv P a.1 j
  rw [Mat.mul_inv hP.det_ne] at this
  refine this.symm.trans ?_
  show (1 : Matrix _ _ K) a.1 j.1 = _
  simp only [Matrix.one_apply, Subtype.ext_iff]

theorem line_iff {Q : Mat m K} (hQ : Par k O Q) (hk : k τ < m τ) {s : Rest m k τ → K} {b : K}
    (hs : ∀ j : Rest m k τ, s j = b * Q τ ⟨k τ, hk⟩ j.1) (hb : b ≠ 0) (g : Mat m K) :
    (∃ a : K, ∀ j : Rest m k τ, (g * Q) τ ⟨k τ, hk⟩ j.1 = a * s j) ↔
      ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  have e : ∀ (x : K) (j : Rest m k τ), Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) x) (blk k τ Q) j
      = x * Q τ ⟨k τ, hk⟩ j.1 := fun x j => by
    rw [Matrix.single_vecMul]
    simp
  constructor
  · rintro ⟨a, ha⟩ j hj
    have h1 : Matrix.vecMul (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) (blk k τ Q) =
        Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (a * b)) (blk k τ Q) := by
      funext l
      rw [← mul_apply_rest hQ, ha, e, hs, mul_assoc]
    have h2 := congrArg (Matrix.vecMul · (blk k τ Q⁻¹)) h1
    simp only [Matrix.vecMul_vecMul, blk_mul_inv hQ, Matrix.vecMul_one] at h2
    have h3 := congrFun h2 ⟨j, hj.le⟩
    rwa [Pi.single_eq_of_ne (fun h => hj.ne' (congrArg (fun x : Rest m k τ => (x.1 : ℕ)) h))] at h3
  · intro h
    refine ⟨g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩ / b, fun j => ?_⟩
    have h1 : (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) =
        Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩) := by
      funext l
      by_cases hl : l = ⟨⟨k τ, hk⟩, le_rfl⟩
      · rw [hl, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hl]
        exact h _ (lt_of_le_of_ne l.2 fun h' => hl (Subtype.ext (Fin.ext h'.symm)))
    rw [mul_apply_rest hQ, h1, e, hs, ← mul_assoc, div_mul_cancel₀ _ hb]

theorem par_succ_iff {k' : ι → ℕ} (hk : k τ < m τ) (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (g : Mat m K) :
    Par k' O g ↔ Par k O g ∧ ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  constructor
  · intro h
    refine ⟨h.mono (fun t => ?_) le_rfl, fun j hj => (h τ).2.2.2 _ j (by rw [h1]; exact Nat.lt_succ_self _) hj⟩
    by_cases ht : t = τ
    · rw [ht, h1]; exact Nat.le_succ _
    · exact (h2 t ht).ge
  · rintro ⟨h, h'⟩ t
    refine ⟨(h t).1, (h t).2.1, (h t).2.2.1, fun i j hi hij => ?_⟩
    by_cases ht : t = τ
    · subst ht
      rw [h1] at hi
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | hi
      · exact (h t).2.2.2 i j hi hij
      · obtain rfl : i = ⟨k t, hk⟩ := Fin.ext hi
        exact h' j hij
    · exact (h t).2.2.2 i j (h2 t ht ▸ hi) hij

theorem exists_completion (hk : k τ < m τ) (c : Rest m k τ → K) (i : Rest m k τ) (hi : c i = 1) :
    ∃ N : Mat m K, (∀ j : Rest m k τ, N τ ⟨k τ, hk⟩ j.1 = c j) ∧
      ∀ O : Subring K, (∀ j, c j ∈ O) → Par k O N := by
  classical
  let v : Fin (m τ) → K := fun j => if h : k τ ≤ (j : ℕ) then c ⟨j, h⟩ else 0
  have hv : ∀ j : Rest m k τ, v j.1 = c j := fun j => dif_pos j.2
  let T : Matrix (Fin (m τ)) (Fin (m τ)) K :=
    ((1 : Matrix _ _ K).updateRow i.1 v).submatrix (Equiv.swap ⟨k τ, hk⟩ i.1) id
  have hd : T.det * T.det = 1 := by
    have e : ((1 : Matrix _ _ K).updateRow i.1 v).det = 1 := by
      rw [← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
      exact (hv i).trans hi
    rw [Matrix.det_permute, e, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  refine ⟨Function.update (1 : Mat m K) τ T, fun j => ?_, fun O hO t => ?_⟩
  · rw [Function.update_self]
    show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k τ, hk⟩ i.1 ⟨k τ, hk⟩) j.1 = _
    rw [Equiv.swap_apply_left, Matrix.updateRow_self, hv]
  by_cases ht : t = τ
  · subst ht
    rw [Function.update_self]
    have hm : ∀ a b, T a b ∈ O := fun a b => by
      show ((1 : Matrix _ _ K).updateRow i.1 v) _ b ∈ O
      rw [Matrix.updateRow_apply]
      split_ifs
      · show dite _ _ _ ∈ O
        split_ifs
        exacts [hO _, O.zero_mem]
      · rw [Matrix.one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
    refine ⟨hm, left_ne_zero_of_mul_eq_one hd, ?_, fun a b ha hab => ?_⟩
    · rw [← eq_inv_of_mul_eq_one_left hd]; exact det_mem hm
    · have h1 : a ≠ ⟨k t, hk⟩ := fun h => ha.ne (congrArg Fin.val h)
      have h2 : a ≠ i.1 := fun h => (h ▸ ha).not_ge i.2
      show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k t, hk⟩ i.1 a) b = 0
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Matrix.updateRow_ne h2, Matrix.one_apply_ne hab.ne]
  · rw [Function.update_of_ne ht]
    exact Par.one t

end StepLoc


open StepLoc in
theorem exists_fr_stepSet (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ))
    (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) :
    ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  refine ⟨⟨stepSet S τ hk A₀ M' φ f s, fun z' => ?_⟩, fun _ => rfl⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc (f z')
  have hAU : ∀ w ∈ U, A ∈ S.S w := fun w hw => (hU w hw A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  obtain ⟨hd, hE'⟩ := hE _ A (hAU _ hz)
  obtain ⟨i, hi⟩ := hP.cover z' _ hd hE'
  set c := ((dualBlock k τ A₀ A).map φ).mulVec s with hc
  let ψ : Ω →+* Ω' := φ
  obtain ⟨N, hN, hNO⟩ := exists_completion hk (fun j => c j / c i) i (div_self hi.1)
  have hAφ : ∀ t, (A.map ψ t).det ≠ 0 := fun t => by rw [Mat.det_map]; exact (map_ne_zero ψ).2 (hA t)
  have hN0 : Par k ⊤ N := hNO ⊤ fun _ => trivial
  have hP0 : Par k ⊤ ((A * A₀⁻¹).map ψ) :=
    ((Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))).map ψ fun _ _ => trivial
  have hs : s = Matrix.vecMul c (blk k τ ((A * A₀⁻¹).map ψ)) := by
    have hP1 := (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))
    have e1 : (blk k τ (A * A₀⁻¹))⁻¹ * blk k τ (A * A₀⁻¹) = 1 :=
      Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse (blk_mul_inv hP1))
    have e2 : c = Matrix.vecMul s ((blk k τ (A * A₀⁻¹))⁻¹.map ψ) := by
      rw [hc, ← Matrix.mulVec_transpose]
      rfl
    have e3 : blk k τ ((A * A₀⁻¹).map ψ) = (blk k τ (A * A₀⁻¹)).map ψ := rfl
    rw [e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, e1, Matrix.map_one _ ψ.map_zero ψ.map_one,
      Matrix.vecMul_one]
  have hQ : ∀ j : Rest m k τ, s j = c i * (N * (A * A₀⁻¹).map ψ) τ ⟨k τ, hk⟩ j.1 := fun j => by
    have e : (fun l : Rest m k τ => N τ ⟨k τ, hk⟩ l.1) = (c i)⁻¹ • c := by
      funext l
      rw [hN, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [mul_apply_rest hP0, e, Matrix.smul_vecMul, ← hs, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hi.1]
  have hA₁ : ∀ t, ((N * A.map ψ) t).det ≠ 0 := fun t => by
    rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hN0.det_ne t) (hAφ t)
  refine ⟨f ⁻¹ᵁ U ⊓ ⟨_, M'.isOpen_setOf_div c i⟩, N * A.map ψ, ⟨hz, hi⟩, hA₁, fun w hw A' => ?_⟩
  have hNw : Par k (M'.O w).toSubring N := hNO _ hw.2.2
  have hAw : A ∈ S.S (f w) := hAU _ hw.1
  rw [par_succ_iff hk h1 h2, ← line_iff (hN0.mul hP0) hk hQ hi.1]
  have e1 : A' * (N * A.map ψ)⁻¹ * (N * (A * A₀⁻¹).map ψ) = A' * (A₀.map ψ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul]
  rw [e1]
  refine and_congr_left' ⟨fun h => ?_, fun h B hB => ?_⟩
  · have := (h A hAw).mul hNw.inv
    rwa [Mat.mul_inv_rev, ← mul_assoc]
  · have h3 : Par k (M'.O w).toSubring ((A * B⁻¹).map ψ) :=
      ((Fr.mem_iff hB).1 hAw).map ψ fun _ hx => hP.hom.map_mem_O hx
    have := h.mul (hNw.mul h3)
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul] at this
    exact this

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGenAt
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemTame

theorem exists_tameGenAt :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∃ γ : G E Ω, TameGenAt A γ :=
  @GlobalTheory.TameInertiaGen.exists_tameGenAt

end GlobalTheory.MemTame
end

