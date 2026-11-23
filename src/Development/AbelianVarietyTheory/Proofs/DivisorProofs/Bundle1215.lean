module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunct
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinTrace

variable {D : D7}

local instance (V : HSp D) : Submodule.IsLattice D.host.E (frameLat V) :=
  Submodule.IsLattice.of_fg D.host.E (frameLat_fg V)

theorem finFn_mem_SB (V : HSp D) {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) : finFn V ff ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  have hm := hff.tensorFin_mem
  rw [show finFn V ff = tensorFin D.sp.cm.sig V.gram ff ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
    funext fun y => GlobalTheory.TrConv.finFn_eq_tensorFin V ff y]
  exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
    hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

theorem hasTrace_finFn : ∀ (D : D7) (V : HSp D) (ν : Measure (GfC V)) [ν.IsHaarMeasure] (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c) ∧ ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → IsCompact (K : Set (GfC V)) → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x := by
  intro D V ν _ ff hff W _ _ σ hσ
  obtain ⟨hlc, hcs⟩ := finFn_mem_SB V hff
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) (smoothOp σ ν (finFn V ff)) := by
    intro v l
    refine ⟨?_, ?_⟩
    · have h := GlobalTheory.OpTrace.integrable_map (μ := ν) (hσ.1.smoothOp_integrand hlc hcs v).1
        (hσ.1.smoothOp_integrand hlc hcs v).2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using h
    · rw [hσ.1.map_smoothOp hlc hcs l v]
      simp only [smul_eq_mul]
  obtain ⟨K₀, ho, hc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfd := hσ.finiteDimensional_range_smoothOp (μ := ν) hlc hcs ho hc
  refine ⟨⟨_, _, hA, hfd, rfl⟩, fun K _ _ hK hne => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, smoothOp σ ν (finFn V ff) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by convert hA using 1; exact (LinearMap.ext h).symm)
  exact ⟨_, hv, GlobalTheory.OpTrace.mem_fixed.1 (hσ.1.smoothOp_mem_fixed hlc hcs hK v)⟩

end GlobalTheory.FinTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.Conormal

namespace GlobalTheory.LieVB

variable {O : Type} [CommRing O]

theorem surjective_sec_epsZero : Function.Surjective (sec (epsZero O)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O O).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (DualNumber O)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O O).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (DualNumber O)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem appLE_sec_epsZero_epsFn {V : (Sp O).Opens} {T : (specO O (DualNumber O)).left.Opens}
    (h : V ≤ sec (epsZero O) ⁻¹ᵁ T) :
    (sec (epsZero O)).appLE T V h (resG _ le_top (epsFn O)) = 0 := by
  have e : (sec (epsZero O)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn O) = 0 :=
    congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans
      (map_zero (Scheme.ΓSpecIso (.of O)).inv.hom)
  rw [GlobalTheory.DualPull.appLE_resG, ← GlobalTheory.DualPull.resG_appLE _ le_top (le_preimage_top _ _), e,
    map_zero]

variable {G : Over (Sp O)} [GrpObj G]

theorem sec_epsZero_comp (x : LieG G) : sec (epsZero O) ≫ x.1.left = unitSec G :=
  congrArg (·.left) (epsZero_comp x)

theorem preimage_le_of_lieG (x : LieG G) {U : (Sp O).Opens} {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) : (specO O (DualNumber O)).hom ⁻¹ᵁ U ≤ x.1.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero O) ≫ (specO O (DualNumber O)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := h h₁
  rw [← sec_epsZero_comp x] at h₂
  exact h₂

theorem appLE_lieG (x : LieG G) {U : (Sp O).Opens} (hU : IsAffineOpen U) {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) (f : Γ(G.left, W)) :
    x.1.left.appLE W _ (preimage_le_of_lieG x h) f =
      (specO O (DualNumber O)).hom.appLE U _ le_rfl ((unitSec G).appLE W U h f) +
        (specO O (DualNumber O)).hom.appLE U _ le_rfl
          (GlobalTheory.VB.dualApp (tangent x) le_top (dUnit G h f)) * resG _ le_top (epsFn O) := by
  obtain ⟨⟨a, b⟩, e⟩ := (_root_.GlobalTheory.LieVB.bijective_add_mul_epsFn O U hU).2 (x.1.left.appLE W _ (preimage_le_of_lieG x h) f)
  have hV : U ≤ sec (epsZero O) ⁻¹ᵁ (specO O (DualNumber O)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero O))).2 le_rfl
  have hb := dualApp_tangent_dUnit x h f hV le_rfl (preimage_le_of_lieG x h) a b e.symm
  have ha : (unitSec G).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero O)).appLE _ U hV) e
    simp only [map_add (f := _), map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      GlobalTheory.LB.resG_self, appLE_appLE (sec_epsZero_comp x) _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact e.symm

theorem tangent_injective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Injective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro x y hxy
  refine Subtype.ext (Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_))
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom (MonObj.one (X := G))) (V := ⊤)
    (x := (specO O (DualNumber O)).hom t) trivial
  have hT : IsAffineOpen ((specO O (DualNumber O)).hom ⁻¹ᵁ U) := c.affine_base.preimage _
  have e : x.1.left.appLE W _ (preimage_le_of_lieG x c.le) =
      y.1.left.appLE W _ (preimage_le_of_lieG y c.le) := by
    ext f
    exact (appLE_lieG x c.affine_base c.le f).trans
      (hxy ▸ (appLE_lieG y c.affine_base c.le f).symm)
  refine ⟨(specO O (DualNumber O)).hom ⁻¹ᵁ U, hU, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG x c.le),
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG y c.le), e]

end GlobalTheory.LieVB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section Laws

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F κ) in
def intPts : Set (κ → Af F) :=
  Set.univ.pi fun _ => {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem indicator_intPts_mem_SB : (intPts F κ).indicator (1 : (κ → Af F) → ℂ) ∈ SB (κ → Af F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hC : IsCompact {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1
  have hU : IsOpen (intPts F κ) := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hK : IsCompact (intPts F κ) := isCompact_univ_pi fun _ => hC
  refine ⟨?_, HasCompactSupport.intro' hK hK.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ intPts F κ
  · filter_upwards [hU.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem zero_mem_intPts : (0 : κ → Af F) ∈ intPts F κ := fun _ _ v => zero_mem _

def ptAt (a : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), y i)

theorem pureA_ptAt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (a : κ → mixedEmbedding.mixedSpace F)
    (y : κ → Af F) : pureA F f g (ptAt a y) = f a * g y := by
  change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i))) * g y = f a * g y
  congr 1
  congr 1
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)

theorem fin_eq_zero_of_at {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem at_of_fin_eq_zero {z : κ → AF F} (hz : ∀ i, (z i).2 = 0) : At (evI F) z := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * (z i).1 = 0
    rw [hu1, zero_mul]
  · change u.2 * (z i).2 = 0
    rw [hz i, mul_zero]

theorem tens_eq_pureA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    tens (evI F) f r = pureA F f (fun y => r (fun i => ((0 : Ainf F), y i))) := by
  funext x
  simp only [tens, pureA, evI]
  congr 1
  have h := hr (fun i => ((0 : Ainf F), (x i).2)) (fun i => ((x i).1, (0 : Af F)))
    (at_of_fin_eq_zero fun i => rfl)
  rw [← h]
  congr 1
  funext i
  exact Prod.ext (zero_add _).symm (add_zero _).symm

theorem mem_SB_of_pureA_mem {f : SInf F κ} (hf : f ≠ 0) {g : (κ → Af F) → ℂ} (h : pureA F f g ∈ schA F κ) :
    g ∈ SB (κ → Af F) := by
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hf (SchwartzMap.ext h0)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ) := LinearMap.funLeft ℂ ℂ (ptAt a)
  have hle : schA F κ ≤ (SB (κ → Af F)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f', g', hg', rfl⟩
    change (fun y => pureA F f' g' (ptAt a y)) ∈ SB (κ → Af F)
    simp_rw [pureA_ptAt]
    exact (SB (κ → Af F)).smul_mem (f' a) hg'
  have h1 : L (pureA F f g) ∈ SB (κ → Af F) := hle h
  have h2 : L (pureA F f g) = f a • g := by
    funext y
    change pureA F f g (ptAt a y) = _
    rw [pureA_ptAt]
    rfl
  rw [h2] at h1
  have h3 := (SB (κ → Af F)).smul_mem (f a)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3

theorem eval_mem_adm (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end Laws

section Main

open scoped Classical

theorem actsLaws : ActsLaws := by
  intro F _ _ κ _ f f₁ f₂
  set g₀ : (κ → Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl

  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : Rest (evI F) (⇑f) r₀ := ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩

  have hext : ∀ h₁ h₂ : SInf F κ, (∀ a, pureA F h₁ g₀ (ptAt a 0) = pureA F h₂ g₀ (ptAt a 0)) → h₁ = h₂ := by
    intro h₁ h₂ h
    ext a
    simpa [pureA_ptAt, hg₀0] using h a

  have hzero : ∀ g : (κ → Af F) → ℂ, pureA F ⇑(0 : SInf F κ) g = 0 := by
    intro g; funext x; simp [pureA]
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T hT0 hSD r hr x
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSD g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
        simp only [LinearMap.proj_apply, hzero, hT0] at h
        rw [hzero]
        exact (h.unique (hasDerivAt_const 0 (0 : ℂ)))
      subst hf₁
      rw [hzeroT]
      simp only [hT0, Pi.zero_apply]
      exact hasDerivAt_const 0 (0 : ℂ)
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      have h := hSD _ hg _ (eval_mem_adm x)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact h
  · intro T hT0 hSA r hr
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSA g₀ hg₀
        rw [hzero, hT0] at h
        rw [← h, hzero]
      subst hf₁
      rw [hzeroT, hT0]
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact hSA _ hg
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ r₀ hrest₀ (ptAt a 0)
    have e₂ := h₂ r₀ hrest₀ (ptAt a 0)
    rw [htens₀] at e₁ e₂
    exact e₁.unique e₂
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e := (h₁ r₀ hrest₀).symm.trans (h₂ r₀ hrest₀)
    rw [htens₀, htens₀] at e
    exact congrFun e (ptAt a 0)
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    have e₂ := h₂ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    exact e₁.unique e₂

end Main

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativeAdditiveCommutator
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisDerivLaws

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

noncomputable def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

lemma evI_eq (a : AF F) : evI F a = evIHom a := rfl

lemma evI_realAd' (r : ℝ) : evI F (realAd F r) = algebraMap ℝ (mixedEmbedding.mixedSpace F) r := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ r)) = _
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

noncomputable def trPair (w : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℂ where
  toFun y := ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * w i) : ℝ) : ℂ)
  map_add' a b := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _), Complex.ofReal_add]
  map_smul' c a := by
    simp [smul_mul_assoc, ← Finset.smul_sum, Complex.real_smul]

lemma trPair_apply (w y : κ → mixedEmbedding.mixedSpace F) :
    trPair w y = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * w i) : ℝ) : ℂ) := rfl

lemma trPair_add (w w' y : κ → mixedEmbedding.mixedSpace F) :
    trPair (w + w') y = trPair w y + trPair w' y := by
  simp only [trPair_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _), Complex.ofReal_add]

lemma trPair_smul (r : ℝ) (w y : κ → mixedEmbedding.mixedSpace F) :
    trPair (r • w) y = (r : ℂ) * trPair w y := by
  simp [trPair_apply, mul_smul_comm, ← Finset.smul_sum]

lemma hasFDerivAt_trPair (w x : κ → mixedEmbedding.mixedSpace F) :
    HasFDerivAt (fun y => trPair w y) (LinearMap.toContinuousLinearMap (trPair w)) x :=
  (LinearMap.toContinuousLinearMap (trPair w)).hasFDerivAt

lemma fderiv_step (f : SInf F κ) (c : ℂ) (w v' x v : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (fun y => fderiv ℝ (⇑f) y v' - c * trPair w y * f y) x v =
      fderiv ℝ (fderiv ℝ (⇑f)) x v v' - c * (trPair w x * fderiv ℝ (⇑f) x v + f x * trPair w v) := by
  have hf2 : DifferentiableAt ℝ (fderiv ℝ (⇑f)) x :=
    ((f.smooth ⊤).fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable
      one_ne_zero x
  have h1 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y v')
      ((fderiv ℝ (⇑f) x).comp 0 + (fderiv ℝ (fderiv ℝ (⇑f)) x).flip v') x :=
    hf2.hasFDerivAt.clm_apply (hasFDerivAt_const v' x)
  have h2 := ((hasFDerivAt_trPair w x).const_mul c).mul (f.differentiableAt (x := x)).hasFDerivAt
  have h3 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y v' - c * trPair w y * f y) _ x := h1.sub h2
  rw [h3.fderiv]
  simp
  ring

lemma evV_add (a b : κ → AF F) :
    (fun i => evI F ((a + b) i)) = (fun i => evI F (a i)) + (fun i => evI F (b i)) := by
  funext i
  show evI F (a i + b i) = evI F (a i) + evI F (b i)
  rw [evI_eq, map_add (f := _)]; rfl

lemma evV_smul (r : ℝ) (a : κ → AF F) :
    (fun i => evI F ((realAd F r • a) i)) = r • (fun i => evI F (a i)) := by
  funext i
  show evI F (realAd F r * a i) = r • evI F (a i)
  rw [evI_eq, map_mul, ← evI_eq, ← evI_eq, evI_realAd', Algebra.smul_def]

lemma isSymm (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) : IsSymmSndFDerivAt ℝ (⇑f) x :=
  ((f.smooth ⊤).contDiffAt).isSymmSndFDerivAt (by simp)

theorem heis_deriv_laws : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    (∀ u u', At (evI F) u → At (evI F) u' → D (u + u') = D u + D u') ∧
    (∀ u (r : ℝ), At (evI F) u → D (realAd F r • u) = (r : ℂ) • D u) ∧
    (∀ u u', At (evI F) u → At (evI F) u' → ∀ f, D u (D u' f) - D u' (D u f) =
      ((-2 * Real.pi * Complex.I : ℂ) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ)) • f) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ JA JB d D hD
  have at_add : ∀ u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' h h' a ha => by rw [smul_add, h a ha, h' a ha, add_zero]
  have at_smul : ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : AF F), At (evI F) u → At (evI F) (r • u) :=
    fun u r h a ha => by rw [smul_comm, h a ha, smul_zero]
  have hD' : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ (⇑f) x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        trPair (fun i => evI F ((d.e u).2 i)) x * f x := hD
  refine ⟨fun u u' hu hu' => ?_, fun u r hu => ?_, fun u u' hu hu' f => ?_⟩
  · ext f x
    rw [ContinuousLinearMap.add_apply, SchwartzMap.add_apply, hD' _ (at_add u u' hu hu'), hD' u hu,
      hD' u' hu', map_add, Prod.fst_add, Prod.snd_add, evV_add, evV_add, map_add, trPair_add]
    ring
  · ext f x
    rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, hD' _ (at_smul u _ hu), hD' u hu,
      map_smul, Prod.smul_fst, Prod.smul_snd, evV_smul, evV_smul, map_smul, trPair_smul]
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  · have e : ⇑(D u f) = fun y => fderiv ℝ (⇑f) y (fun i => evI F ((d.e u).1 i)) -
        2 * Real.pi * Complex.I * trPair (fun i => evI F ((d.e u).2 i)) y * f y := funext (hD' u hu f)
    have e' : ⇑(D u' f) = fun y => fderiv ℝ (⇑f) y (fun i => evI F ((d.e u').1 i)) -
        2 * Real.pi * Complex.I * trPair (fun i => evI F ((d.e u').2 i)) y * f y :=
      funext (hD' u' hu' f)
    have key : ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ) =
        trPair (fun i => evI F ((d.e u').2 i)) (fun i => evI F ((d.e u).1 i)) -
        trPair (fun i => evI F ((d.e u).2 i)) (fun i => evI F ((d.e u').1 i)) := by
      rw [d.form u u', evI_eq, map_sub]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_sum, map_mul, ← evI_eq, trPair_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, Complex.ofReal_sub]
    ext x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, hD' u hu (D u' f), hD' u' hu' (D u f), e', e,
      fderiv_step, fderiv_step, (isSymm f x).eq (fun i => evI F ((d.e u').1 i)), key, smul_eq_mul]
    ring

end GlobalTheory.HeisDerivLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValueStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  first | exact @GlobalTheory.BackForm.exists_multMap | exact GlobalTheory.BackForm.exists_multMap | (intros; apply GlobalTheory.BackForm.exists_multMap <;> assumption)
end

