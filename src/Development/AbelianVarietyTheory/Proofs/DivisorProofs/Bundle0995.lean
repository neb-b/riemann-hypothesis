module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RestrSchA

variable {κ₁ κ : Type} {j : κ₁ → κ}

theorem extend_map {M N : Type} [Zero M] [Zero N] (hj : Function.Injective j) (φ : M → N) (h0 : φ 0 = 0)
    (y : κ₁ → M) : (fun i => φ (Function.extend j y 0 i)) = Function.extend j (fun a => φ (y a)) 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, h0]

theorem extend_add {M : Type} [AddZeroClass M] (hj : Function.Injective j) (y z : κ₁ → M) :
    Function.extend j (y + z) 0 = Function.extend j y 0 + Function.extend j z 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_smul {R M : Type} [Zero M] [SMulZeroClass R M] (hj : Function.Injective j) (c : R) (y : κ₁ → M) :
    Function.extend j (c • y) 0 = c • Function.extend j y 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem continuous_extend {M : Type} [TopologicalSpace M] [Zero M] (hj : Function.Injective j) :
    Continuous (fun y : κ₁ → M => Function.extend j y 0) := by
  refine continuous_pi fun i => ?_
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp only [hj.extend_apply]
    exact continuous_apply a
  · simp only [Function.extend_apply' _ _ _ h]
    exact continuous_const

theorem isClosedEmbedding_extend {M : Type} [TopologicalSpace M] [Zero M] [T2Space M] (hj : Function.Injective j) :
    Topology.IsClosedEmbedding (fun y : κ₁ → M => Function.extend j y 0) :=
  Function.LeftInverse.isClosedEmbedding (f := fun x : κ → M => x ∘ j)
    (fun y => by funext a; simp [hj.extend_apply]) (by fun_prop) (continuous_extend hj)

end GlobalTheory.RestrSchA

namespace GlobalTheory.RestrSchA

open scoped Classical

variable {κ₁ κ : Type} {j : κ₁ → κ}

def extL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (hj : Function.Injective j) :
    (κ₁ → V) →L[ℝ] (κ → V) where
  toFun y := Function.extend j y 0
  map_add' y z := extend_add hj y z
  map_smul' c y := extend_smul hj c y
  cont := continuous_extend hj

theorem norm_le_extL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype κ₁] [Fintype κ]
    (hj : Function.Injective j) (y : κ₁ → V) : ‖y‖ ≤ ‖extL V hj y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  have h : extL V hj y (j a) = y a := by simp [extL, hj.extend_apply]
  rw [← h]
  exact norm_le_pi_norm _ _

def restrS (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j) :
    SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ₁ → NumberField.mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (extL (NumberField.mixedEmbedding.mixedSpace F) hj).hasTemperateGrowth
    ⟨1, 1, fun y => by
      have := norm_le_extL hj y
      have h0 := norm_nonneg (extL (NumberField.mixedEmbedding.mixedSpace F) hj y)
      simp only [pow_one, one_mul]
      linarith⟩

theorem restrS_apply (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (y : κ₁ → NumberField.mixedEmbedding.mixedSpace F) :
    restrS F hj f y = f (Function.extend j y 0) := by
  simp [restrS, extL]

theorem sb_comp_extend (F : Type) [Field F] [NumberField F] (hj : Function.Injective j)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y => g (Function.extend j y 0)) ∈ SB (κ₁ → FiniteAdeleRing (𝓞 F) F) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
  exact ⟨hg.1.comp_continuous (continuous_extend hj), hg.2.comp_isClosedEmbedding (isClosedEmbedding_extend hj)⟩

theorem pureA_extend (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ₁ → AdeleRing (𝓞 F) F) :
    pureA F f g (Function.extend j y 0) = pureA F (restrS F hj f) (fun z => g (Function.extend j z 0)) y := by
  simp only [pureA, restrS_apply]
  rw [extend_map hj (fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
      (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0; exact map_zero _) y,
    extend_map hj (fun x : AdeleRing (𝓞 F) F => x.2) rfl y]

theorem mem_schA_comp_extend : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ Φ ∈ schA F κ, (fun y => Φ (Function.extend j y 0)) ∈ schA F κ₁ := by
  intro F _ _ κ₁ κ _ _ j hj Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨restrS F hj f, fun z => g (Function.extend j z 0), sb_comp_extend F hj hg, ?_⟩
    funext y
    exact pureA_extend F hj f g y
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.RestrSchA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMap
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section

namespace GlobalTheory.SchwartzBruhatRestrict

theorem map_funLeft_extendZero : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ v : Pl (F := F), (SB (κ → Fv F v)).map (LinearMap.funLeft ℂ ℂ (fun y : κ₁ → Fv F v => Function.extend j y 0)) = SB (κ₁ → Fv F v) := by
  intro F _ _ κ₁ κ _ _ j hj v
  classical
  set ext : (κ₁ → Fv F v) → (κ → Fv F v) := fun y => Function.extend j y 0 with hext
  have hr : Function.LeftInverse (fun x : κ → Fv F v => x ∘ j) ext :=
    fun y => funext fun i => hj.extend_apply y 0 i
  have hcr : Continuous (fun x : κ → Fv F v => x ∘ j) :=
    continuous_pi fun i => continuous_apply (j i)
  have hce : Continuous ext := by
    refine continuous_pi fun k => ?_
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simp only [ext, hj.extend_apply]
      exact continuous_apply i
    · simp only [ext, Function.extend_apply' _ _ _ hk]
      exact continuous_const
  have hemb : Topology.IsClosedEmbedding ext := hr.isClosedEmbedding hcr hce
  apply le_antisymm
  · rintro _ ⟨φ, ⟨hlc, hcs⟩, rfl⟩
    exact ⟨hlc.comp_continuous hce, hcs.comp_isClosedEmbedding hemb⟩
  · rintro φ₁ ⟨hlc, hcs⟩
    let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hOeq : O = ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F)) := by
      ext x
      simp only [O, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        Valuation.mem_integer_iff]
    have hOo : IsOpen O := by rw [hOeq]; exact Valued.isOpen_integer _
    have hOc : IsClosed O := by rw [hOeq]; exact Valued.isClosed_integer _
    have hOk : IsCompact O :=
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    have hO0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
    let S : Set (κ → Fv F v) := {x | ∀ k, k ∉ Set.range j → x k ∈ O}
    have hSeq : S = ⋂ k ∈ (Set.range j)ᶜ, (fun x : κ → Fv F v => x k) ⁻¹' O := by
      ext x; simp [S]
    have hSo : IsOpen S := by
      rw [hSeq]
      exact Set.Finite.isOpen_biInter (Set.toFinite _) fun k _ => hOo.preimage (continuous_apply k)
    have hSc : IsClosed S := by
      rw [hSeq]
      exact isClosed_biInter fun k _ => hOc.preimage (continuous_apply k)
    set g : (κ → Fv F v) → ℂ := fun x => φ₁ (x ∘ j) with hg
    have hglc : IsLocallyConstant g := hlc.comp_continuous hcr
    refine ⟨S.indicator g, ⟨?_, ?_⟩, ?_⟩
    · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
      by_cases hx : x ∈ S
      · filter_upwards [hSo.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hglc x] with y hy hgy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hgy]
      · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · let C : κ → Set (Fv F v) := fun k =>
        if h : k ∈ Set.range j then (fun y : κ₁ → Fv F v => y (Classical.choose h)) '' tsupport φ₁ else O
      have hC : IsCompact (Set.univ.pi C) := by
        refine isCompact_univ_pi fun k => ?_
        by_cases h : k ∈ Set.range j
        · simp only [C, dif_pos h]
          exact hcs.isCompact.image (continuous_apply _)
        · simp only [C, dif_neg h]
          exact hOk
      refine HasCompactSupport.intro hC fun x hx => ?_
      by_contra hne
      have hxS : x ∈ S := by
        by_contra hxS; exact hne (Set.indicator_of_notMem hxS _)
      have hgx : g x ≠ 0 := by rwa [Set.indicator_of_mem hxS] at hne
      apply hx
      intro k _
      by_cases h : k ∈ Set.range j
      · simp only [C, dif_pos h]
        refine ⟨x ∘ j, subset_tsupport _ hgx, ?_⟩
        simp only [Function.comp_apply]
        rw [Classical.choose_spec h]
      · simp only [C, dif_neg h]
        exact hxS k h
    · funext y
      rw [LinearMap.funLeft_apply]
      have hyS : ext y ∈ S := by
        intro k hk
        have hk' : ¬ ∃ i, j i = k := hk
        simp only [ext, Function.extend_apply' _ _ _ hk']
        exact hO0
      rw [Set.indicator_of_mem hyS]
      exact congrArg φ₁ (hr y)

end GlobalTheory.SchwartzBruhatRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgFunctionField
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.FGFun

theorem fg_functionField : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (sG : G ⟶ Sp F), IsProjOver sG → ∀ (P Ω : Type) [Field P] [Field Ω] (φ : P →+* G.functionField) (t : Sp P ⟶ Sp F) (ι : G.functionField →+* Ω), spMap ι ≫ G.fromSpecStalk (genericPoint G) ≫ sG = spMap ι ≫ spMap φ ≫ t → (letI := φ.toAlgebra; (⊤ : IntermediateField P G.functionField).FG) := by
  intro F _ G _ sG hproj P Ω _ _ φ t ι h
  letI := φ.toAlgebra
  obtain ⟨τ, rfl⟩ := Spec.map_surjective t
  obtain ⟨β, hβ⟩ := Spec.map_surjective (G.fromSpecStalk (genericPoint G) ≫ sG)
  have hβτ : ∀ c : F, β.hom c = φ (τ.hom c) := by
    rw [← hβ] at h
    simp only [← Spec.map_comp] at h
    have h' := Spec.map_injective h
    intro c
    apply ι.injective
    have := congrArg (fun f => f.hom c) h'
    simpa using this
  have hft : LocallyOfFiniteType sG := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    haveI := isProper_str F N
    infer_instance
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint G))
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have e : U ≤ sG ⁻¹ᵁ ⊤ := by simp
  have hfin := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) sG hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  have key : sG.appLE ⊤ U e ≫ G.presheaf.germ U _ hx = (Scheme.ΓSpecIso (.of F)).hom ≫ β := by
    rw [← Scheme.ΓSpecIso_naturality, hβ, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have h3 : (Spec (G.presheaf.stalk (genericPoint G))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (G.presheaf.stalk (genericPoint G))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
    rw [h3]
    simp
  classical
  letI : Algebra Γ(Sp F, ⊤) Γ(G, U) := (sG.appLE ⊤ U e).hom.toAlgebra
  have hfin' : Algebra.FiniteType Γ(Sp F, ⊤) Γ(G, U) := hfin
  obtain ⟨s, hs⟩ := hfin'.out
  have hmem : ∀ a : Γ(G, U), (G.presheaf.germ U _ hx).hom a ∈
      IntermediateField.adjoin P ((s.image (G.presheaf.germ U _ hx).hom : Finset _) : Set G.functionField) := by
    intro a
    have ha : a ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(G, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx' =>
      exact IntermediateField.subset_adjoin _ _ (by rw [Finset.coe_image]; exact ⟨x, hx', rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f.hom r) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [RingHom.algebraMap_toAlgebra, this, hβτ]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨s.image (G.presheaf.germ U _ hx).hom, eq_top_iff.2 fun f _ => ?_⟩
  have := functionField_isFractionRing_of_isAffineOpen G U hU
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(G, U)) f
  exact div_mem (hmem a) (hmem b)

end GlobalTheory.FGFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumns
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ColsInLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat

variable {D : D7}

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (finIncl D).rTensor D.host.E

theorem lift_eq (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    lift D z = finEmb D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lift_finPart (z : AE D) (h : infPart D z = 0) : lift D (finPart D z) = z := by
  have key : ∀ z : AE D, z =
      (show Ainf D.host.F →ₗ[D.host.F] AF D.host.F from
        LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E (infPart D z) +
      lift D (finPart D z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a e =>
      change _ = (pairA D.host.F a.1 0) ⊗ₜ[D.host.F] e + (pairA D.host.F 0 a.2) ⊗ₜ[D.host.F] e
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero a.1).symm (zero_add a.2).symm
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  have := key z
  rw [h, map_zero, zero_add] at this
  exact this.symm

def col (V W : HSp D) (b : Fin V.rank) : (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ WO V W where
  toFun z := Matrix.of fun i j => if j = b then lift D (z i) else 0
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _)]
    split_ifs <;> simp

theorem col_mem (V W : HSp D) (hV : V.gram = 1) (k : GA D W) (b : Fin V.rank)
    (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ latGHat W k) :
    col V W b z ∈ latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E))
      (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hz
    have hz' : z ∈ hat D.host.F (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) := by
      rw [← SetLike.mem_coe, GlobalTheory.MovedLat.hat_hLat]
      rw [gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1] at hz
      exact hz
    have hs : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
      intro i _
      by_cases h : i = b
      · subst h; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have := rankOne_mem_latO V W _ _ a ha _ (pure_mem_hatL _ 1 (one_mem _) _ hs) _
      (GlobalTheory.PrincInLevel.swap_mem_hatL _ z hz')
    convert this using 1
    ext i j
    change (if j = b then lift D (((1 : Af D.host.F) ⊗ₜ a) * z i) else 0) = _
    simp only [rankOne, Matrix.of_apply, hV, cF_tmul, eToEAf, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← TensorProduct.sum_tmul]
    have e : ∑ l, star ((Pi.single b 1 : Fin V.rank → D.host.E) l) *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) l j = if j = b then 1 else 0 := by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Pi.single_apply]
      split_ifs <;> simp
    rw [e]
    split_ifs
    · rw [lift_eq, map_mul, ← Algebra.TensorProduct.one_def, mul_one]
      rfl
    · simp
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem mem_latO_of_cols : ∀ (D : D7) (V W : HSp D), V.gram = 1 → ∀ (k : GA D W) (x : WO V W), x.map (infPart D) = 0 → (∀ b, (fun a => finPart D (x a b)) ∈ latGHat W k) → x ∈ (latO V W (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) (Bridge.hLat W (fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) := by
  intro D V W hV k x h0 hc
  have e : x = ∑ b, col V W b fun a => finPart D (x a b) := by
    ext i j
    rw [Matrix.sum_apply]
    change _ = ∑ b, if j = b then lift D (finPart D (x i b)) else 0
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    exact (lift_finPart _ (congrFun (congrFun h0 i) j)).symm
  rw [e]
  exact sum_mem fun b _ => col_mem V W hV k b _ (hc b)

end GlobalTheory.ColsInLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOpenHopfOrder
section
open Matrix Polynomial
open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

namespace GlobalTheory.SemilocalConj

theorem exists_cyclic_of_finite_maximal {R : Type} [CommRing R]
    (hfin : Set.Finite {I : Ideal R | I.IsMaximal}) {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (hs : g.charpoly.Separable) : ∃ v, IsUnit (krylov g v).det := by
  classical
  haveI : Finite (MaximalSpectrum R) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun m : MaximalSpectrum R =>
      (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal R | I.IsMaximal}))
      (fun a b h => MaximalSpectrum.ext (congrArg Subtype.val h))
  have hloc : ∀ m : MaximalSpectrum R, ∃ v : Fin r → R ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : R, ∀ m : MaximalSpectrum R,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

theorem conj_of_charpoly_eq_of_separable : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} →
    ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable →
      ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  intro R _ hfin n γ δ hχ hs
  obtain ⟨v, hv⟩ := exists_cyclic_of_finite_maximal hfin γ hs
  obtain ⟨w, hw⟩ := exists_cyclic_of_finite_maximal hfin δ (hχ ▸ hs)
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have h1 := GlobalTheory.Orb.mul_krylov_eq γ v
  have h2 := GlobalTheory.Orb.mul_krylov_eq δ w
  rw [← ha] at h1
  rw [← hb, ← hχ] at h2
  refine ⟨a * b⁻¹, ?_⟩
  set C := GlobalTheory.Orb.companionMat n γ.charpoly
  rw [Units.val_mul]
  calc (a : Matrix (Fin n) (Fin n) R) * ↑b⁻¹ * δ = ↑a * ↑b⁻¹ * (δ * ↑b) * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = ↑a * ↑b⁻¹ * (↑b * C) * ↑b⁻¹ := by rw [h2]
    _ = ↑a * C * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = γ * ↑a * ↑b⁻¹ := by rw [h1]
    _ = γ * (↑a * ↑b⁻¹) := by rw [mul_assoc]

end GlobalTheory.SemilocalConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominatorsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formGroup_testFunction_support_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  first | (exact @GlobalTheory.LKCx.BoundedDen.main) | (exact GlobalTheory.LKCx.BoundedDen.main) | (intros; apply GlobalTheory.LKCx.BoundedDen.main  <;> assumption)
end

