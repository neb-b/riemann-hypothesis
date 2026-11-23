module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKilledCapelliSpaceFiniteDimensionalOfFiniten
section
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

noncomputable section

namespace GlobalTheory.CapKilled

open Polynomial

theorem aeval_restrict_val {M : Type} [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M) (p : Submodule ℂ M)
    (h : ∀ x ∈ p, f x ∈ p) (P : ℂ[X]) (v : p) :
    ((aeval (f.restrict h) P) v : M) = aeval f P (v : M) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [map_add (f := _), hP, hQ]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul]
    congr 1
    induction n generalizing v with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem finiteDimensional_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ)) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → (∀ z ∈ Zalg E b, ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q) → FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) := by
  intro E _ _ _ b hP hint L hL W hW q hq hstab
  classical
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := b) τ u ∈ Zalg E b := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let V := GlobalTheory.CapKilled.space E b L W q
  let R : (E →+* ℂ) × Fin (b + 1) → Module.End ℂ V := fun p =>
    (cap (a := b) p.1 ((p.2 : ℕ) : ℂ)).restrict (fun ψ hψ => hstab _ (hcap _ _) ψ hψ)
  have hR : ∀ p (v : V), ((R p v : V) : Sm E b) = cap (a := b) p.1 ((p.2 : ℕ) : ℂ) (v : Sm E b) := fun _ _ => rfl
  let T : Finset (Module.End ℂ V) := Finset.univ.image R
  have key := GlobalTheory.FinEig.fd_of_finset T ?_ ?_ ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_
  · exact Module.Finite.equiv Submodule.topEquiv
  · intro u hu u' hu'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.1 hu'
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hR, hR, hR, hR, ← Module.End.mul_apply,
      (GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hcap _ _) (hcap _ _)).eq, Module.End.mul_apply]
  · intro u hu
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨q p.1 ((p.2 : ℕ) : ℂ), hq _ _, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [aeval_restrict_val]
    exact (GlobalTheory.CapKilled.mem_space.1 v.2).2.2.2.1 _ _
  · intro c
    let w : (E →+* ℂ) → ℂ → Fin (b + 1) → ℂ := fun τ u => Classical.choose (hint τ u)
    have hw : ∀ τ u, cap (a := b) τ u = ∑ j : Fin (b + 1), w τ u j • cap (a := b) τ ((j : ℕ) : ℂ) :=
      fun τ u => Classical.choose_spec (hint τ u)
    let c' : (E →+* ℂ) → ℂ → ℂ := fun τ u => ∑ j : Fin (b + 1), w τ u j * c (R (τ, j))
    let χ : Module.End ℂ (Sm E b) → ℂ := fun z =>
      if h : z ∈ Zalg E b then Classical.choose (GlobalTheory.CuspRep.Zalg_acts_by_scalar E b c' z h) else 0
    let J := (⊤ : Submodule ℂ V) ⊓ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ V) (c u))
    have hJcap : ∀ v ∈ J, ∀ τ u, cap (a := b) τ u ((v : V) : Sm E b) = c' τ u • ((v : V) : Sm E b) := by
      intro v hv τ u
      have hj : ∀ j : Fin (b + 1), cap (a := b) τ ((j : ℕ) : ℂ) ((v : V) : Sm E b) =
          c (R (τ, j)) • ((v : V) : Sm E b) := by
        intro j
        have h1 : v ∈ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ V) (c u)) := hv.2
        rw [Submodule.mem_iInf] at h1
        have h1' := h1 (R (τ, j))
        rw [Submodule.mem_iInf] at h1'
        have h2 := h1' (Finset.mem_image_of_mem R (Finset.mem_univ _))
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h2
        have h3 := congrArg (fun x : V => (x : Sm E b)) h2
        simpa only [hR, Submodule.coe_smul] using h3
      rw [hw τ u, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, hj, smul_smul, c', Finset.sum_smul]
    have hJz : ∀ v ∈ J, ∀ z ∈ Zalg E b, z ((v : V) : Sm E b) = χ z • ((v : V) : Sm E b) := by
      intro v hv z hz
      simp only [χ, dif_pos hz]
      exact Classical.choose_spec (GlobalTheory.CuspRep.Zalg_acts_by_scalar E b c' z hz) _ (hJcap v hv)
    have hmem : ∀ v ∈ J, ((v : V) : Sm E b) ∈ GlobalTheory.HCF.formsGL E b L W {χ} 1 := by
      intro v hv
      obtain ⟨hleft, hfix, hK, _, htame⟩ := GlobalTheory.CapKilled.mem_space.1 (v : V).2
      have hkfin : FiniteDimensional ℂ
          (Submodule.span ℂ (Set.range fun k => cptRep E b k ((v : V) : Sm E b))) := by
        obtain ⟨s, bb, hb⟩ := GlobalTheory.HCFct.exists_interp W hW
        have e : ∀ k, cptRep E b k ((v : V) : Sm E b) =
            ∑ i : s, (bb i).1 k • cptRep E b i.1 ((v : V) : Sm E b) := by
          intro k
          apply Subtype.ext
          funext g
          have := hb _ (hK g) k
          simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          rw [this]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        haveI : FiniteDimensional ℂ
            (Submodule.span ℂ (Set.range fun i : s => cptRep E b i.1 ((v : V) : Sm E b))) :=
          FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
        refine Submodule.finiteDimensional_of_le
          (S₂ := Submodule.span ℂ (Set.range fun i : s => cptRep E b i.1 ((v : V) : Sm E b)))
          (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        show cptRep E b k ((v : V) : Sm E b) ∈ _
        rw [e k]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      refine ⟨⟨hleft, ?_, hkfin, ?_, growth_of_tame htame⟩, hfix, hK, χ, rfl, ?_⟩
      · exact isOpen_stab_of_mem_nhds (finRep E b) _
          (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
      · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {((v : V) : Sm E b)})
          (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        show z _ ∈ _
        rw [hJz v hv z hz]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · intro zs hlen hzs
        obtain ⟨z, rfl⟩ := List.length_eq_one_iff.1 hlen
        simp only [List.foldr_cons, List.foldr_nil]
        rw [hJz v hv z (hzs z (List.mem_singleton_self z)), sub_self]
    haveI := hP L hL W hW {χ} (Set.finite_singleton χ) 1
    let Φ : J →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W {χ} 1) :=
      LinearMap.codRestrict _ (V.subtype.comp J.subtype) fun v => Submodule.subset_span (hmem v.1 v.2)
    have hinj : Function.Injective Φ := fun v v' h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W {χ} 1) => (x : Sm E b)) h))
    exact Module.Finite.of_injective Φ hinj

end GlobalTheory.CapKilled

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRight
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
open GlobalTheory.SliceSchwartz
open scoped RestrictedProduct

open scoped Classical

noncomputable section

namespace GlobalTheory.TamePartR

theorem td_of_inj {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

theorem totallyDisconnected_finiteAdele : ∀ (F : Type) [Field F] [NumberField F], TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) := fun v => td_adic v
  haveI : TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]) :=
    td_of_inj (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem pureA_sum (F : Type) [Field F] [NumberField F] {κ ι : Type} [Fintype ι] (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F f (∑ i, g i) = ∑ i, pureA F f (g i) := by
  funext x
  simp [pureA, Finset.sum_apply, Finset.mul_sum]

theorem isTame_partR : ∀ (F : Type) [Field F] [NumberField F] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ₁' → AF F) → ℂ)), IsTame F T → IsTame F (partR (κ := κ) T) := by
  intro F _ _ κ κ' κ₁' _ _ _ T hT g hg
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele (F := F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField (F := F)
  haveI := totallyDisconnected_finiteAdele F
  obtain ⟨ι₀, _, g₁, g₂, hg₁, hg₂, rfl⟩ := GlobalTheory.T.schwartz_product_decomposition _ κ κ' g hg
  choose ι inst P g' hg' hP using fun i => hT (g₂ i) (hg₂ i)
  choose Q hQ using fun (p : Σ i, ι i) => _root_.GlobalTheory.SliceOp.exists_tensor_clm (mixedEmbedding.mixedSpace F) κ κ' κ₁' (P p.1 p.2)
  refine ⟨Σ i, ι i, inferInstance, Q, fun p z => g₁ p.1 (z ∘ Sum.inl) * g' p.1 p.2 (z ∘ Sum.inr),
    fun p => GlobalTheory.SchwartzBox.sb_box (hg₁ p.1) (hg' p.1 p.2), fun f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pureA_sum, map_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext s
  rw [partR_apply, Finset.sum_apply]
  set xa : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (s (Sum.inl k)).1
  have hfun : (fun x₂ => pureA F f (fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr)) (Sum.elim (s ∘ Sum.inl) x₂)) =
      g₁ i (fun k => (s (Sum.inl k)).2) • pureA F (sliceR f xa) (g₂ i) := by
    funext x₂
    simp only [pureA, Pi.smul_apply, smul_eq_mul, sliceR_apply]
    have e : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((Sum.elim (s ∘ Sum.inl) x₂ : κ ⊕ κ' → AF F) k).1) =
        Sum.elim xa (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₂ k).1) := by
      funext k; cases k <;> rfl
    rw [e]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [hfun, map_smul, hP i (sliceR f xa)]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pureA, hQ]
  simp only [Function.comp_def]
  ring

end GlobalTheory.TamePartR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaExtend

theorem isRegularRing_sections {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsRegularRing Γ(Y, V) := by
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  rw [isRegularRing_iff]
  intro q hq
  let y : PrimeSpectrum Γ(Y, V) := ⟨q, hq⟩
  have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (hV.fromSpec y)) :=
    Y.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hy⟩
  have h : IsLocalization q.primeCompl (Y.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hy
  have := hY (hV.fromSpec y)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Y.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_stalk {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (f : X ⟶ Y) [Smooth f] (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  have hs : (f.appLE V U hUV).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have := isRegularRing_sections hY hV
  algebraize [(f.appLE V U hUV).hom]
  have : IsRegularRing Γ(X, U) := isRegularRing_of_smooth Γ(Y, V) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact ExtendRig.isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem ufd_of_regular (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE R

end GlobalTheory.ThetaExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNonzero
section
namespace GlobalTheory.StepFacNe

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_continuous {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (h : Continuous χ) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    Continuous (fun x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ => (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x : ℂ)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW
  have h1 := _root_.GlobalTheory.LFun.continuous_locChar h (_root_.GlobalTheory.AdelicU.splitPrime τ)
  have h2 := Continuous.units_map
    (_root_.GlobalTheory.LFun.complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom
    (_root_.GlobalTheory.LFun.SplitChart.continuous_complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ))
  exact h1.comp h2


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_ram {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (h : ¬ _root_.GlobalTheory.LFun.UnrAt χ (_root_.GlobalTheory.AdelicU.splitPrime τ)) :
    ∃ x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ, (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x ≠ 1 := by
  have hw := _root_.GlobalTheory.AdelicU.splitPrime_under τ
  unfold _root_.GlobalTheory.LFun.UnrAt at h
  push_neg at h
  obtain ⟨y, hy1, hy2⟩ := h
  unfold _root_.Formalism.L2.Host.IsUnitAt at hy1
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.LFun.SplitTie.complMap_bijective τ hw).2 (y : _)
  have hv : Valued.v a = 1 := by
    rw [← _root_.GlobalTheory.LFun.SplitTie.valued_complMap τ hw, ha]
    exact hy1
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hv
  refine ⟨Units.mk0 a ha0, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · intro h1
    apply hy2
    have hy : Units.map (_root_.GlobalTheory.LFun.complMap hw).toMonoidHom (Units.mk0 a ha0) = y :=
      Units.ext (by simpa using ha)
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW at h1
    rw [MonoidHom.comp_apply, hy] at h1
    exact h1

end GlobalTheory.StepFacNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem reads_linear_injective_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx f f' φ φ' hf hf'
  obtain ⟨-, -, hlin⟩ := thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hS hev x hx φ hf.1
  obtain ⟨hl, hinj⟩ := hlin φ' hf'.1
  obtain ⟨-, -, -, -, hp⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x
  obtain ⟨p, -, hp, -⟩ := hp hx
  refine ⟨fun a b => ⟨(hl a b).1, fun w hw => ?_⟩, fun h => hinj ?_, fun h h' e => ?_⟩
  · rw [(hl a b).2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.2 w hw, hf'.2 w hw]
    ring
  · funext z
    have h1 := hf.2 (p z) (hp z).1
    have h2 := hf'.2 (p z) (hp z).1
    rw [h, h2, (hp z).2] at h1
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) h1).symm
  · refine theta_eq_of_real D ψ V W hψ f f' h h' fun w hw => ?_
    rw [hf.2 w hw, hf'.2 w hw, e]

theorem IsONFr.mem_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}
    (hx : IsONFr X x) : x ∈ X.dom :=
  PIW.FdPA.orthonormal_domain r X x hx

theorem reads_linear_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx
  exact reads_linear_injective_dom D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx.mem_dom

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullVanish

theorem withBot_lt_of_add_one_le_nat {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) :=
  withBot_lt_of_add_one_lt (lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self n))

theorem topSelf_pull_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  intro k _ X Y _ _ p q D hq hX hY π hπ B hB
  letI := GlobalTheory.algebraΓOfHom q
  have hs : strHom k Y = q := GlobalTheory.strHom_eq (f := q) fun _ => rfl
  have hη : genericPoint X ∈ (closure ({π (genericPoint Y)} : Set X))ᶜ := fun h =>
    hπ (((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes _)).eq)
  have h1 := dim_closure_add_one_le (genericPoint_specializes (π (genericPoint Y)))
    isClosed_closure.isOpen_compl hη (fun h => h (subset_closure rfl))
  have h2 : topologicalKrullDim (closure ({genericPoint X} : Set X)) = topologicalKrullDim X := by
    rw [(genericPoint_spec X).def]
    exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  have h3 := withBot_lt_of_add_one_le_nat (h1.trans (h2.trans_le hX))
  have h := interNum_pull_eq_zero k 0 D Y X (hs ▸ hq) (by rwa [Nat.zero_add]) π h3
    (fun i => i.elim0) (fun i => i.elim0) (fun _ => B) (fun _ => hB)
  rw [topSelf_def, ← interNum_comp_equiv k _ (fun _ => pull_isLB hB π)
    (Equiv.emptySum (Fin 0) (Fin D)), ← h]
  congr 1
  funext x
  rcases x with i | a
  · exact i.elim0
  · rfl

end GlobalTheory.PullVanish
end
end

