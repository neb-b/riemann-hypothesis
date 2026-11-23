module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcFrameOb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0007
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galCount :
    HcPublished → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M), (∀ m, IsLocallyConstant fun g => ρ g m) → (∀ q ∈ Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → ρ (toGS Ω SP g) = 1) → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k ((galFrame SP T Q v0 pl K).Ob ρ) ∧ Module.Finite k ((galFrame SP T Q v0 pl K).H1c ρ) ∧ finrank k ((galFrame SP T Q v0 pl K).Ob ρ) = finrank k ((galFrame SP T Q v0 pl K).H1c ρ) + finrank k (LinearMap.ker (ρ (toGS Ω SP σ) - 1)) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro P Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ ρ hlc hN σ hσ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : Finite M := Module.finite_of_finite k
  have hρ : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    exact fun m => (hlc m).continuous
  have hN' : ∀ q, ∀ n ∈ (galFrame SP T Q v0 pl K).N q, ρ ((galFrame SP T Q v0 pl K).ψ q n) = 1 :=
    fun q n hn => hN q.1 q.2 n.1 hn.1 hn.2
  have tail := galTail P.lf P.gf P.pt Ω l v0 hD k M ρ hρ
  have hG : Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
    obtain ⟨S, e, rfl, hS, -⟩ := galIdx Ω l v0 hD
    exact globEuler P.gf P.ge Ω l hD.l_odd S hS k M ρ hρ σ hσ
  obtain ⟨g1, g2, g3⟩ := hG
  have hc : ∀ p, ContAction (ρ.comp (locHom SP (pl p))) := fun p =>
    hρ.comp ((continuous_locHom SP (pl p)).prodMap continuous_id)
  have loc := fun p (hp : p ∈ T ∨ p ∈ Q) => locEuler P.lf P.lt P.le Ω l p (hD.prime p hp) (pl p) (hD.isOver p hp) k M _ (hc p)
  obtain ⟨a1, a2⟩ := framed_h1_euler_formula (galFrame SP T Q v0 pl K) ρ hρ hN' g1
  obtain ⟨b1, b2⟩ := frameOb (galFrame SP T Q v0 pl K) ρ hρ hN' g1 g2 (fun v => (loc v.1 (.inl v.2)).1)
    (fun q => (loc q.1 (.inr q.2)).1)
  refine ⟨b1, a1, ?_⟩
  have hT : ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) = ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) +
      ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + finrank k M := by
    rw [Finset.sum_congr rfl fun (v : T) _ => (loc v.1 (.inl v.2)).2.2.1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨l, hD.l_mem⟩]
    · simp
    · intro b _ hb
      exact if_neg fun h => hb (Subtype.ext h)
    · simp
  have hQ : ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) =
      ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) +
      ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hql : (q : ℕ) ≠ l := fun h => Finset.disjoint_left.1 hD.disj hD.l_mem (h ▸ q.2)
    obtain ⟨φ, h1, h2⟩ := decZhat Ω q (hD.prime _ (.inr q.2)) (pl q) (hD.isOver _ (.inr q.2))
    rw [(loc q.1 (.inr q.2)).2.2.1, if_neg hql, add_zero,
      urIndex l _ (hc q) ((Ine (F := ℚ) (pl q)).subgroupOf (Dec (F := ℚ) (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))
        (Subgroup.comap_mono inf_le_left) ?_,
      urAbs _ (hc q) _ φ h1 h2]
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
    exact hD.idx q q.2
  change _ + _ = _ + ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) at a2
  change _ + _ + ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) =
    _ + ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) + _ at b2
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkRes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.bkRes :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), c ∈ Z1 ρ → IsBK l ρ c → (fun s : G K Ω => c (s.restrictScalars ℚ)) ∈ Z1 (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) ∧ IsBK l (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (fun s : G K Ω => c (s.restrictScalars ℚ)) := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ _ _ _ _ _ _ ρ c hc hbk
  obtain ⟨hcont, hcc⟩ := (mem_Z1_iff_cocycle _ _).1 hc
  have hcont' : Continuous fun s : G K Ω => c (s.restrictScalars ℚ) :=
    hcont.comp (continuous_restrictScalarsHom ℚ K Ω)
  have hcc' : ∀ s t : G K Ω, c ((s * t).restrictScalars ℚ) =
      c (s.restrictScalars ℚ) + ρ (s.restrictScalars ℚ) (c (t.restrictScalars ℚ)) :=
    fun s t => hcc (s.restrictScalars ℚ) (t.restrictScalars ℚ)
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨hcont', hcc'⟩,
    UpperTheory.V.X.Kato.resAway l K Ω C V ρ c hcc hbk.away, fun τ => ?_⟩
  obtain ⟨j₀, -, -, x, hx⟩ := hbk.above (τ.comp (algebraMap ℚ K))
  obtain ⟨g, hg⟩ := UpperTheory.V.X.Kato.embConj l K Ω j₀ τ
  refine ⟨j₀.comp (g : Ω →+* Ω), hg, ⟨hcont'.comp (continuous_fst.comp continuous_subtype_val),
    fun s t => hcc' s.1.1 t.1.1⟩,
    TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id x - c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l), ?_⟩
  rintro ⟨⟨s, σ⟩, hs⟩
  have ht : (g * s.restrictScalars ℚ * g⁻¹, σ) ∈ decJ ℚ j₀ := by
    intro y
    have h := hs (g⁻¹ y)
    change σ (j₀ (g (g.symm y))) = j₀ (g (s (g.symm y))) at h
    rw [AlgEquiv.apply_symm_apply] at h
    exact h
  have h1 := hx ⟨_, ht⟩
  change c (s.restrictScalars ℚ) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (s.restrictScalars ℚ)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap _ - _
  change c (g * s.restrictScalars ℚ * g⁻¹) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (g * s.restrictScalars ℚ * g⁻¹))
      ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap x - x at h1
  generalize s.restrictScalars ℚ = u at h1 ⊢
  have e1 : g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ := by group
  have e2 := hcc g⁻¹ (g * u * g⁻¹)
  rw [e1, hcc] at e2
  have key : ∀ y : TensorProduct ℚ_[l] V (UpperTheory.V.Loc.Bcr l),
      TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id
        (TensorProduct.AlgebraTensorModule.map (ρ (g * u * g⁻¹)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap y) =
      TensorProduct.AlgebraTensorModule.map (ρ u) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap
        (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹)
    (LinearMap.id : UpperTheory.V.Loc.Bcr l →ₗ[ℚ_[l]] UpperTheory.V.Loc.Bcr l)) h1
  rw [map_sub, key, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h2
  rw [map_sub, TensorProduct.AlgebraTensorModule.map_tmul, eq_sub_of_add_eq e2, TensorProduct.sub_tmul,
    TensorProduct.add_tmul, h2]
  simp only [AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, map_one]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocTors
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.locTors : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ n : ℤ, n ≠ 0 → n ≠ 1 → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 k) ∉ v.asIdeal → ∀ z : G k Ω → O, Coc (ψ * chiO k Ω l O ^ n) z → Alg.AdicCont (maximalIdeal O) z → CobOn (ψ * chiO k Ω l O ^ n) z (Dec (F := k) A) := by
  intro lf lt le k Ω _ _ _ _ _ l hl O _ _ _ _ _ ψ ho n h0 h1 v A hA hv z hz hc
  haveI : CharZero O := charZero_of_injective_algebraMap (dvrFacts l O).1
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hlm : (l : O) ∈ maximalIdeal O := by
    haveI := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O)]
    exact map_nonunit _ _ PadicInt.p_nonunit
  obtain ⟨B, hB⟩ := So.locKill lf lt le k Ω l O ψ ho n h0 h1 v A hA hv
  obtain ⟨g, hg, hne⟩ := So.decNe k Ω l O ψ ho n h0 v A hA
  obtain ⟨a, ha, m, hm⟩ := So.cobLim O (Dec (F := k) A) ((ψ * chiO k Ω l O ^ n).comp (Dec (F := k) A).subtype) l B hl0 hlm
    ⟨⟨g, hg⟩, hne⟩ (fun r => hB _ _ _ (isLev_lev (pow_ne_zero r hl0) _)) (fun g => z g) (fun g h => hz g h)
    fun N => (hc N).comp_continuous continuous_subtype_val
  exact ⟨a, ha, m, fun g hg => hm ⟨g, hg⟩ trivial⟩
end

