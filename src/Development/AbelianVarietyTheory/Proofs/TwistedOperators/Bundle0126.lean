module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
section
noncomputable section

namespace GlobalTheory.LFun.HeckeScalar

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LFun.SatCompare

variable {G V M : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}

def finOrbit (τ : Representation ℂ G M) (K : Subgroup G) : Submodule ℂ M where
  carrier := {m | (Set.range fun k : K => τ k m).Finite}
  zero_mem' := (Set.finite_singleton 0).subset (by rintro _ ⟨k, rfl⟩; simp)
  add_mem' {a b} ha hb := (Set.Finite.add ha hb).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, _, ⟨k, rfl⟩, by simp⟩)
  smul_mem' c a ha := (Set.Finite.image (c • ·) ha).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, by simp⟩)

private theorem mem_fixed_iff_twisted_operators {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W)
    (L : Subgroup G) (v : W) : v ∈ fixed τ L ↔ ∀ k : L, τ k v = v := by
  change (∀ k : L, τ k v = ((1 : L →* ℂˣ) k : ℂ) • v) ↔ _
  simp

theorem exists_fixed_preimage {τ : Representation ℂ G M} (π : M →ₗ[ℂ] V) (hπ : ∀ g m, π (τ g m) = ρ g (π m))
    {m : M} (hm : m ∈ finOrbit τ K) (hy : π m ∈ fixed ρ K) : ∃ m' ∈ fixed τ K, π m' = π m := by
  classical

  have hfin : (Set.range fun k : K => τ k m).Finite := hm
  obtain ⟨O, hO⟩ : ∃ O : Finset M, ∀ o, o ∈ O ↔ ∃ k : K, τ k m = o :=
    ⟨hfin.toFinset, fun o => by rw [Set.Finite.mem_toFinset]; try exact Iff.rfl⟩
  have hmul : ∀ (a b : K) (o : M), τ (a : G) (τ (b : G) o) = τ ((a * b : K) : G) o := by
    intro a b o
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have hperm : ∀ a : K, ∑ o ∈ O, τ (a : G) o = ∑ o ∈ O, o := by
    intro a
    refine Finset.sum_nbij' (fun o => τ (a : G) o) (fun o => τ ((a⁻¹ : K) : G) o) ?_ ?_ ?_ ?_ ?_
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a * k, (hmul a k m).symm⟩
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a⁻¹ * k, (hmul a⁻¹ k m).symm⟩
    · intro o _
      show τ ((a⁻¹ : K) : G) (τ (a : G) o) = o
      rw [hmul, inv_mul_cancel]
      simp
    · intro o _
      show τ (a : G) (τ ((a⁻¹ : K) : G) o) = o
      rw [hmul, mul_inv_cancel]
      simp
    · intro o _
      rfl
  have hne : (O.card : ℂ) ≠ 0 := by
    have hm' : m ∈ O := (hO m).2 ⟨1, by simp⟩
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hm')
  refine ⟨(O.card : ℂ)⁻¹ • ∑ o ∈ O, o, ?_, ?_⟩
  · rw [mem_fixed_iff_twisted_operators]
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, hperm a]
  · have hconst : ∀ o ∈ O, π o = π m := by
      intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      rw [hπ]
      exact (mem_fixed_iff_twisted_operators ρ K (π m)).1 hy k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hne, one_smul]

def permRep (K : Subgroup G) : Representation ℂ G (G ⧸ K →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (g • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

theorem permRep_single (g : G) (c : G ⧸ K) (a : ℂ) :
    permRep K g (Finsupp.single c a) = Finsupp.single (g • c) a := by
  change Finsupp.mapDomain (g • ·) (Finsupp.single c a) = _
  exact Finsupp.mapDomain_single

private theorem permRep_apply_eq_mapDomain (g : G) (φ : G ⧸ K →₀ ℂ) :
    permRep K g φ = Finsupp.mapDomain (g • ·) φ :=
  rfl

theorem permRep_apply (g : G) (φ : G ⧸ K →₀ ℂ) (c : G ⧸ K) : permRep K g φ (g • c) = φ c := by
  rw [permRep_apply_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) φ c

theorem mem_finOrbit (hK : IsCommensurated K) (φ : G ⧸ K →₀ ℂ) : φ ∈ finOrbit (permRep K) K := by
  classical

  have hpi : (Set.pi Set.univ fun c : φ.support => MulAction.orbit K (c : G ⧸ K)).Finite := by
    refine Set.Finite.pi fun c => ?_
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (c : G ⧸ K)
    rw [← hs]
    exact Formalism.UG.P.orbit_coset_finite K hK s
  change (Set.range fun k : K => permRep K k φ).Finite
  refine (hpi.image fun t => ∑ c : φ.support, Finsupp.single (t c) (φ c)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨fun c => k • (c : G ⧸ K), ?_, ?_⟩
  · rw [Set.mem_univ_pi]
    intro c
    exact MulAction.mem_orbit _ k
  · show (∑ c : φ.support, Finsupp.single (k • (c : G ⧸ K)) (φ c)) = permRep K (k : G) φ
    rw [permRep_apply_eq_mapDomain]
    exact Finset.sum_coe_sort φ.support fun a => Finsupp.single ((k : G) • a) (φ a)

def orbitMap (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) : (G ⧸ K →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun c => ρ c.out x

theorem orbitMap_single (hx : x ∈ fixed ρ K) (g : G) (a : ℂ) :
    orbitMap ρ K x (Finsupp.single (g : G ⧸ K) a) = a • ρ g x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (s := K) g
  simp only [orbitMap, Finsupp.linearCombination_single]
  rw [hk, map_mul, Module.End.mul_apply, (mem_fixed_iff_twisted_operators ρ K x).1 hx k]

theorem orbitMap_permRep (hx : x ∈ fixed ρ K) (g : G) (φ : G ⧸ K →₀ ℂ) :
    orbitMap ρ K x (permRep K g φ) = ρ g (orbitMap ρ K x φ) := by
  induction φ using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add φ₁ φ₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | single c a =>
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
    rw [permRep_single, MulAction.Quotient.smul_mk, smul_eq_mul, orbitMap_single hx, orbitMap_single hx, map_smul,
      map_mul, Module.End.mul_apply]

theorem orbitMap_surjective (hρ : ρ.IsIrreducible) (hx : x ∈ fixed ρ K) (h0 : x ≠ 0) :
    Function.Surjective (orbitMap ρ K x) := by

  let S : Subrepresentation ρ := ⟨LinearMap.range (orbitMap ρ K x), by
    intro g v hv
    obtain ⟨φ, rfl⟩ := LinearMap.mem_range.1 hv
    exact LinearMap.mem_range.2 ⟨permRep K g φ, orbitMap_permRep hx g φ⟩⟩
  have hxS : x ∈ S.toSubmodule := by
    show x ∈ LinearMap.range (orbitMap ρ K x)
    refine LinearMap.mem_range.2 ⟨Finsupp.single ((1 : G) : G ⧸ K) 1, ?_⟩
    rw [orbitMap_single hx, one_smul, map_one, Module.End.one_apply]
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top S with h | h
  · rw [h] at hxS
    exact absurd ((Submodule.mem_bot ℂ).1 hxS) h0
  · intro y
    have hy : y ∈ S.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact LinearMap.mem_range.1 hy

end GlobalTheory.LFun.HeckeScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultNormalisedInductionExact
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.IndExact

section General

variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem smIndMap_injective (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι) :
    Function.Injective (smIndMap ι) := fun φ ψ h =>
  Subtype.ext (Subtype.ext (funext fun g =>
    hι (congrFun (congrArg (fun χ : smoothPart (ind P ρ) => χ.1.1) h) g)))

theorem exists_smIndMap_eq (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι)
    (F : smoothPart (ind P ρ)) (hF : ∀ g, ∃ u, ι u = F.1.1 g) : ∃ F', smIndMap ι F' = F := by
  choose u hu using hF
  refine ⟨⟨⟨u, fun h g => hι ?_⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds F.2 (by simp)) fun g hg => ?_)⟩, Subtype.ext (Subtype.ext (funext hu))⟩
  · rw [ι.isIntertwining, hu, hu, F.1.2 h g]
  · have hg' : ind P ρ g F.1 = F.1 := hg
    refine Subtype.ext (funext fun x => hι ?_)
    show ι (u (x * g)) = ι (u x)
    rw [hu, hu]
    exact congrFun (congrArg Subtype.val hg') x

theorem exists_normalised_pi {α : Type} [Finite α] {Γ : α → Type} [∀ i, Group (Γ i)]
    [∀ i, TopologicalSpace (Γ i)] (K : ∀ i, Subgroup (Γ i))
    (h : ∀ i, ∀ U ∈ nhds (1 : Γ i), ∃ J : Subgroup (Γ i), IsOpen (J : Set (Γ i)) ∧ (J : Set (Γ i)) ⊆ U ∧
      J ≤ K i ∧ ∀ x ∈ K i, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ nhds (1 : ∀ i, Γ i), ∃ J : Subgroup (∀ i, Γ i), IsOpen (J : Set (∀ i, Γ i)) ∧
      (J : Set (∀ i, Γ i)) ⊆ U ∧ J ≤ Subgroup.pi Set.univ K ∧
        ∀ x ∈ Subgroup.pi Set.univ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hI⟩ := hU
  choose J h1 h2 h3 h4 using fun i => h i (t i) (ht i)
  exact ⟨Subgroup.pi Set.univ J, isOpen_set_pi Set.finite_univ fun i _ => h1 i,
    fun x hx => hI fun i _ => h2 i (hx i trivial), fun x hx i _ => h3 i (hx i trivial),
    fun x hx j hj i _ => h4 i _ (hx i trivial) _ (hj i trivial)⟩

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSmoothChar_relDeltaHalf : IsSmoothChar (relDeltaHalf k c) := by
  unfold relDeltaHalf
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (isSmoothChar_deltaHalf k).comp _ (continuous_apply a)

theorem relInd_surjective (f : ∀ i, (Σ j, c i j) ≃ m i)
    {π : Representation ℂ (∀ i, Levi k (c i)) W} {π' : Representation ℂ (∀ i, Levi k (c i)) W'}
    (p : π.IntertwiningMap π') (hp : Function.Surjective p) (hπ : IsSmooth π) :
    Function.Surjective (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) := by
  have H := fun i => GlobalTheory.SmGL.LeviInt.levi_integral_facts k β (m i) (c i) (f i)
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hP : IsClosed (relParab k f : Set (Levi k m)) :=
    isClosed_set_pi fun i _ => (H i).2.2.2.2.2.2.1
  have hK : IsCompact (Subgroup.pi Set.univ (fun i => KO k (m i)) : Set (Levi k m)) :=
    isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hPK : ∀ g : Levi k m, ∃ q ∈ relParab k f, ∃ x ∈ Subgroup.pi Set.univ (fun i => KO k (m i)),
      g = q * x := fun g => by
    choose q hq x hx e using fun i => (H i).2.2.2.2.2.2.2.2 (g i)
    exact ⟨q, fun i _ => hq i, x, fun i _ => hx i, funext e⟩
  have hcont : Continuous (relProj k f) := continuous_pi fun i =>
    (H i).2.2.2.2.2.1.comp (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  let σ₀ : Representation ℂ (relParab k f) W := (twist π (relDeltaHalf k c)).comp (relProj k f)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (Levi k m) (relParab k f) _ hP hK hPK
    (exists_normalised_pi _ fun i => GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (m i)) _ _ _ _
    (isSmooth_comp (isSmooth_twist hπ isSmoothChar_relDeltaHalf) _ hcont)
    (compMap (twistMap p _) _) Unit (fun _ => z) hp ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

end Local

theorem jhMult_relInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (W W₁ W₂ : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (π : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W) (π₁ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₁) (π₂ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₂) (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → GlobalTheory.PRep.IsSmooth π → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GlobalTheory.SmGL.Levi k m) Y), τ.IsIrreducible → GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π) = GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₁) + GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₂) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f W W₁ W₂ _ _ _ _ _ _ π π₁ π₂ ι p hι hp h0 hker hπ Y _ _ τ hτ
  refine GlobalTheory.JHMult.jhMult_exact
    (smIndMap (compMap (twistMap ι (relDeltaHalf k c)) (relProj k f)))
    (smIndMap (compMap (twistMap p (relDeltaHalf k c)) (relProj k f))) hτ
    (smIndMap_injective _ hι) (relInd_surjective f p hp hπ)
    (fun u => Subtype.ext (Subtype.ext (funext fun g => h0 _))) fun F hF => ?_
  exact exists_smIndMap_eq _ hι F fun g =>
    hker _ (congrFun (congrArg (fun χ => χ.1.1) hF) g)

end GlobalTheory.SmGL.IndExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix GlobalTheory.AdelicLatMove
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatStab

variable {D : D7}

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  ext i j
  rfl

theorem mulVec_mem_of_mem_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (x : Fin n → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨y, rfl⟩ := hM
  rw [hβ _]
  have hx' := (hβ x).1 hx
  have e : (β⁻¹).val * (frGL β y).val = (intGL D.host.F D.host.E n y).val * (β⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    change β⁻¹ * (β * intGL D.host.F D.host.E n y * β⁻¹) = _
    group
  intro i
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  change ∑ j, (intGL D.host.F D.host.E n y).val i j * ((β⁻¹).val *ᵥ x) j ∈ _
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (y.val i j).2 (hx' j)

theorem rankOne_smul_mem_latO (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop)
    (γ : Af D.host.F) (hγ : γ ∈ Formalism.UG.intAd D.host.F) (hP : ∀ v, ¬ Pv v → evalV D.host.F v γ = 0)
    (a : D.host.E) (ha : a ∈ D.host.AA)
    (s : Fin S.rank → Lev.EAf D) (hs : s ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (t : Fin T.rank → Lev.EAf D) (ht : t ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT) :
    rankOne S T a s (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • t) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  have hs' := mem_closure_of_mem_hatL ΛS s hs
  have ht' := mem_closure_of_mem_hatL ΛT t ht
  clear hs ht
  change rankOneHom S T a s _ ∈ _
  induction hs' using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht' using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      have e : (((1 : D.host.E) ⊗ₜ[D.host.F] γ : Lev.EAf D) • fun i => (y i ⊗ₜ[D.host.F] β : Lev.EAf D)) =
          fun i => y i ⊗ₜ[D.host.F] (γ * β) := by
        ext i
        simp
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨γ * β * α, (mul_mem (mul_mem hγ hβ) hα : γ * β * α ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_,
        a, ha, x, hx, y, hy, rankOne_pure S T a x y α (γ * β)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [smul_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add, map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := rankOneHom S T a), AddMonoidHom.add_apply]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (g : GA D S) (h : GA D T)
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv) :
    actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) Pv := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    have e2 : (fun i => (t i ⊗ₜ[D.host.F] α : Lev.EAf D)) =
        ((1 : D.host.E) ⊗ₜ[D.host.F] α : Lev.EAf D) • fun i => (t i ⊗ₜ[D.host.F] (1 : Af D.host.F) : Lev.EAf D) := by
      ext i
      simp
    rw [← e, actO_rankOne, e2, Matrix.mulVec_smul, ← finE_val, ← finE_val]
    exact rankOne_smul_mem_latO S T ΛS ΛT Pv α hα hP a ha _
      (mulVec_mem_of_mem_St ΛS βS _ hS hg _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_of_mem_St ΛT βT _ hT hh _ (pure_mem_hatL ΛT 1 (one_mem _) t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh Pv u
  refine ⟨actO_mem S T ΛS ΛT βS βT hS hT g h hg hh Pv u, fun hu => ?_⟩
  have h1 := actO_mem S T ΛS ΛT βS βT hS hT g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg)
    (by rw [map_inv]; exact inv_mem hh) Pv _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LatStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorDoublyIndexedSwapBlocksEquiv
section
open scoped TensorProduct

noncomputable section

open PiTensorProduct GlobalTheory.PRep GlobalTheory.JacStages

namespace GlobalTheory.SmGL

section SwapTensor

def sigmaPairSwap (α β : Type) : (Σ _ : α, β) ≃ (Σ _ : β, α) where
  toFun p := ⟨p.2, p.1⟩
  invFun q := ⟨q.2, q.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {α β : Type} [Finite α] [Finite β]
  (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)] [∀ i j, Module ℂ (Y i j)]

theorem exists_pairCurry : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] i, ⨂[ℂ] j, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun i => tprod ℂ fun j => x ⟨i, j⟩ := by
  classical
  exact ⟨sigmaCurry (fun p : (Σ _ : α, β) => Y p.1 p.2),
    sigmaCurry_tprod (fun p : (Σ _ : α, β) => Y p.1 p.2)⟩


omit [Finite α] [Finite β] in
theorem exists_pairSwap :
    ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] q : (Σ _ : β, α), Y q.2 q.1,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2,
      e (tprod ℂ x) = tprod ℂ fun q : (Σ _ : β, α) => x ⟨q.2, q.1⟩ :=
  ⟨reindex ℂ (fun p : (Σ _ : α, β) => Y p.1 p.2) (sigmaPairSwap α β),
    fun x => reindex_tprod (sigmaPairSwap α β) x⟩

theorem exists_pairCurrySwap : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] j, ⨂[ℂ] i, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun j => tprod ℂ fun i => x ⟨i, j⟩ := by
  obtain ⟨e₁, h₁⟩ := exists_pairSwap Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurry (fun j i => Y i j)
  refine ⟨e₁.trans e₂, fun x => ?_⟩
  rw [LinearEquiv.trans_apply, h₁]
  exact h₂ _

end SwapTensor

theorem piTensor_swapBlocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] (c : α → β → Type)
    [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)]
    [∀ i j, Module ℂ (Y i j)] (σ : ∀ i j, Representation ℂ (GL (c i j) k) (Y i j)),
    Nonempty (Representation.Equiv
      ((GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.piTensor fun j => σ i j).comp (GlobalTheory.SmGL.swapBlocks k c))
      (GlobalTheory.SmGL.piTensor fun j => GlobalTheory.SmGL.piTensor fun i => σ i j)) := by
  intro k _ _ _ _ α β _ _ c _ _ Y _ _ σ
  obtain ⟨e₁, h₁⟩ := exists_pairCurry Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurrySwap Y
  refine ⟨Representation.Equiv.mk (e₁.symm.trans e₂) fun g => ?_⟩
  have key : ∀ w : ⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2,
      e₂ (e₁.symm ((piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ w))) =
        (piTensor fun j => piTensor fun i => σ i j) g (e₂ w) := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      have h : (piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ (tprod ℂ x)) =
          e₁ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₁, h₁, piTensor_tprod]
        congr 1
        funext i
        exact piTensor_tprod (fun j => σ i j) _ _
      have h' : (piTensor fun j => piTensor fun i => σ i j) g (e₂ (tprod ℂ x)) =
          e₂ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₂, h₂, piTensor_tprod]
        congr 1
        funext j
        exact piTensor_tprod (fun i => σ i j) _ _
      rw [map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, h, h', LinearEquiv.symm_apply_apply]
    | add w w' hw hw' =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hw, hw']
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := e₁.surjective v
  have h := key w
  rw [← e₁.symm_apply_apply w, e₁.apply_symm_apply] at h
  exact h

end GlobalTheory.SmGL
end
end

