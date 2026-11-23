module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import GroundTheory.PAdicHodge.TiltField
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationally

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSum
section
noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Present.SumRed

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}

theorem exists_proj {T T' Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L)
    (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) :
    ∃ (p : LatHom Z.L T.L) (p' : LatHom Z.L T'.L), latAdd (latComp f p) (latComp g p') = latId Z := by
  let e : (T.V × T'.V) ≃ₗ[LL] Z.V := LinearEquiv.ofBijective _ hb
  have he : ∀ x y, e.symm (f.f x + g.f y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; rfl
  have hz : ∀ z, f.f (e.symm z).1 + g.f (e.symm z).2 = z := fun z => e.apply_symm_apply z
  have hρ : ∀ σ z, e.symm (Z.ρ σ z) = (T.ρ σ (e.symm z).1, T'.ρ σ (e.symm z).2) := fun σ z => by
    rw [← he, f.equiv, g.equiv, ← map_add (f := _), hz]
  haveI := T.mtop.toContinuousSMul
  haveI := T'.mtop.toContinuousSMul
  refine ⟨⟨LinearMap.fst LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩,
    ⟨LinearMap.snd LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩, ?_⟩
  · exact congrArg Prod.fst (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).1 ∈ _
    rw [he]; exact hx
  · exact congrArg Prod.snd (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).2 ∈ _
    rw [he]; exact hy
  · unfold latAdd latId
    congr 1
    exact LinearMap.ext hz

variable (W : LocWach PD LL O v n₀)

theorem map_mem {T Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (x : ↥(DΔ W T)) :
    W.map f (x : W.DD T) ∈ DΔ W Z := fun δ hδ => by
  rw [← W.map_γ, x.2 δ hδ]

theorem red_sum {k : Type} [Field k] [Algebra O k] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam} (p : Pres W F ι τ γ)
    {T T' Z : LocLat G Qp LL O} {A A' C : Ob k G} {q q' r}
    (hq : Onto T A q) (hq' : Onto T' A' q') (hr : Onto Z C r)
    (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ) (hZ : IsCrys PD Z.ρ)
    (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)) (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) (ha : IsHom A C a) (hb' : IsHom A' C b)
    (hfa : ∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x))
    (hgb : ∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x))
    (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y)
    (hN' : ∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ W T'), (x : W.DD T') ∈ W.N T' ∧ p.j T' A' q' i x = y)
    (hL : ∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ W Z), (x : W.DD Z) ∈ W.N Z ∧ p.j Z C r i x = y) (i : ZMod n) :
    L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  obtain ⟨π, π', hπ⟩ := exists_proj f g hb hs
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (hL i y).1 hy
    let x₁ : ↥(DΔ W T) := ⟨_, map_mem W π x⟩
    let x₂ : ↥(DΔ W T') := ⟨_, map_mem W π' x⟩
    have hsum : x = ⟨_, map_mem W f x₁⟩ + ⟨_, map_mem W g x₂⟩ := by
      apply Subtype.ext
      have := W.map_id Z x
      rw [← hπ, W.map_latAdd, W.map_comp, W.map_comp] at this
      exact this.symm
    rw [hsum, map_add (f := _), p.j_map T A q Z C r hq hr f a ha hfa i x₁ _ rfl,
      p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x₂ _ rfl]
    exact Submodule.add_mem_sup
      ⟨_, (hN i _).2 ⟨x₁, W.map_N π hZ hT _ hx, rfl⟩, rfl⟩
      ⟨_, (hN' i _).2 ⟨x₂, W.map_N π' hZ hT' _ hx, rfl⟩, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W f x⟩, W.map_N f hT hZ _ hx,
        p.j_map T A q Z C r hq hr f a ha hfa i x _ rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN' i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W g x⟩, W.map_N g hT' hZ _ hx,
        p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x _ rfl⟩

end General

theorem reduction_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A' : Ob k S.G) q' (U' : ZMod S.n → Multiset ℤ), Onto T' A' q' → KerIs S.Γ.lam q' → CrysWith (P.PD S.K) S.emb T'.ρ U' → ∀ (Z : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (C : Ob k S.G) r (V : ZMod S.n → Multiset ℤ), Onto Z C r → KerIs S.Γ.lam r → CrysWith (P.PD S.K) S.emb Z.ρ V → ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) → (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b → (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) → (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) → ∀ (N : Lats k S.n A.m) (N' : Lats k S.n A'.m) (L : Lats k S.n C.m), (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → (∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ (S.W H) T'), (x : (S.W H).DD T') ∈ (S.W H).N T' ∧ p.j T' A' q' i x = y) → (∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ (S.W H) Z), (x : (S.W H).DD Z) ∈ (S.W H).N Z ∧ p.j Z C r i x = y) → ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  intro l _ P H S k _ _ _ _ R ι F τ γ p _ _ _ _ T A q U hq _ hT T' A' q' U' hq' _ hT' Z C r V hr _ hZ
    f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i
  exact red_sum (S.W H) p hq hq' hr hT.1 hT'.1 hZ.1 f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i

end GlobalTheory.Present.SumRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct

noncomputable section

namespace GlobalTheory.InducedSectionsSpanStatement

section General

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def trCochain (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O) :
    (G → T.V) →ₗ[O] (G' → T.V) where
  toFun f g := ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply, Finset.smul_sum]

theorem trCochain_apply (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O)
    (f : G → T.V) (g : G') : trCochain ι T f g = ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out))) := rfl

theorem trCochain_Z1T [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCocycles (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCocycles T.L := by
  obtain ⟨⟨hcont, hcoc⟩, hT⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
  haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho
      (fun g => IsModuleTopology.continuous_of_linearMap (T.ρ g))
      (fun g => c (Function.invFun ι g)) ?_
    have h1 : (ι.range : Set G') = ι '' Set.univ := by
      rw [Set.image_univ]; rfl
    rw [h1, he.isInducing.continuousOn_image_iff]
    have h2 : ((fun g => c (Function.invFun ι g)) ∘ ι) = c := by
      funext g; simp only [Function.comp_apply, hj]
    rw [h2]
    exact hcont.continuousOn
  · refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.1
      (fun g => c (Function.invFun ι g)) ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, hj, hj, hj]
    exact hcoc a b
  · intro g _
    rw [trCochain_apply]
    exact Submodule.sum_mem _ fun q _ => T.L.stable _ _ (hT _ (Set.mem_univ _))

theorem trCochain_B1T (ι : G →* G') (hι : Continuous ι) (hinj : Function.Injective ι)
    [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCoboundaries (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCoboundaries T.L := by
  obtain ⟨x, hx, rfl⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun hinj
  refine ⟨∑ q : G' ⧸ ι.range, T.ρ q.out x,
    Submodule.sum_mem _ fun q _ => T.L.stable _ _ hx, ?_⟩
  funext g
  symm
  refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.2.1
    (fun g => T.ρ (ι (Function.invFun ι g)) x - x) x ?_ g
  rintro _ ⟨a, rfl⟩
  rw [hj]

def corH1 [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) : LatticeCohomology (LiftingTheory.resLoc ι hι T).L →ₗ[O] LatticeCohomology T.L :=
  Submodule.mapQ _ _
    (((trCochain ι T).comp (latticeCocycles (LiftingTheory.resLoc ι hι T).L).subtype).codRestrict (latticeCocycles T.L)
      (fun c => trCochain_Z1T ι hι he ho T c c.2))
    (by
      intro c hc
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
      exact trCochain_B1T ι hι he.injective T c hc)

theorem corH1_res [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (κ : LatticeCohomology T.L) :
    corH1 ι hι he ho T (LiftingTheory.resH1 ι hι T κ) = ((ι.range.index : ℕ) : O) • κ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  rw [← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.eq _).2 ?_
  obtain ⟨c, ⟨hcont, hcoc⟩, hT⟩ := c
  refine ⟨∑ q : G' ⧸ ι.range, c q.out,
    Submodule.sum_mem _ fun q _ => hT _ (Set.mem_univ _), ?_⟩
  funext g
  have H := GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range
  have h4 := H.2.2.2 c hcoc g
  have hj : ∀ q : G' ⧸ ι.range, ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out))
      = (g • q).out⁻¹ * g * q.out := fun q => Function.invFun_eq (H.1 g q)
  change T.ρ g (∑ q : G' ⧸ ι.range, c q.out) - ∑ q : G' ⧸ ι.range, c q.out
    = ∑ q : G' ⧸ ι.range, T.ρ (g • q).out
        (c (ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))) - ((ι.range.index : ℕ) : O) • c g
  simp only [hj]
  simp only at h4
  rw [h4, Nat.cast_smul_eq_nsmul]
  abel

theorem corH1_natural [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T₁ T₂ : LocLat G' Qp LL O) (F : LatHom T₁.L T₂.L) (κ : LatticeCohomology (LiftingTheory.resLoc ι hι T₁).L) :
    corH1 ι hι he ho T₂ ((LiftingTheory.resHom ι hι F).H1map κ) = F.H1map (corH1 ι hι he ho T₁ κ) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  funext g
  change ∑ q : G' ⧸ ι.range, T₂.ρ (g • q).out
        (F.f (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
    = F.f (∑ q : G' ⧸ ι.range, T₁.ρ (g • q).out
        (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => (F.equiv _ _).symm

variable {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]

def repVB (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) :
    Representation LL G' (T.V ⊗[Qp] B) where
  toFun g := actVB PD' T.ρ g
  map_one' := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]
  map_mul' g h := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]

theorem actVB_tmul_one (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) (g : G')
    (x : T.V) : actVB PD' T.ρ g (x ⊗ₜ[Qp] (1 : B)) = T.ρ g x ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem actVB_res (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b)
    (T : LocLat G' Qp LL O) (g : G) (x : T.V ⊗[Qp] B) :
    actVB PD (LiftingTheory.resLoc ι hι T).ρ g x = actVB PD' T.ρ (ι g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hact]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem coreCor_of_isOpen [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR)
    (PD' : PeriodData G' Qp K₀' K' B BdR) (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [ι.range.FiniteIndex]
    (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) :
    LiftingTheory.coreCor PD PD' LL O ι hι ι.range.index := by
  haveI : Fintype (G' ⧸ ι.range) := Fintype.ofFinite _
  refine ⟨?_, corH1 ι hι he ho, corH1_res ι hι he ho, ?_, corH1_natural ι hι he ho⟩
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := LiftingTheory.resFun_Z1T ι hι T c c.2
    refine ⟨⟨LiftingTheory.resFun ι T c, hz⟩, ⟨hz, hz.1, x, fun g => ?_⟩, rfl⟩
    rw [actVB_res PD PD' ι hι hact]
    exact hx (ι g)
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := trCochain_Z1T ι hι he ho T c c.2
    have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
    refine ⟨⟨trCochain ι T c, hz⟩,
      ⟨hz, hz.1, ∑ q : G' ⧸ ι.range, actVB PD' T.ρ q.out x, fun g => ?_⟩, rfl⟩
    have h3 := (GlobalTheory.transfer_cocycle_formula LL G' _ (repVB PD' T) ι.range).2.2.1
      (fun g => c.1 (Function.invFun ι g) ⊗ₜ[Qp] (1 : B)) x (by
        rintro _ ⟨a, rfl⟩
        have := hx a
        rw [actVB_res PD PD' ι hι hact] at this
        rw [hj]
        exact this) g
    refine Eq.trans ?_ h3
    change trCochain ι T c g ⊗ₜ[Qp] (1 : B) = _
    rw [trCochain_apply, sum_tmul]
    exact Finset.sum_congr rfl fun q _ => (actVB_tmul_one PD' T _ _).symm

end General

open Formalism.BasicNotions.Loc

theorem GK_index_eq_finrank {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    (GK K).index = Module.finrank ℚ_[l] ↥K.1 :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K.1).symm

theorem inclusion_GK_index {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (hle : GK K ≤ GK K') :
    (Subgroup.inclusion hle).range.index * Module.finrank ℚ_[l] ↥K'.1
      = Module.finrank ℚ_[l] ↥K.1 := by
  rw [Subgroup.inclusion_range, ← GK_index_eq_finrank, ← GK_index_eq_finrank]
  exact Subgroup.relIndex_mul_index hle

end GlobalTheory.InducedSectionsSpanStatement

namespace GlobalTheory

open Formalism.BasicNotions.Loc

theorem res_cor_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    LiftingTheory.adm20 D HW F := by
  intro D HW F l _ K K' _ hle LL
  haveI := K.2
  haveI := K'.2
  have hidx := InducedSectionsSpanStatement.inclusion_GK_index K K' hle
  have hpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  have hpos' : 0 < Module.finrank ℚ_[l] ↥K'.1 := Module.finrank_pos
  have hg : Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1
      = (Subgroup.inclusion hle).range.index := by
    rw [← hidx, Nat.mul_div_cancel _ hpos']
  haveI : (Subgroup.inclusion hle).range.FiniteIndex := ⟨fun h => by
    rw [h, zero_mul] at hidx; omega⟩
  rw [hg]
  refine InducedSectionsSpanStatement.coreCor_of_isOpen _ _ _ _ (Topology.IsEmbedding.inclusion hle) ?_ ?_
  · rw [Subgroup.inclusion_range]
    exact (IntermediateField.fixingSubgroup_isOpen K.1).preimage continuous_subtype_val
  · intro g b
    rw [(D.loc l).PD_actB, (D.loc l).PD_actB]
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubMemMaximalIdealIff
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.TameRed

theorem part_spec {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a M : ℕ, M ≠ 0 ∧ M.Coprime l ∧ Formalism.CyclotomicNorms.primeToPart l x ^ M = 1 ∧
      Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, M, hM0, hcop, ?_, ?_⟩
  · rw [hz, pow_mul, ← pow_mul _ u, mul_comm u, pow_mul, hone, one_pow]
  · rw [hz, ← pow_mul, mul_comm, pow_mul]
    have := pow_eq_pow_of_modEq hmod hone
    rwa [pow_one] at this

theorem eq_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ} (hM : (M : k) ≠ 0)
    {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (h : f x = f y) : x = y := by
  first
  | (rename_i h_2 h_3 h_4; revert O k h_2 h_3 h_4 f M hM x y hx hy h; exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main)
  | exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main ..)

end GlobalTheory.TameRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltComplexPadicIsAlgClosedUnitBallStatement
section
open Formalism.Per GlobalTheory.PSer GroundTheory.PAdicHodge
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_complexPadic_isAlgClosed_unitBall : ∀ (l : ℕ) [Fact l.Prime],
    IsAlgClosed (FractionRing (PreTilt (normInteger ℂ_[l]) l)) ∧
      ∃ ι : Fl l →+* FractionRing (PreTilt (normInteger ℂ_[l]) l),
        (∀ x, tiltSharp ℂ_[l] l (ι x) = sh x) ∧
        (∀ z : FractionRing (PreTilt (normInteger ℂ_[l]) l), ‖z‖ ≤ 1 → ∃ x, ι x = z) :=
  GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOne
section
namespace GlobalTheory.TiltComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

section General

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

theorem coeff_sum_stable (t : Perfection R p) (a : ℕ → Perfection R p) (n M N : ℕ)
    (hM : Perfection.coeff R p n t ^ M = 0) (h : M ≤ N) :
    Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) =
      Perfection.coeff R p n (∑ i ∈ Finset.range M, t ^ i * a i) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih =>
    rw [Finset.sum_range_succ, map_add (f := _), ih, map_mul, map_pow, pow_eq_zero_of_le h hM, zero_mul,
      add_zero]

theorem exists_limit (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) (a : ℕ → Perfection R p) :
    ∃ x : Perfection R p, ∀ n N, M n ≤ N →
      Perfection.coeff R p n x = Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) := by
  refine ⟨⟨fun n => Perfection.coeff R p n (∑ i ∈ Finset.range (M n), t ^ i * a i), fun n => ?_⟩,
    fun n N h => ?_⟩
  · beta_reduce
    rw [← coeff_sum_stable t a (n + 1) _ _ (hM _) (le_max_left (M (n + 1)) (M n)),
      ← coeff_sum_stable t a n _ _ (hM _) (le_max_right (M (n + 1)) (M n)),
      Perfection.coeff_pow_p']
  · rw [Perfection.coeff_mk, coeff_sum_stable t a n _ _ (hM _) h]

theorem separated_complete (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) :
    (∀ x : Perfection R p, (∀ m : ℕ, t ^ m ∣ x) → x = 0) ∧
      ∀ a : ℕ → Perfection R p, ∃ x : Perfection R p, ∀ m : ℕ,
        t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i := by
  refine ⟨fun x hx => Perfection.ext fun n => ?_, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hx (M n)
    rw [map_mul, map_pow, hM, zero_mul, map_zero]
  · obtain ⟨x, hx⟩ := exists_limit t M hM a
    refine ⟨x, fun m => ?_⟩
    obtain ⟨y, hy⟩ := exists_limit t M hM fun i => a (m + i)
    refine ⟨y, Perfection.ext fun n => ?_⟩
    rw [map_sub, map_mul, hx n (m + M n) (Nat.le_add_left _ _), hy n (M n) le_rfl, ← map_mul,
      ← map_sub, Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_assoc]

end General

theorem tilt_separated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), (∀ x : OCb l, (∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x) → x = 0) ∧ ∀ a : ℕ → OCb l, ∃ x : OCb l, ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x - ∑ i ∈ Finset.range m, (AI.εroot s - 1) ^ i * a i := by
  intro l _ P AI s
  refine separated_complete (R := ModP (OC l) l) (p := l) (AI.εroot s - 1 : OCb l)
    (fun n => l ^ (s + n)) fun n => ?_
  change PreTilt.coeff n (AI.εroot s - 1) ^ l ^ (s + n) = 0
  have h := ζ_add_pow AI 0 (s + n)
  rw [zero_add, AI.ζ_zero] at h
  rw [map_sub, map_one, sub_pow_char_pow, coeff_εroot, ← map_pow, h, map_one, one_pow, sub_self]

end GlobalTheory.TiltComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationallyStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xiQuotient_invariants_lift_rationally : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (a e b : ℤ) (j : ℕ) (hle : Gj K j ≤ GK K), s ≤ j → a ≤ e → e ≤ b → IsCrysOn S S.W.GKs T → ∀ p : Qab (AinfSub l) (xiU (D.locA l)) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU (D.locA l)) a e, (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) → letI := zlMod LL T; ∀ z : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a e)), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a e) g z = z) → ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b))), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) g x = x) ∧ LinearMap.lTensor ↥T.L.T p x = (l : ℤ_[l]) ^ k • z := by
  first | exact @GlobalTheory.InvariantLift.invariants_lift | exact GlobalTheory.InvariantLift.invariants_lift | (intros; apply GlobalTheory.InvariantLift.invariants_lift <;> assumption)
end

