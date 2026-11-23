module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirst
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0116

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ProdFiniteLength

open GlobalTheory.SmGL

theorem piTensor_mulSingle_eq_map {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (a : α)
    (g : Γ a) :
    piTensor ρ (Pi.mulSingle a g) =
      PiTensorProduct.map (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) a (ρ a g)) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem exists_mem_adjoin_eq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible)
    (hS : ∀ φ : V →ₗ[ℂ] V, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id)
    (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ T ∈ Algebra.adjoin ℂ (Set.range π), ∀ x ∈ s, T x = f x := by
  classical
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range π)
  have hmem : ∀ g, π g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  haveI : IsSimpleOrder (Subrepresentation π) := hirr
  haveI : IsSimpleModule A V := by
    rw [isSimpleModule_iff]
    refine { exists_pair_ne := ?_, eq_bot_or_eq_top := fun U => ?_ }
    · obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by
        by_contra h
        push_neg at h
        apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
        ext v
        simp [h v]
      refine ⟨⊥, ⊤, fun h => hx ?_⟩
      have : x ∈ (⊤ : Submodule A V) := trivial
      rw [← h] at this
      exact (Submodule.mem_bot A).1 this
    · let W : Subrepresentation π :=
        { toSubmodule := U.restrictScalars ℂ
          apply_mem_toSubmodule := fun g v hv => U.smul_mem (⟨π g, hmem g⟩ : A) hv }
      rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
      · left
        ext v
        constructor
        · intro hv
          have : v ∈ W.toSubmodule := hv
          rw [h] at this
          exact (Submodule.mem_bot A).2 this
        · intro hv
          rw [(Submodule.mem_bot A).1 hv]
          exact U.zero_mem
      · right
        refine eq_top_iff.2 fun v _ => ?_
        have : v ∈ (⊤ : Subrepresentation π).toSubmodule := trivial
        rw [← h] at this
        exact this
  have hscal : ∀ φ : Module.End A V, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := hS (φ.restrictScalars ℂ) fun g x => φ.map_smul (⟨π g, hmem g⟩ : A) x
    exact ⟨c, fun m => by simpa using LinearMap.congr_fun hc m⟩
  let F : Module.End (Module.End A V) V :=
    { toFun := fun m => f m
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun x hx => (hr x hx).symm⟩

theorem piTensor_isIrreducible_of_schur {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hirr : ∀ a, (ρ a).IsIrreducible)
    (hS : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id) :
    (piTensor ρ).IsIrreducible := by
  classical
  cases nonempty_fintype α
  have hnt : ∀ a, Nontrivial (X a) := fun a => by
    haveI : IsSimpleOrder (Subrepresentation (ρ a)) := hirr a
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
    ext v
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim v 0⟩
  haveI : ∀ a, Nontrivial (X a) := hnt
  haveI : Nontrivial (PiTensorProduct ℂ fun a => X a) := GlobalTheory.ProdSupport.nontrivial_piTensor X hnt
  have hcomp : ∀ (f g : ∀ a, X a →ₗ[ℂ] X a) (x : PiTensorProduct ℂ fun a => X a),
      PiTensorProduct.map (fun a => f a ∘ₗ g a) x =
        PiTensorProduct.map f (PiTensorProduct.map g x) := by
    intro f g x
    rw [PiTensorProduct.map_comp]; rfl
  show IsSimpleOrder (Subrepresentation (piTensor ρ))
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · obtain ⟨x, hx⟩ := exists_ne (0 : PiTensorProduct ℂ fun a => X a)
    have : x ∈ (⊤ : Subrepresentation (piTensor ρ)).toSubmodule := trivial
    rw [← h] at this
    exact hx this
  by_cases hU : ∀ x ∈ U.toSubmodule, x = 0
  · left
    ext v
    refine ⟨hU v, fun h => ?_⟩
    rw [show v = 0 from h]
    exact U.toSubmodule.zero_mem
  push_neg at hU
  obtain ⟨x, hxU, hx0⟩ := hU
  right
  let Asub : ∀ a, Subalgebra ℂ (Module.End ℂ (X a)) := fun i =>
    { carrier := {T | ∀ x ∈ U.toSubmodule,
        PiTensorProduct.map (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) i T) x ∈ U.toSubmodule}
      mul_mem' := fun {a b} ha hb x hx => by
        have := ha _ (hb x hx)
        rw [← hcomp] at this
        convert this using 3
        funext ρ
        by_cases hρ : ρ = i
        · subst hρ; simp [Module.End.mul_eq_comp]
        · simp [Function.update_of_ne hρ]
      add_mem' := fun {a b} ha hb x hx => by
        rw [PiTensorProduct.map_update_add]
        exact U.toSubmodule.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul]
        have : Function.update (fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)) i (1 : Module.End ℂ (X i)) =
            fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ) := Function.update_eq_self i _
        rw [this, PiTensorProduct.map_id]
        exact U.toSubmodule.smul_mem c hx }
  have hA : ∀ a, Algebra.adjoin ℂ (Set.range (ρ a)) ≤ Asub a := fun a =>
    Algebra.adjoin_le (by
      rintro _ ⟨g, rfl⟩ y hy
      rw [← piTensor_mulSingle_eq_map]
      exact U.apply_mem_toSubmodule _ hy)
  have h3 : ∀ T : ∀ a, Module.End ℂ (X a), (∀ a, T a ∈ Asub a) →
      ∀ y ∈ U.toSubmodule, PiTensorProduct.map T y ∈ U.toSubmodule := by
    intro T hT
    have h2 : ∀ s : Finset α, ∀ y ∈ U.toSubmodule,
        PiTensorProduct.map (fun a => if a ∈ s then T a else LinearMap.id) y ∈ U.toSubmodule := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro y hy; simpa using hy
      | insert j s hj ih =>
        intro y hy
        have := hT j _ (ih y hy)
        rw [← hcomp] at this
        convert this using 3
        funext b
        by_cases hb : b = j
        · subst hb; simp [hj]
        · simp [hb]
    intro y hy
    simpa using h2 Finset.univ y hy
  have htop : U.toSubmodule = ⊤ := by
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    let b := fun a => Module.Free.chooseBasis ℂ (X a)
    let B := Basis.piTensorProduct b
    obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
    let f : ∀ a, Module.End ℂ (X a) := fun a => ((b a).coord (p a)).smulRight (v a)
    have hT : ∀ a, ∃ T ∈ Asub a, ∀ y ∈ (B.repr x).support.image (fun q => b a (q a)), T y = f a y :=
      fun a => by
        obtain ⟨T, hT1, hT2⟩ := exists_mem_adjoin_eq (ρ a) (hirr a) (hS a) (f a)
          ((B.repr x).support.image (fun q => b a (q a)))
        exact ⟨T, hA a hT1, hT2⟩
    choose T hTA hTf using hT
    have e : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext w
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
        Module.Basis.coord_apply, B, f, Basis.piTensorProduct_repr_tprod_apply]
      exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
    have hmap : PiTensorProduct.map T x = PiTensorProduct.map f x := by
      rw [← B.linearCombination_repr x, Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr fun q hq => ?_
      rw [map_smul, map_smul, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod]
      congr 2
      funext a
      exact hTf a _ (Finset.mem_image_of_mem _ hq)
    have h4 := h3 T hTA x hxU
    rw [hmap, e] at h4
    exact (U.toSubmodule.smul_mem_iff hp).1 h4
  ext y
  exact ⟨fun _ => trivial, fun _ => by rw [htop]; trivial⟩

theorem multiProd_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ)
    (σ : ∀ a, Irr k (d a)) (e : (Σ a, Fin (d a)) ≃ Fin n),
    HasFiniteLength (multiProd e fun a => (σ a).π) := by
  intro hBZ k _ _ _ _ s n d σ e
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    piTensor_isIrreducible_of_schur (fun a => (σ a).π) (fun a => (σ a).irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible (GL (Fin (d a)) k) (KO k (Fin (d a))) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (σ a).V (σ a).π (σ a).irr
        (hAdm (Fin (d a)) (σ a).V (σ a).π (σ a).smooth (σ a).irr) φ hφ
  exact hInd (Fin s) (Fin n) (fun a => Fin (d a)) e _ _ (isSmooth_piTensor fun a => (σ a).smooth)
    (hasFiniteLength_of_isIrreducible hirr)

end GlobalTheory.ProdFiniteLength
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAdd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DirectSumLocal

open Module

noncomputable def splitEquiv (k : Type) [Field k] (a b : ℕ) : (Fin (a + b) → k) ≃ₗ[k] (Fin a → k) × (Fin b → k) :=
  (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) k k)

theorem splitEquiv_sumRep {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r₁ : Γ →* GL (Fin a) k)
    (r₂ : Γ →* GL (Fin b) k) (g : Γ) (v : Fin (a + b) → k) :
    splitEquiv k a b ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : Matrix _ _ k).mulVec v) =
      (((r₁ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).1, ((r₂ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).2) := by
  ext i
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl

end GlobalTheory.DirectSumLocal

namespace GlobalTheory.DirectSumLocal

theorem isdRE_sumRep_and_multE_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ) (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1), (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧ ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ), Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw LL' a b r₁ r₂
  obtain ⟨T⟩ := hT
  have he : ∀ g v, splitEquiv (↥LL'.1) a b (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) g v) =
      (Bw.repE LL' r₁ g (splitEquiv (↥LL'.1) a b v).1, Bw.repE LL' r₂ g (splitEquiv (↥LL'.1) a b v).2) := by
    intro g v
    exact splitEquiv_sumRep r₁ r₂ _ v
  obtain ⟨h1, -, h3⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T Bw.Kw LL' (Fin (a + b) → ↥LL'.1)
    (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂)) (Fin a → ↥LL'.1) (Bw.repE LL' r₁) (Fin b → ↥LL'.1)
    (Bw.repE LL' r₂) (splitEquiv (↥LL'.1) a b) he
  refine ⟨?_, fun τ' c => h3 τ' c⟩
  unfold Formalism.BasicNotions.LocBridge.IsdRE
  unfold Formalism.MainNotions.N.IsDR at h1
  simpa only [Module.finrank_fin_fun] using h1

end GlobalTheory.DirectSumLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_eq_on_units {ψ θ : kˣ →* ℂˣ} (hθ : IsSmoothChar θ)
    (h : ∀ u : kˣ, valuation k (u : k) = 1 → ψ u = θ u) : IsSmoothChar ψ := by
  have h1 : IsUnram (ψ * θ⁻¹) := fun u hu => by simp [h u hu]
  have h2 : ψ = (ψ * θ⁻¹) * θ := by ext u; simp
  rw [h2]
  exact (isSmoothChar_of_isUnram h1).mul hθ

theorem exists_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {n : ℕ} (π : Irr k n) {v : π.V} {θ : Fin n → kˣ →* ℂˣ}
    (hθ : ∀ i, IsSmoothChar (θ i)) (hv : v ≠ 0) (h : IsIwVec θ π.π v) :
    ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u) ∧
      (∀ i, InSupport π.π (ψ i)) ∧ IsSubquotient π.π (prinSeries ψ) := by
  have hl : HasFiniteLength (jacB π.π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π.π π.smooth (hasFiniteLength_of_isIrreducible π.irr))
  obtain ⟨ψ, l, hl0, hψ, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π.π) (Submodule.Quotient.mk v) θ
    (isSmooth_jacB π.smooth) hl hθ (GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero hD k n π v θ hv h) fun t ht => by
      rw [UnramFixed.jacB_apply, jacBU_mk, h.2 t ht]
      have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
        UnramFixed.deltaHalf_torusO k ht
      rw [this]
      simp
  exact ⟨ψ, hu, _root_.GlobalTheory.EigenSupport.inSupport_of_torus_eigenform k n _ π.π ψ l hl0 hψ,
    SatakeExists.isSubquotient_of_eigenform π.smooth π.irr _ l hl0 hψ⟩

theorem hasFiniteLength_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) : HasFiniteLength (prinSeries ψ) := by
  have hs : IsSmoothChar (torusChar ψ) := by
    unfold torusChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one fun a _ => ?_
    exact (hψ a).comp _ (continuous_apply a)
  refine (hBZ k).2.2.1 _ _ _ (points (Fin n)) _ _ ?_ ?_
  · refine isSmooth_comp ((isSmooth_ofChar_iff _).2 hs) _ (continuous_pi fun i => ?_)
    exact continuous_glDet.comp (continuous_apply i)
  · exact (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).symm.surjective).2
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _))

theorem exists_model (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (A : Representation ℂ (GL (Fin n) k) V),
      Nonempty (A.Equiv (prinSeries ψ)) ∧ IsSmooth A ∧ HasFiniteLength A :=
  ⟨_, _, _, prinSeries ψ, ⟨.refl _⟩, isSmooth_parInd _ _, hasFiniteLength_prinSeries hBZ hψ⟩

theorem isCuspSupport_of_prinSeries {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) :
    IsCuspSupport σ.π (fun _ : Fin n => 1) fun a => (Irr.ofDet 1 (ψ a) (hψ a)).π :=
  ⟨σ.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hψ a)⟩, _,
    h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)⟩

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) {μ : kˣ →* ℂˣ}
    (hμ : InSupport σ.π μ) : ∃ i, μ = ψ i := by
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ _ _ μ (isSmooth_parInd _ _)
    (h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)) hμ
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k _ _ _ _ _ _ μ
    (fun a => (Irr.ofDet 1 (ψ a) (hψ a)).smooth) (fun a => isIrreducible_ofChar _) h1
  exact ⟨a, (Model.inSupport_one_iff _ _).1 ha⟩

def twistIrr {n : ℕ} (σ : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := σ.V
  π := twist σ.π (detChar (Fin n) χ)
  smooth := isSmooth_twist σ.smooth hχ.detChar
  irr := by
    have φ : Subrepresentation (twist σ.π (detChar (Fin n) χ)) ≃o Subrepresentation σ.π :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have := S.toSubmodule.smul_mem (((detChar (Fin n) χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at this⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
          S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact φ.isSimpleOrder_iff.2 σ.irr

theorem tameSplit : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  intro hBZ hG hU hD k _ _ _ _ r t χ π v hχ htame hram hv hpar
  let θ : Fin (r + t) → kˣ →* ℂˣ := Fin.append (fun _ : Fin r => 1) fun _ : Fin t => χ
  have hθ : ∀ i, IsSmoothChar (θ i) := fun i => by
    induction i using Fin.addCases with
    | left i => simpa [θ] using isSmoothChar_one
    | right i => simpa [θ] using hχ
  obtain ⟨ψ, hψθ, -, hsub⟩ := exists_prinSeries hBZ hD π hθ hv (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ π.π v htame hpar)
  have hψ : ∀ i, IsSmoothChar (ψ i) := fun i => isSmoothChar_of_eq_on_units (hθ i) (hψθ i)
  let ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i)
  let ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i)
  have hψ₁ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₁ i u = 1 := fun i u hu => by
    simpa [θ] using hψθ (Fin.castAdd t i) u hu
  have hψ₂ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₂ i u = χ u := fun i u hu => by
    simpa [θ] using hψθ (Fin.natAdd r i) u hu
  have happ : Fin.append ψ₁ ψ₂ = ψ := Fin.append_castAdd_natAdd
  rw [← happ] at hsub
  obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ : ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π (prinSeries ψ₁) ∧
      IsSubquotient σ₂.π (prinSeries ψ₂) ∧ IsSubquotient π.π (prod₂ σ₁.π σ₂.π) := by
    obtain ⟨V, _, _, A, ⟨φA⟩, sA, lA⟩ := exists_model hBZ (ψ := ψ₁) fun i => hψ _
    obtain ⟨W, _, _, B, ⟨φB⟩, sB, lB⟩ := exists_model hBZ (ψ := ψ₂) fun i => hψ _
    obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ := _root_.GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ k r t _ _ _ π.π A B π.irr sA sB lA lB
      (hsub.trans (_root_.GlobalTheory.SmGL.PrinProd.prinSeries_append k r t ψ₁ ψ₂ V W A B ⟨φA⟩ ⟨φB⟩))
    exact ⟨σ₁, σ₂, h₁.trans (.of_injective φA.toIntertwiningMap φA.injective),
      h₂.trans (.of_injective φB.toIntertwiningMap φB.injective), hπ⟩
  have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
    refine hU k r t r t σ₁ σ₂ _ _ _ _ (isCuspSupport_of_prinSeries σ₁ (fun i => hψ _) h₁)
      (isCuspSupport_of_prinSeries σ₂ (fun i => hψ _) h₂) ?_
    rintro a b h α ⟨φ⟩
    refine hram fun u hu => ?_
    let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar (Fin 1) u
    have hg : Matrix.GeneralLinearGroup.det g = u := ProdSupport.det_scalar_one rfl u
    obtain ⟨c, hc⟩ : ∃ c : ℂ, φ (1 : ℂ) = c := ⟨_, rfl⟩
    have h0 : c ≠ 0 := fun h => one_ne_zero (α := ℂ) (φ.injective ((hc.trans h).trans (map_zero φ).symm))
    have h1 : φ (detRep (Fin 1) (ψ₁ a) g (1 : ℂ)) = (detChar (Fin 1) (unrChar k α) g : ℂ) •
        detRep (Fin 1) (ψ₂ b) g c := hc ▸ φ.toIntertwiningMap.isIntertwining _ _ g (1 : ℂ)
    simp only [detRep, ofChar_apply, detChar_apply, hg, hψ₁ a u hu, hψ₂ b u hu, isUnram_unrChar k α u hu,
      Units.val_one, one_mul, one_smul] at h1
    exact Units.ext ((mul_eq_right₀ h0).1 (h1.symm.trans hc))
  obtain ⟨φ⟩ := hπ.nonempty_equiv π.irr hirr
  let f := φ.symm v
  have hf0 : f ≠ 0 := fun h => hv (φ.symm.injective (h.trans (map_zero φ.symm).symm))
  have hf : IsParahoricVec χ (prod₂ σ₁.π σ₂.π) f := fun h hh hl u hu => by
    have := φ.symm.toIntertwiningMap.isIntertwining _ _ h v
    rw [hpar h hh hl u hu, map_smul] at this
    exact this.symm
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.ParahoricPerm.exists_perm_ne_zero k r t χ _ _ σ₁.π σ₂.π f hf0 hf
  obtain ⟨s, y, hy0, hy⟩ := _root_.GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst k r t θ _ _ σ₁.π σ₂.π f w (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ _ f htame hf) hw
  obtain ⟨μ, hμ, hμs, -⟩ := exists_prinSeries hBZ hD σ₁ (fun i => hθ _) hy0 hy
  have hwP : GlobalTheory.Parabolic.permGL k w ∈ parab k (two (stdSum (rfl : r + t = r + t))) := by
    have key : ∀ (i : Fin r) (j : Fin t), Fin.castAdd t i ≠ w (Fin.natAdd r j) := fun i j hij => by
      obtain ⟨i, rfl⟩ := s.surjective i
      obtain ⟨a, ha⟩ := exists_eq_of_inSupport hG σ₁ (fun i => hψ _) h₁ (hμs i)
      refine hram fun u hu => ?_
      have h1 := hμ i u hu
      rw [ha, hij, Equiv.symm_apply_apply] at h1
      simpa [θ] using h1.symm.trans (hψ₁ a u hu)
    refine (mem_parab_two k).2 fun j i => (GlobalTheory.Parabolic.permGL_apply w _ _).trans (if_neg fun hji => ?_)
    have hF : ∀ b, ∃ c, w (Fin.natAdd r b) = Fin.natAdd r c := fun b => by
      generalize hx : w (Fin.natAdd r b) = x
      induction x using Fin.addCases with
      | left a => exact absurd hx.symm (key a b)
      | right c => exact ⟨c, rfl⟩
    choose c hc using hF
    have hinj : Function.Injective c := fun b b' h =>
      Fin.natAdd_injective _ _ (w.injective (by rw [hc, hc, h]))
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj j
    have h2 : w (Fin.natAdd r b) = w (Fin.castAdd t i) := by rw [hc, hb]; exact hji
    have h3 := congrArg Fin.val (w.injective h2)
    have := i.2
    simp at h3
    omega
  have hf1 : f.1.1 1 ≠ 0 := fun h => hw (by
    have := f.1.2 ⟨_, hwP⟩ 1
    rw [mul_one, h, map_zero] at this
    exact this)
  obtain ⟨s₁, s₂⟩ := _root_.GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec k r t χ _ _ σ₁.π σ₂.π f hf hf1
  refine ⟨σ₁, twistIrr σ₂ χ⁻¹ hχ.inv, s₁, s₂, ?_⟩
  have e : twist (twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ) = σ₂.π := by
    ext g x
    simp [smul_smul]
  show Nonempty (π.π.Equiv (prod₂ σ₁.π (twist (twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
  rw [e]
  exact ⟨φ.symm⟩

end GlobalTheory.TameIwahori
end
end

