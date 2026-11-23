module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.EdgeGeo
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

private lemma conj_toAdd {Γ : Type} [Group Γ] {m : ℕ} (x : Γ →* Multiplicative (ZMod m)) (s h : Γ) :
    (x (s * h * s⁻¹)).toAdd = (x h).toAdd := by
  have e : x (s * h * s⁻¹) = x h := by
    rw [map_mul, map_mul, map_inv, mul_comm (x s) (x h), mul_inv_cancel_right]
  rw [e]

private lemma mul_toAdd {Γ : Type} [Group Γ] {m : ℕ} (x : Γ →* Multiplicative (ZMod m)) (g h : Γ) :
    (x (g * h)).toAdd = (x g).toAdd + (x h).toAdd := by
  rw [map_mul, toAdd_mul]

theorem UpperTheory.V.Z.Kato.Sym.PT.edgeGeo :
    UpperTheory.V.Z.Kato.Sym.PT.EdgeGeo := by
  intro Γ _ m Δ x y η hc
  refine ⟨fun g hg h hh => ?_, fun σ hσ g hg h hh => ?_⟩
  · have ha : g * h * g⁻¹ ∈ Δ := Δ.mul_mem (Δ.mul_mem hg hh) (Δ.inv_mem hg)
    have e : g * h * g⁻¹ * g = g * h := by group
    have h1 := hc _ ha g hg
    have h2 := hc g hg h hh
    rw [e, conj_toAdd x] at h1
    simp only [GlobalTheory.KEdge.edge]
    linear_combination h2 - h1
  · have hg' := hσ g hg
    have hh' := hσ h hh
    have e : σ * (g * h) * σ⁻¹ = (σ * g * σ⁻¹) * (σ * h * σ⁻¹) := by group
    have h1 := hc _ hg' _ hh'
    have h2 := hc g hg h hh
    rw [conj_toAdd x, conj_toAdd y] at h1
    simp only [GlobalTheory.KEdge.edge, e, mul_toAdd x, mul_toAdd y]
    linear_combination h1 - h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.FixInv
section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

attribute [local instance] algMdl

private theorem e_model (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (f : topF X M) :
    e (algebraMap (topF X M) (topBar X M) f) = io X f := by
  rw [IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M) f]
  exact he _

private theorem cj_spec (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (σ : RingAut (Kb X))
    (hσ : FixF X M σ) (z : topBar X M) : e (cj X M e σ z) = σ (e z) := by
  have hex : ∃ g : topGal X M, ∀ z, e (g z) = σ (e z) := by
    refine ⟨AlgEquiv.ofRingEquiv (f := e.trans (σ.trans e.symm)) ?_, ?_⟩
    · intro f
      simp only [RingEquiv.trans_apply]
      rw [e_model X M e he f, hσ f f.2, ← e_model X M e he f, RingEquiv.symm_apply_apply]
    · intro w
      simp [AlgEquiv.ofRingEquiv_apply]
  exact Classical.epsilon_spec (p := fun g : topGal X M => ∀ w, e (g w) = σ (e w)) hex z

private theorem fix_mul (X : Tower Ω ε) (M : ℕ) {σ τ : RingAut (Kb X)} (hσ : FixF X M σ) (hτ : FixF X M τ) :
    FixF X M (σ * τ) := fun f hf => by
  show σ (τ (io X f)) = io X f
  rw [hτ f hf, hσ f hf]

private theorem fix_inv (X : Tower Ω ε) (M : ℕ) {σ : RingAut (Kb X)} (hσ : FixF X M σ) : FixF X M σ⁻¹ := fun f hf => by
  show σ.symm (io X f) = io X f
  rw [RingEquiv.symm_apply_eq]
  exact (hσ f hf).symm

private theorem cj_mul (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) {σ τ : RingAut (Kb X)}
    (hσ : FixF X M σ) (hτ : FixF X M τ) : cj X M e (σ * τ) = cj X M e σ * cj X M e τ := by
  ext z
  apply e.injective
  rw [cj_spec X M e he _ (fix_mul X M hσ hτ), AlgEquiv.mul_apply, cj_spec X M e he _ hσ, cj_spec X M e he _ hτ]
  rfl

private theorem cj_one (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) :
    cj X M e 1 = 1 := by
  ext z
  apply e.injective
  rw [cj_spec X M e he _ (fun f _ => rfl)]
  rfl

private theorem cj_inv (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) {σ : RingAut (Kb X)}
    (hσ : FixF X M σ) : cj X M e σ⁻¹ = (cj X M e σ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← cj_mul X M e he (fix_inv X M hσ) hσ, inv_mul_cancel, cj_one X M e he]

private theorem e_zeta (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (l n : ℕ) :
    e (topZeta X M l n) = zt X (l ^ n) := by
  unfold topZeta zt
  rw [he]
  push_cast
  rfl

theorem cjB : CjB := by
  intro Ω _ _ _ ε X M e he
  refine ⟨fun σ hσ z => cj_spec X M e he σ hσ z, fun σ τ hσ hτ =>
    ⟨fix_mul X M hσ hτ, fix_inv X M hσ, cj_mul X M e he hσ hτ, cj_inv X M e he hσ⟩, fun σ hσ => ?_,
    fun l n => e_zeta X M e he l n, ?_⟩
  · have hF : FixF X M σ := fun f hf => hσ f (mdl_le_lev X _ _ hf)
    have key : ∀ f : topL X M, cj X M e σ (algebraMap (topL X M) (topBar X M) f) = algebraMap (topL X M) (topBar X M) f := by
      intro f
      apply e.injective
      rw [cj_spec X M e he σ hF, he]
      exact hσ _ f.2
    refine ⟨hF, ?_⟩
    rintro ⟨_, f, rfl⟩
    exact key f
  · intro l n hl σ _ a b hb i hab
    have hm : 0 < l ^ n := pow_pos (Nat.pos_of_ne_zero hl) n
    refine (lgB Ω ε X (l ^ n) hm).2.2.1 (e a) (e b) i (by simpa using hb) ?_
    rw [hab, map_mul, map_pow, e_zeta X M e he l n]

end UpperTheory.V.Z.Kato.Sym.PT

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.IsIntegralOfMemOverY
section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem isIntegral_of_mem_overY (X : Tower Ω ε) (x : X.K) (h : ∀ W, X.OverY W → x ∈ W) :
    IsIntegral (Algebra.adjoin Ω {X.jK}) x := by
  by_contra hx
  obtain ⟨V, hRV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (K := X.K) (x := x) (R := (integralClosure (Algebra.adjoin Ω {X.jK}) X.K).toSubring)
    (fun hm => hx hm)
  apply hxV
  refine h V ⟨fun c => hRV ?_, hRV ?_⟩
  · change algebraMap Ω X.K c ∈ integralClosure (Algebra.adjoin Ω {X.jK}) X.K
    have : algebraMap Ω X.K c = algebraMap (Algebra.adjoin Ω {X.jK}) X.K (algebraMap Ω _ c) := rfl
    rw [this]
    exact isIntegral_algebraMap
  · change X.jK ∈ integralClosure (Algebra.adjoin Ω {X.jK}) X.K
    have : X.jK = algebraMap (Algebra.adjoin Ω {X.jK}) X.K ⟨X.jK, Algebra.subset_adjoin rfl⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap

theorem intU : IntU := by
  intro Ω _ _ _ ε X M u hu
  refine ⟨isIntegral_of_mem_overY X u fun W hW => ?_, isIntegral_of_mem_overY X u⁻¹ fun W hW => ?_⟩
  · exact (ValuationSubring.valuation_le_one_iff W u).1 (hu.2 W hW).le
  · refine (ValuationSubring.valuation_le_one_iff W u⁻¹).1 ?_
    rw [map_inv₀, hu.2 W hW, inv_one]

end UpperTheory.V.Z.Kato.Sym.PT

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.IsoEx
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

theorem UpperTheory.V.Z.Kato.Sym.PT.isoEx :
    UpperTheory.V.Z.Kato.Sym.PT.IsoEx := by
  intro Ω _ _ _ ε X M
  let L := topL X M
  let L' : IntermediateField Ω X.K :=
    { L with algebraMap_mem' := fun c => algebraMap_mem_lev X _ c }
  let F : IntermediateField Ω X.K := IntermediateField.adjoin Ω {X.jK}
  have hFL : F ≤ L' :=
    IntermediateField.adjoin_simple_le_iff.mpr (jK_mem_lev X _)
  have hle : F.toSubfield ≤ L := fun x hx => hFL hx
  letI : Algebra F L := (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower F L X.K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic L X.K :=
    ⟨fun f => (X.alg_j f).tower_top L⟩
  haveI : IsAlgClosure L (Kb X) := IsAlgClosure.ofAlgebraic L X.K (Kb X)
  let e : topBar X M ≃ₐ[L] Kb X := IsAlgClosure.equiv L (topBar X M) (Kb X)
  refine ⟨e.toRingEquiv, fun f => ?_⟩
  change e (algebraMap L (topBar X M) f) = algebraMap X.K (Kb X) (f : X.K)
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply L X.K (Kb X) f
end

