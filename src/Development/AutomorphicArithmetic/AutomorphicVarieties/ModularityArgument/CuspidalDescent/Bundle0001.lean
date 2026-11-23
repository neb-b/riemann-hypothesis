module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescUse
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Desc

def RegWt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) : Prop :=
  ∀ v : InfinitePlace E, ∃ (φ : E →+* ℂ) (lam : DomWeight n), InfinitePlace.mk φ = v ∧ StrictAnti lam.w ∧ π.HasInfChar φ (infOfWeight lam)

def DescUse : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → RegWt π → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU σ w) ∧
        ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
          ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
            IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ GlobalTheory.LFun.HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

end UpperTheory.V.Z.Desc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.IrrComp
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.LocGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem irreducible_component_of_speh {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} (U : Submodule ℂ (UA E n → ℂ))
    (hn : ∑ _i : Fin 1, m = n) (P : CuspSub E n) (w : HeightOneSpectrum (𝓞 E))
    (ρ : SmIrr (GL (Fin n) (w.adicCompletion E))) (σ : SmIrr (GL (Fin m) (w.adicCompletion E)))
    (hρ : P.IsLocComp w ρ) (hs : IsSpeh (cl ρ) 1 σ.ρ)
    (hc : IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => m) hn w fun _ => σ))
    (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hτ : P.IsLocComp w τ) :
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain rfl : m = n := by simpa using hn
  obtain ⟨φ₀⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one σ.smooth
    (GlobalTheory.SmGL.stdBlocks (fun _ : Fin 1 => m) hn)
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val]; obtain rfl := Subsingleton.elim a 0; simp))
  obtain ⟨hd, h1⟩ := hs
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (cl ρ)
  obtain ⟨e⟩ := h1.unique h2
  obtain ⟨u⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w τ ρ hτ hρ
  let q : τ.ρ.Equiv (locProd (N := fun _ : Fin 1 => m) hn w fun _ => σ) :=
    (u.trans ((IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e)).trans φ₀
  obtain ⟨-, f, f0, fm, fe⟩ := hc
  refine ⟨τ.irred, f ∘ₗ q.toLinearMap, fun h0 => f0 (LinearMap.ext fun v => ?_), fun v => fm _, fun x v => ?_⟩
  · obtain ⟨u', rfl⟩ := q.toLinearEquiv.surjective v
    exact LinearMap.congr_fun h0 u'
  · exact (congrArg f (LinearMap.congr_fun (q.isIntertwining' _) v)).trans (fe x _)

theorem UpperTheory.V.Z.Desc.irrComp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)) (hn : ∑ _i : Fin 1, 1 * n = n) (P : CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin n) (w.adicCompletion E))) (σ : SmIrr (GL (Fin (1 * n)) (w.adicCompletion E))),
    P.IsLocComp w ρ → IsSpeh (cl ρ) 1 σ.ρ →
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hn w fun _ => σ) →
    ∀ τ, P.IsLocComp w τ → IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  intro E _ _ _ n U hn P w ρ σ hρ hs hc τ hτ
  exact irreducible_component_of_speh U hn P w ρ σ hρ hs hc τ hτ
end

