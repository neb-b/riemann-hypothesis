module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
section
noncomputable section

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands UpperTheory.Zero.LLC

namespace UpperTheory.One.M

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsQg (k : Type) [Field k] [TopologicalSpace k] : Prop := ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i

theorem good_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩

variable [CharZero k]

theorem good_of_one (x : IrrGL (k := k)) (h : x.1 = 1) : Good x := by
  obtain ⟨χ, hχ, rfl⟩ := ((clBasic k x).2.2.2.2.1 h).2
  exact good_ofChar χ hχ

theorem good_of_fixed (hq : IsQg k) (x : IrrGL (k := k)) (hD : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥) : Good x := by
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport Pr.zel x
  refine ⟨s, hs, fun y hy => Or.inr ⟨hq, y, 1, isSmoothChar_one, ?_, ((clBasic k y).2.2.1 _).symm⟩⟩
  obtain ⟨n, xs, hxs, hcs⟩ := hs
  have H := Pr.dzs _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
    (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hD)
  rw [← hxs] at hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨v, hv, hv0⟩ := H i
  exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩

theorem good_cls_of_fixed (hq : IsQg k) {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (hD : fixed τ.ρ (KOne k (Fin n)) ≠ ⊥) :
    Good (cls τ) :=
  good_of_fixed hq _ (fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hD)

section Close

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E _).injective

theorem New.close (H : LawsM a ha ε rc) : IsRecT h rc := cls_of H

theorem New.artin (hL : RecTExists) (h : IsPlaceOver A w) : ∃ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a :=
  let ⟨_, a, ha, _⟩ := hL E Ω A w h
  ⟨a, ha⟩

end Close

end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC GlobalTheory.Published GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

section Laws

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def GoodI {n : ℕ} (π : Irr k n) : Prop := Good (cls (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k)))

structure RecLawsH (rc : ∀ n, Irr k n → WD h) : Prop where
  dim : ∀ n π, (rc n π).lpDim = n
  iso : ∀ n (π π' : Irr k n), GoodI π' → (rc n π = rc n π' ↔ Nonempty (π.π.Equiv π'.π))
  isoMp : ∀ n (π π' : Irr k n), Nonempty (π.π.Equiv π'.π) → rc n π = rc n π'
  prod : ∀ r t (σ : Irr k r) (τ : Irr k t) (π : Irr k (r + t)),
    Nonempty (π.π.Equiv (prod₂ σ.π τ.π)) → rc (r + t) π = (rc r σ).lpSum (rc t τ)
  det : ∀ t (χ : kˣ →* ℂˣ) (c : Irr k 1) (τ : Irr k t),
    Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → Nonempty (τ.π.Equiv (detRep (Fin t) χ)) → rc t τ = speh (rc 1 c) t
  twist : ∀ n (χ : kˣ →* ℂˣ) (c : Irr k 1) (π π' : Irr k n),
    GoodI π → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (π'.π.Equiv (twist π.π (detChar (Fin n) χ))) → rc n π' = (rc n π).lpChar (rc 1 c)
  sph : ∀ n (π : Irr k n), (rc n π).unr ↔ IsSpherical π.π
  sat : ∀ n (π : Irr k n) (α : Fin n → ℂˣ), HasSatake π.π α →
    (rc n π).frobEig = Finset.univ.val.map fun i => ((α i)⁻¹ : ℂˣ).1

theorem Old.rlTwist {rc : ∀ n, Irr k n → WD h} (H : RecLaws rc) : ∀ n (χ : kˣ →* ℂˣ) (c : Irr k 1) (π π' : Irr k n),
    GoodI π → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (π'.π.Equiv (GlobalTheory.SmGL.twist π.π (detChar (Fin n) χ))) → rc n π' = (rc n π).lpChar (rc 1 c) :=
  fun n χ c π π' _ => H.twist n χ c π π'

end Laws

end UpperTheory.One.M
end
end

