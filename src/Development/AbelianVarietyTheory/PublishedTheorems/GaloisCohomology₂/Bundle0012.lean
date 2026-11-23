module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExhUnipRadOne
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine ValuativeRel

noncomputable section
namespace GlobalTheory.LocGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exh_unipRad_one {s : ℕ} {d : Fin s → ℕ} (e : (Σ a : Fin s, Fin (d a)) ≃ Fin 1) : unipRad k e = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  have h := det_eq_one_of_mem_unipRad k hu
  have h2 : (u : Matrix (Fin 1) (Fin 1) k).det = 1 := by
    simpa using congrArg Units.val h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h2

theorem exh_deg_one (c : IrrCl (GL (Fin 1) k)) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (IrrGL.rep ⟨1, c⟩) := by
  have hc : IrrGL.IsCusp (⟨1, c⟩ : IrrGL (k := k)) := ⟨one_pos, c.rep.smooth, fun s d e he => absurd (exh_unipRad_one e) he⟩
  exact ⟨_, (single_spec hc).2.2.2⟩

theorem exh_equiv_zero {m : Fin 0 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin 0)
    {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Levi k m) W)
    (E : W ≃ₗ[ℂ] ℂ) (π : Representation ℂ (GL (Fin 0) k) V) (hirr : π.IsIrreducible) :
    Nonempty ((parInd e ρ).Equiv π) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  have hspan : ∀ w : V, ∃ a : ℂ, a • v = w := fun w => by
    have : w ∈ S := by rw [hS]; trivial
    exact Submodule.mem_span_singleton.1 this
  let f : (parInd e ρ).IntertwiningMap π :=
    { toFun := fun φ => E (φ.1.1 1) • v
      map_add' := fun φ ψ => by
        show E (φ.1.1 1 + ψ.1.1 1) • v = _
        rw [map_add (f := _), add_smul]
      map_smul' := fun a φ => by
        show E (a • φ.1.1 1) • v = a • (E (φ.1.1 1) • v)
        rw [map_smul, smul_eq_mul, mul_smul]
      isIntertwining' := fun g => by rw [hg g, map_one, map_one]; rfl }
  have hinj : Function.Injective f := fun φ ψ h => by
    have h1 : E (φ.1.1 1) • v = E (ψ.1.1 1) • v := h
    have h2 := E.injective (smul_left_injective ℂ hv h1)
    exact Subtype.ext (Subtype.ext (funext fun g => by rw [hg g]; exact h2))
  have hsurj : Function.Surjective f := fun w => by
    obtain ⟨a, rfl⟩ := hspan w
    refine ⟨⟨⟨fun _ => E.symm a, fun p g => ?_⟩, ?_⟩, ?_⟩
    · have : p = 1 := Subtype.ext (hg _)
      subst this; simp
    · exact mem_smoothPart_of_nhds (Filter.univ_mem' fun g => by rw [hg g]; simp)
    · show E (E.symm a) • v = a • v
      simp
  exact ⟨equivOfBijective f ⟨hinj, hsurj⟩⟩

theorem exh_deg_zero (c : IrrCl (GL (Fin 0) k)) : IsL (0 : Multiset (Segment k)) (IrrGL.rep ⟨0, c⟩) := by
  let x : Fin 0 → IrrGL (k := k) := Fin.elim0
  have hd : ∑ a, (x a).1 = 0 := by simp
  refine ⟨0, x, hd, ⟨Fin.elim0, ⟨rfl, fun i => i.elim0⟩, fun i => i.elim0⟩, ?_⟩
  obtain ⟨φ⟩ := exh_equiv_zero (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)
    (PiTensorProduct.isEmptyEquiv (Fin 0)) c.rep.ρ c.rep.irr
  exact (isCosocle_self c.rep.irr).of_equiv (.refl _) φ.symm

theorem exh_le_one (x : IrrGL (k := k)) (hx : x.1 ≤ 1) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep := by
  obtain ⟨n, c⟩ := x
  obtain rfl | rfl : n = 0 ∨ n = 1 := by simp at hx; omega
  · exact ⟨0, exh_deg_zero c⟩
  · exact exh_deg_one c

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LanglandsDataDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    (∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL (k := k), IsL 𝔪 x.rep) ∧
    ∀ (l : List (Segment k)) (x y : IrrGL (k := k)), IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
      ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def GlobalTheory.Published.LocalGlobalAboveLPst : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → GKCoh.IsCohomological π →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} {π : CuspSub E a}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
  {P : LocPrime l} {AI : LocAinf l P} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

end

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RestrictMem
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.DepthZeroTypeModel
open GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem v_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {k : ℚ_[g]} (hk : ‖k‖ < 1) :
    Valued.v (i k) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (i k) ^ n) Filter.atTop (nhds 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hk)
    simpa [Function.comp_def] using this
  have h2 : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) := by
    have : IsOpen {y : w.adicCompletion E | Valued.v y < 1} := by
      simpa using Valued.isOpen_ball (w.adicCompletion E) 1
    exact this.mem_nhds (by simp)
  obtain ⟨n, hn⟩ := (h1.eventually h2).exists
  simp only [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

end GlobalTheory.Published.DepthZeroTypeModel
end
end

