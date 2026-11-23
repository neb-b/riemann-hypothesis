module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueOfRayClass
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TopA



theorem exists_label_of_eq {g : ℕ} [Fact g.Prime] {t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ} (e : t' = t)
    (h : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (h' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t h ζ hζ)) (h1 : Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O) (h2 : LabTwLawO O) :
    ∃ O' : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t' h' ζ hζ), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O' ∧ LabTwLawO O' ∧
      ∀ r f, eSerO O' r f = eSerO O r f := by
  subst e
  exact ⟨O, h1, h2, fun _ _ => rfl⟩


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_grp_setTy (D : D7) (hE : IsEmpty D.nd.Loc) (X : NTypes D.naut) (h1 h0) (e1 : X.tg = D.ntypes.tg)
    (e2 : X.teichC = D.ntypes.teichC) (e3 : X.eSer = D.ntypes.eSer) (Γ : GrpSide D) :
    ∃ Γ' : GrpSide (setTy D hE X h1 h0), Γ'.ζ = Γ.ζ := by
  have hO := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_label_of_eq (congrFun e2 k) (D.ntypes.teichC_inj k) (X.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k) (Γ.O k) (Γ.O_equiv k) (Γ.O_tw k)
  choose O hO1 hO2 hO3 using hO
  refine ⟨{ tA := Γ.tA, tκ := Γ.tκ, teichC_def := fun k => ?_, ζ := Γ.ζ, ζ_gen := Γ.ζ_gen, O := O, eSer_def := fun k f => ?_
            kv := Γ.kv, tg_tame := fun k v => ?_, O_equiv := hO1, O_tw := hO2 }, rfl⟩
  · have := Γ.teichC_def k
    rw [← e2] at this
    exact this
  · exact ((congrFun (congrFun e3 k) f).trans (Γ.eSer_def k f)).trans (hO3 k _ f).symm
  · have := Γ.tg_tame k v
    rw [← e1] at this
    exact this




theorem exists_kv_of_eq (D : D7) {g : ℕ} [Fact g.Prime] {w w' : PlE D.host} (e : w' = w) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 w) ≃+* Formalism.CyclotomicNorms.Fbar g)
    (h : TameCoupled (D.nd.plOm.1 w) κ σ ζ) :
    ∃ κ' : IsLocalRing.ResidueField (D.nd.plOm.1 w') ≃+* Formalism.CyclotomicNorms.Fbar g, TameCoupled (D.nd.plOm.1 w') κ' σ ζ := by
  subst e
  exact ⟨κ, h⟩


theorem exists_eq_of_heq {P P' : Fin 2 → Type} {β : Type} (e : P' = P) {f : ∀ k, P k → β} {f' : ∀ k, P' k → β} (h : HEq f' f)
    (k : Fin 2) (v : P' k) : ∃ v₀, f k v₀ = f' k v := by
  subst e
  exact ⟨v, by rw [eq_of_heq h]⟩


end GlobalTheory.HeightCounting.TopA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightPolynomialFramesMemSpanBideterminantProduc
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

noncomputable section

namespace GlobalTheory.Mem.WeightBideterminants

open MvPolynomial

private theorem prod_eval_mem_span_prod_of_mem_span {L : Type} [Field L] {ι : Type} [Fintype ι] {X : Type}
    (A : ι → Set (X → L)) (s : Finset ι) :
    ∀ h : ι → X → L, (∀ τ ∈ s, h τ ∈ Submodule.span L (A τ)) → (∀ τ ∉ s, h τ ∈ A τ) →
      (fun y : ι → X => ∏ τ, h τ (y τ)) ∈
        Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h _ h2
    exact Submodule.subset_span ⟨h, fun τ => h2 τ (by simp), rfl⟩
  | insert a s ha ih =>
    intro h h1 h2

    have hsplit : ∀ x : X → L, (fun y : ι → X => ∏ τ, Function.update h a x τ (y τ)) =
        fun y => x (y a) * ∏ τ ∈ Finset.univ.erase a, h τ (y τ) := by
      intro x
      funext y
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro τ hτ
        rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hτ)]

    have key : ∀ x ∈ Submodule.span L (A a), (fun y : ι → X => ∏ τ, Function.update h a x τ (y τ)) ∈
        Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro τ hτ
          have hne : τ ≠ a := fun e => ha (e ▸ hτ)
          rw [Function.update_apply, if_neg hne]
          exact h1 τ (Finset.mem_insert_of_mem hτ)
        · intro τ hτ
          by_cases e : τ = a
          · subst e
            simpa using hx
          · rw [Function.update_apply, if_neg e]
            exact h2 τ (by simp [e, hτ])
      | zero =>
        rw [hsplit]
        convert Submodule.zero_mem _ using 1
        funext y
        simp
      | add x x' _ _ hx hx' =>
        rw [hsplit] at hx hx' ⊢
        convert Submodule.add_mem _ hx hx' using 1
        funext y
        simp [add_mul]
      | smul c x _ hx =>
        rw [hsplit] at hx ⊢
        convert Submodule.smul_mem _ c hx using 1
        funext y
        simp [mul_assoc]
    simpa using key (h a) (h1 a (Finset.mem_insert_self a s))

theorem prod_mem_span_prod {L : Type} [Field L] {ι : Type} [Fintype ι] {X : Type} (A : ι → Set (X → L))
    (h : ι → X → L) (hh : ∀ τ, h τ ∈ Submodule.span L (A τ)) :
    (fun y : ι → X => ∏ τ, h τ (y τ)) ∈
      Submodule.span L {F | ∃ g : ι → X → L, (∀ τ, g τ ∈ A τ) ∧ F = fun y => ∏ τ, g τ (y τ)} :=
  prod_eval_mem_span_prod_of_mem_span A Finset.univ h (fun τ _ => hh τ) (fun τ hτ => absurd (Finset.mem_univ τ) hτ)

theorem eval_rowAct {L : Type} [Field L] {N : ℕ} (g Y : Matrix (Fin N) (Fin N) L)
    (f : MvPolynomial (Fin N × Fin N) L) :
    eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct L g f) =
      eval (fun v : Fin N × Fin N => (g * Y) v.1 v.2) f := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [Matrix.mul_apply]

def evFn (L : Type) [Field L] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) L →ₗ[L] (Matrix (Fin N) (Fin N) L → L) :=
  LinearMap.pi fun Y => (aeval fun v : Fin N × Fin N => Y v.1 v.2).toLinearMap

theorem evFn_apply (L : Type) [Field L] (N : ℕ) (P : MvPolynomial (Fin N × Fin N) L) (Y : Matrix (Fin N) (Fin N) L) :
    evFn L N P Y = eval (fun v : Fin N × Fin N => Y v.1 v.2) P := by
  simp [evFn]

theorem evFn_mem_span (L : Type) [Field L] (N : ℕ) (ν : Fin N → ℕ) (P : MvPolynomial (Fin N × Fin N) L)
    (hP : P ∈ Formalism.GradedWeylDivisibility.dualWeyl L N N ν) : evFn L N P ∈ Submodule.span L (bideterminantFunctionsOfShape L N ν) := by

  obtain ⟨b, hb, hbm⟩ := Formalism.GradedWeylDivisibility.sSBasis L N N ν
  have hP' : P ∈ Submodule.span L (Set.range b) := by
    rw [hb.2.1]
    exact hP
  have h1 : evFn L N P ∈ (Submodule.span L (Set.range b)).map (evFn L N) := Submodule.mem_map_of_mem hP'
  rw [Submodule.map_span] at h1
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  obtain ⟨-, -, Kc, sz, hsz, I, hs, hI, hbI⟩ := hbm m
  refine ⟨Kc, sz, hsz, I, hs, hI, ?_⟩
  funext Y
  rw [evFn_apply, hbI]

theorem weightPolynomial_mem_span_bideterminantProducts : ∀ (K L : Type) [Field K] [Field L] [Infinite K] (φ : K →+* L) (ι : Type) [Fintype ι] (N : ℕ)
    (ν : ι → Fin N → ℕ) (M : ι → Matrix (Fin N) (Fin N) L), ∀ Q ∈ WtPol K ν,
    (fun y : ι → Matrix (Fin N) (Fin N) L =>
      MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ Q)) ∈
    Submodule.span L {F | ∃ g : ι → Matrix (Fin N) (Fin N) L → L, (∀ τ, g τ ∈ bideterminantFunctionsOfShape L N (ν τ)) ∧
      F = fun y => ∏ τ, g τ (y τ)} := by
  intro K L _ _ _ φ ι _ N ν M Q hQ

  have hT := Formalism.L2.Ker.wtPol_le_tensor (K := K) ν hQ
  clear hQ
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx

    have hfun : (fun y : ι → Matrix (Fin N) (Fin N) L =>
        MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2)
          (MvPolynomial.map φ (∏ s, Formalism.GradedWeylDivisibility.blockEmb K s (F s)))) =
        fun y => ∏ τ, evFn L N (Formalism.GradedWeylDivisibility.rowAct L (M τ) (MvPolynomial.map φ (F τ))) (y τ) := by
      funext y
      simp only [map_prod, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename, MvPolynomial.eval_rename, evFn_apply,
        eval_rowAct, Function.comp_def]
    rw [hfun]
    apply prod_mem_span_prod
    intro τ
    apply evFn_mem_span
    exact Formalism.GradedWeylDivisibility.dualWeylRowStable L N N (ν τ) (M τ) _ (Formalism.GradedWeylDivisibility.dualWeylMap K L φ N N (ν τ) (F τ) (hF τ))
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext y
    simp
  | add x x' _ _ hx hx' =>
    convert Submodule.add_mem _ hx hx' using 1
    funext y
    simp
  | smul c x _ hx =>
    convert Submodule.smul_mem _ (φ c) hx using 1
    funext y
    simp [MvPolynomial.smul_eq_C_mul]

end GlobalTheory.Mem.WeightBideterminants
end
end

