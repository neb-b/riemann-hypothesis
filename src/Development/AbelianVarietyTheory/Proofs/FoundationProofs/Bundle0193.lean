module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundary
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubrepClosureAnalyticVectors
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AnalyticClosure
open GlobalTheory.FockTensor

variable {p q : ℕ} {T : GrpData p q}

def restrictRep (πU : URep T) (K : Submodule ℂ πU.H) (hK : IsClosed (K : Set πU.H))
    (hinv : ∀ g, ∀ x ∈ K, πU.π g x ∈ K) : URep T :=
  haveI : CompleteSpace K := hK.completeSpace_coe
  { H := K
    π :=
      { toFun := fun g => ((πU.π g).comp K.subtypeL).codRestrict K (fun x => hinv g x x.2)
        map_one' := by ext x; simp
        map_mul' := fun a b => by ext x; simp; rfl }
    isom := fun g x => πU.isom g x
    cont := fun x => (πU.cont x).subtype_mk _ }

theorem inner_orbit_eq_zero (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (y : V) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (w : πU.H) (hw : ∀ v, inner ℂ w (E v) = 0) (t : ℝ) :
    inner ℂ w (πU.π (T.expt (t • Y)) (E y)) = 0 := by
  have key := GlobalTheory.FactorialJet.eq_zero_of_factorial_bound ℂ
    (fun k t => inner ℂ w (πU.π (T.expt (t • Y)) (E ((A ^ k) y)))) (‖w‖ * C) ρ
    (mul_nonneg (norm_nonneg _) hC) hρ ?_ ?_ ?_ 0 t
  · simpa using key
  · intro k s
    have h1 := hasDerivAt_orbit πU hY (hd ((A ^ k) y)) s
    have h2 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    rw [pow_succ', Module.End.mul_apply]
    exact h2
  · intro k s
    refine (norm_inner_le_norm _ _).trans ?_
    rw [πU.isom, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← mul_assoc]
    exact hb k
  · intro k
    simp [T.expt_zero, hw]

theorem orbit_mem_closure (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (hb : ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (t : ℝ) (x : πU.H) (hx : x ∈ (LinearMap.range E).topologicalClosure) :
    πU.π (T.expt (t • Y)) x ∈ (LinearMap.range E).topologicalClosure := by
  have h0 : ∀ y, πU.π (T.expt (t • Y)) (E y) ∈ (LinearMap.range E).topologicalClosure := by
    intro y
    obtain ⟨C, ρ, hC, hρ, h⟩ := hb y
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    refine inner_orbit_eq_zero πU A E hY hd y hC hρ h w (fun v => ?_) t
    exact (Submodule.mem_orthogonal' _ _).1 hw _ (LinearMap.mem_range_self _ v)
  have hcl : IsClosed ((πU.π (T.expt (t • Y))) ⁻¹'
      ((LinearMap.range E).topologicalClosure : Set πU.H)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
  have hsub : ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) ⊆
      (πU.π (T.expt (t • Y))) ⁻¹' ((LinearMap.range E).topologicalClosure : Set πU.H) := by
    rintro _ ⟨y, rfl⟩
    exact h0 y
  exact closure_minimal hsub hcl hx

theorem exists_subrep_closure : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  intro p q T hgen πU V _ _ act E hd hb
  have hinv : ∀ g : T.G, ∀ x ∈ (LinearMap.range E).topologicalClosure,
      πU.π g x ∈ (LinearMap.range E).topologicalClosure := by
    intro g
    have hg : g ∈ Subgroup.closure (T.expt '' upq p q) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      simpa using orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) 1 x hx
    | inv_mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      have he : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
        have := T.expt_add Y hY 1 (-1)
        rw [add_neg_cancel, zero_smul, one_smul, T.expt_zero] at this
        exact inv_eq_of_mul_eq_one_right this.symm
      rw [he]
      exact orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) (-1) x hx
    | one => intro x hx; simpa using hx
    | mul a b _ _ ha hb' =>
      intro x hx
      rw [map_mul, ContinuousLinearMap.mul_apply]
      exact ha _ (hb' x hx)
  set K := (LinearMap.range E).topologicalClosure with hKdef
  have hK : IsClosed (K : Set πU.H) := Submodule.isClosed_topologicalClosure _
  have hmem : ∀ x, E x ∈ K := fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
  refine ⟨restrictRep πU K hK hinv, E.codRestrict K hmem, K.subtypeₗᵢ, ?_, fun x => rfl,
    fun g y => rfl, ?_⟩
  · show Dense (Set.range (E.codRestrict K hmem : V → K))
    rw [Subtype.dense_iff]
    intro x hx
    have : (Subtype.val '' Set.range (E.codRestrict K hmem : V → K)) =
        ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) := by
      rw [← Set.range_comp, LinearMap.coe_range]; rfl
    exact this ▸ (hx : x ∈ closure ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H))
  · intro Y hY x
    have h := hd Y hY x
    rw [hasDerivAt_iff_isLittleO_nhds_zero, ← Asymptotics.isLittleO_norm_left] at h ⊢
    exact h

end GlobalTheory.AnalyticClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRange
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockUniq

theorem genSub_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (N : Submodule ℂ V)
    (h1 : S ⊆ N) (h2 : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act S ≤ N :=
  sInf_le ⟨h1, h2⟩

theorem subset_genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub act S := by
  intro x hx
  simp only [genSub, SetLike.mem_coe, Submodule.mem_sInf]
  exact fun N hN => hN.1 hx

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) (y : V)
    (hy : y ∈ genSub act S) : act Z y ∈ genSub act S := by
  simp only [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  intro p q n T0 T1 T2 F M₁ W M I e₀ v₀ hgen hK hirr hM he hv hI
  refine ⟨?_, ?_, ?_⟩
  · intro io hio h0
    have h1 : ∀ v, io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := by
      let N : Submodule ℂ M.V := LinearMap.eqLocus (io ∘ₗ TensorProduct.mk ℂ W M.V e₀)
        (I ∘ₗ TensorProduct.mk ℂ M₁.V M.V e₀)
      have hN : ∀ v, v ∈ N ↔ io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
      rcases hM.2 N (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hio.2, ← hI.2, hy]) with h | h
      · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (hN v₀).2 h0)) hv
      · intro v
        exact (hN v).1 (h ▸ Submodule.mem_top)
    refine TensorProduct.ext' fun e v => ?_
    let N : Submodule ℂ W := LinearMap.eqLocus (io ∘ₗ (TensorProduct.mk ℂ W M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v ∘ₗ W.subtype)
    have hN : ∀ e, e ∈ N ↔ io (e ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
    have hst : KStable M₁.act (N.map W.subtype) := by
      rintro Z hZ _ ⟨w, hw, rfl⟩
      refine ⟨⟨M₁.act Z w, hK Z hZ w w.2⟩, ?_, rfl⟩
      have hw' := (hN w).1 hw
      refine (hN _).2 ?_
      rw [← hio.1 Z hZ w _ v rfl, hw', hI.1]
    have h0' : (e₀ : M₁.V) ∈ N.map W.subtype := ⟨e₀, (hN e₀).2 (h1 v), rfl⟩
    rcases hirr _ (Submodule.map_subtype_le W N) hst with h | h
    · rw [h, Submodule.mem_bot] at h0'
      exact absurd (Subtype.ext h0') he
    · have : (e : M₁.V) ∈ N.map W.subtype := by rw [h]; exact e.2
      obtain ⟨e', he', hee⟩ := this
      have : e' = e := Subtype.ext hee
      subst this
      simpa using (hN e').1 he'
  · intro I' hI' hW
    refine TensorProduct.ext' fun x v => ?_
    let N : Submodule ℂ M₁.V := LinearMap.eqLocus (I' ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
    have hN : ∀ e, e ∈ N ↔ I' (e ⊗ₜ v) = I (e ⊗ₜ v) := fun v => Iff.rfl
    have := genSub_le M₁.act (W : Set M₁.V) N (fun w hw => (hN w).2 (hW ⟨w, hw⟩ v))
      (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hI'.1, ← hI.1, hy])
    rw [hgen] at this
    exact (hN x).1 (this Submodule.mem_top)
  · intro v
    let f : M₁.V →ₗ[ℂ] Pol p q n 0 := I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v
    have hf : ∀ x, f x = I (x ⊗ₜ v) := fun x => rfl
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      have := genSub_le M₁.act (W : Set M₁.V)
        ((genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v))).comap f)
        (fun w hw => subset_genSub F.act1 _ ⟨⟨w, hw⟩, rfl⟩)
        (fun Z y hy => by
          rw [Submodule.mem_comap, hf] at hy ⊢
          rw [← hI.1]
          exact genSub_stable _ _ _ _ hy)
      rw [hgen] at this
      exact this (Submodule.mem_top : x ∈ ⊤)
    · have := genSub_le F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) (LinearMap.range f)
        (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
        (by rintro Z _ ⟨x, rfl⟩; exact ⟨M₁.act Z x, by rw [hf, hf, hI.1]⟩)
      intro y hy
      obtain ⟨x, hx⟩ := this hy
      exact ⟨x, hx⟩

end GlobalTheory.FockUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantInnerFormsProportionalWeightLine
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockForm

theorem act_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V} (h : x ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  have := (Submodule.mem_iInf _).1 h a
  simpa [LinearMap.mem_ker, sub_eq_zero] using this

theorem form_eq_zero {p q : ℕ} (M : GKMod p q) (D : M.V → M.V → ℂ)
    (hadd₁ : ∀ x x' y, D (x + x') y = D x y + D x' y)
    (hsmul₁ : ∀ (c : ℂ) x y, D (c • x) y = star c * D x y)
    (hadd₂ : ∀ x y y', D x (y + y') = D x y + D x y')
    (hsmul₂ : ∀ (c : ℂ) x y, D x (c • y) = c * D x y)
    (hinv : ∀ Z x y, D (M.act Z x) y = D x (M.act (adjZ Z) y))
    (μ : Ix p q → ℚ) (v : M.V) (hv : v ∈ wtSub M.act μ)
    (hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) (hgen : genSub M.act {v} = ⊤)
    (hvv : D v v = 0) : ∀ x y, D x y = 0 := by
  have hv0 : ∀ y, D v y = 0 := by
    intro y
    refine Submodule.iSup_induction (motive := fun y => D v y = 0) _ (M.wts y) ?_ ?_ ?_
    · intro ν y hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, rfl⟩ := hline y hy
        rw [hsmul₂, hvv, mul_zero]
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h := hinv (Eab a a) v y
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_of_mem_wtSub hv, act_of_mem_wtSub hy, hsmul₁, hsmul₂] at h
        have hs : star ((μ a : ℚ) : ℂ) = ((μ a : ℚ) : ℂ) := by simp
        rw [hs] at h
        have hne : ((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha.symm
        have : (((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ)) * D v y = 0 := by linear_combination h
        exact (mul_eq_zero.1 this).resolve_left hne
    · have := hsmul₂ 0 v 0
      simpa using this
    · intro y y' h h'
      rw [hadd₂, h, h', add_zero]
  let N : Submodule ℂ M.V :=
    { carrier := {x | ∀ y, D x y = 0}
      add_mem' := fun {x x'} h h' y => by rw [hadd₁, h y, h' y, add_zero]
      zero_mem' := fun y => by simpa using hsmul₁ 0 0 y
      smul_mem' := fun c x h y => by rw [hsmul₁, h y, mul_zero] }
  have hN : genSub M.act {v} ≤ N := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hv0
    · intro Z x hx y
      rw [hinv]
      exact hx _
  intro x y
  exact hN (hgen ▸ Submodule.mem_top) y

theorem inner_eq_mul : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  intro p q M H₁ _ _ H₂ _ _ j E₁ E₂ hj hE μ v hv hline hgen hnorm x y
  have := form_eq_zero M
    (fun x y => inner ℂ (E₁ x) (E₂ y) - inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y))
    (fun x x' y => by simp only [map_add (f := _), inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_left, starRingEnd_apply]; ring)
    (fun x y y' => by simp only [map_add (f := _), inner_add_right]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_right]; ring)
    (fun Z x y => by simp only [hj, hE])
    μ v hv hline hgen (by simp [inner_self_eq_norm_sq_to_K, hnorm]) x y
  exact sub_eq_zero.1 this

end GlobalTheory.FockForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKilledByLowerNilradicalActBlockDiagonal
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.KilledByLowerStable

theorem act_eq_zero_of_lower {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) (hx : KilledByLower act x) (Y : Mat p q)
    (h1 : ∀ (a : Fin p) (j : Ix p q), Y (Sum.inl a) j = 0)
    (h2 : ∀ (i : Ix p q) (b : Fin q), Y i (Sum.inr b) = 0) : act Y x = 0 := by
  have hY : Y = ∑ i, ∑ j, Y i j • Eab i j := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Eab, Matrix.smul_single]
  rw [hY]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rcases i with a | b
  · rw [h1, zero_smul]
  · rcases j with a | b'
    · rw [hx a b, smul_zero]
    · rw [h2, zero_smul]

theorem killedByLower_act : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z →
    ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  intro p q V _ _ act hact Z hZ x hx a b
  have h := congrArg (fun f : Module.End ℂ V => f x) (hact (Eab (Sum.inr b) (Sum.inl a)) Z)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hx a b, map_zero, sub_zero] at h
  rw [← h]
  apply act_eq_zero_of_lower act x hx
  · intro a' j
    have h0 : Z (Sum.inl a') (Sum.inr b) = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hj : j = Sum.inl a
    · subst hj
      simp [Eab, h0]
    · simp [Eab, hj]
  · intro i b'
    have h0 : Z (Sum.inl a) (Sum.inr b') = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hi : i = Sum.inr b
    · subst hi
      simp [Eab, h0]
    · simp [Eab, hi]

end GlobalTheory.KilledByLowerStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundaryStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cocycle_twisted_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k : ℕ) (χ κ : Gal p Ω → ZMod (p ^ k)), IsKum T k (Ggeo p Ω) (T.qq k) κ →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω) a → IsTwistedOneCocycle 0 k (Ggeo p Ω) χ a →
      ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧
        IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => (p : Ω) ^ c * a g - o * ((κ g).val : Ω))) ∧
  (∀ o : Ω, IsInt (p := p) o → (∀ g ∈ Ggeo p Ω, g o = o) →
      IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => o * ((κ g).val : Ω)) → Cong (p := p) k ((p : Ω) ^ c * o) 0) := by
  first | exact @GlobalTheory.K5.TopGeo.top | exact GlobalTheory.K5.TopGeo.top | (intros; apply GlobalTheory.K5.TopGeo.top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LatBasisAt

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  haveI := w.isPrime
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

lemma mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∉ w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

lemma algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∉ w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have : s = 0 := (IsFractionRing.injective (𝓞 K) K) (by simpa using h)
  exact hs (this ▸ w.asIdeal.zero_mem)

lemma mem_localization_iff (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ M :=
  Iff.rfl

lemma mem_localization_iff_mem_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ x ∈ Submodule.span (locRing w) (M : Set (Fin d → K)) := by
  constructor
  · intro h
    obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w M x).mp h
    have hs0 := algebraMap_ne_zero w hs
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ locRing w := (mem_locRing w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : locRing w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_localization_iff w M y).mpr ⟨1, h1, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_localization_iff w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp a.2
      refine (mem_localization_iff w M _).mpr ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

theorem basisAtEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
      (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsFullLattice K M →
      ∀ w : HeightOneSpectrum (𝓞 K), ∃ B : GL (Fin n) K, Formalism.L2.DIV.IsBasisAt w M B := by
  intro K _ _ d L hL w
  haveI := w.isPrime
  have : IsDiscreteValuationRing (locRing w) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot (locRing w)
  set N : Submodule (locRing w) (Fin d → K) := Submodule.span (locRing w) (L : Set (Fin d → K))
    with hN
  have : Module.Finite (locRing w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (locRing w) N := inferInstance
  let b := Module.Free.chooseBasis (locRing w) N
  let v : Module.Free.ChooseBasisIndex (locRing w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (locRing w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (locRing w) K).mp hliA
  have hspanA : Submodule.span (locRing w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (locRing w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (locRing w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (locRing w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hli' : LinearIndependent K (v ∘ e.symm) := hli.comp _ e.symm.injective
  let P : Matrix (Fin d) (Fin d) K := Matrix.of fun a j => (v ∘ e.symm) j a
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  refine ⟨hP.unit, ?_⟩
  have hcol : Formalism.L2.DIV.colLat hP.unit = Submodule.span (𝓞 K) (Set.range (v ∘ e.symm)) := rfl
  unfold Formalism.L2.DIV.IsBasisAt
  ext x
  rw [hcol, mem_localization_iff_mem_span, mem_localization_iff_mem_span, Submodule.span_span_of_tower,
    EquivLike.range_comp, hspanA]

end GlobalTheory.LatBasisAt
end
end

