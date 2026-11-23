module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.DecompOfNormalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariant
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfMemBoth
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.OntoLinAlg

open Formalism.IndefR.U2

variable {I A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

theorem op_mem_ker {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (i : I) {k : A} (hk : k ∈ LinearMap.ker θ) : op i k ∈ LinearMap.ker θ := by
  rw [LinearMap.mem_ker] at hk ⊢
  rw [hI, hk, map_zero]

theorem op_mem_orth {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (hA : AdjClosed op) (i : I) {v : A} (hv : v ∈ (LinearMap.ker θ)ᗮ) :
    op i v ∈ (LinearMap.ker θ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨i', hi'⟩ := hA i
  rw [← LinearMap.adjoint_inner_left, ← hi']
  exact hv _ (op_mem_ker hI i' hu)

theorem eq_zero_of_mem_both {K : Submodule ℂ A} {z : A} (h1 : z ∈ K) (h2 : z ∈ Kᗮ) : z = 0 := by
  have := (Submodule.mem_orthogonal _ _).mp h2 z h1
  exact inner_self_eq_zero.mp this

theorem ontoParts_of {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    {good : Submodule ℂ A} {goodB : Submodule ℂ B} (Ix : Set (I → ℂ))
    (hI : Intw θ op opB) (hA : AdjClosed op) (hOnto : goodB ≤ LinearMap.range θ)
    (hPr : ∀ y ∈ good, ((LinearMap.ker θ).starProjection y : A) ∈ good)
    (hInj : ∀ (c : I → ℂ) (x y : A), x ∈ eigPart op c → θ x ≠ 0 → y ∈ eigPart op c ⊓ good → θ y = 0 → y = 0) :
    OntoParts (LinearMap.adjoint θ) op opB good goodB Ix := by
  intro c hc y hy
  set K := LinearMap.ker θ with hK
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.2
  obtain ⟨x0, hx0⟩ := hOnto hw.2
  set x := x0 - K.starProjection x0 with hxdef
  have hxo : x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x0
  have hθx : θ x = w := by
    have : θ (K.starProjection x0) = 0 := LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem K x0)
    rw [hxdef, map_sub, this, sub_zero, hx0]
  have hxe : x ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hz1 : op i x - c i • x ∈ Kᗮ := Submodule.sub_mem _ (op_mem_orth hI hA i hxo) (Submodule.smul_mem _ _ hxo)
    have hz2 : op i x - c i • x ∈ K := by
      rw [hK, LinearMap.mem_ker, map_sub, map_smul, hI, hθx, (mem_eigPart.mp hw.1) i, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz2 hz1)
  set y1 := K.starProjection y with hy1
  have hy1K : y1 ∈ K := Submodule.starProjection_apply_mem K y
  have hy2 : y - y1 ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal y
  have hy1e : y1 ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hyi := (mem_eigPart.mp hy.1) i
    have e : op i y1 - c i • y1 = -(op i (y - y1) - c i • (y - y1)) := by
      rw [map_sub, smul_sub, hyi]; abel
    have hz1 : op i y1 - c i • y1 ∈ K := Submodule.sub_mem _ (op_mem_ker hI i hy1K) (Submodule.smul_mem _ _ hy1K)
    have hz2 : op i y1 - c i • y1 ∈ Kᗮ := by
      rw [e]
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (op_mem_orth hI hA i hy2) (Submodule.smul_mem _ _ hy2))
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz1 hz2)
  have hy10 : y1 = 0 := hInj c x y1 hxe (by rw [hθx]; exact hw0) ⟨hy1e, hPr y hy.2⟩ (LinearMap.mem_ker.mp hy1K)
  rw [← LinearMap.orthogonal_ker]
  have : y = y - y1 := by rw [hy10, sub_zero]
  rw [this]
  exact hy2

end GlobalTheory.OntoLinAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmOfGramEqSmulStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clm_of_gram_eq_smul' : ∀ {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E) (K : ℝ), (∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  first | exact @GlobalTheory.exists_clm_of_gram_eq_smul | exact GlobalTheory.exists_clm_of_gram_eq_smul | (intros; apply GlobalTheory.exists_clm_of_gram_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDescendPeriodicTrig
section
open MeasureTheory

namespace GlobalTheory

theorem trigPoly_dense_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → ∀ ε : ℝ, 0 < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ x, ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | (apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteReproducingOfSubmodule
section
namespace GlobalTheory

open Finset

theorem exists_finite_reproducing_of_submodule {X : Type} (V : Submodule ℂ (X → ℂ))
    (F : Finset ↥V) :
    ∃ (S : Finset X) (u : X → ↥V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  first
  | exact @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | (apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation ..)

theorem finsupp_sum_multilinear_eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : ι → Type} (V : ∀ k, Submodule ℂ (X k → ℂ)) {R : Type} [AddCommGroup R] [Module ℂ R]
    (M : (∀ k, ↥(V k)) →ₘₗ[ℂ] R) {A : Type} (τ τ' : A →₀ ℂ)
    (φ φ' : A → ∀ k, ↥(V k))
    (h : ∀ z : ∀ k, X k, (τ.sum fun a c => c * ∏ k, (φ a k : X k → ℂ) (z k)) =
      τ'.sum fun a c => c * ∏ k, (φ' a k : X k → ℂ) (z k)) :
    (τ.sum fun a c => c • M (φ a)) = τ'.sum fun a c => c • M (φ' a) := by
  classical
  let T : Finset A := τ.support ∪ τ'.support
  let F : ∀ k, Finset ↥(V k) := fun k => T.image (fun a => φ a k) ∪ T.image (fun a => φ' a k)
  choose S u hSu using fun k => exists_finite_reproducing_of_submodule (V k) (F k)
  have key : ∀ w : ∀ k, ↥(V k), (∀ k, w k ∈ F k) →
      M w = ∑ z ∈ Fintype.piFinset S, (∏ k, (w k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro w hw
    have hw' : w = fun k => ∑ x ∈ S k, (w k : X k → ℂ) x • u k x :=
      funext fun k => hSu k (w k) (hw k)
    conv_lhs => rw [hw']
    rw [MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  have expand : ∀ (σ : A →₀ ℂ) (ψ : A → ∀ k, ↥(V k)), σ.support ⊆ T →
      (∀ a ∈ T, ∀ k, ψ a k ∈ F k) →
      (σ.sum fun a c => c • M (ψ a)) = ∑ z ∈ Fintype.piFinset S,
        (σ.sum fun a c => c * ∏ k, (ψ a k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro σ ψ hσ hψ
    unfold Finsupp.sum
    rw [Finset.sum_congr rfl fun a ha => congrArg (σ a • ·) (key (ψ a) (hψ a (hσ ha)))]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [expand τ φ Finset.subset_union_left
      (fun a ha k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    expand τ' φ' Finset.subset_union_right
      (fun a ha k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  exact Finset.sum_congr rfl fun z _ => by rw [h z]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBounded
section
open scoped TensorProduct

namespace GlobalTheory.StabGen

open GlobalTheory.TensHead

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}

theorem rel_le_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Rel ≤ stabClosure Op Rel S :=
  le_sInf fun _ hN => hN.1

theorem subset_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx

theorem stab_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)

theorem closure_le {Op : Set (Module.End ℂ M)} {Rel N : Submodule ℂ M} {S : Set M}
    (h1 : Rel ≤ N) (h2 : Stab Op N) (h3 : S ⊆ N) : stabClosure Op Rel S ≤ N :=
  sInf_le ⟨h1, h2, h3⟩

theorem closure_mono {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))

noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)

theorem exists_finset_generating (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) :
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N →
      (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  classical
  obtain ⟨L, hL⟩ := hL
  by_contra hne
  push_neg at hne
  have hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M) := by
    intro F
    obtain ⟨N, h1, h2, h3, h4⟩ := hne F
    by_contra h
    push_neg at h
    exact h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))
  choose pick hpick using hx
  have hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M) := by
    refine strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_
    · exact closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    · intro h
      apply hpick (chainSet pick n)
      have hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M) :=
        subset_closure Op Rel _ (by simp [chainSet])
      rw [← h] at hmem
      exact hmem
  have := hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M))
    (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)
  omega

end GlobalTheory.StabGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGenerating
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_maximal_stab_of_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (G : Set (Module.End ℂ V)) (R : Submodule ℂ V) (F : Finset V)
    (hF : ∀ N : Submodule ℂ V, R ≤ N → Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) :
    ∀ N : Submodule ℂ V, R ≤ N → Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  intro N hRN hN hNtop
  let s : Set (Submodule ℂ V) := {U | R ≤ U ∧ Stab G U ∧ ¬ (↑F : Set V) ⊆ ↑U}
  have hcomp := (isCompactElement_iff_le_of_directed_sSup_le _).1
    (Submodule.finset_span_isCompactElement (R := ℂ) F)
  have hNs : N ∈ s := ⟨hRN, hN, fun h => hNtop (hF N hRN hN h)⟩
  obtain ⟨M, hNM, hM⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro g hg x hx
      obtain ⟨U, hU, hxU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨U, hU, (hcs hU).2.1 g hg x hxU⟩
    · intro hFc
      have hspan : Submodule.span ℂ (↑F : Set V) ≤ sSup c := Submodule.span_le.2 hFc
      obtain ⟨U, hU, hle⟩ := hcomp c hne hdir hspan
      exact (hcs hU).2.2 (Submodule.span_le.1 hle)) N hNs
  refine ⟨M, hNM, hM.prop.2.1, fun h => hM.prop.2.2 (by rw [h]; exact fun _ _ => trivial), ?_⟩
  intro U hU hMU
  by_cases hFU : (↑F : Set V) ⊆ ↑U
  · exact Or.inr (hF U (le_trans hM.prop.1 hMU) hU hFU)
  · exact Or.inl (le_antisymm (hM.2 ⟨le_trans hM.prop.1 hMU, hU, hFU⟩ hMU) hMU)

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap (RingHom.id ℂ) H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap (RingHom.id ℂ) H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  first | exact @GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | exact GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | (intros; apply GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmulMemSupLattice
section
open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory.DenominatorExistenceTwistedOperators

theorem abs_eq_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ∉ v.asIdeal) : FinitePlace.mk v (x : K) = 1 := by
  rw [FinitePlace.mk_apply]
  have h1 := FinitePlace.norm_le_one K v x
  have h2 := (FinitePlace.norm_lt_one_iff_mem K v x).not.mpr hx
  exact le_antisymm h1 (not_lt.mp h2)

theorem exists_prime_to_part {R : Type} [CommRing R] [IsDedekindDomain R] (p : HeightOneSpectrum R) (d : R)
    (hd : d ≠ 0) : ∃ s ∉ p.asIdeal, ∀ q : HeightOneSpectrum R, q ≠ p → ∃ t ∉ q.asIdeal, ∃ u, t * s = u * d := by
  have hI : Ideal.span {d} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hd
  obtain ⟨n, J, hJ, hfac⟩ := WfDvdMonoid.max_power_factor hI p.irreducible
  rw [Ideal.dvd_iff_le] at hJ
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJ
  refine ⟨s, hsp, fun q hq => ?_⟩
  have hnle : ¬ p.asIdeal ^ n ≤ q.asIdeal := by
    intro h
    have := q.isPrime
    have h1 : p.asIdeal ≤ q.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨t, htq, ?_⟩
  have : t * s ∈ Ideal.span {d} := by
    rw [hfac]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
  exact ⟨u, hu.symm⟩

theorem exists_denominator {R K M : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M] (N : Submodule R M) (x : M)
    (hx : x ∈ Submodule.span K (N : Set M)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
    have hwK : algebraMap R K w ≠ 0 := by simpa using hw0
    refine ⟨a * w, mul_ne_zero ha hw0, ?_⟩
    have : (a * w) • (algebraMap R K u / algebraMap R K w) • x = u • a • x := by
      rw [← algebraMap_smul K (a * w), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [this]
    exact N.smul_mem _ hx

theorem exists_smul_mem_supLattice (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type)
    [(σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [(σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [Group G]
    (Φ : FormsL LL Ks WL W G) (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK)
    (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK) (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s ∉ la.asIdeal, s • (f : WL) ∈ Φ.MK := by
  obtain ⟨d, hd, hdf⟩ := exists_denominator (K := Ks) Φ.MK (f : WL) (by rw [hspan]; exact f.2)
  obtain ⟨s, hs, hq⟩ := exists_prime_to_part la d hd
  refine ⟨s, hs, ?_⟩
  have hsm : ∀ (a : 𝓞 Ks) (g : WL), a • g = (a : Ks) • g := fun a g => (algebraMap_smul Ks a g).symm
  have hm : s • (f : WL) ∈ Φ.WK := by rw [hsm]; exact Φ.WK.smul_mem _ f.2
  refine ⟨hm, fun q y => ?_⟩
  by_cases h : q = la
  · subst h
    have h1 : (⟨s • (f : WL), hm⟩ : Φ.WK) = (s : Ks) • f := Subtype.ext (hsm s f)
    rw [h1, Φ.nrm_smul, abs_eq_one q s hs, one_mul]
    exact hf y
  · obtain ⟨t, ht, u, htu⟩ := hq q h
    have hmem : t • s • (f : WL) ∈ Φ.MK := by
      rw [smul_smul, htu, mul_smul]; exact Φ.MK.smul_mem _ hdf
    obtain ⟨hw, hb⟩ := hmem
    have h1 : (⟨t • s • (f : WL), hw⟩ : Φ.WK) = (t : Ks) • ⟨s • (f : WL), hm⟩ := Subtype.ext (hsm t _)
    have h2 := hb q y
    rwa [h1, Φ.nrm_smul, abs_eq_one q t ht, one_mul] at h2

end GlobalTheory.DenominatorExistenceTwistedOperators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsetFunctionsRecoveredFromValuesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ)), (∀ u ∈ F, u ∈ V) →
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  first | exact @GlobalTheory.finset_functions_recovered_from_values | exact GlobalTheory.finset_functions_recovered_from_values | (intros; apply GlobalTheory.finset_functions_recovered_from_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FubiniRightConvolutionBoundedContinuousStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G), μ 𝓕 < ⊤ → ∀ (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (ψ φ : G → ℂ), Continuous ψ → Continuous φ → ∀ (A B : ℝ), (∀ g, ‖ψ g‖ ≤ A) → (∀ g, ‖φ g‖ ≤ B) → IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧ Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧ ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  first | exact @GlobalTheory.fubini_right_convolution_bounded_continuous | exact GlobalTheory.fubini_right_convolution_bounded_continuous | (intros; apply GlobalTheory.fubini_right_convolution_bounded_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomain
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_eq_of_fundamentalDomain (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H)) (κ : Measure N) (𝓝 : Set N)
    (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤) (n₀ : N) :
    κ.map (· * n₀) = κ := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨((x : N) : H), x.2⟩ : Γ)) ?_
    intro a b h
    have h' : ((a : N) : H) = ((b : N) : H) := congrArg (fun y : Γ => (y : H)) h
    exact Subtype.ext (Subtype.ext h')
  haveI : (κ.map (· * n₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right κ n₀
  have hc := Measure.isMulLeftInvariant_eq_smul (κ.map (· * n₀)) κ
  set c := Measure.haarScalarFactor (κ.map (· * n₀)) κ
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf N) ((· * n₀) ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv (quasiMeasurePreserving_mul_right κ n₀) (e := id) bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : κ ((· * n₀) ⁻¹' 𝓝) = κ 𝓝 := h𝓝'.measure_eq h𝓝
  have h0 : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hmap : (κ.map (· * n₀)) 𝓝 = κ ((· * n₀) ⁻¹' 𝓝) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight n₀) 𝓝
  have h1 : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    calc (c : ENNReal) * κ 𝓝 = (c • κ) 𝓝 := by simp [Measure.smul_apply]
      _ = (κ.map (· * n₀)) 𝓝 := by rw [hc]
      _ = 1 * κ 𝓝 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerMapEqConstMulProdInnerStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner : ∀ {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)] [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : (Π i, Xs i) →ₘₗ[ℂ] E) (K : ℝ), (∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) → ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
  first | exact @GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | exact GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | (intros; apply GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner <;> assumption)
end

