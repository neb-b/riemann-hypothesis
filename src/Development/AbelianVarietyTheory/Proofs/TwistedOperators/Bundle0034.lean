module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSupportUniform
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.RowSupport
open GlobalTheory.RootEx.ExchangeSupport

theorem exists_box {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (W : Set (n → k)) (hW : W ∈ 𝓝 (0 : n → k)) :
    ∃ B : Set (n → k), IsCompact B ∧ ∀ u, u ∉ B → ∃ β ∈ W, ψ (u ⬝ᵥ β) ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (AddChar.map_zero_eq_one ψ)
  have hU : ∀ s : n, {x : k | (Pi.single s x : n → k) ∈ W} ∈ 𝓝 (0 : k) := by
    intro s
    have hcont : Continuous fun x : k => (Pi.single s x : n → k) := by
      refine continuous_pi fun j => ?_
      simp only [Pi.single_apply]
      split_ifs
      · exact continuous_id
      · exact continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp (Filter.iInter_mem.mpr hU)
  refine ⟨Set.univ.pi fun _ => {x : k | valuation k x ≤ valuation k a / (γ : ValueGroupWithZero k)},
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩
  intro u hu
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, not_forall, not_le] at hu
  obtain ⟨s, hs⟩ := hu
  have hus : u s ≠ 0 := by
    intro h
    rw [h, map_zero] at hs
    exact not_lt.mpr zero_le hs
  have hv : 0 < valuation k (u s) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hus
  refine ⟨Pi.single s (a / u s), ?_, ?_⟩
  · have hsmall : valuation k (a / u s) < γ := by
      rw [map_div₀, div_lt_iff₀ hv]
      have hg : (0 : ValueGroupWithZero k) < γ := by
        rw [zero_lt_iff]
        exact γ.ne_zero
      rw [div_lt_iff₀ hg] at hs
      simpa [mul_comm] using hs
    exact Set.mem_iInter.mp (hγ hsmall) s
  · rw [dotProduct_single, mul_div_cancel₀ _ hus]
    exact ha

theorem row_support_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : ψ ≠ 1) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (F : A) (Ω : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact Ω), ∃ B : Set (n → k), IsCompact B ∧ ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∀ w ∈ Ω, ∀ u, u ∉ B → l (σ (rowE c p u) (σ w F)) = 0 := by
  intro k _ _ _ _ n _ _ c p hp hc ψ hψ A _ _ σ hσ F Ω hΩ
  set S : Set (GL (n ⊕ Fin c) k) := {g | σ g F = F} with hSdef
  have hS : IsOpen S := hσ F
  have hcol : Continuous fun β : n → k => colE (k := k) c (p + 1) β :=
    ExchangeSupport.continuous_colE
  have hfix : ∀ᶠ β in 𝓝 (0 : n → k), ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F := by
    refine hΩ.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc2 : Continuous fun z : (n → k) × GL (n ⊕ Fin c) k => z.2⁻¹ * colE c (p + 1) z.1 * z.2 :=
      ((continuous_snd.inv).mul (hcol.comp continuous_fst)).mul continuous_snd
    have hmem : ((0 : n → k), w).2⁻¹ * colE c (p + 1) ((0 : n → k), w).1 * ((0 : n → k), w).2 ∈ S := by
      simp [hSdef, ExchangeSupport.colE_zero]
    filter_upwards [hc2.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with z hz
    have hz' : σ (z.2⁻¹ * colE c (p + 1) z.1 * z.2) F = F := hz
    calc σ (colE c (p + 1) z.1) (σ z.2 F)
        = σ (z.2 * (z.2⁻¹ * colE c (p + 1) z.1 * z.2)) F := by
          rw [map_mul σ z.2, Module.End.mul_apply, map_mul, map_mul, Module.End.mul_apply,
            Module.End.mul_apply]
          rw [← Module.End.mul_apply (σ z.2), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ z.2 F := by rw [map_mul, Module.End.mul_apply, hz']
  obtain ⟨B, hB, hBout⟩ := exists_box hψ {β | ∀ w ∈ Ω, σ (colE c (p + 1) β) (σ w F) = σ w F} hfix
  refine ⟨B, hB, fun l hl w hw u hu => ?_⟩
  obtain ⟨β, hβ, hne⟩ := hBout u hu
  obtain ⟨hN, hsum⟩ := ExchangeSupport.conj_col (k := k) (n := n) hp hc u β
  have key := hl _ hN (σ (rowE c p u) (σ w F))
  rw [hsum] at key
  have lhs : σ (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹) (σ (rowE c p u) (σ w F)) =
      σ (rowE c p u) (σ w F) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hβ w hw]
  rw [lhs] at key
  have hne' : (ψ (u ⬝ᵥ β) : ℂ) ≠ 1 := by
    intro h
    exact hne (Subtype.ext (by simpa using h))
  have : (1 - (ψ (u ⬝ᵥ β) : ℂ)) * l (σ (rowE c p u) (σ w F)) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne'
  · exact h

end GlobalTheory.RootEx.RowSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatDistributionEqZeroBaire
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.BaireDistribution

section General

variable {X : Type} [TopologicalSpace X]

theorem indicator_mem {C : Set X} (hC : IsClopen C) (φ : SB X) : C.indicator φ.1 ∈ SB X := by
  refine ⟨?_, φ.2.2.mono fun x hx => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨U, hU, hxU, h⟩ := φ.2.1.exists_open x
      exact ⟨C ∩ U, hC.2.inter hU, ⟨hx, hxU⟩, fun y hy => by
        rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hx, h y hy.2]⟩
    · exact ⟨Cᶜ, hC.1.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · rw [Set.support_indicator] at hx
    exact hx.2

theorem isCompact_support (φ : SB X) : IsCompact (Function.support φ.1) := by
  have h : IsClosed (Function.support φ.1) := by
    have := (φ.2.1 {0}).isClosed_compl
    convert this using 1
    ext x
    simp
  have h2 := φ.2.2.isCompact
  rwa [tsupport, h.closure_eq] at h2

theorem glue (D : SB X →ₗ[ℂ] ℂ) (𝒞 : Set X → Prop) (hcl : ∀ C, 𝒞 C → IsClopen C) (h0 : 𝒞 ∅)
    (hu : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∪ C')) (hi : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∩ C'))
    (hd : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C \ C')) (φ : SB X)
    (h : ∀ x ∈ Function.support φ.1, ∃ C, 𝒞 C ∧ x ∈ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) : D φ = 0 := by
  have key : ∃ C, 𝒞 C ∧ Function.support φ.1 ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0 := by
    refine (isCompact_support φ).induction_on (p := fun s => ∃ C, 𝒞 C ∧ s ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, h0, subset_rfl, fun C' _ hC' ψ hψ => ?_⟩
      have : ψ = 0 := Subtype.ext (by rw [hψ, Set.subset_empty_iff.1 hC']; ext; simp)
      rw [this, map_zero]
    · rintro s t hst ⟨C, h1, h2, h3⟩
      exact ⟨C, h1, hst.trans h2, h3⟩
    · rintro s t ⟨C, h1, h2, h3⟩ ⟨E, e1, e2, e3⟩
      refine ⟨C ∪ E, hu _ _ h1 e1, Set.union_subset_union h2 e2, fun C' hC' hs ψ hψ => ?_⟩
      have a1 := h3 (C' ∩ C) (hi _ _ hC' h1) Set.inter_subset_right
        ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ rfl
      have a2 := e3 (C' \ C) (hd _ _ hC' h1) (fun x hx => (hs hx.1).resolve_left hx.2)
        ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ rfl
      have : ψ = ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ +
          ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ := by
        apply Subtype.ext
        rw [hψ]
        ext x
        by_cases a : x ∈ C' <;> by_cases b : x ∈ C <;> simp [Set.indicator, a, b]
      rw [this, map_add (f := _), a1, a2, add_zero]
    · intro x hx
      obtain ⟨C, h1, h2, h3⟩ := h x hx
      exact ⟨C, mem_nhdsWithin_of_mem_nhds ((hcl _ h1).2.mem_nhds h2), C, h1, subset_rfl, h3⟩
  obtain ⟨C, h1, h2, h3⟩ := key
  exact h3 C h1 subset_rfl φ (Set.indicator_eq_self.2 h2).symm

end General

section Group

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClopen_of_invariant {K : Subgroup G} (hK : IsOpen (K : Set G)) {C : Set G}
    (hC : ∀ a ∈ K, ∀ b ∈ K, ∀ g, a * g * b ∈ C ↔ g ∈ C) : IsClopen C := by
  have aux : ∀ S : Set G, (∀ a ∈ K, ∀ g ∈ S, a * g ∈ S) → IsOpen S := by
    intro S hS
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun y => y * g⁻¹) ⁻¹' K, fun y hy => ?_, hK.preimage (by fun_prop), by simp⟩
    simpa using hS _ hy g hg
  refine ⟨isOpen_compl_iff.1 (aux _ fun a ha g hg h => hg ?_), aux _ fun a ha g hg => ?_⟩
  · exact (hC a ha 1 K.one_mem g).1 (by simpa using h)
  · simpa using (hC a ha 1 K.one_mem g).2 hg


omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem doubleCoset_invariant (K : Subgroup G) (x : G) : ∀ a ∈ K, ∀ b ∈ K, ∀ g,
    a * g * b ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} ↔
      g ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} := by
  intro a ha b hb g
  constructor
  · rintro ⟨c, hc, d, hd, h⟩
    refine ⟨a⁻¹ * c, K.mul_mem (K.inv_mem ha) hc, d * b⁻¹, K.mul_mem hd (K.inv_mem hb), ?_⟩
    have : g = a⁻¹ * (a * g * b) * b⁻¹ := by group
    rw [this, h]; group
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, K.mul_mem ha hc, d * b, K.mul_mem hd hb, by group⟩

theorem exists_nhds_invariant (φ : SB G) :
    ∃ U ∈ nhds (1 : G), ∀ a ∈ U, ∀ b ∈ U, ∀ g, φ.1 (a * g * b) = φ.1 g := by
  have h1 := GlobalTheory.OpTrace.isOpen_leftStabilizer φ.2.1 φ.2.2
  have h2 := GlobalTheory.OpTrace.isOpen_leftStabilizer (f := fun g => φ.1 g⁻¹)
    (φ.2.1.comp_continuous continuous_inv) (φ.2.2.comp_homeomorph (Homeomorph.inv G))
  refine ⟨_, (h1.inter h2).mem_nhds ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩,
    fun a ha b hb g => ?_⟩
  have e1 : ∀ g, φ.1 (a * g) = φ.1 g := ha.1
  have e2 : ∀ g, φ.1 (b * g)⁻¹ = φ.1 g⁻¹ := hb.2
  rw [mul_assoc, e1]
  simpa using (e2 (g * b)⁻¹).symm

end Group

theorem eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by
  intro G _ _ _ _ _ ι _ K hK hb D hD
  let O : Set G := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ φ : SB G, Function.support φ.1 ⊆ W → D φ = 0}
  have hO : IsOpen O := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, h1, h2, h3⟩
    exact ⟨W, fun y hy => ⟨W, h1, hy, h3⟩, h1, h2⟩
  have h1 : ∀ φ : SB G, Function.support φ.1 ⊆ O → D φ = 0 := by
    intro φ hφ
    refine glue D IsClopen (fun _ h => h) isClopen_empty (fun _ _ => IsClopen.union)
      (fun _ _ => IsClopen.inter) (fun _ _ => IsClopen.diff) φ fun x hx => ?_
    obtain ⟨W, w1, w2, w3⟩ := hφ hx
    obtain ⟨i, -⟩ := hD x
    obtain ⟨m, hm⟩ := hb i ((fun y => x * y) ⁻¹' W)
      ((w1.preimage (by fun_prop)).mem_nhds (by simpa using w2))
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' K i m, IsClopen.preimage
      ⟨(K i m).isClosed_of_isOpen (hK i m).1, (hK i m).1⟩ (by fun_prop), by simp,
      fun C' _ hC' ψ hψ => w3 ψ fun y hy => ?_⟩
    rw [hψ, Set.support_indicator] at hy
    simpa using hm (hC' hy.1)
  suffices hall : ∀ x, x ∈ O from LinearMap.ext fun φ => h1 φ fun x _ => hall x
  by_contra hne
  push_neg at hne
  let Z : ι → Set G := fun i => {x | ∀ (m : ℕ) (φ : SB G), φ.1 =
    Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0}
  haveI : LocallyCompactSpace (Oᶜ : Set G) := hO.isClosed_compl.locallyCompactSpace
  haveI : Nonempty (Oᶜ : Set G) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨i, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (X := (Oᶜ : Set G))
    (f := fun i => Subtype.val ⁻¹' closure (Z i))
    (fun i => isClosed_closure.preimage continuous_subtype_val)
    (Set.eq_univ_of_forall fun x => by
      obtain ⟨i, hi⟩ := hD x.1
      exact Set.mem_iUnion.2 ⟨i, subset_closure hi⟩)
  obtain ⟨t, t1, t2, t3⟩ := mem_interior.1 hy
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 t2
  refine y.2 ⟨W, hW, t3, fun φ hφ => ?_⟩
  obtain ⟨U, hU, hinv⟩ := exists_nhds_invariant φ
  obtain ⟨m, hm⟩ := hb i U hU
  refine glue D (fun C => ∀ a ∈ K i m, ∀ b ∈ K i m, ∀ g, a * g * b ∈ C ↔ g ∈ C)
    (fun C hC => isClopen_of_invariant (hK i m).1 hC) (by simp)
    (fun C C' h h' a ha b hb g => or_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (not_congr (h' a ha b hb g))) φ
    fun x hx => ⟨_, doubleCoset_invariant (K i m) x,
      ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩, fun C hC hs ψ hψ => ?_⟩
  have hval : ∀ g ∈ C, φ.1 g = φ.1 x := fun g hg => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
    exact hinv a (hm ha) b (hm hb) x
  by_cases hCO : C ⊆ O
  · refine h1 ψ fun g hg => hCO ?_
    rw [hψ, Set.support_indicator] at hg
    exact hg.1
  obtain ⟨w, w1, w2⟩ := Set.not_subset.1 hCO
  have w3 : w ∈ closure (Z i) := t1 (show (⟨w, w2⟩ : (Oᶜ : Set G)) ∈ Subtype.val ⁻¹' W from
    hφ (show φ.1 w ≠ 0 by rw [hval w w1]; exact hx))
  obtain ⟨z, z1, z2⟩ := mem_closure_iff.1 w3 C (isClopen_of_invariant (hK i m).1 hC).2 w1
  have hCz : C = {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * z * b} := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
      obtain ⟨c, hc, d, hd, rfl⟩ := hs z1
      exact ⟨a * c⁻¹, mul_mem ha (inv_mem hc), d⁻¹ * b, mul_mem (inv_mem hd) hb, by group⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact (hC a ha b hb z).2 z1
  have hx' : φ.1 x ≠ 0 := hx
  have := z2 m ((φ.1 x)⁻¹ • ψ) (by
    rw [← hCz, Submodule.coe_smul, hψ]
    ext g
    by_cases hg : g ∈ C
    · simp [Set.indicator_of_mem hg, hval g hg, hx']
    · simp [Set.indicator_of_notMem hg])
  simpa [hx'] using this

end GlobalTheory.BaireDistribution
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.CuspMax

theorem subsingleton_jacquet_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (g : G) (h : ∀ u ∈ N, g * u * g⁻¹ ∈ N')
    (hN : Subsingleton (Jacquet π N)) : Subsingleton (Jacquet π N') := by
  have h1 : twKer π N 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hN
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have h2 : twKer π N 1 ≤ (twKer π N' 1).comap (π g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    refine Submodule.subset_span ⟨⟨_, h u u.2⟩, π g w, ?_⟩
    simp [← Module.End.mul_apply, ← map_mul]
  have h3 : π g⁻¹ v ∈ twKer π N 1 := h1 ▸ Submodule.mem_top
  have h4 : π g (π g⁻¹ v) ∈ twKer π N' 1 := h2 h3
  simpa [← Module.End.mul_apply, ← map_mul] using h4

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases (not_lt.1 hij).lt_or_eq with h | h
    · rw [mem_parab.1 h1 i j h, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
      obtain rfl : b = a := by simpa using h
      rw [h2]
      simp [Matrix.one_apply]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
    · rw [h i j hij.not_gt, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp [Matrix.one_apply]

theorem unipRad_ne_bot_iff [Nontrivial R] {e : (Σ a, m a) ≃ n} :
    unipRad R e ≠ ⊥ ↔ ∃ i j, blk e i < blk e j := by
  constructor
  · intro h
    by_contra hc
    refine h ((Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_)
    ext i j
    exact mem_unipRad_iff_entries.1 hu i j fun hij => hc ⟨i, j, hij⟩
  · rintro ⟨i, j, hij⟩ hb
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    let u : GL n R := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩
    have hu : u ∈ unipRad R e := mem_unipRad_iff_entries.2 fun a b hab => by
      show Matrix.transvection i j (1 : R) a b = _
      rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hab hij
    rw [hb, Subgroup.mem_bot] at hu
    have : Matrix.transvection i j (1 : R) i j = (1 : Matrix n n R) i j :=
      congrArg (fun g : GL n R => (g : Matrix n n R) i j) hu
    simp [Matrix.transvection] at this

theorem subsingleton_jacquet_of_perm {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n R) V) {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n} (σ : Equiv.Perm n)
    (h : ∀ i j, blk e (σ i) < blk e (σ j) → blk e' i < blk e' j)
    (hN : Subsingleton (Jacquet π (unipRad R e))) : Subsingleton (Jacquet π (unipRad R e')) := by
  let g : GL n R := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
  refine subsingleton_jacquet_of_conj π g (fun u hu => ?_) hN
  refine mem_unipRad_iff_entries.2 fun i j hij => ?_
  show (σ.toPEquiv.toMatrix * (u : Matrix n n R) * σ.symm.toPEquiv.toMatrix : Matrix n n R) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.submatrix_apply, id, Equiv.symm_symm]
  rw [mem_unipRad_iff_entries.1 hu _ _ fun hh => hij (h i j hh)]
  simp [Matrix.one_apply]

theorem isCuspidal_iff_maximal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal π ↔ IsSmooth π ∧ ∀ (r t : ℕ) (h : r + t = N), 0 < r → 0 < t →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h)))) := by
  refine and_congr_right fun _ => ⟨fun H r t h hr ht => ?_, fun H s d e he => ?_⟩
  · let f : Fin N → Fin 2 := fun i => if blk (two (stdSum h)) i then 1 else 0
    let e : (Σ a : Fin 2, Fin (Fintype.card {i // f i = a})) ≃ Fin N :=
      (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // f i = a}).symm).trans
        (Equiv.sigmaFiberEquiv f)
    have hb : ∀ i, blk e i = f i := fun i => rfl
    have hlt : ∀ i j, blk e i < blk e j ↔ blk (two (stdSum h)) i < blk (two (stdSum h)) j := by
      intro i j
      rw [hb, hb]
      simp only [f]
      cases blk (two (stdSum h)) i <;> cases blk (two (stdSum h)) j <;> decide
    refine subsingleton_jacquet_of_perm π (e := e) 1 (fun i j hij => (hlt i j).1 hij)
      (H 2 _ e (unipRad_ne_bot_iff.2 ⟨two (stdSum h) ⟨false, ⟨0, hr⟩⟩, two (stdSum h) ⟨true, ⟨0, ht⟩⟩,
        (hlt _ _).2 ?_⟩))
    rw [blk_apply, blk_apply]
    decide
  · obtain ⟨i₀, j₀, hij⟩ := unipRad_ne_bot_iff.1 he
    let p : Fin N → Prop := fun i => blk e i ≤ blk e i₀
    have hsum : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} = N := by
      rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl p), Fintype.card_fin]
    let τ : Fin (Fintype.card {i // p i}) ⊕ Fin (Fintype.card {i // ¬ p i}) ≃ Fin N :=
      (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl p)
    refine subsingleton_jacquet_of_perm π (τ.symm.trans (stdSum hsum)) (fun i j hh => ?_)
      (H _ _ hsum (Fintype.card_pos_iff.2 ⟨⟨i₀, le_rfl⟩⟩) (Fintype.card_pos_iff.2 ⟨⟨j₀, hij.not_ge⟩⟩))
    obtain ⟨i, rfl⟩ := τ.surjective i
    obtain ⟨j, rfl⟩ := τ.surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hh
    rcases i with i | i <;> rcases j with j | j
    · rw [← two_false, ← two_false, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · have h1 : p (τ (.inl i)) := ((Fintype.equivFin {i // p i}).symm i).2
      have h2 : ¬ p (τ (.inr j)) := ((Fintype.equivFin {i // ¬ p i}).symm j).2
      exact lt_of_le_of_lt h1 (not_le.1 h2)
    · rw [← two_false, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · rw [← two_true, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)

end GlobalTheory.SmGL.CuspMax
end

