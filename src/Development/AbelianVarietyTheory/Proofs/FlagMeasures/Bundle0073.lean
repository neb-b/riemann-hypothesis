module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassProdEqMul
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.ProdMass

noncomputable def wt (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) (x : α) : ℝ≥0∞ :=
  if x ∈ X then ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ else 0

theorem orbMass_eq (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) :
    orbMass G X = ∑' q : MulAction.orbitRel.Quotient G α, wt G X (Quotient.out q) := by
  unfold orbMass orbSum
  have := tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
  refine this.trans (tsum_congr fun q => ?_)
  simp [Set.indicator, wt]

theorem wt_rel (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) (hX : Stable G X)
    {x y : α} (h : MulAction.orbitRel G α x y) : wt G X x = wt G X y := by
  have hc : ENat.card (MulAction.stabilizer G x) = ENat.card (MulAction.stabilizer G y) :=
    ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv
  obtain ⟨g, hg⟩ := h
  simp only at hg
  have hm : x ∈ X ↔ y ∈ X := by
    constructor
    · intro hx
      have := hX g⁻¹ x hx
      rwa [← hg, inv_smul_smul] at this
    · intro hy
      rw [← hg]; exact hX g y hy
  unfold wt
  rw [hc]
  simp only [hm]

variable {Γ G G' α β : Type} [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β]
  [MulAction Γ (α × β)] (φ : Γ ≃* G × G')
  (hφ : ∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2))

include hφ in
theorem rel_iff (p q : α × β) : MulAction.orbitRel Γ (α × β) p q ↔
    MulAction.orbitRel G α p.1 q.1 ∧ MulAction.orbitRel G' β p.2 q.2 := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    rw [hφ]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩
    refine ⟨φ.symm (g, g'), ?_⟩
    rw [hφ]
    simp [hg, hg']

def stabEquiv (p : α × β) : MulAction.stabilizer Γ p ≃
    MulAction.stabilizer G p.1 × MulAction.stabilizer G' p.2 where
  toFun γ := (⟨(φ γ).1, by
      have := hφ γ p
      rw [γ.2] at this
      exact (congrArg Prod.fst this).symm⟩, ⟨(φ γ).2, by
      have := hφ γ p
      rw [γ.2] at this
      exact (congrArg Prod.snd this).symm⟩)
  invFun g := ⟨φ.symm (g.1, g.2), by
    rw [MulAction.mem_stabilizer_iff, hφ]
    have h1 : (g.1 : G) • p.1 = p.1 := g.1.2
    have h2 : (g.2 : G') • p.2 = p.2 := g.2.2
    simp [h1, h2]⟩
  left_inv γ := by simp
  right_inv g := by simp

include hφ in
theorem wt_prod (X : Set α) (Y : Set β) (p : α × β) :
    wt Γ (X ×ˢ Y) p = wt G X p.1 * wt G' Y p.2 := by
  unfold wt
  by_cases h1 : p.1 ∈ X <;> by_cases h2 : p.2 ∈ Y <;> simp only [Set.mem_prod, h1, h2, and_self,
    and_true, and_false, if_true, if_false, mul_zero, zero_mul]
  rw [ENat.card_congr (stabEquiv φ hφ p), ENat.card_prod, ENat.toENNReal_mul, ENNReal.mul_inv]
  · left
    exact_mod_cast (ENat.card_pos (α := MulAction.stabilizer G p.1)).ne'
  · right
    exact_mod_cast (ENat.card_pos (α := MulAction.stabilizer G' p.2)).ne'

noncomputable def orbEquiv : MulAction.orbitRel.Quotient Γ (α × β) ≃
    MulAction.orbitRel.Quotient G α × MulAction.orbitRel.Quotient G' β where
  toFun := Quotient.lift (fun p => (Quotient.mk _ p.1, Quotient.mk _ p.2)) fun p q h => by
    obtain ⟨h1, h2⟩ := (rel_iff φ hφ p q).1 h
    exact Prod.ext (Quotient.sound h1) (Quotient.sound h2)
  invFun q := Quotient.mk _ (Quotient.out q.1, Quotient.out q.2)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h p =>
      refine Quotient.sound ((rel_iff φ hφ _ _).2 ⟨?_, ?_⟩)
      · exact Quotient.mk_out (s := MulAction.orbitRel G α) p.1
      · exact Quotient.mk_out (s := MulAction.orbitRel G' β) p.2
  right_inv q := by
    simp

theorem orbMass_prod : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α]
    [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β),
    (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y →
    (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) →
    orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by
  intro Γ G G' α β _ _ _ _ _ _ φ X Y hφ hX hY _ _
  have hXY : Stable Γ (X ×ˢ Y) := by
    intro γ p hp
    rw [hφ]
    exact ⟨hX _ _ hp.1, hY _ _ hp.2⟩
  rw [orbMass_eq, orbMass_eq, orbMass_eq, ← (orbEquiv φ hφ).symm.tsum_eq, ENNReal.tsum_prod',
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [← wt_prod φ hφ X Y (Quotient.out a, Quotient.out b)]
  exact wt_rel Γ _ hXY (Quotient.mk_out (s := MulAction.orbitRel Γ (α × β)) _)

end GlobalTheory.Mass.ProdMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumEqSumOrbitReps
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass


open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.orbSum_eq_sum_reps : ∀ (G α : Type) [Group G] [MulAction G α]
    (X : Set α) (N : α → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → (∀ (g : G) x, N (g • x) = N x) →
    ∀ s : Finset α, (∀ x ∈ s, x ∈ X) → (∀ x ∈ X, ∃! y, y ∈ s ∧ ∃ g : G, g • y = x) →
    _root_.GlobalTheory.Mass.orbSum G X N =
      ∑ x ∈ s, ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
  intro G α _ _ X N hX hN s hs huniq
  have hX' : ∀ (g : G), ∀ x ∈ X, g • x ∈ X := hX
  unfold _root_.GlobalTheory.Mass.orbSum
  have hout : ∀ x : α, ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G α) x).out := fun x =>
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G α) x))))
  have hterm : ∀ x : α,
      ((ENat.card (MulAction.stabilizer G (Quotient.mk (MulAction.orbitRel G α) x).out) : ℕ∞) :
          ℝ≥0∞)⁻¹ * N (Quotient.mk (MulAction.orbitRel G α) x).out
        = ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
    intro x
    obtain ⟨g, hg⟩ := hout x
    rw [← hg, hN,
      ENat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv.symm]
  let e : {x // x ∈ s} → {q : MulAction.orbitRel.Quotient G α // q.out ∈ X} := fun x =>
    ⟨Quotient.mk _ x.1, by obtain ⟨g, hg⟩ := hout x.1; rw [← hg]; exact hX' g _ (hs _ x.2)⟩
  have he_inj : Function.Injective e := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hq : Quotient.mk (MulAction.orbitRel G α) x = Quotient.mk _ y := congrArg Subtype.val hxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))
    obtain ⟨z, -, hz⟩ := huniq x (hs x hx)
    have h1 := hz x ⟨hx, 1, one_smul G x⟩
    have h2 := hz y ⟨hy, g, hg⟩
    exact Subtype.ext (h1.trans h2.symm)
  have he_surj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨y, ⟨hy, g, hg⟩, -⟩ := huniq q.out hq
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    show Quotient.mk _ y = q
    calc Quotient.mk (MulAction.orbitRel G α) y = Quotient.mk _ q.out :=
          Quotient.sound (MulAction.orbitRel_apply.mpr
            (MulAction.mem_orbit_iff.mpr ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩))
      _ = q := Quotient.out_eq q
  rw [← (Equiv.ofBijective e ⟨he_inj, he_surj⟩).tsum_eq, tsum_fintype, ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun x _ => hterm x.1

end GlobalTheory.Mass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditive
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbMono

theorem orbSum_eq (G α : Type) [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) :
    orbSum G X N = ∑' q : MulAction.orbitRel.Quotient G α,
      if Quotient.out q ∈ X then
        ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q)
      else 0 := by
  exact (tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ *
      N (Quotient.out q))).trans (tsum_congr fun q => by simp [Set.indicator_apply])

theorem main : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  intro G α _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y N N' hXY hN
    simp only [orbSum_eq]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · rw [if_pos hq, if_pos (hXY hq)]
      gcongr
      exact hN _ hq
    · rw [if_neg hq]
      exact zero_le
  · intro X B
    simp only [orbMass, orbSum]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun q => by rw [mul_one, mul_comm]
  · intro ι s X Xi N hX
    simp only [orbSum_eq]
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (hX hq)
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => zero_le) hi)
      simp [hq, hqi]
    · rw [if_neg hq]
      exact zero_le
  · intro X s hs
    have key : ∀ q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ∃ y : s, (Quotient.mk _ (y : α) : MulAction.orbitRel.Quotient G α) = q.1 := by
      rintro ⟨q, hq⟩
      obtain ⟨y, hy, g, hg⟩ := hs _ hq
      refine ⟨⟨y, hy⟩, ?_⟩
      exact (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g⁻¹, by simp [← hg]⟩)).trans
        (Quotient.out_eq q)
    choose φ hφ using key
    have hinj : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      rw [← hφ a, ← hφ b, h]
    calc orbMass G X
        = ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := rfl
      _ ≤ ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            (fun _ : s => (1 : ℝ≥0∞)) (φ q) := by
          refine ENNReal.tsum_le_tsum fun q => ?_
          rw [mul_one]
          apply ENNReal.inv_le_one.2
          have h1 : (1 : ℕ∞) ≤ ENat.card (MulAction.stabilizer G (Quotient.out q.1)) :=
            (ENat.one_le_card_iff_nonempty _).2 ⟨1⟩
          exact_mod_cast h1
      _ ≤ ∑' _ : s, (1 : ℝ≥0∞) := (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective hinj _); exact _root_.le_rfl)
      _ = s.encard := ENNReal.tsum_set_one s
  · intro X N N'
    simp only [orbSum]
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun q => mul_add _ _ _

end GlobalTheory.Mass.OrbMono
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumRestrictSlice
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Slice

theorem exists_smul_eq_out (G : Type) {α : Type} [Group G] [MulAction G α] (x : α) :
    ∃ g : G, g • x = Quotient.out (Quotient.mk (MulAction.orbitRel G α) x) := by
  have h : (MulAction.orbitRel G α) (Quotient.out (Quotient.mk (MulAction.orbitRel G α) x)) x :=
    Quotient.exact (Quotient.out_eq _)
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)

theorem card_stabilizer_smul (G : Type) {α : Type} [Group G] [MulAction G α] (g : G) (x : α) :
    ENat.card (MulAction.stabilizer G (g • x)) = ENat.card (MulAction.stabilizer G x) := by
  have h : (MulAction.orbitRel G α) (g • x) x :=
    MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g)
  exact ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

theorem card_stabilizer_subgroup {G α : Type} [Group G] [MulAction G α] (H : Subgroup G) (x : α)
    (h : ∀ g : G, g • x = x → g ∈ H) :
    ENat.card (MulAction.stabilizer H x) = ENat.card (MulAction.stabilizer G x) :=
  ENat.card_congr
    { toFun := fun a => ⟨(a.1 : G), a.2⟩
      invFun := fun a => ⟨⟨a.1, h a.1 a.2⟩, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem orbSum_restrict : ∀ (G α : Type) [Group G] [MulAction G α] (H : Subgroup G) (X X₀ : Set α) (N : α → ℝ≥0∞), X₀ ⊆ X → Stable G X → Stable H X₀ → (∀ (g : G) x, N (g • x) = N x) → (∀ x ∈ X, ∃ g : G, g • x ∈ X₀) → (∀ (g : G), ∀ x ∈ X₀, g • x ∈ X₀ → g ∈ H) → orbSum H X₀ N = orbSum G X N := by
  intro G α _ _ H X X₀ N hsub hX hX₀ hN hmeet hret
  let f : {q : MulAction.orbitRel.Quotient H α // Quotient.out q ∈ X₀} →
      {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X} := fun q =>
    ⟨Quotient.mk (MulAction.orbitRel G α) (Quotient.out q.1), by
      obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
      rw [← hg]
      exact hX g _ (hsub q.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (MulAction.orbitRel G α) (Quotient.out a.1) (Quotient.out b.1) :=
      Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h1)
    have hgH : g ∈ H := hret g _ b.2 (hg ▸ a.2)
    have h2 : (MulAction.orbitRel H α) (Quotient.out a.1) (Quotient.out b.1) :=
      MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨g, hgH⟩, hg⟩)
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq b.1]
    exact Quotient.sound h2
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hmeet _ b.2
    obtain ⟨k, hk⟩ := exists_smul_eq_out H (g • Quotient.out b.1)
    refine ⟨⟨Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1), ?_⟩, ?_⟩
    · rw [← hk]; exact hX₀ k _ hg
    · apply Subtype.ext
      show Quotient.mk (MulAction.orbitRel G α)
        (Quotient.out (Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1))) = b.1
      rw [← hk]
      conv_rhs => rw [← Quotient.out_eq b.1]
      apply Quotient.sound
      refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨(k : G) * g, ?_⟩)
      rw [mul_smul]; rfl
  unfold orbSum
  rw [← (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
  have e : Quotient.out ((Equiv.ofBijective f ⟨hinj, hsurj⟩) q).1 = g • Quotient.out q.1 := hg.symm
  rw [e, hN, card_stabilizer_smul, card_stabilizer_subgroup H _
    (fun a ha => hret a _ q.2 (by rw [ha]; exact q.2))]

end GlobalTheory.Mass.Slice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariant
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbTransport

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma exists_smul_eq_orbit_out {G α : Type} [Group G] [MulAction G α] (y : α) :
    ∃ g : G, g • y = (Quotient.mk (orbitRel G α) y).out := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G α) y
  exact ⟨g, hg⟩

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma card_stabilizer_smul_eq' {G α : Type} [Group G] [MulAction G α] (g : G) (a : α) :
    ENat.card (stabilizer G (g • a)) = ENat.card (stabilizer G a) :=
  (ENat.card_congr (stabilizerEquivStabilizer (g := g) rfl).toEquiv).symm


open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
theorem _root_.GlobalTheory.Mass.OrbTransport.main : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → _root_.GlobalTheory.Mass.orbSum G X (fun x => N (f x)) = _root_.GlobalTheory.Mass.orbSum G' Y N := by
  intro G G' α β _ _ _ _ φ f X Y N hX hY hf hequiv hN
  have hcard : ∀ x ∈ X, ENat.card (stabilizer G' (f x)) = ENat.card (stabilizer G x) := by
    intro x hx
    refine (ENat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun g => ?_)).symm
    simp only [mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← hequiv g x hx]
    exact ⟨fun h => by rw [h], fun h => hf.injOn (hX g x hx) hx h⟩
  have hout : ∀ q : {q : orbitRel.Quotient G α // q.out ∈ X},
      (Quotient.mk (orbitRel G' β) (f q.1.out)).out ∈ Y := by
    intro q
    obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
    rw [← hg]
    exact hY g _ (hf.mapsTo q.2)
  let F : {q : orbitRel.Quotient G α // q.out ∈ X} → {q : orbitRel.Quotient G' β // q.out ∈ Y} :=
    fun q => ⟨Quotient.mk _ (f q.1.out), hout q⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
      obtain ⟨g', hg'⟩ := Quotient.exact (congrArg Subtype.val h)
      apply Subtype.ext
      show q₁ = q₂
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      apply Quotient.sound
      refine ⟨φ.symm g', ?_⟩
      apply hf.injOn (hX _ _ h₂) h₁
      rw [hequiv _ _ h₂, MulEquiv.apply_symm_apply]
      exact hg'
    · rintro ⟨q', hq'⟩
      obtain ⟨x, hx, hfx⟩ := hf.surjOn hq'
      obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G) x
      have hmem : (Quotient.mk (orbitRel G α) x).out ∈ X := by rw [← hg]; exact hX g x hx
      refine ⟨⟨Quotient.mk _ x, hmem⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (f (Quotient.mk (orbitRel G α) x).out) = q'
      rw [← Quotient.out_eq q', ← hg, hequiv g x hx, hfx]
      exact Quotient.sound ⟨φ g, rfl⟩
  unfold _root_.GlobalTheory.Mass.orbSum
  rw [← (Equiv.ofBijective F hF).tsum_eq]
  congr 1
  funext q
  obtain ⟨g', hg'⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
  show _ = (ENat.card (stabilizer G' (Quotient.mk (orbitRel G' β) (f q.1.out)).out) : ℝ≥0∞)⁻¹ *
    N (Quotient.mk (orbitRel G' β) (f q.1.out)).out
  rw [← hg', card_stabilizer_smul_eq', hN, hcard _ q.2]

end GlobalTheory.Mass.OrbTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumOverDataTermCountEqLatticeMass
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sumData_nT_eq_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (C : Set S.FrP) (P : S.Datum → Submodule L.O S.V → Prop), (∀ h ∈ S.H0, ∀ d Λ, S.IsTerm d Λ → P d Λ → P (h • d) (h • Λ)) → (S.sumData fun d => S.nT d C (P d)) = ∑' o : MulAction.orbitRel.Quotient S.H0 (Submodule L.O S.V), if ∃ d, S.IsTerm d o.out ∧ P d o.out ∧ S.Fr d o.out = C then ENNReal.ofReal (invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV o.out)) else 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S C P hP
  let π : Submodule L.O S.V → S.Datum := fun Λ =>
    if H : ∃ d, S.IsTerm d Λ then H.choose else (⊥, ⊥, ∅)
  have hπ : ∀ d Λ, S.IsTerm d Λ → π Λ = d := by
    intro d Λ hd
    have H : ∃ d, S.IsTerm d Λ := ⟨d, hd⟩
    simp only [π, dif_pos H]
    exact (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hd).2.2.2.2.2.2.2 _ H.choose_spec
  obtain ⟨v1, v2⟩ := GlobalTheory.HL.Frames.stab_commensurable_invVol_smul L r k S
  have hlat : ∀ d Λ, S.IsTerm d Λ → IsLat L Λ := fun d Λ hd =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hd).1.1
  have key := mass_orbits_eq_tsum_fiber S.H0 S.complementReferenceCompactSubgroup
    (fun Λ : Submodule L.O S.V => ∃ d, S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C) π inf_le_left
    (by
      rintro h hh Λ ⟨d, hd, hp, hc⟩
      obtain ⟨a1, -, -, -, -, a6⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hd h hh
      refine ⟨⟨h • d, a1, hP h hh d Λ hd hp, a6.trans hc⟩, ?_, (v1 Λ (hlat d Λ hd)).2.2 h hh⟩
      rw [hπ _ _ a1, hπ _ _ hd])
    (by
      rintro Λ ⟨d, hd, -, -⟩
      rw [hπ _ _ hd]
      exact ⟨(v1 Λ (hlat d Λ hd)).1, (v1 Λ (hlat d Λ hd)).2.1, (v2 d Λ hd).1, (v2 d Λ hd).2⟩)
  refine Eq.trans ?_ (key.symm.trans ?_)
  · unfold Frames.sumData Frames.nu Frames.nT
    refine tsum_congr fun c => ?_
    refine congrArg (fun s : Set (Submodule L.O S.V) => _ * ((s.encard : ℕ∞) : ℝ≥0∞)) ?_
    ext Λ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hd, hp, hc⟩
      exact ⟨⟨_, hd, hp, hc⟩, hπ _ _ hd⟩
    · rintro ⟨⟨d, hd, hp, hc⟩, e⟩
      rw [hπ _ _ hd] at e
      rw [← e]
      exact ⟨hd, hp, hc⟩
  · refine tsum_congr fun o => ?_
    congr

end GlobalTheory.HL
end

