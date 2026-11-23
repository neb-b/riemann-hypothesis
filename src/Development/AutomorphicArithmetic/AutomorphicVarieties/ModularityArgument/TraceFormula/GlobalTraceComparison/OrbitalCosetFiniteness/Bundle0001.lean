module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import GroundTheory.AutomorphicForms.Cartan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.AvgConst
section
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private lemma avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have hS : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k
    simp [GlobalTheory.BCT.rStab]
  unfold GlobalTheory.BCT.avg
  rw [hS]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
  simp [finsum_unique]

private lemma avg_orbit {G : Type} [Group G] (K : Subgroup G) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (δ x : G) (h : G → ℂ) (hh : ∀ k ∈ K, ∀ y, h (k * y) = h y ∧ h (y * k) = h y) :
    GlobalTheory.BCT.avg (fun k : K => h ((x * k)⁻¹ * δ * θ (x * k))) = h (x⁻¹ * δ * θ x) := by
  have hc : (fun k : K => h ((x * k)⁻¹ * δ * θ (x * k))) = fun _ : K => h (x⁻¹ * δ * θ x) := by
    funext k
    have e : (x * (k : G))⁻¹ * δ * θ (x * k) = (k : G)⁻¹ * ((x⁻¹ * δ * θ x) * θ k) := by
      simp only [map_mul, mul_inv_rev, mul_assoc]
    rw [e, (hh _ (K.inv_mem k.2) _).1, (hh _ (hθ _ k.2) _).2]
  rw [hc, avg_const]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.twLin :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.TwLin := by
  intro G _ _ _ K _ _ θ hθ δ hfin f g c hf hg
  let W : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) → ℂ := fun q =>
    (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ)
  let y : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) → G := fun q =>
    (Quotient.out q)⁻¹ * δ * θ (Quotient.out q)
  have form : ∀ h : G → ℂ, (∀ k ∈ K, ∀ z, h (k * z) = h z ∧ h (z * k) = h z) →
      GlobalTheory.BCT.twOrb θ K δ h = ∑ᶠ q, W q * h (y q) := by
    intro h hh
    unfold GlobalTheory.BCT.twOrb
    exact finsum_congr fun q => by rw [avg_orbit K θ hθ δ _ h hh]
  have fin : ∀ h : G → ℂ, GlobalTheory.BCT.IsHecke K h → (Function.support fun q => W q * h (y q)).Finite := by
    intro h hh
    refine (hfin _ hh.1.isCompact).subset fun q hq => ?_
    exact subset_tsupport h (right_ne_zero_of_mul hq)
  have inv : ∀ k ∈ K, ∀ z, (fun u => f u + c * g u) (k * z) = (fun u => f u + c * g u) z ∧
      (fun u => f u + c * g u) (z * k) = (fun u => f u + c * g u) z := by
    intro k hk z
    simp only [(hf.2 k hk z).1, (hf.2 k hk z).2, (hg.2 k hk z).1, (hg.2 k hk z).2, and_self]
  have fin' : (Function.support fun q => c * (W q * g (y q))).Finite :=
    (fin g hg).subset fun q hq => right_ne_zero_of_mul hq
  rw [form _ inv, form f hf.2, form g hg.2, mul_finsum _ c,
    ← finsum_add_distrib (fin f hf) fin']
  exact finsum_congr fun q => by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.OrbFub
section
noncomputable section

open scoped Classical
open MulAction

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

section SlopeTestRemainingChoices

variable {T : Type} [Group T]

private abbrev omk (T : Type) [Group T] {Z : Type} [MulAction T Z] (z : Z) : orbitRel.Quotient T Z :=
  Quotient.mk (orbitRel T Z) z

private lemma omk_eq_iff {Z : Type} [MulAction T Z] (a b : Z) :
    omk T a = omk T b ↔ ∃ t : T, t • b = a := by
  constructor
  · intro h
    have h' : orbitRel T Z a b := Quotient.exact h
    rw [orbitRel_apply] at h'
    exact h'
  · intro h
    apply Quotient.sound
    show orbitRel T Z a b
    rw [orbitRel_apply]
    exact h

private lemma exists_smul_out {Z : Type} [MulAction T Z] (z : Z) :
    ∃ t : T, t • z = Quotient.out (omk T z) :=
  (omk_eq_iff _ _).1 (Quotient.out_eq (omk T z))

private lemma inv_out {Z α : Type} [MulAction T Z] (f : Z → α) (hf : ∀ (t : T) z, f (t • z) = f z) (z : Z) :
    f (Quotient.out (omk T z)) = f z := by
  obtain ⟨t, ht⟩ := exists_smul_out (T := T) z
  rw [← ht, hf]

private lemma relIndex_stab_smul {Z : Type} [MulAction T Z] (C : Subgroup T) [hC : C.Normal] (t : T) (z : Z) :
    (stabilizer T (t • z)).relIndex C = (stabilizer T z).relIndex C := by
  have hmap : C.map (MulAut.conj t).toMonoidHom = C := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hC.conj_mem b hb t
    · intro ha
      refine ⟨t⁻¹ * a * t, ?_, ?_⟩
      · simpa using hC.conj_mem a ha t⁻¹
      · simp [MulAut.conj_apply, mul_assoc]
  have h := Subgroup.relIndex_map_map_of_injective (stabilizer T z) C
    (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  rw [hmap] at h
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact h

private lemma stab_pair_le {X Y : Type} [MulAction T X] [MulAction T Y] (x : X) (y : Y) :
    stabilizer T ((x, y) : X × Y) ≤ stabilizer T x := by
  intro t ht
  rw [mem_stabilizer_iff] at ht ⊢
  exact congrArg Prod.fst ht

private lemma stab_swap {X Y : Type} [MulAction T X] [MulAction T Y] (x : X) (y : Y) :
    stabilizer T ((y, x) : Y × X) = stabilizer T ((x, y) : X × Y) := by
  ext t
  simp only [mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq]
  exact and_comm

private lemma card_fiber {X Y : Type} [MulAction T X] [MulAction T Y] (x : X) (y0 : Y) (S : Finset Y)
    (hS : ∀ y, omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y) → y ∈ S) :
    (S.filter fun y => omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y)).card =
      (stabilizer T ((x, y0) : X × Y)).relIndex (stabilizer T x) := by
  have h1 := index_stabilizer (stabilizer T x) y0
  have h2 : stabilizer (stabilizer T x) y0 = (stabilizer T ((x, y0) : X × Y)).subgroupOf (stabilizer T x) := by
    ext ⟨h, hh⟩
    rw [mem_stabilizer_iff] at hh
    simp only [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Prod.smul_mk, Prod.mk.injEq, hh, true_and]
    rfl
  have h3 : orbit (stabilizer T x) y0 =
      ((S.filter fun y => omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y) : Finset Y) : Set Y) := by
    ext y
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h, hh0⟩, rfl⟩
      have hh : h • x = x := mem_stabilizer_iff.1 hh0
      have e : omk T ((x, (⟨h, hh0⟩ : stabilizer T x) • y0) : X × Y) = omk T ((x, y0) : X × Y) :=
        (omk_eq_iff _ _).2 ⟨h, by simp [hh]⟩
      exact ⟨hS _ e, e⟩
    · rintro ⟨-, e⟩
      obtain ⟨t, ht⟩ := (omk_eq_iff _ _).1 e
      simp only [Prod.smul_mk, Prod.mk.injEq] at ht
      exact ⟨⟨t, mem_stabilizer_iff.2 ht.1⟩, ht.2⟩
  rw [Subgroup.relIndex, ← h2, h1, h3, Set.ncard_coe_finset]

private lemma one_side {X Y : Type} [MulAction T X] [MulAction T Y] (C : Subgroup T) [C.Normal]
    (hX : ∀ x : X, stabilizer T x ≤ C) (F : X → Y → ℂ)
    (hF : ∀ (t : T) x y, F (t • x) (t • y) = F x y) (hfin : ∀ x, {y | F x y ≠ 0}.Finite)
    (hP : {p : orbitRel.Quotient T (X × Y) | F (Quotient.out p).1 (Quotient.out p).2 ≠ 0}.Finite) :
    ∑ᶠ q : orbitRel.Quotient T X,
        (((stabilizer T (Quotient.out q)).relIndex C : ℕ) : ℂ) * ∑ᶠ y, F (Quotient.out q) y =
      ∑ᶠ p : orbitRel.Quotient T (X × Y),
        (((stabilizer T (Quotient.out p)).relIndex C : ℕ) : ℂ) * F (Quotient.out p).1 (Quotient.out p).2 := by
  have hFp : ∀ z : X × Y, F (Quotient.out (omk T z)).1 (Quotient.out (omk T z)).2 = F z.1 z.2 :=
    inv_out (fun z : X × Y => F z.1 z.2) (fun t z => hF t z.1 z.2)
  have hGp : ∀ z : X × Y, (((stabilizer T (Quotient.out (omk T z))).relIndex C : ℕ) : ℂ) *
      F (Quotient.out (omk T z)).1 (Quotient.out (omk T z)).2 =
      (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.1 z.2 :=
    inv_out (fun z : X × Y => (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.1 z.2)
      (fun t z => by rw [relIndex_stab_smul]; simp only [Prod.smul_fst, Prod.smul_snd, hF])
  let π : orbitRel.Quotient T (X × Y) → orbitRel.Quotient T X := fun p => omk T (Quotient.out p).1
  have hπ : ∀ z : X × Y, π (omk T z) = omk T z.1 :=
    inv_out (fun z : X × Y => omk T z.1) (fun t z => (omk_eq_iff _ _).2 ⟨t, rfl⟩)
  have hRHS := finsum_eq_sum_of_support_subset (s := hP.toFinset)
    (fun p : orbitRel.Quotient T (X × Y) => (((stabilizer T (Quotient.out p)).relIndex C : ℕ) : ℂ) *
      F (Quotient.out p).1 (Quotient.out p).2) (by
      intro p hp
      simp only [Function.mem_support] at hp
      simpa using right_ne_zero_of_mul hp)
  have hLHS := finsum_eq_sum_of_support_subset (s := hP.toFinset.image π)
    (fun q : orbitRel.Quotient T X => (((stabilizer T (Quotient.out q)).relIndex C : ℕ) : ℂ) *
      ∑ᶠ y, F (Quotient.out q) y) (by
      intro q hq
      simp only [Function.mem_support] at hq
      have hs := right_ne_zero_of_mul hq
      have : ∃ y, F (Quotient.out q) y ≠ 0 := by
        by_contra hno
        push_neg at hno
        exact hs (by simp [hno])
      obtain ⟨y, hy⟩ := this
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨omk T ((Quotient.out q, y) : X × Y), ?_, ?_⟩
      · rw [hFp]; exact hy
      · rw [hπ]; exact Quotient.out_eq q)
  rw [hLHS, hRHS, ← Finset.sum_fiberwise_of_maps_to (s := hP.toFinset) (t := hP.toFinset.image π) (g := π)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  refine Finset.sum_congr rfl fun q _ => ?_
  set x := Quotient.out q with hxdef
  have hq : omk T x = q := Quotient.out_eq q
  have h1 : ∑ᶠ y, F x y = ∑ y ∈ (hfin x).toFinset, F x y :=
    finsum_eq_sum_of_support_subset _ (by intro y hy; simpa using hy)
  rw [h1, Finset.mul_sum]
  have maps : ∀ y ∈ (hfin x).toFinset, omk T ((x, y) : X × Y) ∈ hP.toFinset.filter fun p => π p = q := by
    intro y hy
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy ⊢
    refine ⟨?_, ?_⟩
    · rw [hFp]; exact hy
    · rw [hπ]; exact hq
  rw [← Finset.sum_fiberwise_of_maps_to maps]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
  obtain ⟨hpP, hpq⟩ := hp
  obtain ⟨t, ht⟩ : ∃ t : T, t • (Quotient.out p).1 = x := (omk_eq_iff _ _).1 (hq.trans hpq.symm)
  have hp0 : omk T ((x, t • (Quotient.out p).2) : X × Y) = p := by
    refine Eq.trans ((omk_eq_iff _ _).2 ⟨t, ?_⟩) (Quotient.out_eq p)
    exact Prod.ext ht rfl
  obtain ⟨y0, hy0⟩ : ∃ y0, omk T ((x, y0) : X × Y) = p := ⟨_, hp0⟩
  subst hy0
  have hne : F x y0 ≠ 0 := by
    have := hpP
    rw [hFp] at this
    exact this
  have hconst : ∀ y ∈ (hfin x).toFinset.filter fun y => omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y),
      (((stabilizer T x).relIndex C : ℕ) : ℂ) * F x y = (((stabilizer T x).relIndex C : ℕ) : ℂ) * F x y0 := by
    intro y hy
    obtain ⟨s, hs⟩ := (omk_eq_iff _ _).1 (Finset.mem_filter.1 hy).2
    simp only [Prod.smul_mk, Prod.mk.injEq] at hs
    have := hF s x y0
    rw [hs.1, hs.2] at this
    rw [this]
  have hcard := card_fiber (T := T) x y0 (hfin x).toFinset (by
    intro y hy
    obtain ⟨s, hs⟩ := (omk_eq_iff _ _).1 hy
    simp only [Prod.smul_mk, Prod.mk.injEq] at hs
    have := hF s x y0
    rw [hs.1, hs.2] at this
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [this]
    exact hne)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, hGp, nsmul_eq_mul,
    ← Subgroup.relIndex_mul_relIndex _ _ _ (stab_pair_le x y0) (hX x)]
  push_cast
  ring

end SlopeTestRemainingChoices

theorem orbFub : OrbFub := by
  intro T X Y _ _ _ C _ hX hY F hF hx hy hq
  have hFp : ∀ z : X × Y, F (Quotient.out (omk T z)).1 (Quotient.out (omk T z)).2 = F z.1 z.2 :=
    inv_out (fun z : X × Y => F z.1 z.2) (fun t z => hF t z.1 z.2)
  have hFp' : ∀ z : Y × X, F (Quotient.out (omk T z)).2 (Quotient.out (omk T z)).1 = F z.2 z.1 :=
    inv_out (fun z : Y × X => F z.2 z.1) (fun t z => hF t z.2 z.1)
  have hP : {p : orbitRel.Quotient T (X × Y) | F (Quotient.out p).1 (Quotient.out p).2 ≠ 0}.Finite := by
    refine (hq.biUnion fun q _ => (hx (Quotient.out q)).image
      (fun y => omk T ((Quotient.out q, y) : X × Y))).subset ?_
    intro p hp
    obtain ⟨t, ht⟩ := exists_smul_out (T := T) (Quotient.out p).1
    have hne : F (Quotient.out (omk T (Quotient.out p).1)) (t • (Quotient.out p).2) ≠ 0 := by
      rw [← ht, hF]; exact hp
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop]
    refine ⟨omk T (Quotient.out p).1, ⟨_, hne⟩, _, hne, ?_⟩
    exact Eq.trans ((omk_eq_iff _ _).2 ⟨t, Prod.ext ht rfl⟩) (Quotient.out_eq p)
  let e : orbitRel.Quotient T (X × Y) ≃ orbitRel.Quotient T (Y × X) :=
    Quotient.congr (Equiv.prodComm X Y) (by
      intro a b
      show orbitRel T _ a b ↔ orbitRel T _ (Equiv.prodComm X Y a) (Equiv.prodComm X Y b)
      rw [orbitRel_apply, orbitRel_apply]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, (Equiv.prodComm X Y).injective ht⟩)
  have he : ∀ z : X × Y, e (omk T z) = omk T (z.2, z.1) := fun z => rfl
  have hP' : {p : orbitRel.Quotient T (Y × X) | F (Quotient.out p).2 (Quotient.out p).1 ≠ 0}.Finite := by
    refine (hP.image e).subset ?_
    intro p hp
    obtain ⟨⟨y, x⟩, rfl⟩ := Quotient.exists_rep p
    refine ⟨omk T ((x, y) : X × Y), ?_, rfl⟩
    have h1 : F x y ≠ 0 := by
      have := hFp' (y, x)
      simp only at this
      rw [← this]
      exact hp
    show F (Quotient.out (omk T ((x, y) : X × Y))).1 (Quotient.out (omk T ((x, y) : X × Y))).2 ≠ 0
    rw [hFp]
    exact h1
  rw [one_side C hX F hF hx hP, one_side C hY (fun y x => F x y) (fun t y x => hF t x y) hy hP']
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun p => ?_
  obtain ⟨⟨x, y⟩, rfl⟩ := Quotient.exists_rep p
  have h1 := inv_out (T := T) (fun z : X × Y => (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.1 z.2)
    (fun t z => by rw [relIndex_stab_smul]; simp only [Prod.smul_fst, Prod.smul_snd, hF]) (x, y)
  have h2 := inv_out (T := T) (fun z : Y × X => (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.2 z.1)
    (fun t z => by rw [relIndex_stab_smul]; simp only [Prod.smul_fst, Prod.smul_snd, hF]) (y, x)
  refine (h1.trans ?_).trans h2.symm
  simp only
  rw [stab_swap x y]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.ThetaInvolutionFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical Pointwise

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private lemma out_orbit {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hθ : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    ∃ k ∈ K, ∃ k' ∈ K,
      (Quotient.out (DoubleCoset.mk (twCent θ δ) K x))⁻¹ * δ * θ (Quotient.out (DoubleCoset.mk (twCent θ δ) K x)) =
        k * (x⁻¹ * δ * θ x) * k' := by
  obtain ⟨h, hh, k, hk, e⟩ := (@DoubleCoset.eq _ _ (twCent θ δ) K _ _).1
    (DoubleCoset.out_eq' (DoubleCoset.mk (twCent θ δ) K x))
  generalize Quotient.out (DoubleCoset.mk (twCent θ δ) K x) = o at e
  have hc : h * δ = δ * θ h := hh
  refine ⟨k, hk, (θ k)⁻¹, K.inv_mem (hθ k hk), ?_⟩
  subst e
  simp only [_root_.mul_inv_rev, map_mul, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right]
  rw [← mul_assoc δ (θ h), ← hc]
  simp [mul_assoc]

private theorem orbFin_prod {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousMul G] [ContinuousMul H] (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H)
    (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set H))
    (hθ : ∀ k ∈ K, θ k ∈ K) (hθ' : ∀ k ∈ K', θ' k ∈ K') (δ : G) (δ' : H)
    (h1 : OrbFin θ K δ) (h2 : OrbFin θ' K' δ') : OrbFin (θ.prodMap θ') (K.prod K') (δ, δ') := by
  intro C hC
  have c1 : IsCompact ((K : Set G) * (Prod.fst '' C) * (K : Set G)) := (hK.mul (hC.image continuous_fst)).mul hK
  have c2 : IsCompact ((K' : Set H) * (Prod.snd '' C) * (K' : Set H)) := (hK'.mul (hC.image continuous_snd)).mul hK'
  let φ : DoubleCoset.Quotient (twCent (θ.prodMap θ') (δ, δ') : Set (G × H)) ((K.prod K' : Subgroup (G × H)) : Set (G × H)) →
      DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) × DoubleCoset.Quotient (twCent θ' δ' : Set H) (K' : Set H) :=
    fun q => (DoubleCoset.mk _ _ (Quotient.out q).1, DoubleCoset.mk _ _ (Quotient.out q).2)
  have hφ : Function.Injective φ := by
    intro q q' e
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨a, ha, k, hk, f1⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 e1
    obtain ⟨b, hb, l, hl, f2⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 e2
    have hab : (a, b) ∈ twCent (θ.prodMap θ') (δ, δ') :=
      Prod.ext (show a * δ = δ * θ a from ha) (show b * δ' = δ' * θ' b from hb)
    have key : DoubleCoset.mk (twCent (θ.prodMap θ') (δ, δ')) (K.prod K') (Quotient.out q) =
        DoubleCoset.mk (twCent (θ.prodMap θ') (δ, δ')) (K.prod K') (Quotient.out q') :=
      (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(a, b), hab, (k, l), ⟨hk, hl⟩, Prod.ext f1 f2⟩
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at key
  refine (Set.Finite.preimage hφ.injOn ((h1 _ c1).prod (h2 _ c2))).subset ?_
  intro q hq
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk, k', hk', e⟩ := out_orbit θ K hθ δ (Quotient.out q).1
    show (Quotient.out (DoubleCoset.mk (twCent θ δ) K (Quotient.out q).1))⁻¹ * δ *
      θ (Quotient.out (DoubleCoset.mk (twCent θ δ) K (Quotient.out q).1)) ∈ (K : Set G) * (Prod.fst '' C) * (K : Set G)
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul hk ⟨_, hq, rfl⟩) hk'
  · obtain ⟨k, hk, k', hk', e⟩ := out_orbit θ' K' hθ' δ' (Quotient.out q).2
    show (Quotient.out (DoubleCoset.mk (twCent θ' δ') K' (Quotient.out q).2))⁻¹ * δ' *
      θ' (Quotient.out (DoubleCoset.mk (twCent θ' δ') K' (Quotient.out q).2)) ∈ (K' : Set H) * (Prod.snd '' C) * (K' : Set H)
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul hk ⟨_, hq, rfl⟩) hk'

theorem theta_involution_facts : Th2 := by
  intro E _ _ _ hE a b w _
  have ta := GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE a w
  have tb := GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE b w
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (ta.1.comp continuous_fst).prodMk (tb.1.comp continuous_snd)
  · intro x
    exact Prod.ext (ta.2.1 x.1) (tb.2.1 x.2)
  · intro k hk
    exact ⟨ta.2.2.1 _ hk.1, tb.2.2.1 _ hk.2⟩
  · rintro ⟨y₁, y₂⟩ h₁ h₂
    exact orbFin_prod (thL a w) (thL b w) _ _ ta.2.2.2.2.2.1 tb.2.2.2.2.2.1 ta.2.2.1 tb.2.2.1 y₁ y₂
      ((GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE a w y₁ h₁ _ ⟨ta.2.2.2.2.1, le_rfl, ta.2.2.1⟩).2)
      ((GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE b w y₂ h₂ _ ⟨tb.2.2.2.2.1, le_rfl, tb.2.2.1⟩).2)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.TrGDiagPow
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.BCT GlobalTheory.LFun GroundTheory.Automorphic PositivityTheory.Rg.BcB.G8
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private def trG {F : Type} [Field F] {n : ℕ} (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨g.val.transpose, (g⁻¹).val.transpose,
    by rw [← Matrix.transpose_mul]; simp,
    by rw [← Matrix.transpose_mul]; simp⟩

private theorem trG_val {F : Type} [Field F] {n : ℕ} (g : GL (Fin n) F) : (trG g).val = g.val.transpose := rfl

private theorem trG_mul {F : Type} [Field F] {n : ℕ} (x y : GL (Fin n) F) : trG (x * y) = trG y * trG x :=
  Units.ext (by simp [trG_val, Matrix.transpose_mul])

private theorem trG_trG {F : Type} [Field F] {n : ℕ} (x : GL (Fin n) F) : trG (trG x) = x :=
  Units.ext (by simp [trG_val])

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem trG_mem {w : HeightOneSpectrum (𝓞 E)} {k : GL (Fin n) (w.adicCompletion E)}
    (hk : k ∈ KGL w (n := n)) : trG k ∈ KGL w (n := n) := by
  have h := GlobalTheory.StabInt.mem_integralGL_of_mem_KGL hk
  rw [GLnLocal.mem_integralGL_iff] at h
  refine GlobalTheory.StabInt.mem_KGL_of_mem_integralGL ?_
  rw [GLnLocal.mem_integralGL_iff]
  exact ⟨fun i j => h.1 j i, fun i j => h.2 j i⟩

private theorem trG_diagPow (w : HeightOneSpectrum (𝓞 E)) (μ : Fin n → ℤ) :
    trG (Cartan.diagPow (w.adicCompletion E) n μ) = Cartan.diagPow (w.adicCompletion E) n μ :=
  Units.ext (by rw [trG_val, Cartan.coe_diagPow, Matrix.diagonal_transpose])

private theorem trG_double (w : HeightOneSpectrum (𝓞 E)) (x : GL (Fin n) (w.adicCompletion E)) :
    ∃ k ∈ KGL w (n := n), ∃ k' ∈ KGL w (n := n), trG x = k * x * k' := by
  obtain ⟨μ, -, k₁, h₁, k₂, h₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul (w.adicCompletion E) n x
  have h₁' := GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h₁
  have h₂' := GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h₂
  refine ⟨trG k₂ * k₁⁻¹, (KGL w (n := n)).mul_mem (trG_mem h₂') ((KGL w (n := n)).inv_mem h₁'),
    k₂⁻¹ * trG k₁, (KGL w (n := n)).mul_mem ((KGL w (n := n)).inv_mem h₂') (trG_mem h₁'), ?_⟩
  rw [trG_mul, trG_mul, trG_diagPow]
  group

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.cvComm2 :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.CvGelfand → UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.CvComm2 := by
  intro h E _ _ _ a b w f g hf hg
  obtain ⟨hoa, hca⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hob, hcb⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  refine h (GLw a w × GLw b w) (K2 a b w) (hoa.prod hob) (hca.prod hcb)
    (fun x => (trG x.1, trG x.2)) ?_ ?_ ?_ ?_ f g hf hg
  · intro x y
    exact Prod.ext (trG_mul _ _) (trG_mul _ _)
  · intro x
    exact Prod.ext (trG_trG _) (trG_trG _)
  · intro k hk
    exact ⟨trG_mem hk.1, trG_mem hk.2⟩
  · intro x
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := trG_double w x.1
    obtain ⟨l₁, i₁, l₂, i₂, e'⟩ := trG_double w x.2
    exact ⟨(k₁, l₁), ⟨h₁, i₁⟩, (k₂, l₂), ⟨h₂, i₂⟩, Prod.ext e e'⟩
end
end

