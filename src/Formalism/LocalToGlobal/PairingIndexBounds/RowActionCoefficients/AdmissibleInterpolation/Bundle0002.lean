module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.PolyKTorsionFree
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Model

section dual

variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [CharZero K]

lemma toK_eq_map {σ : Type} (f : MvPolynomial σ O) : toK O K f = map (algebraMap O K) f := rfl

lemma polyK_torsionFree {σ : Type} : Module.IsTorsionFree O (MvPolynomial σ K) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  rw [← algebraMap_smul K a f, smul_eq_zero] at h
  rcases h with h | h
  · left; exact (IsFractionRing.injective O K) (by rw [h, map_zero])
  · right; exact h

lemma weylK_fg {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    ((weyl O n n le_rfl ν).map (toK O K)).FG := by
  have hM : ((dualWeyl O n n ν).map (toK O K)).FG := by
    apply Submodule.FG.map
    obtain ⟨b, hb, -⟩ := sSBasis O n n ν
    rw [← hb.2.1]
    have := (sSIdxFinite n n ν).to_subtype
    exact Submodule.fg_span (Set.finite_range b)
  have hle : (weyl O n n le_rfl ν).map (toK O K) ≤ (dualWeyl O n n ν).map (toK O K) :=
    Submodule.map_mono (weylLeDual O n n le_rfl ν hν)
  have := isNoetherian_of_fg_of_noetherian _ hM
  have h := IsNoetherian.noetherian (((weyl O n n le_rfl ν).map (toK O K)).comap
    ((dualWeyl O n n ν).map (toK O K)).subtype)
  have h2 := h.map ((dualWeyl O n n ν).map (toK O K)).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2

end dual

theorem dual_bases_holds : DualBases := by
  intro O K _ _ _ _ _ _ _ n ν hν
  classical
  set c := fockR (hw K (le_rfl : n ≤ n) ν) (hw K le_rfl ν) with hc
  set D := (weyl O n n le_rfl ν).map (toK O K) with hD
  have : Module.IsTorsionFree O (MvPolynomial (Fin n × Fin n) K) := polyK_torsionFree
  have : Module.Finite O D := Module.Finite.iff_fg.mpr (weylK_fg ν hν)
  obtain ⟨N, bD⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := D)
  set e : Fin N → MvPolynomial (Fin n × Fin n) K := fun i => (bD i : MvPolynomial (Fin n × Fin n) K) with he_def
  have he : ∀ i, e i ∈ D := fun i => (bD i).2
  have hDV : ∀ x ∈ D, x ∈ dualWeyl K n n ν := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [toK_eq_map]
    exact weylLeDual K n n le_rfl ν hν (sw_weyl_map (algebraMap O K) le_rfl ν y hy)
  have hrep : ∀ x (hx : x ∈ D), x = ∑ i, bD.repr ⟨x, hx⟩ i • e i := by
    intro x hx
    have h := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simpa [he_def] using h.symm
  have hsm : ∀ (a : O) (f : MvPolynomial (Fin n × Fin n) K), a • f = algebraMap O K a • f :=
    fun a f => (algebraMap_smul K a f).symm
  have hDspan : ∀ x ∈ D, x ∈ Submodule.span K (Set.range e) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : dualWeyl K n n ν ≤ Submodule.span K (Set.range e) := by
    rw [← sw_weyl_eq K n n le_rfl ν hν]
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply hDspan
    refine Submodule.mem_map.mpr ⟨applyWord O w (hw O le_rfl ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [toK_eq_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  have hliO : LinearIndependent O e := bD.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  have hli : LinearIndependent K e := (LinearIndependent.iff_fractionRing O K).mp hliO
  set W := Submodule.span K (Set.range e) with hW
  have hWV : W = dualWeyl K n n ν := by
    refine le_antisymm ?_ hspan
    rw [hW, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDV _ (he i)
  let bW : Module.Basis (Fin N) K W := Module.Basis.span hli
  have hbW : ∀ i, (bW i : MvPolynomial (Fin n × Fin n) K) = e i := fun i =>
    congrArg Subtype.val (Module.Basis.span_apply hli i)
  let Bf : LinearMap.BilinForm K W := LinearMap.mk₂ K (fun x y : W => fockR (x : MvPolynomial (Fin n × Fin n) K) y)
    (fun x x' y => by simp [fockR_add_left]) (fun a x y => by simp [fockR_smul_left])
    (fun x y y' => by simp [fockR_add_right]) (fun a x y => by simp [fockR_smul_right])
  have hBf : ∀ x y : W, Bf x y = fockR (x : MvPolynomial (Fin n × Fin n) K) y := fun _ _ => rfl
  have hnd : Bf.Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      refine Top.nondegK K n n le_rfl ν hν x.1 (hWV ▸ x.2) fun P hP => ?_
      rw [fockR_symm]
      exact hx ⟨P, hWV ▸ hP⟩
    · intro y hy
      apply Subtype.ext
      exact Top.nondegK K n n le_rfl ν hν y.1 (hWV ▸ y.2) fun P hP => hy ⟨P, hWV ▸ hP⟩
  let d := Bf.dualBasis hnd bW
  have hd : ∀ i k, fockR (e i) (d k : MvPolynomial (Fin n × Fin n) K) = if i = k then 1 else 0 := by
    intro i k
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd bW k i
    rw [hBf, hbW, fockR_symm] at h
    exact h
  refine ⟨Fin N, inferInstance, inferInstance, e, fun k => c • (d k : MvPolynomial (Fin n × Fin n) K),
    he, ?_, ?_, hspan⟩
  · intro k
    have hkV : c • (d k : MvPolynomial (Fin n × Fin n) K) ∈ dualWeyl K n n ν :=
      Submodule.smul_mem _ _ (hWV ▸ (d k).2)
    refine Top.dualWeylIn O K n n le_rfl ν hν _ hkV fun P hP => ⟨bD.repr ⟨P, hP⟩ k, ?_⟩
    show fockR P (c • (d k : MvPolynomial (Fin n × Fin n) K)) = _
    conv_lhs => rw [hrep P hP]
    rw [fockR_sum_left]
    simp_rw [hsm, fockR_smul_left, fockR_smul_right, hd]
    simp [hc]
  · intro i k
    rw [fockR_smul_right, hd]
    split_ifs <;> simp

end Formalism.L2.PairingIndexBounds.Ent
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ShapeEvenHolds
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS

namespace ConjugatePartitionShape

section Heights

variable {n : ℕ} {ν : Fin n → ℕ}

theorem colH_ge (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : k < ν t) : t.val + 1 ≤ colH ν k := by
  unfold colH
  rw [← Fin.card_Iic t]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_Iic] at hs
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, lt_of_lt_of_le h (hν hs)⟩

theorem colH_le_of (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : ν t ≤ k) : colH ν k ≤ t.val := by
  unfold colH
  rw [← Fin.card_Iio t]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter] at hs
  rw [Finset.mem_Iio]
  by_contra hst
  push_neg at hst
  exact absurd (lt_of_lt_of_le hs.2 (hν hst)) (not_lt.mpr h)

theorem lt_colH_iff (hν : Antitone ν) (k : ℕ) (t : Fin n) : t.val < colH ν k ↔ k < ν t := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    exact absurd (colH_le_of hν t h') (not_le.mpr h)
  · intro h
    exact Nat.lt_of_succ_le (colH_ge hν t h)

end Heights

theorem card_fin_lt (c m : ℕ) (hm : m ≤ c) : (Finset.univ.filter fun k : Fin c => k.val < m).card = m := by
  have e : (Finset.univ.filter fun k : Fin c => k.val < m).map Fin.valEmbedding = Finset.range m := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]

theorem kap_antitone {n : ℕ} {μ : Fin n → ℕ} (hμ : Antitone μ) (c : ℕ) : Antitone fun t : Fin n => c - μ t.rev := by
  intro s t hst
  exact Nat.sub_le_sub_left (hμ (Fin.rev_le_rev.mpr hst)) c

theorem colH_kap {n : ℕ} {μ : Fin n → ℕ} (c : ℕ) (hc : ∀ t, μ t ≤ c) (k : Fin c) :
    n - colH μ k.val = colH (fun t : Fin n => c - μ t.rev) (Fin.rev k).val := by
  simp only [colH]
  have e1 : (Finset.univ.filter fun t : Fin n => (Fin.rev k).val < c - μ t.rev).card =
      (Finset.univ.filter fun s : Fin n => ¬ k.val < μ s).card := by
    refine Finset.card_bij (fun t _ => t.rev) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at ht ⊢
      have := hc t.rev
      have := k.isLt
      omega
    · intro a _ b _ h
      exact Fin.rev_injective h
    · intro s hs
      refine ⟨s.rev, ?_, Fin.rev_rev s⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev, Fin.rev_rev] at hs ⊢
      have := hc s
      have := k.isLt
      omega
  have hsub : (Finset.univ.filter fun s : Fin n => k.val < μ s) ⊆ Finset.univ := Finset.subset_univ _
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 : (Finset.univ.filter fun s : Fin n => ¬ k.val < μ s) =
      Finset.univ \ (Finset.univ.filter fun s : Fin n => k.val < μ s) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [h3] at e1
  omega

theorem card_ge_eq {n K K' : ℕ} (sz : Fin K → ℕ) (sz' : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (hsz' : ∀ k, sz' k ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg sz') (l : ℕ) (hl : 0 < l) :
    (Finset.univ.filter fun k => l ≤ sz k).card = (Finset.univ.filter fun k => l ≤ sz' k).card := by
  by_cases hln : l ≤ n
  · have e := congrFun h ⟨l - 1, by omega⟩
    simp only [shapeDeg] at e
    have e1 : (Finset.univ.filter fun k => l ≤ sz k) = (Finset.univ.filter fun k => l - 1 < sz k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro <;> omega
    have e2 : (Finset.univ.filter fun k => l ≤ sz' k) = (Finset.univ.filter fun k => l - 1 < sz' k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro <;> omega
    rw [e1, e2]
    exact e
  · push_neg at hln
    have e1 : (Finset.univ.filter fun k => l ≤ sz k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ => by have := hsz k; omega
    have e2 : (Finset.univ.filter fun k => l ≤ sz' k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ => by have := hsz' k; omega
    rw [e1, e2, Finset.card_empty, Finset.card_empty]

theorem card_eq_sub {K : ℕ} (sz : Fin K → ℕ) (l : ℕ) :
    (Finset.univ.filter fun k => sz k = l).card =
      (Finset.univ.filter fun k => l ≤ sz k).card - (Finset.univ.filter fun k => l + 1 ≤ sz k).card := by
  have hsub : (Finset.univ.filter fun k => l + 1 ≤ sz k) ⊆ (Finset.univ.filter fun k => l ≤ sz k) := by
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 : (Finset.univ.filter fun k => sz k = l) =
      (Finset.univ.filter fun k => l ≤ sz k) \ (Finset.univ.filter fun k => l + 1 ≤ sz k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor <;> intro <;> omega
  rw [h3]
  omega

theorem card_eq_eq {n K K' : ℕ} (sz : Fin K → ℕ) (sz' : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (hsz' : ∀ k, sz' k ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg sz') (l : ℕ) (hl : 0 < l) :
    Fintype.card {k' // sz' k' = l} = Fintype.card {k // sz k = l} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, card_eq_sub, card_eq_sub,
    card_ge_eq sz sz' hsz hsz' h l hl, card_ge_eq sz sz' hsz hsz' h (l + 1) (Nat.succ_pos l)]

theorem initMinor_cast (B : Type) [CommRing B] {r n s s' : ℕ} (e : s = s') (J : Fin s → Fin r) (hs : s ≤ n)
    (hs' : s' ≤ n) : initMinor B (n := n) (fun j : Fin s' => J (Fin.cast e.symm j)) hs' = initMinor B J hs := by
  subst e
  rfl

theorem initMinor_zero (B : Type) [CommRing B] {r n : ℕ} (J : Fin 0 → Fin r) (hs : 0 ≤ n) :
    initMinor B (n := n) J hs = 1 := by
  rw [initMinor]
  exact Matrix.det_isEmpty

theorem initMinor_eq_one (B : Type) [CommRing B] {r n s : ℕ} (J : Fin s → Fin r) (hs : s ≤ n) (h0 : s = 0) :
    initMinor B (n := n) J hs = 1 := by
  subst h0
  exact initMinor_zero B J hs

end ConjugatePartitionShape

open ConjugatePartitionShape

theorem shape_even_holds : ShapeE := by
  intro n ν hν c hc
  funext t
  simp only [shapeDeg]
  rw [← card_fin_lt c (ν t) (hc t)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_colH_iff hν k.val t

theorem shape_odd_holds : ShapeO := by
  intro n μ hμ c hc
  funext t
  simp only [shapeDeg]
  rw [← card_fin_lt c (c - μ t.rev) (Nat.sub_le c _)]
  refine Finset.card_bij (fun k _ => Fin.rev k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [colH_kap c (fun s => hc s) k] at hk
    exact (lt_colH_iff (kap_antitone hμ c) _ t).mp hk
  · intro a _ b _ h
    exact Fin.rev_injective h
  · intro k hk
    refine ⟨Fin.rev k, ?_, Fin.rev_rev k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [colH_kap c (fun s => hc s) (Fin.rev k), Fin.rev_rev]
    exact (lt_colH_iff (kap_antitone hμ c) _ t).mpr hk

theorem reorder_holds : Reorder := by
  intro B _ r n K K' sz sz' hsz hsz' h I
  classical
  have hE : ∀ l, 0 < l → Nonempty ({k' // sz' k' = l} ≃ {k // sz k = l}) := fun l hl =>
    ⟨Fintype.equivOfCardEq (card_eq_eq sz sz' hsz hsz' h l hl)⟩
  let e : ∀ l, 0 < l → ({k' // sz' k' = l} ≃ {k // sz k = l}) := fun l hl => Classical.choice (hE l hl)
  let I' : ∀ k', Fin (sz' k') → Fin r := fun k' =>
    if hk : 0 < sz' k' then
      fun j => I (e (sz' k') hk ⟨k', rfl⟩).1 (Fin.cast (e (sz' k') hk ⟨k', rfl⟩).2.symm j)
    else fun j => absurd j.2 (by omega)
  refine ⟨I', ?_⟩
  unfold bideterminant
  have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin K)), sz k ∈ Finset.range (n + 1) :=
    fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz k))
  have hmaps' : ∀ k ∈ (Finset.univ : Finset (Fin K')), sz' k ∈ Finset.range (n + 1) :=
    fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz' k))
  rw [← Finset.prod_fiberwise_of_maps_to hmaps, ← Finset.prod_fiberwise_of_maps_to hmaps']
  refine Finset.prod_congr rfl fun l _ => ?_
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rw [Finset.prod_eq_one, Finset.prod_eq_one]
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact initMinor_eq_one B _ _ hk
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact initMinor_eq_one B _ _ hk
  · rw [Finset.prod_subtype _ (p := fun k => sz k = l) (by simp),
      Finset.prod_subtype _ (p := fun k' => sz' k' = l) (by simp)]
    symm
    refine Fintype.prod_equiv (e l hl) _ _ fun x' => ?_
    obtain ⟨k', hk'⟩ := x'
    subst hk'
    have hI : I' k' = fun j => I (e (sz' k') hl ⟨k', rfl⟩).1 (Fin.cast (e (sz' k') hl ⟨k', rfl⟩).2.symm j) :=
      dif_pos hl
    simp only
    rw [hI]
    exact initMinor_cast B (e (sz' k') hl ⟨k', rfl⟩).2 _ _ _

end Formalism.L2.PairingIndexBounds.Ent
end
end

