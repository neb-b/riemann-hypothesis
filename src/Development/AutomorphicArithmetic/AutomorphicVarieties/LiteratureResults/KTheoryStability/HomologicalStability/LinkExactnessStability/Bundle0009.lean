module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleRetractionOfLinkExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInSplitSeqOfExactAtSplitSeq
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx.LinkSplit

variable {R : Type} [CommRing R]

def pad {m N : ℕ} (v : Fin m → R) : Fin N → R := fun i => if h : (i : ℕ) < m then v ⟨i, h⟩ else 0

def restr {m N : ℕ} (h : m ≤ N) (y : Fin N → R) : Fin m → R := fun i => y ⟨i, lt_of_lt_of_le i.2 h⟩

lemma pad_apply_lt {m N : ℕ} (v : Fin m → R) (i : Fin N) (h : (i : ℕ) < m) :
    pad (N := N) v i = v ⟨i, h⟩ := dif_pos h

lemma pad_apply_ge {m N : ℕ} (v : Fin m → R) (i : Fin N) (h : m ≤ (i : ℕ)) :
    pad (N := N) v i = 0 := dif_neg (by omega)

lemma restr_pad {m N : ℕ} (h : m ≤ N) (v : Fin m → R) : restr h (pad (N := N) v) = v := by
  funext i
  exact pad_apply_lt v _ i.2

lemma pad_restr {m N : ℕ} (h : m ≤ N) (y : Fin N → R) (hy : ∀ i : Fin N, m ≤ (i : ℕ) → y i = 0) :
    pad (restr h y) = y := by
  funext i
  by_cases hi : (i : ℕ) < m
  · rw [pad_apply_lt _ _ hi]; rfl
  · rw [pad_apply_ge _ _ (by omega), hy i (by omega)]

lemma pad_dot {m N : ℕ} (h : m ≤ N) (f v : Fin m → R) :
    pad (N := N) f ⬝ᵥ pad v = f ⬝ᵥ v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : ∀ (u : Fin m → R) (i : Fin m), pad (N := m + k) u (Fin.castAdd k i) = u i :=
    fun u i => pad_apply_lt u _ i.2
  have h2 : ∀ (u : Fin m → R) (i : Fin k), pad (N := m + k) u (Fin.natAdd m i) = 0 :=
    fun u i => pad_apply_ge u _ (by simp)
  simp only [dotProduct, Fin.sum_univ_add, h1, h2, mul_zero, Finset.sum_const_zero, add_zero]

end GlobalTheory.SeqCx.LinkSplit

namespace GlobalTheory.SeqCx

private theorem map_mem_splitSeq_iff_of_pairing_preserved {R : Type} [CommRing R] {a b : ℕ}
    (f : (Fin a → R) × (Fin a → R) → (Fin b → R) × (Fin b → R))
    (hf : ∀ x y, (f y).2 ⬝ᵥ (f x).1 = y.2 ⬝ᵥ x.1) (l : List ((Fin a → R) × (Fin a → R))) :
    List.map f l ∈ splitSeq R b ↔ l ∈ splitSeq R a := by
  rw [(GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R b).2.2.1, (GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R a).2.2.1, List.pairwise_map]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hf]


open LinkSplit in
theorem exactAt_link_splitSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ (N m p : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N →
      s ≤ m → ExactAt (splitSeq R m) p → ExactAt (linkIn (splitSeq R N) Set.univ ρ) p := by
  intro R _ s hs N m p ρ hρ hlen hsm hex
  have hmN : m ≤ N := by omega
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_splitSeq_standard_of_stableRangeLe R s hs N ρ hρ (by omega)
    (fun j => (⟨m + (j : ℕ), by omega⟩ : Fin N))
    (by intro a b h; ext; simp only [Fin.mk.injEq] at h; omega)
  let T : (Fin N → R) × (Fin N → R) → (Fin N → R) × (Fin N → R) :=
    fun x => ((↑g : Matrix (Fin N) (Fin N) R) *ᵥ x.1, x.2 ᵥ* (↑g⁻¹ : Matrix (Fin N) (Fin N) R))
  let Ti : (Fin N → R) × (Fin N → R) → (Fin N → R) × (Fin N → R) :=
    fun x => ((↑g⁻¹ : Matrix (Fin N) (Fin N) R) *ᵥ x.1, x.2 ᵥ* (↑g : Matrix (Fin N) (Fin N) R))
  have hTTi : ∀ x, T (Ti x) = x := by
    intro x
    refine Prod.ext ?_ ?_
    · simp only [T, Ti, mulVec_mulVec, Units.mul_inv, one_mulVec]
    · simp only [T, Ti, vecMul_vecMul, Units.mul_inv, vecMul_one]
  have hTiT : ∀ x, Ti (T x) = x := by
    intro x
    refine Prod.ext ?_ ?_
    · simp only [T, Ti, mulVec_mulVec, Units.inv_mul, one_mulVec]
    · simp only [T, Ti, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hTdot : ∀ x y, (T y).2 ⬝ᵥ (T x).1 = y.2 ⬝ᵥ x.1 := by
    intro x y
    simp only [T]
    rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]
  let P : (Fin m → R) × (Fin m → R) → (Fin N → R) × (Fin N → R) :=
    fun x => (LinkSplit.pad x.1, LinkSplit.pad x.2)
  have hPdot : ∀ x y, (P y).2 ⬝ᵥ (P x).1 = y.2 ⬝ᵥ x.1 := fun x y => LinkSplit.pad_dot hmN _ _
  have hPinj : Function.Injective P := by
    intro x y h
    have h1 := congrArg (fun z => LinkSplit.restr hmN z.1) h
    have h2 := congrArg (fun z => LinkSplit.restr hmN z.2) h
    simp only [P, LinkSplit.restr_pad] at h1 h2
    exact Prod.ext h1 h2
  have hTiinj : Function.Injective Ti := fun x y h => by rw [← hTTi x, ← hTTi y, h]
  have hmemT := map_mem_splitSeq_iff_of_pairing_preserved T hTdot
  have hmemP := map_mem_splitSeq_iff_of_pairing_preserved P hPdot
  have hchar := (GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff R N).2.2.1
  have hρT : ∀ j : Fin ρ.length, T (ρ.get j) =
      (Pi.single (⟨m + (j : ℕ), by omega⟩ : Fin N) 1, Pi.single (⟨m + (j : ℕ), by omega⟩ : Fin N) 1) :=
    fun j => Prod.ext (hg j).1 (hg j).2
  have key : linkIn (splitSeq R N) Set.univ ρ = List.map Ti '' (List.map P '' splitSeq R m) := by
    ext w
    constructor
    · rintro ⟨-, hw⟩
      have hw' := (hchar _).1 hw
      rw [List.pairwise_append] at hw'
      obtain ⟨hall, -, hpw, hcross⟩ := hw'
      have wsplit : w ∈ splitSeq R N :=
        (hchar w).2 ⟨fun y hy => hall y (List.mem_append_right _ hy), hpw⟩
      have hvan : ∀ x ∈ w, ∀ i : Fin N, m ≤ (i : ℕ) → (T x).1 i = 0 ∧ (T x).2 i = 0 := by
        intro x hx i hi
        let j : Fin ρ.length := ⟨(i : ℕ) - m, by omega⟩
        have hji : (⟨m + (j : ℕ), by omega⟩ : Fin N) = i := Fin.ext (by simp only [j]; omega)
        have hc := hcross (ρ.get j) (List.get_mem _ _) x hx
        have e := hρT j
        rw [hji] at e
        constructor
        · have := hTdot x (ρ.get j)
          rw [e, single_dotProduct, one_mul] at this
          rw [this]
          exact hc.1
        · have := hTdot (ρ.get j) x
          rw [e, dotProduct_single, mul_one] at this
          rw [this]
          exact hc.2
      let l := w.map (fun x => (LinkSplit.restr hmN (T x).1, LinkSplit.restr hmN (T x).2))
      have hPl : List.map P l = List.map T w := by
        simp only [l, List.map_map]
        apply List.map_congr_left
        intro x hx
        refine Prod.ext ?_ ?_
        · exact LinkSplit.pad_restr hmN _ (fun i hi => (hvan x hx i hi).1)
        · exact LinkSplit.pad_restr hmN _ (fun i hi => (hvan x hx i hi).2)
      have lsplit : l ∈ splitSeq R m := (hmemP l).1 (hPl ▸ (hmemT w).2 wsplit)
      refine ⟨List.map P l, ⟨l, lsplit, rfl⟩, ?_⟩
      rw [hPl, List.map_map]
      simp [Function.comp_def, hTiT]
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
      have hback : List.map T (List.map Ti (List.map P l)) = List.map P l := by
        simp [List.map_map, Function.comp_def, hTTi]
      rw [← hmemT, List.map_append, hback]
      have A := (hchar _).1 ((hmemT ρ).2 hρ)
      have B := (hchar _).1 ((hmemP l).2 hl)
      rw [hchar, List.pairwise_append]
      refine ⟨?_, A.2, B.2, ?_⟩
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact A.1 y hy
        · exact B.1 y hy
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hx
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb
        rw [hρT j]
        have hk : m ≤ ((⟨m + (j : ℕ), by omega⟩ : Fin N) : ℕ) := Nat.le_add_right _ _
        simp only [P, single_dotProduct, dotProduct_single, LinkSplit.pad_apply_ge _ _ hk,
          mul_zero, zero_mul, and_self]
  rw [key, GlobalTheory.T.seqChain_exactAt_map_iff _ _ Ti hTiinj, GlobalTheory.T.seqChain_exactAt_map_iff _ _ P hPinj]
  exact hex

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_linkIn_splitSeq_of_exactAt_splitSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (N m p : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N → s ≤ m → ExactAt (splitSeq R m) p → ExactAt (linkIn (splitSeq R N) Set.univ ρ) p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_link_splitSeq
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtUniSeqOrthogonalSplitSeqOfExactAtUniSeq
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx.LinkCol

variable {R : Type} [CommRing R]

def padZero {m N : ℕ} (v : Fin m → R) : Fin N → R := fun i => if h : (i : ℕ) < m then v ⟨i, h⟩ else 0

def restrFirst {m N : ℕ} (h : m ≤ N) (x : Fin N → R) : Fin m → R := fun i => x (Fin.castLE h i)

lemma dotProduct_padZero {m N : ℕ} (h : m ≤ N) (F : Fin N → R) (v : Fin m → R) :
    F ⬝ᵥ padZero v = restrFirst h F ⬝ᵥ v := by
  unfold dotProduct
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro i hi
    simp only [padZero]
    rw [dite_eq_right, mul_zero]
    intro hlt
    exact hi ⟨⟨i, hlt⟩, Fin.ext rfl⟩
  · intro i
    simp [restrFirst, padZero]

lemma restrFirst_padZero {m N : ℕ} (h : m ≤ N) (v : Fin m → R) : restrFirst h (padZero v) = v := by
  ext i
  simp [restrFirst, padZero]

lemma padZero_restrFirst {m N : ℕ} (h : m ≤ N) (x : Fin N → R) (hx : ∀ i : Fin N, m ≤ (i : ℕ) → x i = 0) :
    padZero (restrFirst h x) = x := by
  ext i
  simp only [padZero, restrFirst]
  split_ifs with hi
  · rfl
  · exact (hx i (not_lt.mp hi)).symm

lemma mem_uniSeq_iff {n : ℕ} (l : List (Fin n → R)) :
    l ∈ uniSeq R n ↔ ∃ f : ℕ → Fin n → R, ∀ i j (hi : i < l.length) (hj : j < l.length),
      f i ⬝ᵥ l[j] = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => if h : i < l.length then f ⟨i, h⟩ else 0, fun i j hi hj => ?_⟩
    have := hf ⟨i, hi⟩ ⟨j, hj⟩
    simp only [dif_pos hi]
    simpa [Fin.ext_iff] using this
  · rintro ⟨f, hf⟩
    refine ⟨fun i => f i, fun i j => ?_⟩
    have := hf i j i.2 j.2
    simpa [Fin.ext_iff] using this

lemma map_mem_uniSeq {m N : ℕ} (e : (Fin m → R) → (Fin N → R)) (A : (Fin N → R) → (Fin m → R))
    (B : (Fin m → R) → (Fin N → R)) (hA : ∀ F v, F ⬝ᵥ e v = A F ⬝ᵥ v)
    (hB : ∀ f v, B f ⬝ᵥ e v = f ⬝ᵥ v) (vs : List (Fin m → R)) :
    vs.map e ∈ uniSeq R N ↔ vs ∈ uniSeq R m := by
  rw [mem_uniSeq_iff, mem_uniSeq_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => A (f i), fun i j hi hj => ?_⟩
    have := hf i j (by simpa using hi) (by simpa using hj)
    rw [List.getElem_map, hA] at this
    exact this
  · rintro ⟨f, hf⟩
    refine ⟨fun i => B (f i), fun i j hi hj => ?_⟩
    rw [List.getElem_map, hB]
    exact hf i j (by simpa using hi) (by simpa using hj)

end GlobalTheory.SeqCx.LinkCol

open GlobalTheory.SeqCx.LinkCol

theorem GlobalTheory.SeqCx.exactAt_uniSeq_killed_by_split : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ (N m q : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N →
    s ≤ m → ExactAt (uniSeq R m) q →
    ExactAt {w | w ∈ uniSeq R N ∧ ∀ y ∈ ρ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} q := by
  intro R _ s hs N m q ρ hρ hN hsm hex
  have hmN : m ≤ N := by omega
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_splitSeq_standard_of_stableRangeLe R s hs N ρ hρ (by omega) (fun j => ⟨m + j, by omega⟩)
    (by intro a b h; simp [Fin.ext_iff] at h; exact Fin.ext h)
  set G : Matrix (Fin N) (Fin N) R := (g : Matrix (Fin N) (Fin N) R) with hGdef
  set Gi : Matrix (Fin N) (Fin N) R := ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) with hGidef
  have hGGi : G * Gi = 1 := Units.mul_inv g
  have hGiG : Gi * G = 1 := Units.inv_mul g
  let e : (Fin m → R) → (Fin N → R) := fun v => Gi *ᵥ padZero v
  have he : Function.Injective e := by
    intro a b hab
    have h1 : G *ᵥ (Gi *ᵥ padZero a) = G *ᵥ (Gi *ᵥ padZero b) := by
      simp only [e] at hab; rw [hab]
    rw [mulVec_mulVec, mulVec_mulVec, hGGi, one_mulVec, one_mulVec] at h1
    have h2 := congrArg (restrFirst hmN) h1
    rwa [restrFirst_padZero, restrFirst_padZero] at h2
  have hdot : ∀ (u : Fin N → R) (j : Fin ρ.length), (ρ.get j).2 ⬝ᵥ u = (G *ᵥ u) ⟨m + j, by omega⟩ := by
    intro u j
    have h1 : u = Gi *ᵥ (G *ᵥ u) := by rw [mulVec_mulVec, hGiG, one_mulVec]
    conv_lhs => rw [h1]
    rw [dotProduct_mulVec, (hg j).2, single_dotProduct, one_mul]
  have hkey : ∀ u : Fin N → R, (∀ y ∈ ρ, y.2 ⬝ᵥ u = 0) ↔ e (restrFirst hmN (G *ᵥ u)) = u := by
    intro u
    constructor
    · intro h
      have hz : ∀ i : Fin N, m ≤ (i : ℕ) → (G *ᵥ u) i = 0 := by
        intro i hi
        have hi2 := i.2
        have h3 := h (ρ.get ⟨i - m, by omega⟩) (List.get_mem _ _)
        rw [hdot] at h3
        convert h3 using 2
        ext
        simp only
        omega
      simp only [e]
      rw [padZero_restrFirst hmN _ hz, mulVec_mulVec, hGiG, one_mulVec]
    · intro h y hy
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hy
      rw [hdot]
      have h1 : G *ᵥ u = padZero (restrFirst hmN (G *ᵥ u)) := by
        conv_lhs => rw [← h]
        simp only [e]
        rw [mulVec_mulVec, hGGi, one_mulVec]
      rw [h1]
      simp [padZero]
  have hA : ∀ F v, F ⬝ᵥ e v = restrFirst hmN (F ᵥ* Gi) ⬝ᵥ v := by
    intro F v
    simp only [e]
    rw [dotProduct_mulVec, dotProduct_padZero hmN]
  have hB : ∀ f v, (padZero f ᵥ* G) ⬝ᵥ e v = f ⬝ᵥ v := by
    intro f v
    simp only [e]
    rw [dotProduct_mulVec, vecMul_vecMul, hGGi, vecMul_one, dotProduct_padZero hmN, restrFirst_padZero]
  have hset : {w | w ∈ uniSeq R N ∧ ∀ y ∈ ρ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} = List.map e '' uniSeq R m := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hw, h⟩
      have hw' : w.map (fun u => e (restrFirst hmN (G *ᵥ u))) = w := by
        conv_rhs => rw [← List.map_id w]
        apply List.map_congr_left
        intro u hu
        exact (hkey u).mp (fun y hy => h y hy u hu)
      refine ⟨w.map (fun u => restrFirst hmN (G *ᵥ u)), ?_, ?_⟩
      · rw [← map_mem_uniSeq e _ _ hA hB, List.map_map]
        convert hw using 1
        exact hw'
      · rw [List.map_map]
        exact hw'
    · rintro ⟨vs, hvs, rfl⟩
      refine ⟨(map_mem_uniSeq e _ _ hA hB vs).mpr hvs, ?_⟩
      intro y hy u hu
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hu
      have h1 : restrFirst hmN (G *ᵥ e v) = v := by
        simp only [e]
        rw [mulVec_mulVec, hGGi, one_mulVec, restrFirst_padZero]
      exact (hkey (e v)).mpr (by rw [h1]) y hy
  rw [hset]
  exact (GlobalTheory.T.seqChain_exactAt_map_iff _ _ e he _ q).mpr hex

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_uniSeq_orthogonal_splitSeq_of_exactAt_uniSeq : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (N m q : ℕ) (ρ : List ((Fin N → R) × (Fin N → R))), ρ ∈ splitSeq R N → ρ.length + m = N → s ≤ m → ExactAt (uniSeq R m) q → ExactAt {w | w ∈ uniSeq R N ∧ ∀ y ∈ ρ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} q := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_uniSeq_killed_by_split
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactHMapOneZeroOfStaircase
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.StairMid

variable {k G : Type} [CommRing k] [Group G]

def shC (C : ℕ → Rep k G) (Z : Rep k G) : ℕ → Rep k G
  | 0 => Z
  | n + 1 => C (n + 2)

def shD (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p) (Z : Rep k G) (b : C 2 ⟶ Z) :
    ∀ p, shC C Z (p + 1) ⟶ shC C Z p
  | 0 => b
  | p + 1 => d (p + 2)

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hs hex hH
  obtain ⟨Z, ι, hι, b, hse, hbι, hbs, hdb, hexb⟩ := GlobalTheory.T.exists_syzygy_factorization k G C d hd hs (hex 0 (by omega))
  have hfun : ∀ {A B : Rep k G} (f : A ⟶ B), hMap f i = (groupHomology.functor k G i).map f := fun f => rfl
  have hsurj : Function.Surjective (hMap b i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i (shC C Z) (shD C d Z b) ?_ hbs ?_ ?_
    · intro p
      cases p with
      | zero => exact hdb
      | succ p => exact hd (p + 2)
    · intro p hp
      cases p with
      | zero => exact hexb (hex 1 (by omega))
      | succ p => exact hex (p + 2) (by omega)
    · intro p q hp hpq
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      exact hH (r + 2) q (by omega) (by omega)
  have hles := (ShortComplex.moduleCat_exact_iff _).1 (groupHomology.mapShortComplex₂_exact hse i)
  have hcomp : hMap (d 1) i = hMap b i ≫ hMap ι i := by
    rw [hfun, hfun, hfun, ← hbι]
    exact (groupHomology.functor k G i).map_comp b ι
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hles x hx
    obtain ⟨z, rfl⟩ := hsurj y
    refine ⟨z, ?_⟩
    rw [hcomp]
    exact hy
  · rintro ⟨z, rfl⟩
    have h0 : hMap (d 1) i ≫ hMap (d 0) i = 0 := by
      have e := (groupHomology.functor k G i).map_comp (d 1) (d 0)
      rw [hd 0, Functor.map_zero] at e
      rw [hfun, hfun]
      exact e.symm
    rw [← ModuleCat.comp_apply, h0]
    rfl

end GlobalTheory.HomStab.StairMid

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exact_hMap_one_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.StairMid.main
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsHomologousCycleWithEntriesInOfExactAtLinks
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem exists_sub_bd_mem_chains_linkIn_nil :
    ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
      (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p →
        ExactAt (linkIn F S τ) (p - τ.length)) →
      ∀ c ∈ chains F p, bd V c = 0 →
        ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p ∧ bd V (c - bd V b) = 0 := by
  intro V F S hF p hex
  have key : ∀ k : ℕ, ∀ c ∈ chains {l ∈ F | ∀ y ∈ l.drop k, y ∈ S} p, bd V c = 0 →
      ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p := by
    intro k
    induction k with
    | zero =>
      intro c hc _
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero, sub_zero]
      refine Finsupp.supported_mono ?_ hc
      rintro l ⟨⟨hl, hS⟩, hp⟩
      exact ⟨⟨by simpa using hS, by simpa using hl⟩, hp⟩
    | succ k ih =>
      intro c hc h0
      obtain ⟨b, hb, hcb⟩ := GlobalTheory.T.seqChain_cycle_retraction_of_link_exact V F S hF p k
        (fun τ hτ x hx hxS _ hle => hex τ hτ x hx hxS hle) c hc h0
      obtain ⟨b', hb', hcb'⟩ := ih (c - bd V b) hcb
        (by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero])
      refine ⟨b + b', Submodule.add_mem _ hb hb', ?_⟩
      rw [map_add (f := _), ← sub_sub]
      exact hcb'
  intro c hc h0
  have hc' : c ∈ chains {l ∈ F | ∀ y ∈ l.drop p, y ∈ S} p := by
    refine Finsupp.supported_mono ?_ hc
    rintro l ⟨hl, hp⟩
    refine ⟨⟨hl, ?_⟩, hp⟩
    intro y hy
    rw [List.drop_eq_nil_of_le hp.le] at hy
    simp at hy
  obtain ⟨b, hb, hcb⟩ := key p c hc' h0
  exact ⟨b, hb, hcb, by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero]⟩

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ∀ c ∈ chains F p, bd V c = 0 → ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p ∧ bd V (c - bd V b) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.exists_sub_bd_mem_chains_linkIn_nil
end
end

