module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ConsMemUniMIffMapSubSmul
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.UniModVec

theorem mem_uniM_iff_nat (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (l : List M) :
    l ∈ uniM R M ↔ ∃ f : ℕ → M →ₗ[R] R, ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      f i l[j] = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => if h : i < l.length then f ⟨i, h⟩ else 0, fun i j hi hj => ?_⟩
    have := hf ⟨i, hi⟩ ⟨j, hj⟩
    simp only [hi, dif_pos]
    simpa [Fin.ext_iff] using this
  · rintro ⟨f, hf⟩
    refine ⟨fun i => f i, fun i j => ?_⟩
    have := hf i j i.isLt j.isLt
    simpa [Fin.ext_iff] using this

end GlobalTheory.UniModVec

namespace GlobalTheory.UniModVec

theorem cons_mem_uniM_iff_map_proj : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (v : M), φ v = 1 → ∀ l : List M, (v :: l) ∈ uniM R M ↔ l.map (fun x => x - φ x • v) ∈ uniM R M := by
  intro R M _ _ _ φ v hv l
  rw [mem_uniM_iff_nat, mem_uniM_iff_nat]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨fun i => F (i+1), fun i j hi hj => ?_⟩
    simp only [List.length_map] at hi hj
    have h1 := hF (i+1) (j+1) (by simp; omega) (by simp; omega)
    have h2 := hF (i+1) 0 (by simp; omega) (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h1 h2
    simp only [List.getElem_map, map_sub, map_smul, smul_eq_mul, h1, h2]
    simp
  · rintro ⟨H, hH⟩
    simp only [List.length_map, List.getElem_map] at hH
    let P : M →ₗ[R] M := LinearMap.id - φ.smulRight v
    have hP : ∀ x, P x = x - φ x • v := fun x => by simp [P]
    have hPv : P v = 0 := by rw [hP, hv, one_smul, sub_self]
    let F : ℕ → M →ₗ[R] R := fun i => match i with
      | 0 => φ - ∑ k : Fin l.length, φ (l.get k) • (H k).comp P
      | k+1 => (H k).comp P
    refine ⟨F, fun i j hi hj => ?_⟩
    simp only [List.length_cons] at hi hj
    rcases i with _ | i <;> rcases j with _ | j
    · simp [F, hPv, hv]
    · have hj' : j < l.length := by omega
      have hF0 : F 0 (l[j]) = φ l[j] - ∑ k : Fin l.length, φ (l.get k) * H k (l[j] - φ l[j] • v) := by
        simp only [F, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, hP, smul_eq_mul]
      simp only [List.getElem_cons_succ]
      rw [hF0, Finset.sum_eq_single ⟨j, hj'⟩]
      · rw [hH j j hj' hj']; simp
      · intro k _ hk
        rw [hH k j k.isLt hj', if_neg (fun h => hk (Fin.ext h)), mul_zero]
      · simp
    · simp [F, hPv]
    · have hi' : i < l.length := by omega
      have hj' : j < l.length := by omega
      simp only [F, List.getElem_cons_succ, LinearMap.comp_apply, hP, hH i j hi' hj']
      simp

end GlobalTheory.UniModVec

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.cons_mem_uniM_iff_map_sub_smul : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (v : M), φ v = 1 → ∀ l : List M, (v :: l) ∈ uniM R M ↔ l.map (fun x => x - φ x • v) ∈ uniM R M := by
  first
  | exact @GlobalTheory.UniModVec.cons_mem_uniM_iff_map_proj
  | exact @GlobalTheory.UniModVec.mem_uniM_iff_nat
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInUniMOfExactAtMapLinearEquiv
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxLinkEquiv

theorem uniM_map_of_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    (l : List M) (h : l ∈ uniM R M) : l.map ψ ∈ uniM R M := by
  obtain ⟨f, hf⟩ := h
  have hl : (l.map ψ).length = l.length := by simp
  refine ⟨fun i => (f (Fin.cast hl i)).comp ψ.symm.toLinearMap, ?_⟩
  intro i j
  have := hf (Fin.cast hl i) (Fin.cast hl j)
  simpa [Fin.ext_iff] using this

theorem linkIn_map {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    (X : Set M) (hX : ∀ x, ψ x ∈ X ↔ x ∈ X) (τ : List M) :
    linkIn (uniM R M) X (τ.map ψ) = List.map ψ '' linkIn (uniM R M) X τ := by
  ext w
  simp only [linkIn, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hw, hmem⟩
    refine ⟨w.map ψ.symm, ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [← hX]
      simpa using hw y hy
    · have := uniM_map_of_mem ψ.symm _ hmem
      simpa [List.map_append, List.map_map, Function.comp_def] using this
    · simp [List.map_map, Function.comp_def]
  · rintro ⟨w', ⟨hw', hmem⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact (hX y).2 (hw' y hy)
    · have := uniM_map_of_mem ψ _ hmem
      simpa [List.map_append] using this

private theorem bd_mapDomain_listMap_comm {V : Type} (g : V → V) (c : List V →₀ ℤ) :
    bd V (Finsupp.mapDomain (List.map g) c) = Finsupp.mapDomain (List.map g) (bd V c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [Finsupp.mapDomain_add, ha, hb]
  | single l n =>
    simp [bd, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul, List.eraseIdx_map]

private theorem mapDomain_listMap_mem_chains_of_map_mem {V : Type} (g : V → V) (F G : Set (List V))
    (hFG : ∀ l ∈ F, l.map g ∈ G) (p : ℕ) (c : List V →₀ ℤ) (hc : c ∈ chains F p) :
    Finsupp.mapDomain (List.map g) c ∈ chains G p := by
  classical
  rw [chains, Finsupp.mem_supported] at hc ⊢
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
  obtain ⟨hlF, hlen⟩ := hc hl
  exact ⟨hFG l hlF, by simp [hlen]⟩

theorem exactAt_linkIn_of_map : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M) (X : Set M), (∀ x, ψ x ∈ X ↔ x ∈ X) → ∀ (τ : List M) (p : ℕ), ExactAt (linkIn (uniM R M) X (τ.map ψ)) p → ExactAt (linkIn (uniM R M) X τ) p := by
  intro R M _ _ _ ψ X hX τ p h
  rw [linkIn_map ψ X hX τ] at h
  intro c hc hbd
  have hc' := mapDomain_listMap_mem_chains_of_map_mem (⇑ψ) (linkIn (uniM R M) X τ)
    (List.map ψ '' linkIn (uniM R M) X τ) (fun l hl => ⟨l, hl, rfl⟩) p c hc
  obtain ⟨b, hb, hbb⟩ := h _ hc' (by rw [bd_mapDomain_listMap_comm, hbd]; simp)
  refine ⟨Finsupp.mapDomain (List.map ψ.symm) b,
    mapDomain_listMap_mem_chains_of_map_mem (⇑ψ.symm) _ _ ?_ _ b hb, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    simpa [List.map_map, Function.comp_def] using hl
  · have hid : (List.map ψ.symm ∘ List.map ψ) = id := by
      funext l
      simp [List.map_map, Function.comp_def]
    rw [bd_mapDomain_listMap_comm, hbb, ← Finsupp.mapDomain_comp, hid, Finsupp.mapDomain_id]

end GlobalTheory.SeqCxLinkEquiv

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_linkIn_uniM_of_exactAt_map_linearEquiv : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M) (X : Set M), (∀ x, ψ x ∈ X ↔ x ∈ X) → ∀ (τ : List M) (p : ℕ), ExactAt (linkIn (uniM R M) X (τ.map ψ)) p → ExactAt (linkIn (uniM R M) X τ) p := by
  first
  | exact @GlobalTheory.SeqCxLinkEquiv.exactAt_linkIn_of_map
  | exact @GlobalTheory.SeqCxLinkEquiv.linkIn_map
  | exact @GlobalTheory.SeqCxLinkEquiv.uniM_map_of_mem
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtUnimodularSeqsOfLinkNilCoordSubspace
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxLow

noncomputable def emb (R : Type) [CommRing R] (m : ℕ) : (Fin m → R) →ₗ[R] (ℕ →₀ R) :=
  Finsupp.lmapDomain R R Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite R R (Fin m)).symm.toLinearMap

theorem emb_apply_val {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) (k : Fin m) :
    emb R m v (k : ℕ) = v k := by
  simp [emb, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

theorem emb_apply_of_le {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) (n : ℕ) (h : m ≤ n) :
    emb R m v n = 0 := by
  simp only [emb, LinearMap.comp_apply, Finsupp.lmapDomain_apply, LinearEquiv.coe_coe]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, hk⟩
  have hk2 := k.isLt
  omega

theorem emb_injective (R : Type) [CommRing R] (m : ℕ) : Function.Injective (emb R m) := by
  intro v w hvw
  funext k
  have e := congrArg (fun x => x (k : ℕ)) hvw
  simpa only [emb_apply_val] using e

theorem emb_mem_low {R : Type} [CommRing R] {m : ℕ} (v : Fin m → R) : emb R m v ∈ low R m :=
  fun n h => emb_apply_of_le v n h

theorem emb_restrict {R : Type} [CommRing R] {m : ℕ} (x : ℕ →₀ R) (hx : x ∈ low R m) :
    emb R m (fun k : Fin m => x k) = x := by
  ext n
  by_cases h : n < m
  · have e := emb_apply_val (fun k : Fin m => x k) ⟨n, h⟩
    simpa using e
  · rw [emb_apply_of_le _ n (not_lt.mp h)]
    exact (hx n (not_lt.mp h)).symm

theorem form_emb {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (v : Fin m → R) :
    (∑ k : Fin m, g k • Finsupp.lapply (R := R) (M := R) (k : ℕ)) (emb R m v) = g ⬝ᵥ v := by
  simp [dotProduct, emb_apply_val]

theorem emb_form {R : Type} [CommRing R] {m : ℕ} (f : (ℕ →₀ R) →ₗ[R] R) (v : Fin m → R) :
    (fun k => f (emb R m (Pi.single k 1))) ⬝ᵥ v = f (emb R m v) := by
  have hs : ∀ k, (Pi.single k (v k) : Fin m → R) = v k • (Pi.single k 1 : Fin m → R) := by
    intro k
    ext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj]
  conv_rhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hs, map_smul, smul_eq_mul, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

theorem link_eq (R : Type) [CommRing R] (m : ℕ) :
    linkIn (uniM R (ℕ →₀ R)) (low R m) [] = List.map (emb R m) '' uniSeq R m := by
  ext w
  simp only [linkIn, Set.mem_ofPred_eq, List.nil_append, Set.mem_image]
  constructor
  · rintro ⟨hw, f, hf⟩
    refine ⟨w.map (fun x (k : Fin m) => x k), ⟨fun i k => f (Fin.cast (by simp) i) (emb R m (Pi.single k 1)), ?_⟩, ?_⟩
    · intro i j
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [emb_form, emb_restrict _ (hw _ (List.getElem_mem _))]
      have e := hf (Fin.cast (by simp) i) (Fin.cast (by simp) j)
      simpa [List.get_eq_getElem, Fin.ext_iff] using e
    · rw [List.map_map]
      refine (List.map_congr_left ?_).trans (List.map_id w)
      intro x hx
      exact emb_restrict x (hw x hx)
  · rintro ⟨u, ⟨g, hg⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact emb_mem_low y
    · refine ⟨fun i => ∑ k : Fin m, g (Fin.cast (by simp) i) k • Finsupp.lapply (R := R) (M := R) (k : ℕ), ?_⟩
      intro i j
      simp only [List.get_eq_getElem, List.getElem_map]
      rw [form_emb]
      have e := hg (Fin.cast (by simp) i) (Fin.cast (by simp) j)
      simpa [List.get_eq_getElem, Fin.ext_iff] using e

end GlobalTheory.SeqCxLow

private theorem exactAt_of_exactAt_image_injective {V U : Type} (e : V → U) (he : Function.Injective e)
    (F : Set (List V)) (q : ℕ) (h : ExactAt (List.map e '' F) q) : ExactAt F q := by
  classical
  have hM : Function.Injective (List.map e) := List.map_injective_iff.mpr he
  have comm : ∀ c, bd U (Finsupp.mapDomain (List.map e) c) = Finsupp.mapDomain (List.map e) (bd V c) := by
    intro c
    have E : (bd U).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) = (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [bd, map_sum, Finsupp.lmapDomain_apply, Finsupp.mapDomain_smul, Finsupp.mapDomain_single, List.eraseIdx_map]
    exact LinearMap.congr_fun E c
  intro c hc hbc
  have hc' : Finsupp.mapDomain (List.map e) c ∈ chains (List.map e '' F) q := by
    rw [chains, Finsupp.mem_supported] at hc ⊢
    intro z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp hz))
    have hl' := hc (Finset.mem_coe.mpr hl)
    exact ⟨⟨l, hl'.1, rfl⟩, by simp [hl'.2]⟩
  obtain ⟨b', hb', hbb⟩ := h _ hc' (by rw [comm, hbc, Finsupp.mapDomain_zero])
  rw [chains, Finsupp.mem_supported] at hb'
  have hrange : ↑b'.support ⊆ Set.range (List.map e) := by
    intro z hz
    obtain ⟨⟨l, _, rfl⟩, _⟩ := hb' hz
    exact ⟨l, rfl⟩
  refine ⟨Finsupp.comapDomain (List.map e) b' hM.injOn, ?_, ?_⟩
  · rw [chains, Finsupp.mem_supported]
    intro l hl
    rw [Finset.mem_coe, Finsupp.comapDomain_support, Finset.mem_preimage] at hl
    obtain ⟨⟨l', hl'F, hl'e⟩, hlen⟩ := hb' (Finset.mem_coe.mpr hl)
    have hll := hM hl'e
    subst hll
    exact ⟨hl'F, by simpa using hlen⟩
  · apply Finsupp.mapDomain_injective hM
    rw [← comm, Finsupp.mapDomain_comapDomain (List.map e) hM b' hrange, hbb]

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_unimodularSeqs_of_link_nil_coordSubspace : ∀ (R : Type) [CommRing R] (m q : ℕ), ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R m) []) q → ExactAt (uniSeq R m) q := by
  intro R _ m q h
  rw [GlobalTheory.SeqCxLow.link_eq] at h
  exact exactAt_of_exactAt_image_injective _ (GlobalTheory.SeqCxLow.emb_injective R m) _ _ h
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsBdOfVbdEqOfOneTermCycle
section
noncomputable section

namespace GlobalTheory.SeqCx.OneTermEnd

open GlobalTheory.SeqCx

open Classical

def slicePr (V W : Type) (w : List W) : (List V × List W →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun q : List V × List W =>
    if q.2 = w then Finsupp.single q.1 (1 : ℤ) else 0

theorem bd_single_one (V : Type) (u : V) :
    bd V (Finsupp.single [u] 1) = Finsupp.single ([] : List V) 1 := by
  simp [bd, Finsupp.linearCombination_single]

theorem lc_single_one (V : Type) (x : List V →₀ ℤ) :
    Finsupp.linearCombination ℤ (fun l : List V => Finsupp.single l (1:ℤ)) x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add (f := _), hf, hg]
  | single l c => rw [Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem slicePr_mapDomain (V W : Type) (w w' : List W) (x : List V →₀ ℤ) :
    slicePr V W w (Finsupp.mapDomain (fun l => (l, w')) x) = if w' = w then x else 0 := by
  unfold slicePr
  rw [Finsupp.linearCombination_mapDomain]
  split_ifs with h
  · simp [Function.comp_def, h, lc_single_one]
  · simp only [Function.comp_def, h, if_false]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add (f := _), hf, hg, add_zero]
    | single l c => simp [Finsupp.linearCombination_single]

theorem slicePr_hbd (V W : Type) (w : List W) :
    (slicePr V W w).comp (hbd V W) = (bd V).comp (slicePr V W w) := by
  apply Finsupp.lhom_ext'
  rintro ⟨l, w'⟩
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [show hbd V W (Finsupp.single (l, w') 1) =
      Finsupp.mapDomain (fun x => (x, w')) (bd V (Finsupp.single l 1)) by
    simp [hbd, Finsupp.linearCombination_single]]
  rw [slicePr_mapDomain]
  simp only [slicePr, Finsupp.linearCombination_single, one_smul]
  split_ifs <;> simp

private theorem slicePr_apply_eq (V W : Type) (w : List W) (z : List V × List W →₀ ℤ)
    (l : List V) : slicePr V W w z l = z (l, w) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single q c =>
    obtain ⟨l', w'⟩ := q
    simp only [slicePr, Finsupp.linearCombination_single]
    by_cases h : w' = w
    · subst h
      simp [Finsupp.single_apply]
    · simp [h, Finsupp.single_apply, Ne.symm h]

theorem slicePr_mem {V W : Type} (D : Set (List V × List W)) (p b : ℕ) (w : List W) :
    ∀ z ∈ chains2 D p b, slicePr V W w z ∈ chains {l | (l, w) ∈ D} p := by
  intro z hz
  rw [chains, Finsupp.mem_supported]
  intro l hl
  rw [Finset.mem_coe, Finsupp.mem_support_iff, slicePr_apply_eq] at hl
  have h := (Finsupp.mem_supported ℤ z).mp hz (Finsupp.mem_support_iff.mpr hl)
  exact ⟨h.1, h.2.1⟩

theorem vbd_eq {V W : Type} (D : Set (List V × List W)) (p : ℕ) :
    ∀ z ∈ chains2 D p 1, vbd V W z =
      Finsupp.mapDomain (fun l => (l, ([] : List W))) (Finsupp.mapDomain Prod.fst z) := by
  intro z hz
  have hs := (Finsupp.mem_supported ℤ z).mp hz
  have e : ∀ y : List V × List W →₀ ℤ,
      Finsupp.mapDomain (fun l => (l, ([] : List W))) (Finsupp.mapDomain Prod.fst y) =
      ((Finsupp.lmapDomain ℤ ℤ (fun l : List V => (l, ([] : List W)))).comp
        (Finsupp.lmapDomain ℤ ℤ (Prod.fst : List V × List W → List V))) y := fun y => rfl
  rw [e]
  conv_lhs => rw [← Finsupp.sum_single z]
  conv_rhs => rw [← Finsupp.sum_single z]
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro q hq
  obtain ⟨l, w⟩ := q
  have h := hs hq
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp h.2.2
  subst hu
  simp [vbd, Finsupp.linearCombination_single, bd_single_one, Finsupp.mapDomain_single,
    Finsupp.smul_single]

theorem sum_slicePr {V W : Type} (z : List V × List W →₀ ℤ) (U : Finset (List W))
    (hU : ∀ q ∈ z.support, q.2 ∈ U) :
    ∑ w ∈ U, slicePr V W w z = Finsupp.mapDomain Prod.fst z := by
  unfold Finsupp.mapDomain
  conv_lhs => rw [← Finsupp.sum_single z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp [slicePr, Finsupp.linearCombination_single, hU q hq, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finsupp.smul_single]

theorem exists_sum_bd {V : Type} (F : Set (List V)) (p : ℕ) {ι : Type} (S : Finset ι)
    (f : ι → List V →₀ ℤ) (hS : ∀ i ∈ S, ∃ b ∈ chains F (p + 1), bd V b = f i) :
    ∃ b ∈ chains F (p + 1), bd V b = ∑ i ∈ S, f i := by
  choose! g hg1 hg2 using hS
  refine ⟨∑ i ∈ S, g i, Submodule.sum_mem _ (fun i hi => hg1 i hi), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl (fun i hi => hg2 i hi)

theorem bd_of_oneTerm_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (F : Set (List V)) (p : ℕ),
    (∀ u : W, (∃ l, (l, [u]) ∈ D) → ∀ c ∈ chains {l | (l, [u]) ∈ D} p, bd V c = 0 →
      ∃ b ∈ chains F (p + 1), bd V b = c) →
    ∀ z ∈ chains2 D p 1, hbd V W z = 0 → ∀ c : List V →₀ ℤ,
      vbd V W z = Finsupp.mapDomain (fun l => (l, ([] : List W))) c →
      ∃ b ∈ chains F (p + 1), bd V b = c := by
  intro V W D F p hyp z hz hh c hc
  rw [vbd_eq D p z hz] at hc
  have hinj : Function.Injective (fun l : List V => (l, ([] : List W))) :=
    fun a b h => (Prod.ext_iff.mp h).1
  have hc' : c = Finsupp.mapDomain Prod.fst z := (Finsupp.mapDomain_injective hinj hc).symm
  have hs := (Finsupp.mem_supported ℤ z).mp hz
  have hU : ∀ q ∈ z.support, q.2 ∈ z.support.image Prod.snd :=
    fun q hq => Finset.mem_image_of_mem _ hq
  rw [hc', ← sum_slicePr z _ hU]
  apply exists_sum_bd
  intro w hw
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
  have h := hs hq
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp h.2.2
  have hmem := slicePr_mem D p 1 q.2 z hz
  have hbd0 : bd V (slicePr V W q.2 z) = 0 := by
    have key := LinearMap.congr_fun (slicePr_hbd V W q.2) z
    simp only [LinearMap.comp_apply] at key
    rw [← key, hh, map_zero]
  have hD : (q.1, [u]) ∈ D := by
    rw [← hu]
    exact h.1
  rw [hu] at hmem hbd0
  rw [hu]
  exact hyp u ⟨q.1, hD⟩ _ hmem hbd0

end GlobalTheory.SeqCx.OneTermEnd

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.exists_bd_of_vbd_eq_of_oneTerm_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (F : Set (List V)) (p : ℕ), (∀ u : W, (∃ l, (l, [u]) ∈ D) → ∀ c ∈ chains {l | (l, [u]) ∈ D} p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c) → ∀ z ∈ chains2 D p 1, hbd V W z = 0 → ∀ c : List V →₀ ℤ, vbd V W z = Finsupp.mapDomain (fun l => (l, ([] : List W))) c → ∃ b ∈ chains F (p + 1), bd V b = c := by
  first
  | exact @GlobalTheory.SeqCx.OneTermEnd.bd_of_oneTerm_cycle
  | exact @GlobalTheory.SeqCx.OneTermEnd.exists_sum_bd
  | exact @GlobalTheory.SeqCx.OneTermEnd.sum_slicePr
  | exact @GlobalTheory.SeqCx.OneTermEnd.vbd_eq
  | exact @GlobalTheory.SeqCx.OneTermEnd.slicePr_mem
  | exact @GlobalTheory.SeqCx.OneTermEnd.slicePr_hbd
  | exact @GlobalTheory.SeqCx.OneTermEnd.slicePr_mapDomain
  | exact @GlobalTheory.SeqCx.OneTermEnd.lc_single_one
  | exact @GlobalTheory.SeqCx.OneTermEnd.bd_single_one
end
end
end

