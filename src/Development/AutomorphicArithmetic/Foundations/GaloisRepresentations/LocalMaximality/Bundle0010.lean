module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdApply
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

private def ctrH {κ E : Type} [LinearOrder κ] [AddCommGroup E] (l : κ) (c : Finset κ → E) : Finset κ → E := fun L =>
  if l ∈ L then 0 else GlobalTheory.cubeSign (insert l L) l • c (insert l L)

private theorem wd_apply' {κ E : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] (w : κ → Module.End ℂ E)
    (c : Finset κ → E) (t : Finset κ) : wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private theorem wd_ctrH {κ E : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] (w : κ → Module.End ℂ E)
    (l : κ) (c : Finset κ → E) (t : Finset κ) :
    wd w (ctrH l c) t + ctrH l (wd w c) t = w l (c t) := by
  by_cases hi : l ∈ t
  · have h0 : ctrH l (wd w c) t = 0 := if_pos hi
    rw [h0, add_zero, wd_apply', Finset.sum_eq_single l]
    · have h1 : ctrH l c (t.erase l) = GlobalTheory.cubeSign t l • c t := by
        simp only [ctrH]
        rw [if_neg (by simp), Finset.insert_erase hi]
      rw [h1, map_zsmul, smul_smul, GlobalTheory.cubeSign_mul_self, one_smul]
    · intro j _ hji
      have h1 : ctrH l c (t.erase j) = 0 := if_pos (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩)
      rw [h1, map_zero, smul_zero]
    · intro h; exact absurd hi h
  · have h0 : ctrH l (wd w c) t = GlobalTheory.cubeSign (insert l t) l • wd w c (insert l t) := if_neg hi
    rw [h0, wd_apply' w c (insert l t), Finset.sum_insert hi, Finset.erase_insert hi, smul_add, smul_smul,
      GlobalTheory.cubeSign_mul_self, one_smul, Finset.smul_sum, wd_apply']
    have key : ∀ j ∈ t, GlobalTheory.cubeSign t j • w j (ctrH l c (t.erase j)) +
        GlobalTheory.cubeSign (insert l t) l • GlobalTheory.cubeSign (insert l t) j • w j (c ((insert l t).erase j)) = 0 := by
      intro j hj
      have hij : l ≠ j := fun h => hi (h ▸ hj)
      have h2 : ctrH l c (t.erase j) =
          GlobalTheory.cubeSign (insert l (t.erase j)) l • c (insert l (t.erase j)) :=
        if_neg (fun h => hi (Finset.mem_of_mem_erase h))
      rw [h2, map_zsmul, ← Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]
      have h1 := GlobalTheory.cubeSign_mul_erase (t := insert l t) (i := l) (j := j) (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hj) hij
      rw [Finset.erase_insert hi] at h1
      have ha := GlobalTheory.cubeSign_mul_self (insert l t) l
      have he := GlobalTheory.cubeSign_mul_self ((insert l t).erase j) l
      have : GlobalTheory.cubeSign t j * GlobalTheory.cubeSign ((insert l t).erase j) l +
          GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign (insert l t) j = 0 := by
        linear_combination (GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign ((insert l t).erase j) l) * h1
          - (GlobalTheory.cubeSign t j * GlobalTheory.cubeSign ((insert l t).erase j) l) * ha
          - (GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign (insert l t) j) * he
      rw [this, zero_smul]
    rw [add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero key, add_zero]

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.htpy_of :
    Htpy := by
  intro S E _ _ _ _ act κ _ _ R M r hS n c hc g hg
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨hcC, hcD⟩ := Submodule.mem_inf.1 hc
  have hD : wd (fun l => act (r l)) c = 0 := hcD
  have hcC' : c ∈ Submodule.pi Set.univ (fun s : Finset κ => if (s.card : ℤ) = n then M else ⊥) := hcC
  have hmem : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = n then M else ⊥ : Submodule ℂ E) :=
    fun s => (Submodule.mem_pi.1 hcC') s (Set.mem_univ _)
  have hcomm : ∀ (p q : S) (x : E), act p (act q x) = act q (act p x) := by
    intro p q x
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hstep : ∀ l t, wd (fun l => act (r l)) (ctrH l c) t = act (r l) (c t) := by
    intro l t
    have := wd_ctrH (fun l => act (r l)) l c t
    rw [hD] at this
    have h0 : ctrH l (0 : Finset κ → E) t = 0 := by
      simp [ctrH]
    rw [h0, add_zero] at this
    exact this
  refine Submodule.mem_map.2 ⟨fun L => ∑ l, act (a l) (ctrH l c L), ?_, ?_⟩
  · have : (fun L => ∑ l, act (a l) (ctrH l c L)) ∈
        Submodule.pi Set.univ (fun s : Finset κ => if (s.card : ℤ) = n - 1 then M else ⊥) := by
      refine Submodule.mem_pi.2 fun s _ => ?_
      by_cases hs : (s.card : ℤ) = n - 1
      · rw [if_pos hs]
        refine Submodule.sum_mem _ fun l _ => hS _ (ha l) _ ?_
        by_cases hl : l ∈ s
        · have : ctrH l c s = 0 := if_pos hl
          rw [this]; exact M.zero_mem
        · have h1 : ctrH l c s = GlobalTheory.cubeSign (insert l s) l • c (insert l s) := if_neg hl
          rw [h1]
          have h2 := hmem (insert l s)
          rw [if_pos (by rw [Finset.card_insert_of_notMem hl]; push_cast; omega)] at h2
          exact zsmul_mem h2 _
      · rw [if_neg hs]
        refine (Submodule.mem_bot _).2 (Finset.sum_eq_zero fun l _ => ?_)
        by_cases hl : l ∈ s
        · have : ctrH l c s = 0 := if_pos hl
          rw [this, map_zero]
        · have h1 : ctrH l c s = GlobalTheory.cubeSign (insert l s) l • c (insert l s) := if_neg hl
          have h2 := hmem (insert l s)
          rw [if_neg (by rw [Finset.card_insert_of_notMem hl]; push_cast; omega),
            Submodule.mem_bot] at h2
          rw [h1, h2, smul_zero, map_zero]
    exact this
  · show wd (fun l => act (r l)) _ = _
    funext t
    rw [wd_apply']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ i ∈ t, GlobalTheory.cubeSign t i • act (r i) (act (a l) (ctrH l c (t.erase i))) =
        act (a l) (act (r l) (c t)) := by
      intro l
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hstep l t, wd_apply', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, hcomm]
    rw [Finset.sum_congr rfl fun l _ => this l, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Module.End.mul_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WeightInverseContinuity
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma card_img {κ : Type} [LinearOrder κ] {d : ℕ} (e : Fin d ↪o κ) : (img e).card = d := by
  simp [img]

private lemma detC_img {S κ : Type} [CommRing S] [LinearOrder κ] {d : ℕ} (ρ : κ → Fin d → S) (e : Fin d ↪o κ)
    (A : Matrix (Fin d) (Fin d) S) (hA : ∀ a, ρ (e a) = A a) : detC ρ (img e) = A.det := by
  have h := card_img e
  have hu : e = (img e).orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique' h (fun x => by simp [img])
  rw [detC, dite_eq_left h]
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [← hu, hA]

private lemma detC_mem {S κ : Type} [CommRing S] [Algebra ℂ S] [LinearOrder κ] {d : ℕ} (R : Subalgebra ℂ S)
    (ρ : κ → Fin d → S) (h : ∀ l b, ρ l b ∈ R) (s : Finset κ) : detC ρ s ∈ R := by
  unfold detC
  split_ifs with hs
  · rw [Matrix.det_apply']
    exact R.sum_mem fun σ _ => R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => h _ _)
  · exact R.zero_mem

private lemma core (hDet : Det) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hKS : KSub) (hWB : WdBasic)
    {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
    {κ κ0 : Type} [LinearOrder κ] [Fintype κ] [LinearOrder κ0] [Fintype κ0]
    (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) {d : ℕ} (ι : κ0 ↪o κ) (e0 e0' : Fin d ↪o κ0)
    (N : Matrix (Fin d) (Fin d) S) (ρ : κ0 → Fin d → S)
    (h1 : ∀ j, ρ (e0 j) = Pi.single j 1) (h2 : ∀ a, ρ (e0' a) = N a) (hρ : ∀ l b, ρ l b ∈ R)
    (hrel : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)))
    (hSt : Stab act R M) (hr : ∀ l, r l ∈ R)
    (hKE : KE (kos act M fun j => r (ι (e0 j))) d) (c : Finset κ → E) (hc : c ∈ (kos act M r).Z d) :
    c ((img e0').map ι.toEmbedding) - act N.det (c ((img e0).map ι.toEmbedding)) ∈
      sm act M (Set.range fun j => r (ι (e0 j))) := by
  have hcC : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥) := fun s =>
    (Submodule.mem_inf.1 hc).1 s (Set.mem_univ _)
  have hcD : wd (fun l => act (r l)) c = 0 := (Submodule.mem_inf.1 hc).2
  obtain ⟨m, hm⟩ : ∃ m, m = c ((img e0).map ι.toEmbedding) := ⟨_, rfl⟩
  rw [← hm]
  have hmM : m ∈ M := by
    have := hcC ((img e0).map ι.toEmbedding)
    rw [if_pos (by simp [card_img])] at this
    rwa [hm]
  have hZ0 : (fun t : Finset κ0 => c (t.map ι.toEmbedding)) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · have := hcC (s.map ι.toEmbedding)
      simpa using this
    · show wd (fun l => act (r (ι l))) (fun t : Finset κ0 => c (t.map ι.toEmbedding)) = 0
      funext s
      have := (hWB κ E (fun _ => M) (fun l => act (r l))).2.2.2.2.2 κ0 ι c s
      rw [this, hcD]; rfl
  have hZ' : (fun s : Finset κ0 => act (detC ρ s) m) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · show act (detC ρ s) m ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥)
      split_ifs with hs
      · exact hSt _ (detC_mem R ρ hρ s) m hmM
      · have : s.card ≠ d := fun h => hs (by rw [h])
        simp [detC, this]
    · show wd (fun l => act (r (ι l))) (fun s : Finset κ0 => act (detC ρ s) m) = 0
      have := hDet S E act κ0 d ρ (fun b => r (ι (e0 b))) m
      rwa [show (fun l => act (∑ b, ρ l b * r (ι (e0 b)))) = fun l => act (r (ι l)) from
        funext fun l => by rw [hrel l]] at this
  have hB := hK2 S E act κ0 R M (fun l => r (ι l)) d e0 hSt (fun l => hr _) hKE _
    (Submodule.sub_mem _ hZ0 hZ') (by
      have h1' : detC ρ (img e0) = 1 := by
        rw [detC_img ρ e0 1 (fun a => by rw [h1 a]; ext b; simp [Matrix.one_apply, Pi.single_apply, eq_comm])]
        simp
      simp only [Pi.sub_apply, h1', map_one, Module.End.one_apply, ← hm, sub_self]
      exact Submodule.zero_mem _)
  have hval := (hKS S E act κ0 R M (fun l => r (ι l)) hSt (fun l => hr _)).2 d _ hB (img e0')
  have hdet : detC ρ (img e0') = N.det := detC_img ρ e0' N h2
  simp only [Pi.sub_apply, hdet] at hval
  refine (?_ : sm act M (Set.range fun l => r (ι l)) ≤ sm act M (Set.range fun j => r (ι (e0 j)))) hval
  unfold sm
  refine iSup₂_le ?_
  rintro _ ⟨l, rfl⟩ _ ⟨x, hx, rfl⟩
  show act (r (ι l)) x ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hrel l, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [mul_comm, map_mul, Module.End.mul_apply]
  exact (le_iSup₂_of_le (f := fun (t : S) (_ : t ∈ Set.range fun j => r (ι (e0 j))) => M.map (act t))
    (r (ι (e0 b))) ⟨b, rfl⟩ le_rfl) (Submodule.mem_map_of_mem (hSt _ (hρ l b) x hx))

theorem UpperTheory.Gal.productCup_of_system.koszulThree_of_det :
    Det → KoszulBoundaryOfComponentMemIdeal → KSub → WdBasic → K3 := by
  intro hDet hK2 hKS hWB S E _ _ _ _ act κ _ _ R M r d e e' N hSt hr hN hrel hdis hKE c hc
  classical
  have hmemL : ∀ j, e j ∈ img e ∪ img e' := fun j => Finset.mem_union_left _ (by simp [img])
  have hmemR : ∀ j, e' j ∈ img e ∪ img e' := fun j => Finset.mem_union_right _ (by simp [img])
  let ι : {l // l ∈ img e ∪ img e'} ↪o κ := OrderEmbedding.subtype _
  let e0 : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e j, hmemL j⟩) fun a b h => e.strictMono h
  let e0' : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e' j, hmemR j⟩) fun a b h => e'.strictMono h
  let ρ : {l // l ∈ img e ∪ img e'} → Fin d → S := fun l =>
    if h : ∃ j, e j = l.1 then Pi.single h.choose 1 else if h' : ∃ a, e' a = l.1 then N h'.choose else 0
  have h1 : ∀ j, ρ (e0 j) = Pi.single j 1 := fun j => by
    have hex : ∃ i, e i = (e0 j).1 := ⟨j, rfl⟩
    have : hex.choose = j := e.injective hex.choose_spec
    simp only [ρ]
    rw [dite_eq_left hex, this]
  have h2 : ∀ a, ρ (e0' a) = N a := fun a => by
    have hn : ¬ ∃ j, e j = (e0' a).1 := fun ⟨j, hj⟩ => hdis a j hj.symm
    have hex : ∃ i, e' i = (e0' a).1 := ⟨a, rfl⟩
    have : hex.choose = a := e'.injective hex.choose_spec
    simp only [ρ]
    rw [dite_eq_right hn, dite_eq_left hex, this]
  have hρ : ∀ l b, ρ l b ∈ R := fun l b => by
    simp only [ρ]
    split_ifs with h h'
    · rw [Pi.single_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · exact hN _ _
    · exact R.zero_mem
  have hrel' : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)) := fun l => by
    obtain ⟨l, hl⟩ := l
    rcases Finset.mem_union.1 hl with h | h
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 h
      have := h1 j
      change r (e j) = ∑ b, ρ (e0 j) b * r (e b)
      rw [this]
      simp [Pi.single_apply]
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h
      have := h2 a
      change r (e' a) = ∑ b, ρ (e0' a) b * r (e b)
      rw [this]
      exact hrel a
  have key := core hDet hK2 hKS hWB act R M r ι e0 e0' N ρ h1 h2 hρ hrel' hSt hr hKE c hc
  have hi : (img e0).map ι.toEmbedding = img e := by
    ext x; simp [img, ι, e0]
  have hi' : (img e0').map ι.toEmbedding = img e' := by
    ext x; simp [img, ι, e0']
  rw [hi, hi'] at key
  exact key
end

