module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BicechCohomologyKunnethDecomposition

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeInj
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_one_eq {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (c : Finset ι → E) : wd (fun _ => (1 : Module.End ℂ E)) c = deltaL ℂ ι E c := by
  funext t
  rw [wd_apply']
  simp [deltaL, GlobalTheory.DI.delta]

private lemma wd_tail {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (v : E) (L : Finset ι)
    (hL : L.Nonempty) :
    wd (fun _ => (1 : Module.End ℂ E)) (fun L' : Finset ι => if L' = ∅ then v else 0) L =
      if L.card = 1 then v else 0 := by
  rw [wd_apply']
  split_ifs with h
  · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h
    simp [GlobalTheory.cubeSign, Finset.filter_singleton]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : L.erase i ≠ ∅ := by
      intro h0
      apply h
      have := Finset.card_erase_of_mem hi
      rw [h0, Finset.card_empty] at this
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [this]

theorem UpperTheory.Gal.productCup_of_system.edgeInj_of :
    WdUni → EdgeInj := by
  intro hU ι E _ _ _ _ G d x hx hB
  obtain ⟨y, hyC, hy⟩ := hB
  have hxC := hx.1
  have hxd : deltaL ℂ ι E x = 0 := hx.2
  have hy' : wd (fun _ => (1 : Module.End ℂ E)) y = edge1 x := hy
  have hyC' : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then
      mixF (fun I J => G (uni I J)) s else ⊥) := fun s => hyC s (Set.mem_univ s)
  have hxC' : ∀ I, x I ∈ (if I.Nonempty ∧ (I.card : ℤ) = (d : ℤ) + 1 then G (uni I ∅) else ⊥) :=
    fun I => hxC I (Set.mem_univ I)
  have hUn := hU ι ι E (fun _ => 1)
  have hl : ∀ (b L : Finset ι), lft (uni b L) = b := fun b L => (hUn y b L).2.1
  have hr : ∀ (b L : Finset ι), rgt (uni b L) = L := fun b L => (hUn y b L).2.2.1
  have hc : ∀ (b L : Finset ι), (uni b L).card = b.card + L.card := fun b L => (hUn y b L).2.2.2.1
  have hs : ∀ s : Finset (ι ⊕ₗ ι), uni (lft s) (rgt s) = s := (hUn y ∅ ∅).2.2.2.2
  have hx0 : ∀ I : Finset ι, (I.card : ℤ) ≠ (d : ℤ) + 1 → x I = 0 := by
    intro I hI
    have := hxC' I
    rw [if_neg (fun h => hI h.2)] at this
    simpa using this
  have hy0 : ∀ s, ¬ ((lft s).Nonempty ∧ (rgt s).Nonempty) → y s = 0 := by
    intro s h
    have := hyC' s
    split_ifs at this
    · simpa [mixF, h] using this
    · simpa using this
  let e : Finset (ι ⊕ₗ ι) → E := fun s => if rgt s = ∅ then x (lft s) else 0
  have he : ∀ b L, e (uni b L) = if L = ∅ then x b else 0 := by
    intro b L
    simp only [e, hl, hr]
  have hwe : ∀ s, wd (fun _ => (1 : Module.End ℂ E)) e s = (-((-1 : ℤ) ^ d)) • edge1 x s := by
    intro s
    rw [← hs s]
    generalize lft s = b
    generalize rgt s = L
    have h1 := (hU ι ι E (fun _ => 1) e b L).1
    simp only [he] at h1
    rw [h1]
    by_cases hL : L = ∅
    · subst hL
      have : edge1 (κ := ι) x (uni b ∅) = 0 := by simp [edge1, hr]
      rw [this, smul_zero]
      have hd : wd (fun _ => (1 : Module.End ℂ E)) x = 0 := by rw [wd_one_eq, hxd]
      have e1 : (fun b' : Finset ι => if (∅ : Finset ι) = ∅ then x b' else 0) = x := by
        funext b'
        simp
      rw [e1, hd]
      simp [wd_apply']
    · have hLn : L.Nonempty := Finset.nonempty_iff_ne_empty.2 hL
      simp only [hL, if_false]
      have h0 : wd (fun _ => (1 : Module.End ℂ E)) (fun _ : Finset ι => (0 : E)) b = 0 := by
        simp [wd_apply']
      have h2 := wd_tail (x b) L hLn
      rw [h0, h2, zero_add]
      simp only [edge1, hl, hr]
      split_ifs with h1c
      · by_cases hb : (b.card : ℤ) = (d : ℤ) + 1
        · have hb' : b.card = d + 1 := by exact_mod_cast hb
          rw [hb', pow_succ]
          simp
        · simp [hx0 b hb]
      · simp
  refine ⟨e + ((-1 : ℤ) ^ d) • y, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro s _
    change (e + ((-1 : ℤ) ^ d) • y) s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) + 1 then G s else ⊥)
    by_cases hr0 : rgt s = ∅
    · have hys : y s = 0 := hy0 s (fun h => h.2.ne_empty hr0)
      have hs' : uni (lft s) ∅ = s := by
        have := hs s
        rwa [hr0] at this
      have hcard : s.card = (lft s).card := by
        have := hc (lft s) ∅
        rw [hs'] at this
        simpa using this
      have hval : (e + ((-1 : ℤ) ^ d) • y) s = x (lft s) := by
        simp [e, hr0, hys]
      rw [hval]
      split_ifs with h
      · have := hxC' (lft s)
        have hlc : ((lft s).card : ℤ) = (d : ℤ) + 1 := by rw [← hcard]; exact h.2
        have hne : (lft s).Nonempty := by
          apply Finset.card_pos.1
          omega
        rw [if_pos ⟨hne, hlc⟩, hs'] at this
        exact this
      · have : x (lft s) = 0 := by
          apply hx0
          intro hlc
          apply h
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by rw [hcard]; exact hlc
          refine ⟨Finset.card_pos.1 ?_, hsc⟩
          omega
        simp [this]
    · have hval : (e + ((-1 : ℤ) ^ d) • y) s = ((-1 : ℤ) ^ d) • y s := by
        simp [e, hr0]
      rw [hval]
      by_cases hcs : (s.card : ℤ) = (d : ℤ) + 2 - 1
      · by_cases hlr : (lft s).Nonempty ∧ (rgt s).Nonempty
        · have := hyC' s
          rw [if_pos hcs] at this
          simp only [mixF, if_pos hlr, hs s] at this
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by omega
          rw [if_pos ⟨Finset.card_pos.1 (by omega), hsc⟩]
          exact zsmul_mem this _
        · simp [hy0 s hlr]
      · have := hyC' s
        rw [if_neg hcs] at this
        have h0 : y s = 0 := by simpa using this
        simp [h0]
  · change deltaL ℂ (ι ⊕ₗ ι) E (e + ((-1 : ℤ) ^ d) • y) = 0
    rw [← wd_one_eq, map_add (f := _), map_zsmul, hy']
    funext s
    simp [hwe]
  · intro J
    have h1 : y (uni ∅ J) = 0 := hy0 _ (fun h => by
      have := h.1
      rw [hl] at this
      simp at this)
    have h2 : x ∅ = 0 := hx0 ∅ (by simp; omega)
    simp [he, h1, h2]
  · intro I
    have h1 : y (uni I ∅) = 0 := hy0 _ (fun h => by
      have := h.2
      rw [hr] at this
      simp at this)
    simp [he, h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PKunDec
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {ι G : Type} [LinearOrder ι] [AddCommGroup G] [Module ℂ G]

private def kdTw (c : Finset (ι ⊕ₗ ι) → G) : Finset ι × Finset ι → G :=
  fun x => ((-1 : ℤ) ^ x.2.card) • c (uni x.1 x.2)

private def kdUn : (Finset ι × Finset ι → G) →ₗ[ℂ] (Finset (ι ⊕ₗ ι) → G) :=
  LinearMap.pi fun s => ((-1 : ℤ) ^ (rgt s).card) •
    LinearMap.proj (R := ℂ) (φ := fun _ : Finset ι × Finset ι => G) (lft s, rgt s)

private theorem kdUn_apply (z : Finset ι × Finset ι → G) (s : Finset (ι ⊕ₗ ι)) :
    kdUn z s = ((-1 : ℤ) ^ (rgt s).card) • z (lft s, rgt s) := by
  simp [kdUn]

private theorem kd_wd_one (c : Finset ι → G) (t : Finset ι) :
    wd (fun _ => (1 : Module.End ℂ G)) c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • c (t.erase i) := by
  simp [wd, LinearMap.sum_apply]

private theorem kd_biD (z : Finset ι × Finset ι → G) (I J : Finset ι) :
    biD ℂ ι ι G z (I, J) = ∑ i ∈ I, GlobalTheory.cubeSign I i • z (I.erase i, J) +
      ((-1 : ℤ) ^ (I.card + 1)) • ∑ j ∈ J, GlobalTheory.cubeSign J j • z (I, J.erase j) := by
  simp [biD, LinearMap.sum_apply]

private theorem kd_neg_sq (n : ℕ) (x : G) : ((-1 : ℤ) ^ n) • ((-1 : ℤ) ^ n) • x = x := by
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

private theorem kdUn_tw (hU : WdUni) (c : Finset (ι ⊕ₗ ι) → G) : kdUn (kdTw c) = c := by
  funext s
  rw [kdUn_apply]
  have h := (hU ι ι G (fun _ => 1) c ∅ ∅).2.2.2.2 s
  simp only [kdTw, h]
  exact kd_neg_sq _ _

private theorem kdTw_un (hU : WdUni) (z : Finset ι × Finset ι → G) : kdTw (kdUn z) = z := by
  funext x
  obtain ⟨I, J⟩ := x
  have h := hU ι ι G (fun _ => 1) (fun _ => 0) I J
  simp only [kdTw]
  rw [kdUn_apply, h.2.1, h.2.2.1]
  exact kd_neg_sq _ _

private theorem kd_biD_tw (hU : WdUni) (c : Finset (ι ⊕ₗ ι) → G) :
    biD ℂ ι ι G (kdTw c) = kdTw (wd (fun _ => (1 : Module.End ℂ G)) c) := by
  funext x
  obtain ⟨I, J⟩ := x
  have h := hU ι ι G (fun _ => 1) c I J
  rw [kd_biD]
  simp only [kdTw, h.1, kd_wd_one]
  simp only [smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.card_erase_of_mem hj]
    obtain ⟨n, hn⟩ : ∃ n, J.card = n + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hj)
    rw [hn, Nat.add_sub_cancel]
    congr 1
    ring

private theorem kd_wd_un (hU : WdUni) (y : Finset ι × Finset ι → G) :
    wd (fun _ => (1 : Module.End ℂ G)) (kdUn y) = kdUn (biD ℂ ι ι G y) := by
  have h := kd_biD_tw hU (kdUn y)
  rw [kdTw_un hU] at h
  rw [h, kdUn_tw hU]

end

section
variable {ι E E' G : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
  [AddCommGroup G] [Module ℂ G]

private theorem kd_cech_val {A : Finset ι → Submodule ℂ E} {a : Finset ι → E} {p : ℤ} (ha : a ∈ (cech A).Z p)
    {s : Finset ι} (hs : (s.card : ℤ) ≠ p + 1) : a s = 0 := by
  unfold cech Cx.Z at ha
  simp [cechC] at ha
  have h := ha.1 s
  rw [if_neg (fun h' => hs h'.2)] at h
  simpa using h

private theorem kd_cech_zero {A : Finset ι → Submodule ℂ E} {a : Finset ι → E} {p : ℤ} (ha : a ∈ (cech A).Z p)
    (hp : p < 0) : a = 0 := by
  unfold cech Cx.Z at ha
  simp [cechC] at ha
  funext s
  have h := ha.1 s
  rw [if_neg] at h
  · simpa using h
  · rintro ⟨hne, hc⟩
    have := hne.card_pos
    omega

private theorem kd_single (μ : E →ₗ[ℂ] E' →ₗ[ℂ] G) (A : Finset ι → Submodule ℂ E) (B : Finset ι → Submodule ℂ E')
    (d : ℕ) (p : ℤ) (a : Finset ι → E) (b : Finset ι → E') (ha : a ∈ (cech A).Z p) (hb : b ∈ (cech B).Z ((d : ℤ) - p)) :
    ∃ (q : ℕ) (a' : Finset ι → E) (b' : Finset ι → E'),
      (q ≤ d ∧ a' ∈ (cech A).Z ((d : ℤ) - q) ∧ b' ∈ (cech B).Z q) ∧ join μ a' b' = kdUn (boxC μ a b) := by
  rcases lt_or_ge p 0 with hp | hp
  · refine ⟨0, 0, 0, ⟨Nat.zero_le _, Submodule.zero_mem _, Submodule.zero_mem _⟩, ?_⟩
    rw [kd_cech_zero ha hp]
    funext s
    simp [join, boxC, kdUn_apply]
  rcases lt_or_ge (d : ℤ) p with hd | hd
  · refine ⟨0, 0, 0, ⟨Nat.zero_le _, Submodule.zero_mem _, Submodule.zero_mem _⟩, ?_⟩
    rw [kd_cech_zero hb (by omega)]
    funext s
    simp [join, boxC, kdUn_apply]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = d - p := ⟨(d - p).toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨q, a, ((-1 : ℤ) ^ (q + 1)) • b, ⟨by omega, ?_, ?_⟩, ?_⟩
  · have e : (d : ℤ) - q = p := by omega
    rw [e]
    exact ha
  · rw [hq]
    exact zsmul_mem hb _
  · funext s
    rw [kdUn_apply]
    simp only [join, boxC, Pi.smul_apply, map_zsmul]
    by_cases hc : (rgt s).card = q + 1
    · rw [hc]
    · have h0 : b (rgt s) = 0 := kd_cech_val hb (by omega)
      simp [h0]

private theorem kd_disj (A : Finset ι → Submodule ℂ E) (B : Finset ι → Submodule ℂ E') :
    Disjoint₂ (TensorProduct.mk ℂ E E') A B := by
  intro I J
  exact TensorProduct.map_injective_of_flat_flat (A I).subtype (B J).subtype
    (A I).injective_subtype (B J).injective_subtype

end

private theorem kdTw_mem_bicech_Z_of_mem_acx_Z {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup E'] [Module ℂ E'] (hU : WdUni) (A : Finset ι → Submodule ℂ E)
    (B : Finset ι → Submodule ℂ E') (d : ℕ) (t : Finset (ι ⊕ₗ ι) → E ⊗[ℂ] E')
    (ht : t ∈ (acx (mixF fun I J => Submodule.map₂ (TensorProduct.mk ℂ E E') (A I) (B J))
      fun _ => (1 : Module.End ℂ (E ⊗[ℂ] E'))).Z ((d : ℤ) + 2)) :
    kdTw t ∈ (bicech (TensorProduct.mk ℂ E E') A B).Z d := by
  unfold acx Cx.Z at ht
  dsimp only at ht
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ,
    true_implies] at ht
  obtain ⟨ht1, ht2⟩ := ht
  unfold bicech Cx.Z
  dsimp only
  simp only [bicechC, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ,
    true_implies]
  refine ⟨?_, ?_⟩
  · rintro ⟨I, J⟩
    dsimp only
    have h := hU ι ι (E ⊗[ℂ] E') (fun _ => 1) t I J
    have hm := ht1 (uni I J)
    rw [h.2.2.2.1] at hm
    simp only [mixF, h.2.1, h.2.2.1] at hm
    simp only [kdTw]
    by_cases hc : I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card : ℕ) : ℤ) = (d : ℤ) + 2
    · rw [if_pos hc]
      rw [if_pos hc.2.2, if_pos ⟨hc.1, hc.2.1⟩] at hm
      exact zsmul_mem hm _
    · rw [if_neg hc]
      have h0 : t (uni I J) = 0 := by
        by_cases h1 : ((I.card + J.card : ℕ) : ℤ) = (d : ℤ) + 2
        · rw [if_pos h1, if_neg (fun h2 => hc ⟨h2.1, h2.2, h1⟩)] at hm
          simpa using hm
        · rw [if_neg h1] at hm
          simpa using hm
      rw [h0, smul_zero]
      exact Submodule.zero_mem _
  · rw [kd_biD_tw hU, ht2]
    funext x
    simp [kdTw]

private theorem kdUn_mem_acx_B_of_mem_bicech_B {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup E'] [Module ℂ E'] (hU : WdUni) (A : Finset ι → Submodule ℂ E)
    (B : Finset ι → Submodule ℂ E') (d : ℕ) (y : Finset ι × Finset ι → E ⊗[ℂ] E')
    (hy : y ∈ (bicech (TensorProduct.mk ℂ E E') A B).B d) :
    kdUn y ∈ (acx (mixF fun I J => Submodule.map₂ (TensorProduct.mk ℂ E E') (A I) (B J))
      fun _ => (1 : Module.End ℂ (E ⊗[ℂ] E'))).B ((d : ℤ) + 2) := by
  unfold bicech Cx.B at hy
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
  show kdUn (biD ℂ ι ι (E ⊗[ℂ] E') w) ∈ _
  rw [← kd_wd_un hU]
  unfold acx Cx.B
  refine Submodule.mem_map.2 ⟨kdUn w, ?_, rfl⟩
  dsimp only at hw ⊢
  simp only [bicechC, Submodule.mem_pi, Set.mem_univ, true_implies] at hw
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  intro s
  rw [kdUn_apply]
  have h := hU ι ι (E ⊗[ℂ] E') (fun _ => 1) (fun _ => 0) (lft s) (rgt s)
  have hcs : s.card = (lft s).card + (rgt s).card := by
    rw [← h.2.2.2.1, h.2.2.2.2 s]
  have hw' := hw (lft s, rgt s)
  dsimp only at hw'
  by_cases hc : (lft s).Nonempty ∧ (rgt s).Nonempty ∧
      (((lft s).card + (rgt s).card : ℕ) : ℤ) = (d : ℤ) - 1 + 2
  · rw [if_pos hc] at hw'
    have hcard : ((s.card : ℕ) : ℤ) = (d : ℤ) + 2 - 1 := by
      rw [hcs]
      have := hc.2.2
      push_cast at this ⊢
      omega
    rw [if_pos hcard]
    simp only [mixF, if_pos (And.intro hc.1 hc.2.1)]
    exact zsmul_mem hw' _
  · rw [if_neg hc] at hw'
    have h0 : w (lft s, rgt s) = 0 := by simpa using hw'
    rw [h0, smul_zero]
    exact Submodule.zero_mem _

theorem UpperTheory.Gal.productCup_of_system.kunDec_of :
    WdUni → KunDec := by
  intro hU
  unfold KunDec
  intro ι E E' _ _ _ _ _ _ A B d hA hB t ht
  have hz := kdTw_mem_bicech_Z_of_mem_acx_Z hU A B d t ht
  obtain ⟨m, p, a, b, hab, hB'⟩ := UpperTheory.Cb.bicech_cohomology_kunneth_decomposition ℂ ι ι E E' (E ⊗[ℂ] E')
    (TensorProduct.mk ℂ E E') A B hA hB (kd_disj A B) (d : ℤ) (kdTw t) hz
  have hs := fun l => kd_single (TensorProduct.mk ℂ E E') A B d (p l) (a l) (b l) (hab l).1 (hab l).2
  choose q a' b' hq hj using hs
  refine ⟨m, q, a', b', fun l => hq l, ?_⟩
  have key := kdUn_mem_acx_B_of_mem_bicech_B hU A B d _ hB'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, kdUn_tw hU, map_sum] at key
  have e : ∑ l, kdUn (boxC (TensorProduct.mk ℂ E E') (a l) (b l)) =
      ∑ l, join (TensorProduct.mk ℂ E E') (a' l) (b' l) :=
    Finset.sum_congr rfl fun l _ => (hj l).symm
  rw [e] at key
  exact key
end

