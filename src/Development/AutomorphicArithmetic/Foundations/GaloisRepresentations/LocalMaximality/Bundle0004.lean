module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulTwoInjectiveOfGl1
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma exists_of_mem_sm_range {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) (x : E)
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ m : Fin d → E, (∀ j, m j ∈ M) ∧ x = ∑ j, act (f j) (m j) := by
  classical
  let L : (Fin d → M) →ₗ[ℂ] E :=
    ∑ j, ((act (f j) : E →ₗ[ℂ] E) ∘ₗ M.subtype ∘ₗ (LinearMap.proj j : (Fin d → M) →ₗ[ℂ] M))
  have hL : ∀ v, L v = ∑ j, act (f j) (v j : E) := by
    intro v
    simp [L, LinearMap.sum_apply]
  have hle : sm act M (Set.range f) ≤ LinearMap.range L := by
    refine iSup₂_le ?_
    rintro _ ⟨j, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨Pi.single j ⟨m, hm⟩, ?_⟩
    rw [hL, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  obtain ⟨v, rfl⟩ := hle hx
  exact ⟨fun j => (v j : E), fun j => (v j).2, hL v⟩

theorem UpperTheory.Gal.productCup_of_system.koszulTwoInjective_of_gl1 :
    FiltrationBoundaryCriterion → SubQEx → KoszulBoundaryOfComponentMemIdeal := by
  intro gl1 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hKE c hc hsm
  classical
  obtain ⟨m, hm, hcm⟩ := exists_of_mem_sm_range act M (fun j => r (e j)) _ hsm
  have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
    refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
    show act (r i) * act (r j) = act (r j) * act (r i)
    rw [← map_mul, ← map_mul, mul_comm]
  have hQ := subq S E act κ M r d e hKE
  have hQc : (img e).card = d := by simp [img]
  have hmem : ∀ j, e j ∈ img e := fun j => by simp [img]
  have hcz : ∀ s : Finset κ, (s.card : ℤ) ≠ d → c s = 0 := by
    intro s hs
    have h := hc.1 s (Set.mem_univ s)
    simpa [hs] using h
  have hcard : ∀ j, (((img e).erase (e j)).card : ℤ) = (d : ℤ) - 1 := by
    intro j
    have := j.pos
    rw [Finset.card_erase_of_mem (hmem j), hQc]
    omega
  have hinj : ∀ i j, (img e).erase (e i) = (img e).erase (e j) → i = j := by
    intro i j h
    by_contra hij
    have hne : e i ≠ e j := fun h' => hij (e.injective h')
    have h1 : e i ∈ (img e).erase (e j) := Finset.mem_erase.mpr ⟨hne, hmem i⟩
    rw [← h] at h1
    exact (Finset.notMem_erase _ _) h1
  let y : Finset κ → E := fun s =>
    ∑ j, if s = (img e).erase (e j) then GlobalTheory.cubeSign (img e) (e j) • m j else 0
  have hyv : ∀ j, y ((img e).erase (e j)) = GlobalTheory.cubeSign (img e) (e j) • m j := by
    intro j
    show (∑ i, if (img e).erase (e j) = (img e).erase (e i) then _ else _) = _
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (hinj _ _ h).symm]
    · simp
  have hy0 : ∀ s, (∀ j, s ≠ (img e).erase (e j)) → y s = 0 := by
    intro s hs
    exact Finset.sum_eq_zero fun j _ => if_neg (hs j)
  have hycard : ∀ s : Finset κ, (s.card : ℤ) ≠ (d : ℤ) - 1 → y s = 0 := by
    intro s hs
    refine hy0 s fun j h => hs ?_
    rw [h, hcard]
  refine gl1 κ E (fun _ => M) (fun l => act (r l)) (img e) d d hW hQ c hc ?_ ?_
  · intro s hs
    exfalso
    apply hs
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := img e))
    rw [hQc] at this
    exact_mod_cast this
  · refine ⟨y, ?_, ?_, ?_⟩
    · intro s _
      show y s ∈ if (s.card : ℤ) = (d : ℤ) - 1 then M else ⊥
      split_ifs with h
      · refine Submodule.sum_mem _ fun j _ => ?_
        split_ifs
        · exact zsmul_mem (hm j) _
        · exact M.zero_mem
      · rw [hycard s h]
        exact Submodule.zero_mem _
    · intro s hs
      refine hy0 s fun j h => hs ?_
      subst h
      rw [Finset.inter_eq_left.mpr (Finset.erase_subset _ _), hcard]
    · intro s hs
      have hsub : img e ⊆ s := by
        have h1 : (s ∩ img e) = img e := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          rw [hQc]
          exact_mod_cast hs.ge
        rw [← h1]
        exact Finset.inter_subset_left
      have hwd : ∀ t : Finset κ, wd (wOn (img e) fun l => act (r l)) y t =
          ∑ i ∈ t, GlobalTheory.cubeSign t i • (wOn (img e) (fun l => act (r l)) i) (y (t.erase i)) := by
        intro t
        simp [wd, LinearMap.sum_apply]
      rw [hwd]
      by_cases hsQ : s = img e
      · subst hsQ
        rw [hcm]
        have hsum : ∀ F : κ → E, ∑ i ∈ img e, F i = ∑ j, F (e j) := fun F =>
          Finset.sum_map _ _ _
        rw [hsum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hw : wOn (img e) (fun l => act (r l)) (e j) = act (r (e j)) := if_pos (hmem j)
        have hsq : GlobalTheory.cubeSign (img e) (e j) * GlobalTheory.cubeSign (img e) (e j) = 1 := by
          rw [GlobalTheory.cubeSign, ← mul_pow]
          simp
        rw [hw, hyv j, map_zsmul, smul_smul, hsq, one_smul]
      · have hlt : img e ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hsQ h.symm⟩
        have hgt : d < s.card := by
          have := Finset.card_lt_card hlt
          rwa [hQc] at this
        rw [hcz s (by omega)]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hycard (s.erase i) ?_]
        · simp
        · rw [Finset.card_erase_of_mem hi]
          omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MapUnitEq
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocDAux
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]

private lemma geo_mem {W : Type} [AddCommGroup W] [Module ℂ W] (φ : S →+* Module.End ℂ W)
    (R : Subalgebra ℂ S) (P : Submodule ℂ W) (hP : ∀ s ∈ R, ∀ x ∈ P, φ s x ∈ P) {a b : S}
    (ha : a ∈ R) (hb : b ∈ R) (x : W) (h1 : φ (1 - a * b) x ∈ P) (N : ℕ)
    (hN : φ (a ^ N) x ∈ P) : x ∈ P := by
  have key : (1 : S) = b ^ N * a ^ N + (∑ i ∈ Finset.range N, (a * b) ^ i) * (1 - a * b) := by
    rw [geom_sum_mul_neg, mul_pow]; ring
  have hx : x = φ (b ^ N) (φ (a ^ N) x) +
      φ (∑ i ∈ Finset.range N, (a * b) ^ i) (φ (1 - a * b) x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← LinearMap.add_apply, ← map_add, ← key]
    simp
  rw [hx]
  exact P.add_mem (hP _ (R.pow_mem hb N) _ hN)
    (hP _ (R.sum_mem fun i _ => R.pow_mem (R.mul_mem ha hb) i) _ h1)

private def pwR (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) : S →+* Module.End ℂ (ι → E) where
  toFun s := LinearMap.pi fun t => act s ∘ₗ LinearMap.proj t
  map_one' := LinearMap.ext fun c => funext fun t => by simp
  map_mul' s s' := LinearMap.ext fun c => funext fun t => by simp
  map_zero' := LinearMap.ext fun c => funext fun t => by simp
  map_add' s s' := LinearMap.ext fun c => funext fun t => by simp

private lemma pwR_apply (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) (s : S) (c : ι → E) (t : ι) :
    pwR act ι s c t = act s (c t) := rfl

private lemma act_comm (act : S →ₐ[ℂ] Module.End ℂ E) (s s' : S) (x : E) :
    act s (act s' x) = act s' (act s x) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

variable {κ : Type} [LinearOrder κ]

private lemma kos_mem_C (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) (r : κ → S) (n : ℤ)
    (c : Finset κ → E) :
    c ∈ (kos act M r).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then M else ⊥ : Submodule ℂ E) := by
  simp [kos, acx, Submodule.mem_pi]

private lemma wd_pw (act : S →ₐ[ℂ] Module.End ℂ E) (r : κ → S) (s : S) (y : Finset κ → E) :
    wd (fun l => act (r l)) (pwR act _ s y) = pwR act _ s (wd (fun l => act (r l)) y) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pwR_apply, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_zsmul, act_comm act s]

private lemma kos_B_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (r : κ → S) (hSt : Stab act R M) (n : ℤ) (s : S) (hs : s ∈ R) (x : Finset κ → E)
    (hx : x ∈ (kos act M r).B n) : pwR act _ s x ∈ (kos act M r).B n := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨pwR act _ s y, ?_, wd_pw act r s y⟩
  rw [SetLike.mem_coe, kos_mem_C] at hy ⊢
  intro t
  have := hy t
  rw [pwR_apply]
  split_ifs at this ⊢ with h
  · exact hSt s hs _ this
  · simp only [Submodule.mem_bot] at this ⊢
    rw [this, map_zero]

private lemma sm_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (T : Set S) (hSt : Stab act R M) (s : S) (hs : s ∈ R) (x : E) (hx : x ∈ sm act M T) :
    act s x ∈ sm act M T := by
  have hle : sm act M T ≤ (sm act M T).comap (act s) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨m, hm, rfl⟩
    rw [Submodule.mem_comap, act_comm]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) t ht le_rfl : _ ≤ sm act M T)
      ⟨_, hSt s hs m hm, rfl⟩
  exact hle hx

private lemma unif_pow (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M M' : Submodule ℂ E)
    (hSt : Stab act R M) {a : S} (ha : a ∈ R) (hloc : ∀ m ∈ M', ∃ N : ℕ, act (a ^ N) m ∈ M)
    {ι : Type} [Fintype ι] (f : ι → E) (hf : ∀ i, f i ∈ M') :
    ∃ N : ℕ, ∀ i, act (a ^ N) (f i) ∈ M := by
  choose n hn using fun i => hloc (f i) (hf i)
  refine ⟨∑ i, n i, fun i => ?_⟩
  have h : ∑ i, n i = (∑ i, n i - n i) + n i := (Nat.sub_add_cancel
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [h, pow_add, map_mul, Module.End.mul_apply]
  exact hSt _ (R.pow_mem ha _) _ (hn i)

private lemma map_unit_eq (act : S →ₐ[ℂ] Module.End ℂ E) (M' : Submodule ℂ E) (v : Sˣ)
    (hv : ∀ m ∈ M', act v m ∈ M' ∧ act (v⁻¹ : Sˣ) m ∈ M') (k : ℕ) :
    M'.map (act ((v ^ k : Sˣ) : S)) = M' := by
  have hP : ∀ k : ℕ, ∀ m ∈ M', act ((v ^ k : Sˣ) : S) m ∈ M' ∧ act (((v ^ k)⁻¹ : Sˣ) : S) m ∈ M' := by
    intro k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      constructor
      · rw [pow_succ, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (ih _ (hv m hm).1).1
      · rw [pow_succ, mul_inv_rev, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (hv _ (ih m hm).2).2
  refine le_antisymm ?_ fun m hm => ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact (hP k m hm).1
  · refine ⟨_, (hP k m hm).2, ?_⟩
    change act ((v ^ k : Sˣ) : S) (act (((v ^ k)⁻¹ : Sˣ) : S) m) = m
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one]
    rfl

end LocDAux

theorem UpperTheory.Gal.productCup_of_system.locD_of :
    RS → Htpy → LocD := by
  intro hRS hH S E _ _ _ _ act κ _ _ R M M' r v a b l0 d hSt hr ha hb hl0 hMM hloc hv
  refine ⟨fun hKE m hm c hc => ?_, fun m hm hsm => ?_⟩
  · have hcC := hc.1
    have hcD : wd (fun l => act (r l)) c = 0 := hc.2

    let u : κ → Sˣ := fun _ => v
    let z : κ → S := fun l => r l * v
    have hrz : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ) := by
      intro l
      simp [z, u, mul_assoc]
    have hmap : ∀ L : Finset κ, M'.map (act ((∏ l ∈ L, u l : Sˣ) : S)) = M' := by
      intro L
      simp only [u, Finset.prod_const]
      exact map_unit_eq act M' v hv _
    have hT : kosT act M' u z = kos act M' z := by
      unfold kosT kos
      simp only [hmap]
    have hR := fun n c => hRS S E act κ M' u r z hrz n c
    have hcC' := (kos_mem_C act M r m c).1 hcC
    have hcZ' : c ∈ (kos act M' r).Z m := by
      refine ⟨(kos_mem_C act M' r m c).2 fun t => ?_, hc.2⟩
      have := hcC' t
      split_ifs at this ⊢ with h
      · exact hMM this
      · exact this
    have hinv : unsc act u (unsc act u⁻¹ c) = c := (hR m c).2.2.2.2
    have hZ : unsc act u⁻¹ c ∈ (kosT act M' u z).Z m :=
      (hR m (unsc act u⁻¹ c)).2.1.2 (by rw [hinv]; exact hcZ')
    have hB : unsc act u⁻¹ c ∈ (kosT act M' u z).B m := by
      rw [hT] at hZ ⊢
      exact hKE m hm hZ
    have hcB : c ∈ (kos act M' r).B m := by
      have := (hR m (unsc act u⁻¹ c)).2.2.1.1 hB
      rwa [hinv] at this
    obtain ⟨y, hy, hyc⟩ := hcB
    have hy' := (kos_mem_C act M' r (m - 1) y).1 hy
    have hyM : ∀ L, y L ∈ M' := by
      intro L
      have := hy' L
      split_ifs at this with h
      · exact this
      · rw [Submodule.mem_bot] at this
        rw [this]
        exact M'.zero_mem
    obtain ⟨N, hN⟩ := unif_pow act R M M' hSt ha hloc y hyM
    refine geo_mem (pwR act _) R ((kos act M r).B m)
      (fun s hs x hx => kos_B_stab act R M r hSt m s hs x hx) ha hb c ?_ N ?_
    · rw [← hl0]
      refine hH S E act κ R M r hSt m c hc (r l0) ⟨Pi.single l0 1, fun l => ?_, ?_⟩
      · by_cases h : l = l0
        · subst h
          simpa using R.one_mem
        · simpa [Pi.single_apply, h] using R.zero_mem
      · simp [Pi.single_apply]
    · refine ⟨pwR act _ (a ^ N) y, (kos_mem_C act M r (m - 1) _).2 fun t => ?_, ?_⟩
      · have := hy' t
        rw [pwR_apply]
        split_ifs at this ⊢ with h
        · exact hN t
        · rw [Submodule.mem_bot] at this ⊢
          rw [this, map_zero]
      · have e := wd_pw act r (a ^ N) y
        change wd (fun l => act (r l)) (pwR act _ (a ^ N) y) = pwR act _ (a ^ N) c
        rw [e]
        rw [← hyc]
        rfl
  · let T : Set S := Set.range r
    let Pn : Submodule ℂ E :=
      { carrier := {x | ∃ N : ℕ, act (a ^ N) x ∈ sm act M T}
        add_mem' := by
          rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
          refine ⟨N₁ + N₂, ?_⟩
          rw [map_add (f := _)]
          refine Submodule.add_mem _ ?_ ?_
          · rw [add_comm, pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₁
          · rw [pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₂
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro k x ⟨N, h⟩
          refine ⟨N, ?_⟩
          rw [map_smul]
          exact Submodule.smul_mem _ k h }
    have hle : sm act M' (Set.range fun l => r l * v) ≤ Pn := by
      refine iSup₂_le fun t ht => ?_
      obtain ⟨l, rfl⟩ := ht
      rintro _ ⟨m', hm', rfl⟩
      obtain ⟨N, hN⟩ := hloc _ (hv m' hm').1
      refine ⟨N, ?_⟩
      have e : act (a ^ N) (act (r l * v) m') = act (r l) (act (a ^ N) (act v m')) := by
        rw [map_mul, Module.End.mul_apply, act_comm act (a ^ N) (r l)]
      rw [e]
      exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l) ⟨l, rfl⟩ le_rfl :
        _ ≤ sm act M T) ⟨_, hN, rfl⟩
    obtain ⟨N, hN⟩ := hle hsm
    refine geo_mem act.toRingHom R (sm act M T)
      (fun s hs x hx => sm_stab act R M T hSt s hs x hx) ha hb m ?_ N hN
    change act (1 - a * b) m ∈ sm act M T
    rw [← hl0]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l0) ⟨l0, rfl⟩ le_rfl :
      _ ≤ sm act M T) ⟨_, hm, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem wd_apply' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem wd_anti' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w w' : σ → Module.End ℂ E) (h : ∀ i j, Commute (w i) (w' j)) (c : Finset σ → E) :
    wd w (wd w' c) + wd w' (wd w c) = 0 := by
  funext t
  have hc : ∀ f : σ → σ → E, ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = ∑ i ∈ t, ∑ j ∈ t.erase i, f j i := by
    intro f
    refine Finset.sum_comm' ?_
    intro x y
    simp only [Finset.mem_erase]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨Ne.symm b, a⟩, c⟩, fun ⟨⟨b, a⟩, c⟩ => ⟨a, Ne.symm b, c⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [wd_apply', map_sum, map_zsmul, Finset.smul_sum, smul_smul, Pi.add_apply, Pi.zero_apply]
  conv_lhs => rhs; rw [hc]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hji : j ≠ i := (Finset.mem_erase.1 hj).1
  have hjt : j ∈ t := (Finset.mem_erase.1 hj).2
  have hcomm : w' j (w i (c ((t.erase j).erase i))) = w i (w' j (c ((t.erase i).erase j))) := by
    rw [show (t.erase j).erase i = (t.erase i).erase j from Finset.erase_right_comm]
    exact (LinearMap.congr_fun (h i j).eq _).symm
  rw [hcomm, ← add_smul, GlobalTheory.cubeSign_mul_erase hi hjt (Ne.symm hji), neg_add_cancel, zero_smul]

private theorem cubeSign_map' {σ σ' : Type} [LinearOrder σ] [LinearOrder σ'] (e : σ' ↪o σ)
    (s : Finset σ') (i : σ') :
    GlobalTheory.cubeSign (s.map e.toEmbedding) (e i) = GlobalTheory.cubeSign s i := by
  simp only [GlobalTheory.cubeSign, Finset.filter_map, Finset.card_map]
  congr 2
  ext x
  simp

theorem UpperTheory.Gal.productCup_of_system.wdBasic_of :
    WdBasic := by
  intro σ E _ _ _ _ A w
  have d2 : (∀ i j, Commute (w i) (w j)) → ∀ c, wd w (wd w c) = 0 := by
    intro h c
    have hx := wd_anti' w w h c
    have h2 : (2 : ℂ) • wd w (wd w c) = 0 := by rw [two_smul]; exact hx
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  refine ⟨d2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hw, hA⟩ n a ha
    refine ⟨?_, d2 hw a⟩
    simp only [acx, Submodule.mem_pi, Set.mem_univ, forall_const] at ha ⊢
    intro s
    rw [wd_apply']
    by_cases hs : (s.card : ℤ) = n + 1
    · rw [if_pos hs]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_
      have hcard : ((s.erase i).card : ℤ) = n := by
        have := Finset.card_erase_add_one hi
        omega
      have hmem := ha (s.erase i)
      rw [if_pos hcard] at hmem
      have := hA (s.erase i) i (by simp) _ hmem
      rwa [Finset.insert_erase hi] at this
    · rw [if_neg hs, Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hcard : ¬ ((s.erase i).card : ℤ) = n := by
        have := Finset.card_erase_add_one hi
        omega
      have hmem := ha (s.erase i)
      rw [if_neg hcard, Submodule.mem_bot] at hmem
      rw [hmem, map_zero, smul_zero]
  · intro w'
    refine LinearMap.ext fun c => funext fun t => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, wd_apply', smul_add, Finset.sum_add_distrib]
  · intro w' h _ c
    exact wd_anti' w w' h c
  · intro c
    funext t
    rw [wd_apply']
    simp only [Module.End.one_apply]
    rfl
  · intro σ' _ e c s
    rw [wd_apply', wd_apply', Finset.sum_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [RelEmbedding.coe_toEmbedding, cubeSign_map']
    rw [Finset.map_erase]
    rfl
end

