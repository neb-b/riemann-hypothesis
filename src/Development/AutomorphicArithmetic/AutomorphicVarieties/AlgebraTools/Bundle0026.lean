module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviLevel
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem leviLevel_reps {G : Type} [Group G] {K K' : Subgroup G} (S : Subgroup G) {m : G} (hS : S ≤ K)
    (hfin : FinOrb K K' m) :
    ∃ r : Finset G, (∀ u ∈ r, u ∈ S) ∧ ∀ x ∈ S, ∃! u, u ∈ r ∧ (u * m)⁻¹ * (x * m) ∈ K' := by
  classical
  let φ : G → G ⧸ K' := fun x => ((x * m : G) : G ⧸ K')
  have h1 : (φ '' (S : Set G)).Finite := by
    refine Set.Finite.subset hfin ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hS hx⟩, rfl⟩
  obtain ⟨t, ht, hb⟩ := Set.exists_subset_bijOn (S : Set G) φ
  have h2 : t.Finite := (hb.finite_iff_finite).2 h1
  refine ⟨h2.toFinset, fun u hu => ht (h2.mem_toFinset.1 hu), fun x hx => ?_⟩
  obtain ⟨u, hu, e⟩ := hb.surjOn ⟨x, hx, rfl⟩
  refine ⟨u, ⟨h2.mem_toFinset.2 hu, QuotientGroup.eq.1 e⟩, ?_⟩
  rintro u' ⟨hu', e'⟩
  exact hb.injOn (h2.mem_toFinset.1 hu') hu ((QuotientGroup.eq.2 e').trans e.symm)

private theorem leviLevel_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) {K K' : Subgroup G} (S : Subgroup G) {m : G} (hS : S ≤ K) (hfin : FinOrb K K' m)
    (hg : ∀ g ∈ K, ∃ x ∈ S, (x * m)⁻¹ * (g * m) ∈ K') (r : Finset G) (f : G → G) (hf : ∀ u ∈ r, f u ∈ S)
    (hr : ∀ x ∈ S, ∃! u, u ∈ r ∧ (f u * m)⁻¹ * (x * m) ∈ K') (v : fixd ρ K') :
    (hk2 ρ K K' m v : M) = ∑ u ∈ r, ρ (f u * m) v := by
  classical
  have hinj : ∀ u ∈ r, ∀ u' ∈ r, ((f u * m : G) : G ⧸ K') = ((f u' * m : G) : G ⧸ K') → u = u' :=
    fun u hu u' hu' e => (hr _ (hf u' hu')).unique ⟨hu, QuotientGroup.eq.1 e⟩ ⟨hu', by simp⟩
  rw [(UpperTheory.V.AlgebraTools.hkApply A G M ρ K K' m hfin).2.1 (r.image fun u => f u * m) ?_ ?_ v, Finset.sum_image]
  · intro u hu u' hu' e
    exact hinj u hu u' hu' (congrArg _ e)
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨⟨f u, hS (hf u hu)⟩, rfl⟩
  · rintro _ ⟨⟨g, hgK⟩, rfl⟩
    obtain ⟨x, hx, e⟩ := hg g hgK
    obtain ⟨u, ⟨hu, e'⟩, -⟩ := hr x hx
    have e2 : ((f u * m : G) : G ⧸ K') = ((g * m : G) : G ⧸ K') :=
      (QuotientGroup.eq.2 e').trans (QuotientGroup.eq.2 e)
    refine ⟨f u * m, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e2⟩, ?_⟩
    rintro y ⟨hy, e3⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
    rw [hinj u' hu' u hu (e3.trans e2.symm)]

private theorem leviLevel_cover {G : Type} [Group G] {K : Subgroup G} (F : LeviFact K) {m : G}
    (hL : ∀ l ∈ F.Lf ⊓ K, m⁻¹ * l * m ∈ K) (hJ : ∀ j ∈ F.Mf ⊓ K, m * j = j * m) :
    ∀ g ∈ K, ∃ x ∈ F.Uf ⊓ K, (x * m)⁻¹ * (g * m) ∈ K := by
  intro g hg
  obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
  refine ⟨u, hu, ?_⟩
  have e : (u * m)⁻¹ * (u * j * l * m) = m⁻¹ * (j * m) * (m⁻¹ * l * m) := by group
  rw [e, ← hJ j hj, inv_mul_cancel_left]
  exact mul_mem hj.2 (hL l hl)

theorem UpperTheory.V.AlgebraTools.leviLevel :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I I' : Subgroup G) (h : I' ≤ I) (F : LeviFact I) (F' : LeviFact I') (m : G), HeckePair I → HeckePair I' → FinOrb I I' 1 → F'.Uf = F.Uf → F'.Mf = F.Mf → F'.Lf = F.Lf → F.Uf ⊓ I ≤ I' → F.Lf ⊓ I ≤ I' → (∀ a ∈ I, ∀ b ∈ I', a * b * a⁻¹ ∈ I') → F.Pos m → (∀ j ∈ F.Mf ⊓ I, m * j = j * m) → hk ρ I' m ∘ₗ inc ρ h = inc ρ h ∘ₗ hk ρ I m ∧ trc ρ I I' ∘ₗ hk ρ I' m = hk ρ I m ∘ₗ trc ρ I I' := by
  intro A G M _ _ _ _ ρ I I' h F F' m hI hI' h1 eU eM eL hU hL hn hm hJ
  obtain ⟨r, hr, hr2⟩ := leviLevel_reps (F.Uf ⊓ I) inf_le_right (hI m)
  obtain ⟨t, ht, ht2⟩ := leviLevel_reps (F.Mf ⊓ I) inf_le_right h1
  have cI := leviLevel_cover F hm.2.2 hJ
  have cI' : ∀ g ∈ I', ∃ x ∈ F.Uf ⊓ I, (x * m)⁻¹ * (g * m) ∈ I' := by
    intro g hg
    obtain ⟨x, hx, e⟩ := leviLevel_cover F' (m := m) (fun l hl => by
      have hl1 : l ∈ F.Lf := eL ▸ hl.1
      refine hL ⟨?_, hm.2.2 l ⟨hl1, h hl.2⟩⟩
      simpa using F.M_L _ (inv_mem hm.1) l hl1) (fun j hj => hJ j ⟨eM ▸ hj.1, h hj.2⟩) g hg
    exact ⟨x, ⟨eU ▸ hx.1, h hx.2⟩, e⟩
  have cJ : ∀ g ∈ I, ∃ x ∈ F.Mf ⊓ I, (x * 1)⁻¹ * (g * 1) ∈ I' := by
    intro g hg
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
    refine ⟨j, hj, ?_⟩
    have := mul_mem (hn _ (I.inv_mem hj.2) _ (hU hu)) (hL hl)
    convert this using 1
    group
  have hr3 : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ r ∧ (u * m)⁻¹ * (x * m) ∈ I' := by
    intro x hx
    obtain ⟨u, ⟨hu, e⟩, huq⟩ := hr2 x hx
    refine ⟨u, ⟨hu, hU ⟨?_, e⟩⟩, fun u' hu' => huq u' ⟨hu'.1, h hu'.2⟩⟩
    have := F.M_U _ (inv_mem hm.1) _ (mul_mem (inv_mem (hr u hu).1) hx.1)
    convert this using 1
    show _ ∈ F.Uf ↔ _
    congr! 1
    group
  have sI := leviLevel_sum ρ (F.Uf ⊓ I) inf_le_right (hI m) cI r id hr hr2
  have sJ := leviLevel_sum ρ (F.Mf ⊓ I) inf_le_right h1 cJ t id ht ht2
  have sI' : ∀ j ∈ F.Mf ⊓ I, ∀ v : fixd ρ I',
      (hk2 ρ I' I' m v : M) = ∑ u ∈ r, ρ (j⁻¹ * u * j * m) v := by
    intro j hj
    have hc : ∀ a ∈ F.Mf ⊓ I, ∀ x ∈ F.Uf ⊓ I, a * x * a⁻¹ ∈ F.Uf ⊓ I := fun a ha x hx =>
      ⟨F.M_U a ha.1 x hx.1, I.mul_mem (I.mul_mem ha.2 hx.2) (I.inv_mem ha.2)⟩
    refine leviLevel_sum ρ (F.Uf ⊓ I) hU (hI' m) cI' r (fun u => j⁻¹ * u * j) (fun u hu => ?_) (fun x hx => ?_)
    · simpa using hc _ (inv_mem hj) u (hr u hu)
    · refine (existsUnique_congr fun u => and_congr_right fun _ => ?_).1 (hr3 _ (hc j hj x hx))
      have e : j * ((j⁻¹ * u * j * m)⁻¹ * (x * m)) * j⁻¹ = (u * m)⁻¹ * (j * x * j⁻¹ * m) := by
        have e1 : j * m⁻¹ * j⁻¹ = m⁻¹ := by
          rw [mul_assoc, ← _root_.mul_inv_rev, ← hJ j hj]; group
        have e2 : m * j⁻¹ = j⁻¹ * m := hJ _ (inv_mem hj)
        calc _ = (j * m⁻¹ * j⁻¹) * u⁻¹ * j * x * (m * j⁻¹) := by group
          _ = _ := by rw [e1, e2]; group
      rw [← e]
      refine ⟨fun hx => ?_, hn _ hj.2 _⟩
      have := hn _ (I.inv_mem hj.2) _ hx
      convert this using 1
      group
  refine ⟨LinearMap.ext fun v => Subtype.ext ?_, LinearMap.ext fun v => Subtype.ext ?_⟩
  · show (hk2 ρ I' I' m (inc ρ h v) : M) = hk2 ρ I I m v
    rw [sI' 1 (one_mem _), sI]
    simp only [inv_one, one_mul, mul_one, id]
    rfl
  · show (hk2 ρ I I' 1 (hk2 ρ I' I' m v) : M) = hk2 ρ I I m (hk2 ρ I I' 1 v)
    rw [sJ, sI, sJ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [id, mul_one, map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sI' j (ht j hj), map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc u, hJ j (ht j hj)]
    congr 2
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleOrbit
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

private noncomputable def elem {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : R) : GL (Fin n) R :=
  ⟨1 + single i j a, 1 - single i j a,
    by simp [add_mul, mul_sub, single_mul_single_of_ne _ _ _ _ h.symm],
    by simp [sub_mul, mul_add, single_mul_single_of_ne _ _ _ _ h.symm]⟩

private theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b
      = (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  rw [← map_inv]
  simp only [Units.val_mul, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq]
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem res_zero (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

private theorem pm_KO (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  show algebraMap 𝒪[k] k ((pm 𝒪[k] n w : Matrix (Fin n) (Fin n) 𝒪[k]) a b) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem conj_mem {C : Subgroup 𝓀[k]ˣ} {i j : Fin n} (hij : (j : ℕ) = i + 1) {g : GL (Fin n) k}
    (hg : g ∈ iwC k n C) :
    (pm k n (Equiv.swap i j))⁻¹ * g * pm k n (Equiv.swap i j) ∈ iwC k n C ↔
      valuation k ((g : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  have hm := (memIwC k n C).1
  obtain ⟨h1, h2⟩ := (hm g).1 hg
  obtain ⟨h3, h4⟩ := mem_iwahori.1 h1
  have hlt : i < j := by rw [Fin.lt_def]; omega
  constructor
  · intro h
    have := (mem_iwahori.1 ((hm _).1 h).1).2 j i hlt
    rwa [conj_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at this
  · intro h
    refine (hm _).2 ⟨mem_iwahori.2 ⟨mul_mem (mul_mem (inv_mem (pm_KO _)) h3) (pm_KO _), fun a b hab => ?_⟩,
      fun a => ?_⟩
    · rw [conj_apply]
      by_cases hc : a = j ∧ b = i
      · rwa [hc.1, hc.2, Equiv.swap_apply_left, Equiv.swap_apply_right]
      · apply h4
        simp only [Equiv.swap_apply_def]
        simp only [Fin.ext_iff, Fin.lt_def] at *
        split_ifs <;> omega
    · rw [conj_apply]
      exact h2 _

private theorem pick {C : Subgroup 𝓀[k]ˣ} {g : GL (Fin n) k} (hg : g ∈ iwC k n C)
    {r : 𝓀[k] → 𝒪[k]} (hr : ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) (a i j : Fin n) :
    ∃ c, valuation k ((g : Matrix (Fin n) (Fin n) k) i j
      - algebraMap 𝒪[k] k (r c) * (g : Matrix (Fin n) (Fin n) k) a a) < 1 := by
  obtain ⟨h1, h2⟩ := ((memIwC k n C).1 g).1 hg
  obtain ⟨_, ⟨u, -, rfl⟩, hu⟩ := h2 a
  obtain ⟨h, rfl⟩ := (mem_iwahori.1 h1).1
  refine ⟨IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ)), ?_⟩
  rw [← hu]
  have := (res_zero ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j -
    r (IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ))) * (u : 𝒪[k]))).1 (by
      rw [map_sub, map_mul, hr, ← map_mul, Units.inv_mul_cancel_right, sub_self])
  rw [map_sub, map_mul] at this
  exact this

private theorem elem_mem {i j : Fin n} (h : i < j) (a : 𝒪[k]) :
    elem h.ne (algebraMap 𝒪[k] k a) ∈ unipO k n := by
  refine ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b _ _ hab => ?_, fun a _ _ => ?_⟩, elem h.ne a, ?_⟩
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a b = 0
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hab h.asymm
    simp [one_apply_ne hab.ne', single_apply, this]
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a a = _
    have : ¬ (i = a ∧ j = a) := by
      rintro ⟨rfl, rfl⟩
      exact h.ne rfl
    simp [single_apply, this]
  · ext p q
    show algebraMap 𝒪[k] k ((1 + single i j a : Matrix (Fin n) (Fin n) 𝒪[k]) p q) =
      (1 + single i j _ : Matrix (Fin n) (Fin n) k) p q
    simp only [Matrix.add_apply, Matrix.one_apply, single_apply, map_add (f := _)]
    split_ifs <;> simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.simpleOrbit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (i j : Fin n), (j : ℕ) = i + 1 → ∀ (r : 𝓀[k] → 𝒪[k]), (∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) → ∃ x : 𝓀[k] → GL (Fin n) k, (∀ c, (x c : Matrix (Fin n) (Fin n) k) = 1 + Matrix.single i j (algebraMap 𝒪[k] k (r c))) ∧ (∀ c, x c ∈ unipO k n) ∧ (∀ q : GL (Fin n) k ⧸ iwC k n C, q ∈ MulAction.orbit (iwC k n C) ((pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) ↔ ∃! c, ((x c * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = q) ∧ ∀ g ∈ iwC k n C, ∃ c, ∃ b ∈ iwC k n C, pm k n (Equiv.swap i j) * g = b * (pm k n (Equiv.swap i j) * x c) := by
  intro k _ _ _ _ n C i j hij r hr
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have hle : unipO k n ≤ iwC k n C := le_sup_of_le_left le_sup_right
  have hx : ∀ c, elem hlt.ne (algebraMap 𝒪[k] k (r c)) ∈ iwC k n C := fun c => hle (elem_mem hlt _)
  have hL : ∀ (a : k) (g : GL (Fin n) k), (((elem hlt.ne a)⁻¹ * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) j j := by
    intro a g
    show ((1 - single i j a) * (g : Matrix (Fin n) (Fin n) k)) i j = _
    simp [sub_mul]
  have hR : ∀ (a : k) (g : GL (Fin n) k), ((g * (elem hlt.ne a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) i i := by
    intro a g
    show ((g : Matrix (Fin n) (Fin n) k) * (1 - single i j a)) i j = _
    simp [mul_sub, mul_comm]
  have hs : (pm k n (Equiv.swap i j))⁻¹ = pm k n (Equiv.swap i j) := by rw [← map_inv, Equiv.swap_inv]
  refine ⟨fun c => elem hlt.ne (algebraMap 𝒪[k] k (r c)), fun c => rfl, fun c => elem_mem hlt _, fun q => ?_,
    fun g hg => ?_⟩
  · constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨c, hc⟩ := pick hg hr j i j
      have h1 : ((elem hlt.ne (algebraMap 𝒪[k] k (r c)) * pm k n (Equiv.swap i j) : GL (Fin n) k) :
          GL (Fin n) k ⧸ iwC k n C) = ((g * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) := by
        rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ g, ← mul_assoc]
        exact (conj_mem hij (mul_mem (inv_mem (hx c)) hg)).2 (by rwa [hL])
      refine ⟨c, h1, fun d hd => ?_⟩
      have h2 := h1.trans (Eq.symm hd)
      rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ (elem _ _), ← mul_assoc,
        conj_mem hij (mul_mem (inv_mem (hx c)) (hx d)), hL] at h2
      have h3 : valuation k (algebraMap 𝒪[k] k (r d - r c)) < 1 := by
        convert h2 using 2
        simp [elem, one_apply_ne hlt.ne, single_apply, hlt.ne]
      have h4 := (res_zero _).2 h3
      rwa [map_sub, hr, hr, sub_eq_zero] at h4
    · rintro ⟨c, rfl, -⟩
      exact ⟨⟨_, hx c⟩, rfl⟩
  · obtain ⟨c, hc⟩ := pick hg hr i i j
    refine ⟨c, _, (conj_mem hij (mul_mem hg (inv_mem (hx c)))).2 (by rwa [hR]), ?_⟩
    rw [mul_assoc, ← mul_assoc (pm k n _) (pm k n _), ← map_mul, Equiv.swap_mul_self, map_one, one_mul, hs,
      mul_assoc, inv_mul_cancel_right]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Patched
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
  {X X' : Type} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X']

private theorem one_tmul_mem (a : Ideal R) {x : X} (hx : x ∈ (a • ⊤ : Submodule R X)) (s : S) :
    s ⊗ₜ[R] x ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) := by
  refine Submodule.smul_induction_on hx (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · rw [TensorProduct.tmul_add]
    exact add_mem hx hy

private theorem kill_tensor {r : R} (h : ∀ x : X, r • x = 0) (z : S ⊗[R] X) :
    algebraMap R S r • z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul s x =>
    rw [algebraMap_smul, ← TensorProduct.tmul_smul, h x, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem bot_tensor (a : Ideal R) (h : (a • ⊤ : Submodule R X) = ⊥) :
    (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro s hs z hz
  clear hz
  rw [Submodule.mem_bot]
  have key : ∀ t ∈ a, ∀ w : S ⊗[R] X, algebraMap R S t • w = 0 := by
    intro t ht w
    apply kill_tensor S
    intro x
    have hm : t • x ∈ (a • ⊤ : Submodule R X) := Submodule.smul_mem_smul ht Submodule.mem_top
    rw [h] at hm
    exact (Submodule.mem_bot R).mp hm
  simp only [Ideal.map] at hs
  induction hs using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact key t ht z
  | zero => exact zero_smul _ _
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]

private theorem ker_tensor (a : Ideal R) (t : X →ₗ[R] X') (ht : Function.Surjective t)
    (hk : LinearMap.ker t = a • ⊤) (h' : (a • ⊤ : Submodule R X') = ⊥) :
    Function.Surjective (t.baseChange S) ∧
      LinearMap.ker (t.baseChange S) = a.map (algebraMap R S) • ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S ht
  · have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map t) ht
    ext w
    constructor
    · intro hw
      rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor] at hw
      obtain ⟨v, rfl⟩ := (hex w).mp hw
      clear hw
      induction v using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | tmul s x =>
        rw [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        have hx : (x : X) ∈ (a • ⊤ : Submodule R X) := hk ▸ x.2
        exact one_tmul_mem S a hx s
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro hw
      have hle : (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) ≤
          LinearMap.ker (t.baseChange S) := by
        rw [Submodule.smul_le]
        intro r hr n _
        rw [LinearMap.mem_ker, LinearMap.map_smul]
        have hb := bot_tensor S a h'
        have hm : r • (t.baseChange S) n ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X')) :=
          Submodule.smul_mem_smul hr Submodule.mem_top
        rw [hb] at hm
        exact (Submodule.mem_bot S).mp hm
      exact hle hw

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.exists_patched_module :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (y : σ → R) (m : Ideal R) (f : R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      (S : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] (𝔶 : Ideal S), 𝔶 = (Ideal.span (Set.range y)).map (algebraMap R S) →
      (∀ a j : ℕ, ∀ᶠ N in F, QRegAt (M N) y (m ^ j) a) →
      ∀ (Y : Type) [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
        (g : ULim F (fun j => Ideal.span (Set.range y) ⊔ m ^ j) M →ₗ[R] Y) [IsLocalizedModule (Submonoid.powers f) g], Module.Finite S Y →
      ∃ (MM : Type) (_ : AddCommGroup MM) (_ : Module S MM) (_ : Module (AdicCompletion 𝔶 S) MM) (_ : IsScalarTower S (AdicCompletion 𝔶 S) MM)
        (q : MM →ₗ[S] Y), Module.Finite (AdicCompletion 𝔶 S) MM ∧ Function.Surjective q ∧ LinearMap.ker q = 𝔶 • ⊤ ∧
        GlobalTheory.IsQuasiRegularSeq MM (fun s => algebraMap R S (y s)) ∧
        ∀ r : R, (∀ k : ℕ, ∃ e : ℕ, ∀ j : ℕ, ∀ᶠ N in F, ∀ x : M N,
            (f ^ e * r) • x ∈ ((Ideal.span (Set.range y) ^ k ⊔ m ^ j) • ⊤ : Submodule R (M N))) →
          ∀ x : MM, algebraMap R S r • x = 0 := by
  intro R σ _ _ F hF y m f M _ _ S _ _ _ 𝔶 h𝔶 hreg Y _ _ _ _ g _ hfin
  classical
  haveI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers f)
  have haFG : (Ideal.span (Set.range y)).FG := Submodule.fg_span (Set.finite_range y)
  have hFG : 𝔶.FG := h𝔶 ▸ haFG.map _
  have anti : Antitone (fun j : ℕ => m ^ j) := fun i j hij => Ideal.pow_le_pow_right hij
  have hle : ∀ k : ℕ, Ideal.span (Set.range y) ^ (k + 1) ≤ Ideal.span (Set.range y) ^ k :=
    fun k => Ideal.pow_le_pow_right (Nat.le_succ k)
  have htk := fun k : ℕ => ULim.trans_ker R F hF (fun j => m ^ j) M
    (Ideal.span (Set.range y) ^ k) (Ideal.span (Set.range y) ^ (k + 1)) haFG.pow anti (hle k)
  have hS := fun k : ℕ => ker_tensor S (Ideal.span (Set.range y) ^ k) _ (htk k).1 (htk k).2.1 (htk k).2.2
  have hB := fun k : ℕ => bot_tensor S (Ideal.span (Set.range y) ^ k) (htk k).2.2
  have hmap : ∀ k : ℕ, (Ideal.span (Set.range y) ^ k).map (algebraMap R S) = 𝔶 ^ k := by
    intro k
    rw [Ideal.map_pow, h𝔶]
  have key : ∀ I : ℕ → Ideal R, I = (fun j => Ideal.span (Set.range y) ⊔ m ^ j) →
      Nonempty (S ⊗[R] ULim F I M ≃ₗ[S] Y) := by
    rintro I rfl
    exact ⟨(IsLocalizedModule.isBaseChange (Submonoid.powers f) S g).equiv⟩
  obtain ⟨e1⟩ := key (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) (by funext j; rw [pow_one])
  haveI := hfin
  haveI : Module.Finite S (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) M) :=
    Module.Finite.equiv e1.symm
  obtain ⟨MM, i1, i2, i3, i4, qq, hfinMM, hsurj, hker, -, hzero⟩ :=
    exists_tower_limit_completion S 𝔶 hFG
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)
      (fun k => LinearMap.baseChange S
        (ULim.map F (fun x => sup_le_sup_right (hle k) ((fun j => m ^ j) x)) fun _ => LinearMap.id))
      (fun k => (hS k).1) (fun k => by rw [(hS k).2, hmap]) (fun k => by rw [← hmap]; exact hB k)
      inferInstance
  refine ⟨MM, i1, i2, i3, i4, e1.toLinearMap ∘ₗ qq 1, hfinMM, e1.surjective.comp (hsurj 1), ?_, ?_, ?_⟩
  · rw [LinearEquiv.ker_comp, hker 1, pow_one]
  · have hspan : Ideal.span (Set.range fun s => algebraMap R S (y s)) = 𝔶 := by
      rw [h𝔶, Ideal.map_span, ← Set.range_comp]
      rfl
    refine isQuasiRegularSeq_of_tower S σ (fun s => algebraMap R S (y s)) MM
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) qq hsurj
      (fun k => by rw [hker k, hspan]) ?_
    intro b k hbk
    have h1 := qRegAt_uLim R σ F hF (fun j => m ^ j) M y b k anti hbk (fun j => hreg b j)
    haveI : IsLocalizedModule (Submonoid.powers f)
        (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) S _).mpr
        (TensorProduct.isBaseChange R _ S)
    have h2 := (qRegAt_map R S σ y ⊥ b).2 (Submonoid.powers f) _ _
      (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) h1
    have h3 := ((qRegAt_map R S σ y ⊥ b).1
      (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)).mp h2
    rwa [Ideal.map_bot] at h3
  · intro r hr x
    apply hzero (algebraMap R S r • x)
    intro k
    obtain ⟨e, he⟩ := hr k
    have hP : ∀ z : ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M, (f ^ e * r) • z = 0 :=
      (ULim.scal_eq R ℕ F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M).2.1 (f ^ e * r) he
    have hQ : ∀ w : S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M,
        algebraMap R S (f ^ e * r) • w = 0 := kill_tensor S hP
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := S) f).pow e
    rw [LinearMap.map_smul, ← hu.smul_eq_zero, ← mul_smul, ← map_pow, ← map_mul]
    exact hQ _
end

