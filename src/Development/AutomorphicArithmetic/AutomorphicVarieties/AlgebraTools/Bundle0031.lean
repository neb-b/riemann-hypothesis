module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFactTorus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unif_lt {x : kˣ} (hx : IsUnif x) : valuation k (x : k) < 1 := by
  obtain ⟨p, hp, h⟩ := hx
  rw [← h]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hp.not_isUnit

private theorem unif_dec {x : kˣ} (hx : IsUnif x) (y : kˣ) :
    ∃ a : ℤ, valuation k (y : k) = valuation k (x : k) ^ a := by
  obtain ⟨p, hp, h⟩ := hx
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := k) hp y.ne_zero
  refine ⟨a, ?_⟩
  have h1 : valuation k (algebraMap 𝒪[k] k (u : 𝒪[k])) = 1 :=
    (Valuation.integer.integers (valuation k)).valuation_unit u
  rw [hu, h, Units.smul_def, Algebra.smul_def, map_mul, h1, one_mul, map_zpow₀]

private theorem dom_zpow {x : kˣ} (hx : IsUnif x) {a : Fin n → ℤ} (ha : Antitone a) : Dom fun i => x ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).2 (ha hij)

private theorem exists_cut (a : Fin n → ℤ) (ha : Antitone a) (c : ℤ) :
    ∃ m ≤ n, ∀ i : Fin n, (i : ℕ) < m ↔ c < a i := by
  classical
  have hex : ∃ m : ℕ, ∀ i : Fin n, m ≤ (i : ℕ) → a i ≤ c := ⟨n, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun i hi => absurd i.2 (not_lt.2 hi), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · have := Nat.find_min hex hi
    push Not at this
    obtain ⟨j, hj, hc⟩ := this
    exact hc.trans_le (ha (Fin.le_def.2 hj))
  · by_contra h
    exact absurd (Nat.find_spec hex i (not_lt.1 h)) (not_le.2 hi)

private theorem const_central (y : kˣ) : diagT k (Fin n) (fun _ => y) ∈ Subgroup.center (GL (Fin n) k) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp only [Units.val_mul, val_diagT, mul_diagonal, diagonal_mul, mul_comm]

private theorem unit_norm (C : Subgroup 𝓀[k]ˣ) (u : Fin n → kˣ) (hu : ∀ i, valuation k (u i : k) = 1) :
    diagT k (Fin n) u ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  obtain ⟨-, -, hn, hv⟩ := memIwC k n C
  have h : diagT k (Fin n) u ∈ iwahori k (Fin n) := by
    rw [← (memIwC k n C).2.1]
    exact Subgroup.mem_sup_right ⟨u, fun i _ => (hv _).2 (hu i), rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  refine ⟨fun hb => hn _ h b hb, fun hb => ?_⟩
  have := hn _ (inv_mem h) _ hb
  simpa [mul_assoc] using this

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.domMul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), (∀ t t' : Fin n → kˣ, Dom t → Dom t' → hk ρ (iwC k n C) (diagT k (Fin n) t) * hk ρ (iwC k n C) (diagT k (Fin n) t') = hk ρ (iwC k n C) (diagT k (Fin n) (t * t'))) ∧ (IsUnit (resCard k : A) → ∀ t : Fin n → kˣ, Dom t → IsUnit (hk ρ (iwC k n C) (diagT k (Fin n) t))) ∧ ∀ (C' : Subgroup 𝓀[k]ˣ) (h : iwC k n C ≤ iwC k n C') (t : Fin n → kˣ), Dom t → hk ρ (iwC k n C) (diagT k (Fin n) t) ∘ₗ inc ρ h = inc ρ h ∘ₗ hk ρ (iwC k n C') (diagT k (Fin n) t) ∧ trc ρ (iwC k n C') (iwC k n C) ∘ₗ hk ρ (iwC k n C) (diagT k (Fin n) t) = hk ρ (iwC k n C') (diagT k (Fin n) t) ∘ₗ trc ρ (iwC k n C') (iwC k n C) := by
  intro k _ _ _ _ n C A M _ _ _ ρ
  have hH := (heckePairIwC k n C).1
  obtain ⟨F, hU, hM, hL, hUI, hLI, hF⟩ := factTorus k n C
  have hmul : ∀ t t' : Fin n → kˣ, Dom t → Dom t' → hk ρ (iwC k n C) (diagT k (Fin n) t) * hk ρ (iwC k n C) (diagT k (Fin n) t') = hk ρ (iwC k n C) (diagT k (Fin n) (t * t')) := by
    intro t t' ht ht'
    rw [map_mul]
    exact (leviMul A _ M ρ _ F _ _ hH ((hF t).2 ht) ((hF t').2 ht') (Or.inl (hF t).1)).2
  refine ⟨hmul, fun hq t ht => ?_, fun C' h t ht => ?_⟩
  · obtain ⟨x, hx⟩ := exists_isUnif (k := k)
    have hfund : ∀ m ≤ n, IsUnit (hk ρ (iwC k n C) (pw x (fund n m))) := by
      intro m hm
      obtain ⟨w, hw⟩ := fundNorm k n C x hx m hm
      obtain ⟨-, -, hu, hx⟩ := hkNorm A _ M ρ _ _ hH hw
      have e : pw x (fund n m) = pm k n w⁻¹ * (pm k n w * pw x (fund n m)) := by
        rw [map_inv, inv_mul_cancel_left]
      rw [e, (hx _).2]
      exact (permUnit k n C A M ρ _ hq).mul hu
    have key : ∀ (c : ℤ) (N : ℕ) (a : Fin n → ℤ), Antitone a → (∀ i, c ≤ a i ∧ a i ≤ c + N) →
        IsUnit (hk ρ (iwC k n C) (diagT k (Fin n) fun i => x ^ a i)) := by
      intro c N
      induction N with
      | zero =>
        intro a _ hb
        have e : (fun i => x ^ a i) = fun _ : Fin n => x ^ c := by
          funext i
          have := hb i
          rw [show a i = c by omega]
        rw [e]
        exact (hkNorm A _ M ρ _ _ hH (Subgroup.center_le_normalizer _ (const_central _))).2.2.1
      | succ N ih =>
        intro a ha hb
        obtain ⟨m, hm, hc⟩ := exists_cut a ha c
        have hfa : Antitone (fund n m) := by
          intro i j hij
          have := Fin.le_def.1 hij
          simp only [fund]
          split_ifs <;> omega
        have ha' : Antitone (a - fund n m) := by
          intro i j hij
          have h1 := ha hij
          have h2 := hc i
          have h3 := hc j
          have h4 := hb i
          have h5 := hb j
          simp only [fund, Pi.sub_apply]
          split_ifs <;> omega
        have hb' : ∀ i, c ≤ (a - fund n m) i ∧ (a - fund n m) i ≤ c + N := by
          intro i
          have h2 := hc i
          have h4 := hb i
          simp only [fund, Pi.sub_apply]
          split_ifs <;> omega
        have e : (fun i => x ^ a i) = (fun i => x ^ (a - fund n m) i) * fun i => x ^ fund n m i := by
          funext i
          simp only [Pi.mul_apply, Pi.sub_apply, ← _root_.zpow_add, sub_add_cancel]
        rw [e, ← hmul _ _ (dom_zpow hx ha') (dom_zpow hx hfa)]
        exact (ih _ ha' hb').mul (hfund m hm)
    choose a hav using fun i => unif_dec hx (t i)
    have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
    have ha : Antitone a := by
      intro i j hij
      have := ht i j hij
      rw [hav, hav] at this
      exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).1 this
    obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd⟩ := (Set.finite_range a).bddAbove
    have hk1 := key c (d - c).toNat a ha fun i => by
      have h1 : c ≤ a i := hc ⟨i, rfl⟩
      have h2 : a i ≤ d := hd ⟨i, rfl⟩
      omega
    have hn := unit_norm C (fun i => t i * (x ^ a i)⁻¹) fun i => by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hav]
      exact mul_inv_cancel₀ (zpow_ne_zero _ h0.ne')
    obtain ⟨-, -, hu, hx⟩ := hkNorm A _ M ρ _ _ hH hn
    have e : t = (fun i => t i * (x ^ a i)⁻¹) * fun i => x ^ a i := by
      funext i
      simp
    rw [e, map_mul, (hx _).1]
    exact hu.mul hk1
  · obtain ⟨F', hU', hM', hL', hUI', hLI', hF'⟩ := factTorus k n C'
    refine leviLevel A _ M ρ _ _ h F' F _ (heckePairIwC k n C').1 hH ((heckePairIwC k n C).2.2 C').1
      (hU.trans hU'.symm) (hM.trans hM'.symm) (hL.trans hL'.symm) ?_ ?_ ?_ ((hF' t).2 ht) ?_
    · rw [hUI', ← hUI]
      exact inf_le_right
    · rw [hLI', ← hLI]
      exact inf_le_right
    · intro a ha b hb
      exact (memIwC k n C).2.2.1 a (((memIwC k n C').1 a).1 ha).1 b hb
    · rintro j ⟨hj, -⟩
      rw [hM'] at hj
      obtain ⟨s, rfl⟩ := hj
      rw [← map_mul, ← map_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomSum
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem domSum_reps {G : Type} [Group G] {N I : Subgroup G} (hN : N ≤ I) (d : G) (h : FinOrb I I d) :
    ∃ s : Finset G, (∀ u ∈ s, u ∈ N) ∧ ∀ y ∈ N, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
  obtain ⟨S, hS, hb⟩ := Set.exists_subset_bijOn (N : Set G) (fun y => ((y * d : G) : G ⧸ I))
  have hq : ((fun y => ((y * d : G) : G ⧸ I)) '' (N : Set G)).Finite := by
    refine h.subset ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hN hy⟩, rfl⟩
  have hf : S.Finite := Set.Finite.of_finite_image (hb.image_eq ▸ hq) hb.injOn
  have key : ∀ u y : G, ((u * d : G) : G ⧸ I) = ((y * d : G) : G ⧸ I) ↔ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
    intro u y
    rw [QuotientGroup.eq]
    have : (u * d)⁻¹ * (y * d) = d⁻¹ * (u⁻¹ * y) * d := by group
    rw [this]
  refine ⟨hf.toFinset, fun u hu => hS (hf.mem_toFinset.1 hu), fun y hy => ?_⟩
  obtain ⟨u, hu, e⟩ := hb.surjOn ⟨y, hy, rfl⟩
  refine ⟨u, ⟨hf.mem_toFinset.2 hu, (key u y).1 e⟩, ?_⟩
  rintro u' ⟨hu', e'⟩
  exact hb.injOn (hf.mem_toFinset.1 hu') hu (((key u' y).2 e').trans e.symm)

private theorem domSum_gen {G : Type} [Group G] {I : Subgroup G} (F : LeviFact I) (d : G) (hI : HeckePair I)
    (hp : F.Pos d) (hn : F.NormJ d) (s : Finset G) (hs : ∀ u ∈ s, u ∈ F.Uf ⊓ I)
    (hs' : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * x) * d ∈ I)
    (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I d v : M) = ∑ u ∈ s, ρ (u * d) v := by
  classical
  have H := leviSum G I F d hI hp {d}
    (fun a ha => ⟨1, one_mem _, 1, one_mem _, by simpa using ha⟩)
    (fun j hj => ⟨d, ⟨Finset.mem_singleton_self d, by simpa [mul_assoc] using (hn j hj).2⟩,
      fun a ha => Finset.mem_singleton.1 ha.1⟩)
    (fun _ => s) (fun a ha => by
      rw [Finset.mem_singleton.1 ha]
      exact ⟨hs, hs'⟩)
  have h2 := (hkApply A G M ρ I I d (hI d)).2.1 (s.image (· * d)) ?_ ?_ v
  · rw [hk, h2, Finset.sum_image (fun a _ b _ h => mul_right_cancel h)]
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨⟨u, (hs u hu).2⟩, rfl⟩
  · intro q hq
    obtain ⟨⟨a, u⟩, ⟨ha, hu, e⟩, huniq⟩ := (H q).1 hq
    have had : a = d := Finset.mem_singleton.1 ha
    subst had
    refine ⟨u * a, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, e'⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
    have := huniq (a, u') ha hu' e'
    rw [show u' = u from (Prod.ext_iff.1 this).2]

theorem UpperTheory.V.AlgebraTools.domSum :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : Fin n → kˣ), Dom t → ∃ s : Finset (GL (Fin n) k), (∀ u ∈ s, u ∈ unipO k n) ∧ (∀ y ∈ unipO k n, ∃! u, u ∈ s ∧ (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n) ∧ ∀ (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (v : fixd ρ (iwC k n C)), (hk ρ (iwC k n C) (diagT k (Fin n) t) v : M) = ∑ u ∈ s, ρ (u * diagT k (Fin n) t) v := by
  intro k _ _ _ _ n t ht
  have key : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ u ∈ unipO k n, ∀ y ∈ unipO k n,
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C ↔
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n := by
    intro C u hu y hy
    obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    rw [← hU] at hu hy ⊢
    have := F.M_U _ (inv_mem ((hF t).2 ht).1) _ (mul_mem (inv_mem hu.1) hy.1)
    rw [inv_inv] at this
    exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩
  have hle : unipO k n ≤ iwC k n ⊤ := le_sup_right.trans le_sup_left
  obtain ⟨s, hs, hs'⟩ := domSum_reps hle (diagT k (Fin n) t) ((heckePairIwC k n ⊤).1 _)
  have hs2 : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ y ∈ unipO k n, ∃! u, u ∈ s ∧
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C := by
    intro C y hy
    refine (existsUnique_congr fun u => and_congr_right fun hu => ?_).1 (hs' y hy)
    rw [key ⊤ u (hs u hu) y hy, key C u (hs u hu) y hy]
  refine ⟨s, hs, fun y hy => ?_, fun C A M _ _ _ ρ v => ?_⟩
  · exact (existsUnique_congr fun u => and_congr_right fun hu => key ⊤ u (hs u hu) y hy).1 (hs' y hy)
  · obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    exact domSum_gen F _ (heckePairIwC k n C).1 ((hF t).2 ht) (hF t).1 s (hU ▸ hs) (hU ▸ hs2 C) A M ρ v
end

