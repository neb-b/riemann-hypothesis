module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermCard
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools.PermCard

private theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b =
      (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  rw [← map_inv, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_apply, pm_apply]
  rw [Fintype.sum_eq_single (w b), Fintype.sum_eq_single (w a)]
  · simp
  · intro x hx
    rw [if_neg, zero_mul]
    rintro rfl
    exact hx (by simp)
  · intro x hx
    rw [if_neg hx, mul_zero]

private theorem map_pm {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (w : Equiv.Perm (Fin n)) :
    GeneralLinearGroup.map (n := Fin n) f (pm R n w) = pm S n w := by
  ext i j
  show f ((pm R n w : Matrix (Fin n) (Fin n) R) i j) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem ncard_orbit {G ι : Type} [Group G] (I : Subgroup G) (s w : G) (x : ι → G) (hx : ∀ c, x c ∈ I)
    (h1 : ∀ g ∈ I, ∃ c, ∃ b ∈ I, g * s = x c * s * b)
    (h2 : ∀ g ∈ I, ∃ c, ∃ b ∈ I, s * g = b * (s * x c))
    (h3 : ∀ c, w⁻¹ * x c * w ∈ I)
    (h4 : ∀ c c', ∀ g ∈ I, ∀ g' ∈ I, w⁻¹ * (g'⁻¹ * (s⁻¹ * ((x c')⁻¹ * x c) * s) * g) * w ∈ I → c = c') :
    (MulAction.orbit I ((s * w : G) : G ⧸ I)).ncard = Nat.card ι * (MulAction.orbit I (w : G ⧸ I)).ncard := by
  have hm : ∀ (c : ι) (q : MulAction.orbit I (w : G ⧸ I)),
      (x c * s) • (q : G ⧸ I) ∈ MulAction.orbit I ((s * w : G) : G ⧸ I) := by
    rintro c ⟨_, g, rfl⟩
    obtain ⟨a, b, hb, e⟩ := h2 g g.2
    refine ⟨⟨x c * b, mul_mem (hx c) hb⟩, ?_⟩
    show ((x c * b * (s * w) : G) : G ⧸ I) = ((x c * s * (g * w) : G) : G ⧸ I)
    rw [QuotientGroup.eq]
    have : x c * s * (g * w) = x c * (s * g) * w := by group
    rw [this, e]
    convert h3 a using 1
    group
  let f : ι × MulAction.orbit I (w : G ⧸ I) → MulAction.orbit I ((s * w : G) : G ⧸ I) :=
    fun p => ⟨_, hm p.1 p.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c, _, g, rfl⟩ ⟨c', _, g', rfl⟩ e
      have e1 : (x c * s) • ((g : G) • (w : G ⧸ I)) = (x c' * s) • ((g' : G) • (w : G ⧸ I)) :=
        congrArg Subtype.val e
      have e2 : ((x c' * s * (g' * w) : G) : G ⧸ I) = ((x c * s * (g * w) : G) : G ⧸ I) := e1.symm
      rw [QuotientGroup.eq] at e2
      have hc : c = c' := h4 c c' g g.2 g' g'.2 (by convert e2 using 1; group)
      subst hc
      exact Prod.ext rfl (Subtype.ext (smul_left_cancel _ e1))
    · rintro ⟨_, g, rfl⟩
      obtain ⟨c, b, hb, e⟩ := h1 g g.2
      refine ⟨(c, ⟨_, ⟨b, hb⟩, rfl⟩), Subtype.ext ?_⟩
      show ((x c * s * (b * w) : G) : G ⧸ I) = ((g * (s * w) : G) : G ⧸ I)
      rw [← mul_assoc, ← e, mul_assoc]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod, Nat.card_eq_of_bijective f hf]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem step (C : Subgroup 𝓀[k]ˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1)
    (hw : w⁻¹ i < w⁻¹ j) :
    (MulAction.orbit (iwC k n C) ((pm k n (Equiv.swap i j * w) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard =
      resCard k * (MulAction.orbit (iwC k n C) ((pm k n w : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard := by
  choose r hr using IsLocalRing.residue_surjective (R := 𝒪[k])
  obtain ⟨x, hx, hxu, ho, h2⟩ := simpleOrbit k n C i j hij r hr
  have hU : unipO k n ≤ iwC k n C := le_sup_right.trans le_sup_left
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨hmem, -, -, hun⟩ := memIwC k n C
  have hdiag : ∀ g ∈ iwC k n C, ∀ a, valuation k ((g : Matrix (Fin n) (Fin n) k) a a) = 1 := by
    intro g hg a
    obtain ⟨c, ⟨d, -, rfl⟩, e⟩ := ((hmem g).1 hg).2 a
    rw [← e]
    exact (hun _).1 ⟨d, trivial, rfl⟩
  have hlow : ∀ g ∈ iwC k n C, ∀ a b, b < a → valuation k ((g : Matrix (Fin n) (Fin n) k) a b) < 1 :=
    fun g hg => (mem_iwahori.1 ((hmem g).1 hg).1).2
  rw [map_mul]
  refine ncard_orbit (iwC k n C) _ _ x (fun c => hU (hxu c)) ?_ h2 ?_ ?_
  · intro g hg
    obtain ⟨c, hc, -⟩ := (ho ((g * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).1
      ⟨⟨g, hg⟩, rfl⟩
    exact ⟨c, _, QuotientGroup.eq.1 hc, by group⟩
  · intro c
    have hK : pm k n w ∈ KO k (Fin n) := ⟨pm 𝒪[k] n w, map_pm _ w⟩
    have hK' : (pm k n w)⁻¹ * x c * pm k n w ∈ KO k (Fin n) := mul_mem (mul_mem (inv_mem hK) (hxu c).2) hK
    refine hU ⟨(mem_unipB k).2 ⟨fun a b hab => ?_, fun a => ?_⟩, hK'⟩
    · rw [conj_apply, hx, Matrix.add_apply, one_apply_ne (w.injective.ne hab.ne'), single_apply, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at hw
      exact lt_asymm hw hab
    · rw [conj_apply, hx, Matrix.add_apply, one_apply_eq, single_apply, if_neg, add_zero]
      rintro ⟨h, h'⟩
      exact hlt.ne (h.trans h'.symm)
  · intro c c' g hg g' hg' h
    set d : k := algebraMap 𝒪[k] k (r c) - algebraMap 𝒪[k] k (r c') with hd
    have hz : (((x c')⁻¹ * x c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 + single i j d := by
      rw [Units.val_mul, Units.inv_mul_eq_iff_eq_mul, hx, hx, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
        single_mul_single_of_ne _ _ _ _ hlt.ne', add_zero, add_assoc, ← single_add, hd, sub_add_cancel]
    have hy : (((pm k n (Equiv.swap i j))⁻¹ * ((x c')⁻¹ * x c) * pm k n (Equiv.swap i j) : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 1 + single j i d := by
      ext a b
      rw [conj_apply, hz]
      simp only [Matrix.add_apply, one_apply, single_apply, Equiv.apply_eq_iff_eq]
      congr 2
      · change (1 : Matrix (Fin n) (Fin n) k) _ _ = (1 : Matrix (Fin n) (Fin n) k) _ _
        simp [Matrix.one_apply]
      · rw [← Equiv.symm_apply_eq, ← Equiv.symm_apply_eq, Equiv.symm_swap, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
    have h5 := hlow _ h _ _ hw
    rw [conj_apply, Units.val_mul, Units.val_mul, hy, mul_add, add_mul, mul_one, Matrix.add_apply] at h5
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h5
    have h6 := hlow _ (mul_mem (inv_mem hg') hg) j i hlt
    rw [Units.val_mul] at h6
    have h7 : (((g'⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * single j i d * (g : Matrix (Fin n) (Fin n) k)) j i =
        ((g'⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) j j * d * (g : Matrix (Fin n) (Fin n) k) i i := by
      rw [Matrix.mul_apply, Fintype.sum_eq_single i, mul_single_apply_same]
      intro a ha
      rw [mul_single_apply_of_ne _ _ _ _ _ ha, zero_mul]
    have h8 := Valuation.map_sub_lt _ h5 h6
    rw [add_sub_cancel_left, h7, map_mul, map_mul, hdiag _ (inv_mem hg'), hdiag _ hg, one_mul, mul_one, hd,
      ← map_sub] at h8
    have h9 : IsLocalRing.residue 𝒪[k] (r c - r c') = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
      exact h8.ne
    rwa [map_sub, hr, hr, sub_eq_zero] at h9

end UpperTheory.V.AlgebraTools.PermCard

open UpperTheory.V.AlgebraTools.PermCard in
theorem UpperTheory.V.AlgebraTools.permCard :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (w : Equiv.Perm (Fin n)), (MulAction.orbit (iwC k n C) ((pm k n w : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard = resCard k ^ invLen w := by
  intro k _ _ _ _ n C w
  generalize hm : invLen w = m
  induction m generalizing w with
  | zero =>
    rw [(lenStep n w).2.1 hm, map_one, pow_zero, Set.ncard_eq_one]
    refine ⟨_, Set.eq_singleton_iff_unique_mem.2 ⟨MulAction.mem_orbit_self _, ?_⟩⟩
    rintro _ ⟨g, rfl⟩
    show (((g : GL (Fin n) k) * 1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = _
    rw [QuotientGroup.eq]
    simpa using g.2
  | succ m ih =>
    have hw : w ≠ 1 := by
      rintro rfl
      have : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
        rw [invLen, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun p _ h => lt_asymm h.1 h.2
      omega
    obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw
    have hl := ((lenStep n w).1 i j hij).2 hlt
    have hs := step C (Equiv.swap i j * w) i j hij (by simpa using hlt)
    rw [Equiv.swap_mul_self_mul] at hs
    rw [hs, ih _ (by omega), pow_succ']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleQuad
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem quadAbs {A G M ι : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] [Fintype ι] [DecidableEq ι]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (s : G) (hs : s * s = 1) (x : ι → G)
    (hx : ∀ c, x c ∈ I) (hT : ∀ v : fixd ρ I, (hk ρ I s v : M) = ∑ c, ρ (x c * s) v) (o : ι) (ho : x o = 1)
    (y d : ι → G) (hy : ∀ c ≠ o, y c ∈ I) (hc : ∀ c ≠ o, ∀ c', x c' * y c = y c * x c')
    (hd : ∀ c ≠ o, d c ∈ Subgroup.normalizer (I : Set G))
    (h : ∀ c ≠ o, s * x c * s = y c * s * d c * y c) :
    hk ρ I s * hk ρ I s = (Fintype.card ι : A) • 1 + ∑ c ∈ Finset.univ.erase o, hk ρ I s * hk ρ I (d c) := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have fx : ∀ (w : fixd ρ I), ∀ g ∈ I, ρ g w = w := fun w => w.2
  have key : ∀ c ≠ o, ∑ c', ρ (x c' * s) (ρ (x c * s) v) = (hk ρ I s (hk ρ I (d c) v) : M) := by
    intro c hco
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← fx (hk ρ I s _) _ (hy c hco), hT, map_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [(hkNorm A G M ρ I (d c) hI (hd c hco)).1]
    conv_rhs => rw [← fx v _ (hy c hco)]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    calc x c' * s * (x c * s) = x c' * (s * x c * s) := by group
      _ = (x c' * y c) * s * d c * y c := by rw [h c hco]; group
      _ = _ := by rw [hc c hco]; group
  have k0 : ∑ c', ρ (x c' * s) (ρ (x o * s) v) = (Fintype.card ι : A) • (v : M) := by
    have : ∀ c', ρ (x c' * s) (ρ (x o * s) v) = v := fun c' => by
      rw [← Module.End.mul_apply, ← map_mul, ho, one_mul, mul_assoc, hs, mul_one, fx v _ (hx c')]
    simp only [this]
    simp [Nat.cast_smul_eq_nsmul]
  rw [Module.End.mul_apply, hT, hT]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ o), k0]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Module.End.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c hc' => key c (Finset.ne_of_mem_erase hc')

private theorem matId {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Rˣ) :
    (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) * (1 + single i j (a : R)) * (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) =
      (1 + single i j ((a⁻¹ : Rˣ) : R)) * (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) *
      (diagT R (Fin n) (fun l => if l = i then a else if l = j then -a⁻¹ else 1) : Matrix (Fin n) (Fin n) R) *
      (1 + single i j ((a⁻¹ : Rˣ) : R)) := by
  have hP : (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) =
      1 - single i i 1 - single j j 1 + single i j 1 + single j i 1 := by
    ext p q
    rw [pm_apply]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, single_apply, Equiv.swap_apply_def]
    by_cases h1 : p = i <;> by_cases h2 : p = j <;> by_cases h3 : q = i <;> by_cases h4 : q = j <;>
      simp_all [eq_comm]
  have hD : (diagT R (Fin n) (fun l => if l = i then a else if l = j then -a⁻¹ else 1) : Matrix (Fin n) (Fin n) R) =
      1 - single i i 1 - single j j 1 + single i i (a : R) - single j j ((a⁻¹ : Rˣ) : R) := by
    ext p q
    rw [val_diagT]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, single_apply, diagonal_apply]
    by_cases h1 : p = i <;> by_cases h2 : p = j <;> by_cases h3 : q = i <;> by_cases h4 : q = j <;>
      simp_all [eq_comm]
  rw [hP, hD]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hij.symm, zero_mul, mul_zero,
    Units.inv_mul, Units.mul_inv]
  abel

private theorem swapDiag {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (t : Fin n → Rˣ) :
    pm R n w * diagT R (Fin n) (t ∘ w) = diagT R (Fin n) t * pm R n w := by
  ext p q
  rw [Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul, pm_apply]
  split_ifs with h
  · simp [h]
  · simp

private theorem diagNorm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) {t : Fin n → kˣ} (ht : t ∈ torusO k (Fin n)) :
    diagT k (Fin n) t ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  have h := diagT_mem_iwahori ht
  have N := (memIwC k n C).2.2.1
  refine Subgroup.mem_normalizer_iff.2 fun b => ⟨N _ h b, fun hb => ?_⟩
  have := N _ (inv_mem h) _ hb
  simpa [mul_assoc] using this

theorem UpperTheory.V.AlgebraTools.simpleQuad :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (i j : Fin n), (j : ℕ) = i + 1 → (IsUnit (resCard k : A) → IsUnit (hk ρ (iwC k n C) (pm k n (Equiv.swap i j)))) ∧ (C = ⊤ → hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) * hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) = ((resCard k : A) - 1) • hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) + (resCard k : A) • 1) := by
  intro k _ _ _ _ n C A M _ _ _ ρ i j hj
  classical
  have hij : i ≠ j := fun h => by rw [h] at hj; omega
  have hI := (heckePairIwC k n C).1
  have hU : unipO k n ≤ iwC k n C := le_sup_right.trans le_sup_left
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  have hq : resCard k = Fintype.card 𝓀[k] := Nat.card_eq_fintype_card
  obtain ⟨r0, hr0⟩ := (IsLocalRing.residue_surjective (R := 𝒪[k])).hasRightInverse
  have hup : ∀ (b : 𝒪[k]) c, IsLocalRing.residue 𝒪[k] (Function.update r0 (IsLocalRing.residue 𝒪[k] b) b c) = c := by
    intro b c
    by_cases h : c = IsLocalRing.residue 𝒪[k] b
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hr0 c
  obtain ⟨x, hx1, hx2, hx3, -⟩ := simpleOrbit k n C i j hj _ (hup 0)
  set r := Function.update r0 (IsLocalRing.residue 𝒪[k] 0) 0 with hr
  set s := pm k n (Equiv.swap i j) with hs
  have hss : s * s = 1 := by rw [hs, ← map_mul, Equiv.swap_mul_self, map_one]
  have hx0 : x 0 = 1 := by
    ext1
    rw [hx1]
    have : r 0 = 0 := by rw [hr, ← map_zero (IsLocalRing.residue 𝒪[k])]; simp
    simp [this]
  have hT : ∀ v : fixd ρ (iwC k n C), (hk ρ (iwC k n C) s v : M) = ∑ c, ρ (x c * s) v := by
    intro v
    have horb : ∀ c, ((x c * s : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) ∈
        MulAction.orbit (iwC k n C) (s : GL (Fin n) k ⧸ iwC k n C) := fun c => ⟨⟨x c, hU (hx2 c)⟩, rfl⟩
    have hinj : Function.Injective fun c => x c * s := fun c c' h =>
      ((hx3 _).1 (horb c)).unique rfl (congrArg _ h.symm)
    have := (hkApply A _ M ρ _ _ s (hI s)).2.1 (Finset.univ.image fun c => x c * s) (fun y hy => by
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
      exact horb c) (fun q hq => by
      obtain ⟨c, hc, hu⟩ := (hx3 q).1 hq
      refine ⟨x c * s, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ c), hc⟩, ?_⟩
      rintro y ⟨hy, hy'⟩
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hy
      rw [hu c' hy']) v
    rw [Finset.sum_image fun c _ c' _ h => hinj h] at this
    exact this
  have hex : ∀ c : 𝓀[k], ∃ (y : GL (Fin n) k) (t : Fin n → kˣ), t ∈ torusO k (Fin n) ∧ (c ≠ 0 → y ∈ iwC k n C ∧
      (∀ c', x c' * y = y * x c') ∧ s * x c * s = y * s * diagT k (Fin n) t * y) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨1, 1, one_mem _, fun h => absurd hc h⟩
    obtain ⟨u, hu⟩ : IsUnit (r c) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hup 0]; exact hc
    obtain ⟨z, hz1, hz2, -⟩ := simpleOrbit k n C i j hj _ (hup ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]))
    let a : kˣ := Units.map (algebraMap 𝒪[k] k).toMonoidHom u
    have ha : valuation k (a : k) = 1 := (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have hz := hz1 (IsLocalRing.residue 𝒪[k] ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]))
    rw [Function.update_self] at hz
    have hz' : (z (IsLocalRing.residue 𝒪[k] ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : Matrix (Fin n) (Fin n) k) =
      1 + single i j ((a⁻¹ : kˣ) : k) := hz
    have hxc : (x c : Matrix (Fin n) (Fin n) k) = 1 + single i j (a : k) := by rw [hx1, ← hu]; rfl
    refine ⟨z (IsLocalRing.residue 𝒪[k] ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])),
      fun l => if l = i then a else if l = j then -a⁻¹ else 1, fun l => ?_, fun _ => ⟨hU (hz2 _), fun c' => ?_, ?_⟩⟩
    · dsimp only
      split_ifs <;> simp [ha]
    · ext1
      rw [Units.val_mul, Units.val_mul, hz', hx1]
      simp only [mul_add, add_mul, mul_one, one_mul, single_mul_single_of_ne _ _ _ _ hij.symm]
      abel
    · ext1
      simp only [Units.val_mul, hz', hxc]
      exact matId i j hij a
  choose y t ht hy using hex
  have Q := quadAbs ρ _ hI s hss x (fun c => hU (hx2 c)) hT 0 hx0 y (fun c => diagT k (Fin n) (t c))
    (fun c h => (hy c h).1) (fun c h => (hy c h).2.1) (fun c _ => diagNorm C (ht c)) (fun c h => (hy c h).2.2)
  rw [← hq] at Q
  refine ⟨fun hu => ?_, fun hC => ?_⟩
  · obtain ⟨q, hq'⟩ := hu
    have hsw : ∀ c, hk ρ (iwC k n C) s * hk ρ (iwC k n C) (diagT k (Fin n) (t c)) =
        hk ρ (iwC k n C) (diagT k (Fin n) (t c ∘ Equiv.swap i j)) * hk ρ (iwC k n C) s := by
      intro c
      have h' : t c ∘ Equiv.swap i j ∈ torusO k (Fin n) := fun l => ht c _
      rw [← ((hkNorm A _ M ρ _ _ hI (diagNorm C (ht c))).2.2.2 s).2,
        ← ((hkNorm A _ M ρ _ _ hI (diagNorm C h')).2.2.2 s).1, hs, ← swapDiag]
      congr 3
      ext l
      simp
    have h1 : hk ρ (iwC k n C) s * (((q⁻¹ : Aˣ) : A) • (hk ρ (iwC k n C) s -
        ∑ c ∈ Finset.univ.erase 0, hk ρ (iwC k n C) (diagT k (Fin n) (t c)))) = 1 := by
      rw [mul_smul_comm, mul_sub, Finset.mul_sum, Q, add_sub_cancel_right, smul_smul, ← hq', Units.inv_mul, one_smul]
    have h2 : (((q⁻¹ : Aˣ) : A) • (hk ρ (iwC k n C) s -
        ∑ c ∈ Finset.univ.erase 0, hk ρ (iwC k n C) (diagT k (Fin n) (t c ∘ Equiv.swap i j)))) * hk ρ (iwC k n C) s = 1 := by
      rw [smul_mul_assoc, sub_mul, Finset.sum_mul, Q]
      simp only [hsw]
      rw [add_sub_cancel_right, smul_smul, ← hq', Units.inv_mul, one_smul]
    refine ⟨⟨_, _, h1, ?_⟩, rfl⟩
    rw [← left_inv_eq_right_inv h2 h1]
    exact h2
  · have h1 : ∀ c, hk ρ (iwC k n C) (diagT k (Fin n) (t c)) = 1 := fun c => by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [(hkNorm A _ M ρ _ _ hI (diagNorm C (ht c))).1]
      refine v.2 _ ?_
      rw [hC, (memIwC k n ⊤).2.1]
      exact diagT_mem_iwahori (ht c)
    rw [Q, add_comm]
    simp only [h1, mul_one, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_sub Fintype.card_pos, hq, Nat.cast_one]
end

