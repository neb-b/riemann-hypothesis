module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0013
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HarProjEqZeroIff
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def RestCloudMaps : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (TT : Finset (Fin n')) (a ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ),
    IsBaseWeight TT aw bw ccl lam0 → IsDominant lam0 → (∀ s, s ∉ TT → lam0 s = 0) →
    (∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) → 2 * ccl ≤ 8 * a →
    ∀ e : Edge R.W R.Qq (mm + 1 + 1), IsEdge p n' 1 e →
    ∃ (nb : ℕ) (io : Vsp R.Kf (flatW (mm + 1) A B) →ₗ[R.Kf]
        Vsp R.Kf (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)))
      (U : Fin nb → Vsp R.Kf (flatW (mm + 1) A B) →ₗ[R.Kf] Vsp R.Kf lam0)
      (L : Fin nb → Vsp R.Kf lam0 →ₗ[R.Kf]
        Vsp R.Kf (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)))
      (ka : Fin nb → ℕ),
      (nb : ℝ) = dimCl TT lam0 ∧ (∀ b, ka b ≤ TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊) ∧
      (∀ a' b F, L a' (U b F) = if a' = b then ((p : R.Kf) ^ ka b) • io F else 0) ∧
      (∀ F, io F ∈ Re p R.ι R.σ R.w 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) e ↔
        F ∈ Re p R.ι R.σ R.w 1 (flatW (mm + 1) A B) e) ∧
      ∀ t c₂ : ℕ, 2 * TT.card * ccl ≤ c₂ →
        (∀ F ∈ CCL R (flatW (mm + 1) A B) t c₂ e,
          io F ∈ CCL R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ e) ∧
        (∀ b, ∀ F ∈ CCL R (flatW (mm + 1) A B) t c₂ e, U b F ∈ CCL R lam0 t c₂ e) ∧
        (∀ a', ∀ g ∈ CCL' R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ e,
          ((p : R.Kf) ^ (Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) - Ar 1 lam0)) •
            (g ∘ₗ L a') ∈ CCL' R lam0 t (c₂ - 2 * TT.card * ccl) e)

theorem lemmaSMat : LemmaSMat := fun O _ _ _ σ ρ z1 z2 h1 h2 N B => KP.lemmaSMat σ ρ z1 z2 h1 h2 N B

theorem cloud_prop_of_maps_retraction_basis (hC : RestCloudMaps) (hRet : LatRetract) (hBP : BePerfect) (hD3 : DualHeightBasis) : CloudLowerBoundWeyl := by
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 t c₂ D₁ κ₁ κ₂ hD hDc hNc hκ0 hκ1 hκ2 hρ1 hρ2 e he
  obtain ⟨nb, io, U, L, ka, hnb, hka, h24, hiso, hmem⟩ :=
    hC p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 e he
  obtain ⟨hio, hU, hL⟩ := hmem t c₂ hNc
  obtain ⟨n1, hX1, f1⟩ := hρ1 e he
  obtain ⟨n2, hX2, f2⟩ := hρ2 e he
  obtain ⟨r, hr, hfac⟩ := cloud_count R lemmaSMat hRet hBP hD3 _ _ lam0 (flattened_weight_dominant _ _ _) (flattened_weight_dominant _ _ _) e he t c₂
    (c₂ - 2 * TT.card * ccl) (Nat.sub_le _ _) D₁ hD hDc nb (TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊) io U L ka hka h24 hiso hio
    hU hL n1 n2 f1 f2
  refine ⟨nb * r, ?_, ?_⟩
  · rw [← hnb]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    linarith
  · have : (2 * D₁ + ((TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊ : ℕ) : ℝ)) =
        2 * D₁ + (TT.card : ℝ) * (⌈kappaOneExponent p a (mm + 1)⌉₊ : ℕ) := by push_cast; ring
    rw [← this]
    exact hfac

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FunctorComparisonOfSingleWeight
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem ex_val {n' : ℕ} {TT : Finset (Fin n')} (f : TT → ℕ) (s : TT) : ex f s.val = f s := by
  unfold ex
  rw [dif_pos s.2]

theorem lamAt_flat_top {n' : ℕ} (m : ℕ) (hm : 1 ≤ m) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : TT) :
    lamAt (flatW m al be) s.val =
      wtPQ m (if Even s.val.val then al s else be s) (if Even s.val.val then be s else al s) := by
  have hl : (Fin.last m) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  funext i
  have r0 : i.rev = 0 ↔ i = Fin.last m := by rw [← Fin.rev_last, Fin.rev_inj]
  have rl : i.rev = Fin.last m ↔ i = 0 := by rw [← Fin.rev_zero, Fin.rev_inj]
  unfold lamAt flatW wtPQ
  by_cases he : Even s.val.val
  · simp only [he, if_true, s.2, dite_true]
  · simp only [he, if_false, s.2, dite_true, r0, rl]
    by_cases h0 : i = 0
    · subst h0
      simp [hl.symm]
    · by_cases h1 : i = Fin.last m
      · subst h1
        simp [hl]
      · simp [h0, h1]

theorem lamAt_flat_off {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∉ TT) :
    lamAt (flatW m al be) s = 0 := by
  apply tn_lamAt_zero
  funext i
  simp [flatW, hs]

theorem functor_comparison_of_single_weight (hIOe : ExistsIO) (hPRe : ExistsPR) (hK2 : RegroupP) (h : SingleWeightLatticeComparison) : LatticeFunctorComparison := by
  classical
  intro p n' R m hm TT a A B hdeg
  let Ps : TT → ℕ := fun s => if Even s.val.val then A s else B s
  let Qs : TT → ℕ := fun s => if Even s.val.val then B s else A s
  have hdeg' : ∀ s, Ps s + Qs s + 1 ≤ 8 * a := fun s => by
    have := hdeg s
    simp only [Ps, Qs]
    split_ifs <;> omega
  have hmin : ∀ s, min (Ps s) (Qs s) = min (A s) (B s) := fun s => by
    simp only [Ps, Qs]
    split_ifs
    · rfl
    · exact min_comm _ _
  choose i1 pr1 hsum1 hrange1 hlat1 using fun s : TT => h p n' R m hm a (Ps s) (Qs s) (hdeg' s)
  choose IO hIO using fun j : TT → ℕ =>
    hIOe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => i1 s (j s))
  choose PR hPR using fun j : TT → ℕ =>
    hPRe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => pr1 s (j s))
  set Jf := Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)) with hJf
  let lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ := fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)
  have hjle : ∀ j ∈ Jf, ∀ s, j s ≤ min (Ps s) (Qs s) := fun j hj s => by
    rw [hmin]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 ((Fintype.mem_piFinset.1 hj) s))
  have hwt : ∀ (j : TT → ℕ) (s : TT), lamAt (lamj j) s.val = wtPQ m (Ps s - j s) (Qs s - j s) := fun j s => by
    rw [lamAt_flat_top m (by omega)]
    simp only [Ps, Qs]
    split_ifs <;> rfl
  have hoff : ∀ (j : TT → ℕ) (s : Fin n'), s ∉ TT → lamAt (lamj j) s = 0 := fun j s hs => lamAt_flat_off m _ _ s hs
  have hhh : ∀ (s : TT) (b : Bool), hhWt m TT (ex A) (ex B) (s, b) = letterWt m (if b then Ps s else Qs s) b := by
    intro s b
    unfold hhWt hhDeg
    cases b <;> simp [ex_val, Ps, Qs]
  have hdom : ∀ j, IsDominant (lamj j) := fun j => flattened_weight_dominant m _ _

  have hVHH : VHH (m := m) R.Kf TT (ex A) (ex B) = tensorLat R.Kf R.Kf
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) := rfl
  have htwoSp : ∀ s : TT, tensorLat R.Kf R.Kf
      (fun b : Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) (s, b)))) =
      twoSp R.Kf m (Ps s) (Qs s) := fun s => by
    unfold twoSp
    congr 1
    funext b
    rw [hhh]
  have hioV : ∀ j ∈ Jf, ∀ y ∈ Vsp R.Kf (lamj j), IO j y ∈ VHH (m := m) R.Kf TT (ex A) (ex B) := by
    intro j hj y hy
    rw [Vsp_eq R.Kf _ (hdom j)] at hy
    have := ioMem (A := R.Kf) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j) _
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1
      (fun s y hy => by
        rw [one_smul, htwoSp]
        rw [hwt] at hy
        exact ((hrange1 s (j s) (hjle j hj s)).2 y hy))
      (fun s hs y hy => by
        rw [hoff j s hs, nuOf_zero] at hy
        exact ⟨_, tn_const _ _ y hy⟩) y hy
    rw [one_pow, one_smul] at this
    exact this
  have hprV : ∀ j ∈ Jf, ∀ x ∈ VHH (m := m) R.Kf TT (ex A) (ex B), PR j x ∈ Vsp R.Kf (lamj j) := by
    intro j hj x hx
    rw [Vsp_eq R.Kf _ (hdom j)]
    have := prMem (A := R.Kf) TT (fun s => pr1 s (j s)) (PR j) (hPR j)
      (fun s => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt (lamj j) s)))
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1
      (fun s x hx => by
        rw [one_smul, hwt]
        rw [htwoSp] at hx
        exact ((hrange1 s (j s) (hjle j hj s)).1 x hx))
      (fun s hs => by
        rw [hoff j s hs, nuOf_zero]
        exact one_mem_dualWeyl _ _ _) x hx
    rw [one_pow, one_smul] at this
    exact this

  have hsumA : ∀ x ∈ VHH (m := m) R.Kf TT (ex A) (ex B), ∑ j ∈ Jf, IO j (PR j x) = x := by
    intro x hx
    rw [hVHH] at hx
    refine Submodule.span_induction (p := fun x _ => ∑ j ∈ Jf, IO j (PR j x) = x) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨F, hF, rfl⟩
      rw [genRegroupT]
      set Y : TT → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf :=
        fun s => ∏ b, blockEmb R.Kf b (F (s, b)) with hY
      have hYm : ∀ s, Y s ∈ twoSp R.Kf m (Ps s) (Qs s) := fun s => by
        rw [← htwoSp]
        exact Submodule.subset_span ⟨fun b => F (s, b), fun b => hF _, rfl⟩
      have e1 : ∀ j, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) =
          ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2))
            (i1 s (j s) (pr1 s (j s) (Y s))) := by
        intro j
        rw [hPR j, prodTopsT TT (fun s => pr1 s (j s) (Y s))]
        have := hIO j (fun s => if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1)
          (fun s hs => by rw [dite_eq_right hs])
        rw [show (∏ s : Fin n', blockEmb R.Kf s (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1)) =
          ∏ s : Fin n', rename (fun v => (s, v)) (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1) from rfl,
          this]
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [dif_pos s.2]
      show ∑ j ∈ Jf, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) =
        ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s)
      simp only [e1]
      rw [hJf, ← Finset.prod_univ_sum (fun s : TT => Finset.range (min (A s) (B s) + 1))
        (fun s j => rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (i1 s j (pr1 s j (Y s))))]
      refine Finset.prod_congr rfl fun s _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hmin s, hsum1 s (Y s) (hYm s)]
    · simp
    · intro x y _ _ hx hy
      simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]
    · intro c x _ hx
      simp only [map_smul]
      rw [← Finset.smul_sum, hx]
  refine ⟨fun j => if hj : j ∈ Jf then
      LinearMap.codRestrict _ ((IO j).comp (Submodule.subtype _)) (fun y => hioV j hj y.1 y.2) else 0,
    fun j => if hj : j ∈ Jf then
      LinearMap.codRestrict _ ((PR j).comp (Submodule.subtype _)) (fun x => hprV j hj x.1 x.2) else 0, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    rw [← hsumA x.1 x.2]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [dif_pos hj]
    rfl
  · intro M hM j hj
    simp only [dif_pos hj]
    have hpow : (p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊) =
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) ^ TT.card := by rw [← pow_mul, mul_comm]
    have htwoLat : ∀ s : TT, tensorLat R.O R.Kf
        (fun b : Bool => H0 R.O m (hhWt m TT (ex A) (ex B) (s, b)) (M s.val)) =
        twoLat R.O m (Ps s) (Qs s) (M s.val) := fun s => by
      unfold twoLat
      congr 1
      funext b
      rw [hhh]
    constructor
    · intro x hx
      have := prMem (A := R.O) TT (fun s => pr1 s (j s)) (PR j) (hPR j)
        (fun s => H0 R.O m (lamAt (lamj j) s) (M s))
        (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val))
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊)
        (fun s x hx => by
          rw [hwt]
          rw [htwoLat] at hx
          exact ((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).1 x hx))
        (fun s hs => by
          rw [hoff j s hs]
          exact (invariant_sections_zero_weight_iff m (M s) (hM s) 1).2 ⟨1, by simp⟩) x.1 hx
      rw [← hpow] at this
      exact this
    · intro y hy
      have := ioMem (A := R.O) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j)
        (fun s => H0 R.O m (lamAt (lamj j) s) (M s))
        (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val))
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊)
        (fun s y hy => by
          rw [htwoLat]
          rw [hwt] at hy
          exact ((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).2 y hy))
        (fun s hs y hy => by
          rw [hoff j s hs] at hy
          exact (invariant_sections_zero_weight_iff m (M s) (hM s) y).1 hy) y.1 hy
      rw [← hpow] at this
      exact this

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightOfModelIdentification
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility Formalism.CountingSumsFrames MvPolynomial

def RS.Ov {p n' : ℕ} (R : RS p n') : ValuationSubring R.Kf :=
  { (algebraMap R.O R.Kf).range with
    mem_or_inv_mem' := by
      intro x
      have := R.std.1.frac_O
      rcases ValuationRing.isInteger_or_isInteger R.O x with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact Or.inl ⟨a, ha⟩
      · exact Or.inr ⟨a, ha⟩ }

theorem RS.mem_Ov {p n' : ℕ} (R : RS p n') (a : R.O) : algebraMap R.O R.Kf a ∈ R.Ov.toSubring := ⟨a, rfl⟩

theorem RS.pLocal {p n' : ℕ} (R : RS p n') : PLocal R.Ov.toSubring p := by
  intro n hn
  have hcop : IsCoprime (n : ℤ) (p : ℤ) := by
    have := (Nat.Prime.coprime_iff_not_dvd R.std.1.prime).2 hn
    exact (Nat.isCoprime_iff_coprime.2 this).symm
  obtain ⟨a, b, hab⟩ := hcop
  have hu : IsUnit (n : R.O) := by
    by_contra hnu
    have h1 : (n : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h2 : (p : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 R.p_not_unit
    have h3 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) ∈ IsLocalRing.maximalIdeal R.O :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    have h4 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) = 1 := by
      have := congrArg (fun z : ℤ => (z : R.O)) hab
      simpa using this
    rw [h4] at h3
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 isUnit_one
  obtain ⟨v, hv⟩ := hu
  refine ⟨((v⁻¹ : R.Oˣ) : R.O), ?_⟩
  have h5 : algebraMap R.O R.Kf ((v⁻¹ : R.Oˣ) : R.O) * (n : R.Kf) = 1 := by
    rw [← map_natCast (algebraMap R.O R.Kf) n, ← hv, ← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h5

def TwoLetterModelIdentification : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m →
    ∃ (α : ∀ P Q : ℕ, twoSp R.Kf m P Q ≃ₗ[R.Kf] PolAB R.Kf (m + 1) P Q)
      (β : ∀ a b : ℕ, PolAB R.Kf (m + 1) a b →ₗ[R.Kf] dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b))),
      (∀ a b, Function.Surjective (β a b)) ∧
      (∀ a b (f : PolAB R.Kf (m + 1) a b), β a b f = 0 ↔
        ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), (f : PolXY R.Kf (m + 1)) = hXY R.Kf (m + 1) * G) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∃ g' : GL (Fin (m + 1)) R.Kf,
        (∀ (P Q : ℕ) (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf), x ∈ twoLat R.O m P Q Λ ↔
          ∃ hx : x ∈ twoSp R.Kf m P Q,
            (α P Q ⟨x, hx⟩ : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring)) ∧
        (∀ (a b : ℕ) (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), y ∈ H0 R.O m (wtPQ m a b) Λ ↔
          ∃ f : PolAB R.Kf (m + 1) a b, (f : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring) ∧
            (β a b f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = y)

theorem expo_le (p a m P Q : ℕ) (hp : 2 ≤ p) (h : P + Q + 1 ≤ 8 * a) :
    (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) ≤ ⌈((m : ℝ) + 2) * lgA p a m⌉₊ := by
  have h1 : (Nat.log p (P + Q + (m + 1)) : ℝ) ≤ Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) := Real.natLog_le_logb _ _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have h2 : Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + m) := by
    apply Real.logb_le_logb_of_le hp1
    · have : 0 < P + Q + (m + 1) := by omega
      exact_mod_cast this
    · have : P + Q + (m + 1) ≤ 8 * a + m := by omega
      exact_mod_cast this
  have h3 : (((m + 1 + 1) * Nat.log p (P + Q + (m + 1)) : ℕ) : ℝ) ≤ ((m : ℝ) + 2) * lgA p a m := by
    unfold lgA
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    have : ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hm
  exact_mod_cast le_trans h3 (Nat.le_ceil _)

theorem single_weight_of_model_identification (h : TwoLetterModelIdentification) : SingleWeightLatticeComparison := by
  classical
  intro p n' R m hm a P Q hPQ
  obtain ⟨α, β, hsurj, hker, hlat⟩ := h p n' R m hm
  have : CharZero R.Kf := R.charZero
  have hp := R.std.1.prime
  obtain ⟨io, pr, hsum, hL⟩ := oneTop_abs R.Kf (m + 1) P Q p (by omega) hp R.Ov R.pLocal (α P Q)
    (fun j => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) (fun j => β (P - j) (Q - j))
    (fun j => hsurj _ _) (fun j f => hker _ _ f)
  set E := (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) with hE
  set U := ⌈((m : ℝ) + 2) * lgA p a m⌉₊ with hU
  have hEU : E ≤ U := expo_le p a m P Q hp.two_le hPQ
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hEU
  have hpd : (p : R.Kf) ^ d ∈ R.Ov.toSubring := Subring.pow_mem _ (natCast_mem _ p) d
  have hexI : ∀ j, ∃ I : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf,
      I ∘ₗ (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype =
        (twoSp R.Kf m P Q).subtype ∘ₗ io j := fun j => LinearMap.exists_extend _
  have hexP : ∀ j, ∃ Pj : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
      Pj ∘ₗ (twoSp R.Kf m P Q).subtype =
        (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype ∘ₗ pr j :=
    fun j => LinearMap.exists_extend _
  choose I hI using hexI
  choose Pj hPj using hexP
  have hI' : ∀ j (y : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))),
      I j (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = (io j y : MvPolynomial _ R.Kf) :=
    fun j y => LinearMap.congr_fun (hI j) y
  have hP' : ∀ j (x : twoSp R.Kf m P Q),
      Pj j (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf) = (pr j x : MvPolynomial _ R.Kf) :=
    fun j x => LinearMap.congr_fun (hPj j) x
  refine ⟨I, Pj, ?_, ?_, ?_⟩
  · intro x hx
    have h0 := congrArg (twoSp R.Kf m P Q).subtype (hsum ⟨x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    calc ∑ j ∈ Finset.range (min P Q + 1), I j (Pj j x)
        = ∑ j ∈ Finset.range (min P Q + 1), (twoSp R.Kf m P Q).subtype (io j (pr j ⟨x, hx⟩)) :=
          Finset.sum_congr rfl fun j _ => by rw [hP' j ⟨x, hx⟩, hI']; rfl
      _ = x := h0
  · intro j _
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rw [hP' j ⟨x, hx⟩]; exact (pr j ⟨x, hx⟩).2
    · rw [hI' j ⟨y, hy⟩]; exact (io j ⟨y, hy⟩).2
  · intro Λ hΛ j hj
    obtain ⟨g', h1, h2⟩ := hlat Λ hΛ
    obtain ⟨hA, hB⟩ := hL g' j hj
    constructor
    · intro x hx
      obtain ⟨hx2, hx3⟩ := (h1 P Q x).1 hx
      obtain ⟨f, hf, hfe⟩ := hA ⟨x, hx2⟩ hx3
      refine (h2 (P - j) (Q - j) _).2 ⟨((p : R.Kf) ^ d) • f, smul_mem_latOf _ g' hpd hf, ?_⟩
      rw [map_smul, hfe, hP' j ⟨x, hx2⟩, Submodule.coe_smul, Submodule.coe_smul, smul_smul, hd, pow_add, mul_comm]
    · intro y hy
      obtain ⟨f, hf, hfe⟩ := (h2 (P - j) (Q - j) y).1 hy
      have h3 := hB f hf
      have hy2 : y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))) := by
        rw [← hfe]; exact (β (P - j) (Q - j) f).2
      have hyf : (⟨y, hy2⟩ : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) = β (P - j) (Q - j) f :=
        Subtype.ext hfe.symm
      refine (h1 P Q _).2 ⟨?_, ?_⟩
      · rw [hI' j ⟨y, hy2⟩]
        exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2
      · have e : (⟨((p : R.Kf) ^ U) • I j y, by
            rw [hI' j ⟨y, hy2⟩]; exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2⟩ : twoSp R.Kf m P Q) =
            ((p : R.Kf) ^ d) • (((p : R.Kf) ^ E) • io j (β (P - j) (Q - j) f)) := by
          have hIy : I j y = (io j (β (P - j) (Q - j) f) : MvPolynomial _ R.Kf) := by
            rw [← hyf]; exact hI' j ⟨y, hy2⟩
          apply Subtype.ext
          show ((p : R.Kf) ^ U) • I j y = _
          rw [Submodule.coe_smul, Submodule.coe_smul, hIy, smul_smul, hd, pow_add, mul_comm]
        rw [e, map_smul, Submodule.coe_smul]
        exact smul_mem_latOf _ g' hpd h3

end Formalism.MainNotions.flipOneThree.Pf

end
end

