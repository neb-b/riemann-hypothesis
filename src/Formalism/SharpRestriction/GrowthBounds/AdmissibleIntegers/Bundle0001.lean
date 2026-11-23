module

public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound
section
noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

theorem sz_div_le_fact {p : ℕ} (hp : p.Prime) (n : ℕ) : n / p ≤ (n.factorial).factorization p := by
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, padicValNat_factorial (b := Nat.log p n + 2) (by omega)]
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p n + 2) := by simp
  have h2 := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simp only [pow_one] at h2
  exact h2

private theorem primesLE_eq_filter_prime_range (n : ℕ) :
    Nat.primesLE n = Finset.filter Nat.Prime (Finset.range (n + 1)) := by
  ext p
  simp [Nat.primesLE, Nat.mem_primesBelow]

theorem sz_sum_div_log (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
  have hsub : Nat.primesLE n ⊆ (n.factorial).factorization.support := by
    intro p hp
    rw [primesLE_eq_filter_prime_range, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finsupp.mem_support_iff]
    exact (hp.2.factorization_pos_of_dvd (Nat.factorial_ne_zero n) (hp.2.dvd_factorial.mpr (by omega))).ne'
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        rw [primesLE_eq_filter_prime_range, Finset.mem_filter] at hp
        apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
        exact_mod_cast sz_div_le_fact hp.2 n
    _ ≤ ∑ p ∈ (n.factorial).factorization.support, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p _ _
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem sz_log_fact (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : (0 : ℝ) < (n.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (n.factorial : ℕ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
    _ = n * Real.log n := Real.log_pow n _

theorem sz_mertens (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hprime : ∀ p ∈ Nat.primesLE n, p.Prime := by
    intro p hp
    rw [primesLE_eq_filter_prime_range, Finset.mem_filter] at hp
    exact hp.2
  have htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4 := by
    have h1 : Real.log ((primorial n : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, Real.log p := by
      rw [primesLE_eq_filter_prime_range, primorial, Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    rw [← h1, ← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast primorial_pos n)
    exact_mod_cast primorial_le_four_pow n
  have hfloor : ∀ p ∈ Nat.primesLE n, (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
    intro p hp
    have hpp := hprime p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [div_le_iff₀ hp0]
    have h1 : (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) = n := by exact_mod_cast Nat.div_add_mod n p
    have h2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hpp.pos
    nlinarith
  have hmain : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * Real.log n + n * Real.log 4 := by
    calc (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
        = ∑ p ∈ Nat.primesLE n, (n : ℝ) / p * Real.log p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ ∑ p ∈ Nat.primesLE n, ((((n / p : ℕ) : ℝ) + 1) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_right (hfloor p hp) (Real.log_natCast_nonneg _)
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ Nat.primesLE n, Real.log p := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ n * Real.log n + n * Real.log 4 := by
          have h := (sz_sum_div_log n).trans (sz_log_fact n)
          linarith
  exact le_of_mul_le_mul_left (by rw [mul_add]; exact hmain) hn0

theorem sz_lpF_le (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) :
    lpF l d Ds ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ s, Ds s := by
  unfold lpF
  have h : 0 ≤ sSup (lpFeasible l d Ds) := by
    apply Real.sSup_nonneg
    rintro y ⟨xs, h0, -, -, rfl⟩
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i
  linarith

end Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.RemainingPrimesOfAdmitted
section
noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

theorem mem_intW_of (D : D7) (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ≠ 0) (h : 0 ≤ vAdd (D.plEq w) x) :
    x ∈ intW D.what₂.places w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w x
  rw [D.val_eq w x hx]
  exact_mod_cast h

theorem vAdd_one (D : D7) (w : D.what₂.places.Pl) : vAdd (D.plEq w) (1 : D.what₂.LL) = 0 := by
  first
  | rfl
  | (simp [vAdd]; done)
  | (norm_num [vAdd]; done)
  | (simp; done)
  | (unfold vAdd; simp; done)
  | aesop

theorem div_mem_intW (D : D7) (w : D.what₂.places.Pl) {a b : D.what₂.LL} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : vAdd (D.plEq w) a ≤ vAdd (D.plEq w) b) : b / a ∈ intW D.what₂.places w := by
  have hq : b / a ≠ 0 := div_ne_zero hb ha
  refine mem_intW_of D w hq ?_
  have h1 : vAdd (D.plEq w) (a * (b / a)) = vAdd (D.plEq w) a + vAdd (D.plEq w) (b / a) := vAdd_mul' _ ha hq
  rw [mul_div_cancel₀ b ha] at h1
  omega

section VGeLemmas

variable {D : D7} {w : D.what₂.places.Pl} {V : Type} [AddCommGroup V] [Module D.what₂.LL V] [Module (𝓞 D.what₂.LL) V]
  {Λ : Submodule (𝓞 D.what₂.LL) V}

theorem VGe_zero (s : ℝ) : VGe D w Λ (0 : V) s := by
  exact ⟨0, 0, zero_mem _, by simp, Or.inl rfl⟩

theorem VGe_of_mem {z : V} (hz : z ∈ locW D.what₂.places w Λ) : VGe D w Λ z 0 := by
  refine ⟨1, z, hz, (one_smul _ _).symm, Or.inr ?_⟩
  rw [vAdd_one]
  first
  | (simp [ur]; done)
  | (norm_num [ur]; done)
  | (unfold ur; simp; done)
  | (simp; done)

theorem valuation_ge_add_of_le {a1 a2 : D.what₂.LL} {z1 z2 : V} {s : ℝ} (h1 : a1 ≠ 0) (h2 : a2 ≠ 0)
    (hz1 : z1 ∈ locW D.what₂.places w Λ) (hz2 : z2 ∈ locW D.what₂.places w Λ)
    (hv : ur D w s ≤ (vAdd (D.plEq w) a1 : ℝ)) (hle : vAdd (D.plEq w) a1 ≤ vAdd (D.plEq w) a2) :
    VGe D w Λ (a1 • z1 + a2 • z2) s := by
  refine ⟨a1, z1 + (⟨a2 / a1, div_mem_intW D w h1 h2 hle⟩ : intW D.what₂.places w) • z2,
    Submodule.add_mem _ hz1 (Submodule.smul_mem _ _ hz2), ?_, Or.inr hv⟩
  rw [Subring.smul_def, smul_add, smul_smul]
  show a1 • z1 + a2 • z2 = a1 • z1 + (a1 * (a2 / a1)) • z2
  rw [mul_div_cancel₀ a2 h1]

theorem VGe_add {y1 y2 : V} {s : ℝ} (h1 : VGe D w Λ y1 s) (h2 : VGe D w Λ y2 s) : VGe D w Λ (y1 + y2) s := by
  obtain ⟨a1, z1, hz1, rfl, ha1⟩ := h1
  obtain ⟨a2, z2, hz2, rfl, ha2⟩ := h2
  by_cases e1 : a1 = 0
  · subst e1
    rw [zero_smul, zero_add]
    exact ⟨a2, z2, hz2, rfl, ha2⟩
  by_cases e2 : a2 = 0
  · subst e2
    rw [zero_smul, add_zero]
    exact ⟨a1, z1, hz1, rfl, ha1⟩
  have hv1 := ha1.resolve_left e1
  have hv2 := ha2.resolve_left e2
  rcases le_total (vAdd (D.plEq w) a1) (vAdd (D.plEq w) a2) with h | h
  · exact valuation_ge_add_of_le e1 e2 hz1 hz2 hv1 h
  · rw [add_comm]
    exact valuation_ge_add_of_le e2 e1 hz2 hz1 hv2 h

theorem VGe_smul_int {y : V} {s : ℝ} (r : intW D.what₂.places w) (h : VGe D w Λ y s) :
    VGe D w Λ ((r : D.what₂.LL) • y) s := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨a, r • z, Submodule.smul_mem _ _ hz, ?_, ha⟩
  rw [Subring.smul_def, smul_smul, smul_smul, mul_comm]

theorem VGe_smul {y : V} {s s' : ℝ} {b : D.what₂.LL} (hb : b = 0 ∨ ur D w s' ≤ (vAdd (D.plEq w) b : ℝ))
    (h : VGe D w Λ y s) : VGe D w Λ (b • y) (s' + s) := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨b * a, z, hz, by rw [smul_smul], ?_⟩
  by_cases e1 : b = 0
  · left; rw [e1, zero_mul]
  by_cases e2 : a = 0
  · left; rw [e2, mul_zero]
  right
  have hv1 := hb.resolve_left e1
  have hv2 := ha.resolve_left e2
  rw [vAdd_mul' _ e1 e2]
  push_cast
  have h1 : ur D w (s' + s) = ur D w s' + ur D w s := by unfold ur; ring
  linarith

end VGeLemmas

section Chain

variable {D : D7} {hc : D.what₂.Tau → HCParam D.R} {C : ColumnChain D.R D.what₂.Tau hc} {A : ColumnsAtT D.R C}
  {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau hc C A P)
  (w : D.what₂.places.Pl)

theorem step_loc (i : ℕ) (s : ℝ)
    (hstep : ∀ x ∈ (M.lat i).L, ∃ y, M.emb (i + 1) y = C.K i (M.emb i x) ∧ VGe D w (M.lat (i + 1)).L y s)
    (z : (M.lat i).V) (hz : z ∈ locW D.what₂.places w (M.lat i).L) :
    ∃ y, M.emb (i + 1) y = C.K i (M.emb i z) ∧ VGe D w (M.lat (i + 1)).L y s := by
  unfold locW at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact hstep x hx
  | zero =>
    refine ⟨0, ?_, VGe_zero s⟩
    show M.emb (i + 1) 0 = C.Klin i (M.emb i 0)
    rw [map_zero, map_zero, map_zero]
  | add a b _ _ ha hb =>
    obtain ⟨ya, hya, hva⟩ := ha
    obtain ⟨yb, hyb, hvb⟩ := hb
    refine ⟨ya + yb, ?_, VGe_add hva hvb⟩
    show M.emb (i + 1) (ya + yb) = C.Klin i (M.emb i (a + b))
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hya, hyb]
    rfl
  | smul r a _ ha =>
    obtain ⟨ya, hya, hva⟩ := ha
    refine ⟨(r : D.what₂.LL) • ya, ?_, VGe_smul_int r hva⟩
    show M.emb (i + 1) ((r : D.what₂.LL) • ya) = C.Klin i (M.emb i (r • a))
    rw [Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.map_smul, hya]
    rfl

theorem step_ge (i : ℕ) (s s0 : ℝ)
    (hstep : ∀ x ∈ (M.lat i).L, ∃ y, M.emb (i + 1) y = C.K i (M.emb i x) ∧ VGe D w (M.lat (i + 1)).L y s)
    (x : (M.lat i).V) (hx : VGe D w (M.lat i).L x s0) :
    ∃ y, M.emb (i + 1) y = C.K i (M.emb i x) ∧ VGe D w (M.lat (i + 1)).L y (s0 + s) := by
  obtain ⟨a, z, hz, rfl, ha⟩ := hx
  obtain ⟨y, hy, hv⟩ := step_loc M w i s hstep z hz
  refine ⟨a • y, ?_, VGe_smul ha hv⟩
  show M.emb (i + 1) (a • y) = C.Klin i (M.emb i (a • z))
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.map_smul, hy]
  rfl

theorem chain_ge (s : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ i < n, ∀ x ∈ (M.lat i).L, ∃ y, M.emb (i + 1) y = C.K i (M.emb i x) ∧
      VGe D w (M.lat (i + 1)).L y (s i))
    (x : (M.lat 0).V) (hx : x ∈ locW D.what₂.places w (M.lat 0).L) :
    ∀ i ≤ n, ∃ y, M.emb i y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap i (M.emb 0 x) ∧
      VGe D w (M.lat i).L y (∑ j ∈ Finset.range i, s j) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨x, rfl, by simpa using VGe_of_mem hx⟩
  | succ i ih =>
    intro hi
    obtain ⟨y, hy, hv⟩ := ih (by omega)
    obtain ⟨y', hy', hv'⟩ := step_ge M w i (s i) _ (hstep i (by omega)) y hv
    refine ⟨y', ?_, by rw [Finset.sum_range_succ]; exact hv'⟩
    rw [hy', hy]
    rfl

end Chain

theorem sum_bounds (m : ℕ) (hm : 1 ≤ m) (sp v : ℝ) :
    ∑ j ∈ Finset.range m, (-((if j = 0 then 1 - sp else 1) * v)) = -((m : ℝ) - sp) * v := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp
  ring

theorem card_lifts (D : D7) : ((SizeData₂.lifts D).card : ℝ) = (D.R.m : ℝ) := by
  first
  | rfl
  | (simp [SizeData₂.lifts]; done)
  | (norm_num [SizeData₂.lifts]; done)
  | (simp; done)
  | (unfold SizeData₂.lifts; simp; done)
  | aesop

theorem base_map_mem_local_lattice {D : D7} (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (hx : x ∈ locW D.what₂.places w ((D.fm u).lat 0).L) :
    T.e0 u μ x ∈ locW D.what₂.places w ((T.fm u μ).lat 0).L := by
  unfold locW at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ((T.twist_preserves_base_lattice u μ x).1 hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ r ha

theorem remaining_primes_of_admitted {D : D7} {Dx : DivX D} {T : TwForms D} {sp : ℝ} (hI : IsotypicPartsInternalDirectSum D Dx T sp) (hD : DGamDef D) :
    ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
      D.what₂.places.resChar w ≠ D.host.d → D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
      ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
        ColGe T u μ w x (-(((SizeData₂.lifts D).card : ℝ) - sp) * vDG D u w) := by
  intro u w hw hd hg μ hUs hμ x hx
  have hx0 : x ∈ locW D.what₂.places w ((D.fm u).lat 0).L := hx.1
  have hm : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  rw [card_lifts, ← sum_bounds D.R.m hm sp (vDG D u w)]
  refine ⟨fun _ => ?_, fun hne => ?_⟩
  · exact chain_ge (D.fm u) w _ D.R.m (fun i hi => (hI hD u w hd hg hw i hi).1) x hx0 D.R.m le_rfl
  · obtain ⟨y, hy, hv⟩ := chain_ge (T.fm u μ) w _ D.R.m (fun i hi => (hI hD u w hd hg hw i hi).2 μ hUs hne hμ)
      (T.e0 u μ x) (base_map_mem_local_lattice T u μ w x hx0) D.R.m le_rfl
    refine ⟨y, ?_, hv⟩
    rw [hy, T.embed_mul_block_embedding]
    rfl

end Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

end
end

