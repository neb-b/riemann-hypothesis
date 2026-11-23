module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SegDefs
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CardLinkIdxMulLe
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem mem_Tset (j : Fin D.J) (m : Fin D.r) (z : D.OL) :
    z ∈ D.Tset j m ↔ (∃ b, D.seg b = j ∧ z = Sum.inl b) ∨ (∃ m', m < m' ∧ z = Sum.inr (j, m')) := by
  simp only [Tset, LLj, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩

theorem Tset_mono (j : Fin D.J) {m m' : Fin D.r} (h : m ≤ m') : D.Tset j m' ⊆ D.Tset j m := by
  intro z hz
  rw [mem_Tset] at hz ⊢
  rcases hz with hz | ⟨m'', hm'', rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨m'', lt_of_le_of_lt h hm'', rfl⟩

theorem Tset_disjoint {j j' : Fin D.J} (h : j ≠ j') (m m' : Fin D.r) :
    Disjoint (D.Tset j m) (D.Tset j' m') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_Tset] at hz hz'
  rcases hz with ⟨b, hb, rfl⟩ | ⟨m1, -, rfl⟩
  · rcases hz' with ⟨b', hb', e⟩ | ⟨m2, -, e⟩
    · have : b = b' := Sum.inl.inj e
      subst this
      exact h (hb.symm.trans hb')
    · cases e
  · rcases hz' with ⟨b', -, e⟩ | ⟨m2, -, e⟩
    · cases e
    · have := Sum.inr.inj e
      exact h (congrArg Prod.fst this)

theorem Tset_pair (x y : Fin D.J × Fin D.r) :
    D.Tset x.1 x.2 ⊆ D.Tset y.1 y.2 ∨ D.Tset y.1 y.2 ⊆ D.Tset x.1 x.2 ∨
      Disjoint (D.Tset x.1 x.2) (D.Tset y.1 y.2) := by
  obtain ⟨j, m⟩ := x
  obtain ⟨j', m'⟩ := y
  by_cases h : j = j'
  · subst h
    rcases le_total m m' with h | h
    · exact Or.inr (Or.inl (D.Tset_mono j h))
    · exact Or.inl (D.Tset_mono j h)
  · exact Or.inr (Or.inr (D.Tset_disjoint h m m'))

def linkIdx : Finset (Fin D.J × Fin D.r) := univ.filter fun x => x.2.val + 2 ≤ D.r

theorem card_linkIdx_le : D.linkIdx.card ≤ D.J * (D.r - 1) := by
  classical
  have h1 : D.linkIdx ⊆ (univ : Finset (Fin D.J)) ×ˢ (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r) := by
    intro x hx
    simp only [linkIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [hx]
  have h2 : (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r).card ≤ D.r - 1 := by
    have := Finset.card_le_card_of_injOn (s := univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r)
      (t := Finset.range (D.r - 1)) (fun m => m.val)
      (by
        intro m hm
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm
        simp only [Finset.coe_range, Set.mem_Iio]
        omega)
      (by intro a _ b _ hab; exact Fin.ext hab)
    simpa using this
  calc D.linkIdx.card ≤ _ := Finset.card_le_card h1
    _ = D.J * (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ D.J * (D.r - 1) := Nat.mul_le_mul_left _ h2

theorem eC_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.eC p C0 := by
  unfold eC
  have := lg_ge_one hp hr (2 * D.totDeg)
  positivity

theorem Dm_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dm p C0 := by
  unfold Dm
  have := D.eC_nonneg' hp hr h1
  exact Finset.sum_nonneg fun j _ => by positivity

theorem Dl_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dl p C0 := by
  unfold Dl
  have := D.eC_nonneg' hp hr h1
  have h2 : (0 : ℝ) ≤ (D.r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
    linarith
  positivity

theorem kapD_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) : 0 ≤ D.kapD p := by
  unfold kapD
  refine le_trans ?_ (kap_ge_card hp hr D.dO)
  positivity

theorem card_linkIdx_mul_le {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) :
    (D.linkIdx.card : ℝ) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, D.dO i)) ≤ D.Dl p C0 := by
  have he : (D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, D.dO i) = D.eC p C0 := rfl
  rw [he]
  unfold Dl
  have h2 : (D.linkIdx.card : ℝ) ≤ (D.J : ℝ) * ((D.r : ℝ) - 1) := by
    have := D.card_linkIdx_le
    have h3 : ((D.linkIdx.card : ℕ) : ℝ) ≤ ((D.J * (D.r - 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_one] at h3
    exact h3
  exact mul_le_mul_of_nonneg_right h2 (D.eC_nonneg' hp hr h1)

end TwistData

section StepB

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem stepB_of (h1 : 1 ≤ C0) (hV2 : V2 K) (hP : PROJ K v p C0) : StepB K v p C0 := by
  classical
  intro hD D hV hc F hF hF0
  obtain ⟨hr, hJ, hc1, -, -, hthl, hga, hgaε⟩ := hV
  haveI : NeZero D.r := ⟨by omega⟩
  have hp : 2 ≤ p := two_le_p hD
  have hr1 : 1 ≤ D.r := hr
  obtain ⟨⟨α0, hα0, hge0, hle0⟩, hbF⟩ := exists_of_vBB_zero v F hF0
  obtain ⟨hFP, -, hFl⟩ := hF
  obtain ⟨Pr, p1, p2, p3, p4, -, -⟩ := prodProj (r := D.r) D.osg D.dO hP hD D.linkIdx
    (fun x => D.Tset x.1 x.2) (fun x => ⌈D.thl x.1 x.2⌉) (fun x _ y _ => D.Tset_pair x y)
  have hα0d : ∀ i, ldeg α0 i = D.dO i := (mem_PolK_iff _ _).mp hFP α0 hα0
  have hmon : (monomial α0 (1 : K)) ∈ PolK K D.r D.dO := by
    rw [mem_PolK_iff]
    intro β hβ
    have := support_monomial_subset hβ
    rw [Finset.mem_singleton] at this
    rw [this]; exact hα0d
  have hDm := D.Dm_nonneg' hp hr1 h1
  have hDl := D.Dl_nonneg' hp hr1 h1
  have hkap := D.kapD_nonneg' hp hr1
  have hcc : 4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c := hc

  have hY1 : Pr (monomial α0 1) ∈ PolK K D.r D.dO := p1 _ hmon
  have hY2 : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
      vala D.osg (D.Tset j m) (D.thl j m) (Pr (monomial α0 1)) := fun j m hm =>
    (vala_iff_Aset _ _ _ _).mpr (p2 _ hmon (j, m) (by simp [TwistData.linkIdx, hm]))
  have hY3 : fock F (Pr (monomial α0 1)) = F.coeff α0 * 1 * (fact α0 : K) := by
    rw [p3 F hFP (fun x hx => ?_) _ hmon, fock_monomial_right]
    have hx' : x.2.val + 2 ≤ D.r := by simpa [TwistData.linkIdx] using hx
    exact (vala_iff_Aset _ _ _ _).mp (hFl x.1 x.2 hx')
  have hY4 : bge v (vN v (fact α0) / 2 - D.Dl p C0) (Pr (monomial α0 1)) := by
    have h := p4 _ hmon _ (bge_monomial v α0 (vge_one v))
    refine bge_mono v ?_ h
    have := D.card_linkIdx_mul_le hp hr1 h1
    linarith
  have hY5 : vle v (vN v (fact α0) / 2) (fock F (Pr (monomial α0 1))) := by
    rw [hY3, mul_one]
    have := vle_mul v hle0 (vle_vN hD (fact_ne_zero α0))
    exact vle_mono v (by linarith) this

  obtain ⟨T, lam, hlam, hT⟩ := hgaε (-1) (Or.inr rfl)
  have hC : CostOK (CostV (K := K) (r := D.r) D.osg Set.univ) :=
    costV_ok _ _ (fun S _ θ F G => vala_add) (fun S _ θ a F => vala_smul a)
  have hch : ∀ (x : D.OL × Fin D.r) (k : ℕ),
      CostV D.osg Set.univ k (fun α : D.OL × Fin D.r →₀ ℕ => ((α x).choose k : K)) :=
    fun x k S _ θ F h => vala_dg_choose hV2 x k h
  obtain ⟨g, hg0, hgc, hgC⟩ := approx_of_trunc (v := v) hC hch T lam hlam (fun α => D.ga α ^ (-1 : ℤ)) hT

  have hsplit : D.gaAct (dg g (Pr (monomial α0 1))) =
      Pr (monomial α0 1) + dg (fun α => D.ga α * g α - 1) (Pr (monomial α0 1)) := by
    rw [gaAct_eq_dg]
    ext α
    rw [MvPolynomial.coeff_add, coeff_dg, coeff_dg, coeff_dg]
    ring
  have herr : ∀ α, vge v (D.c : ℝ) (D.ga α * g α - 1) := by
    intro α
    have hne : D.ga α ≠ 0 := by
      intro h0
      have := hga α
      rw [h0, AddValuation.map_zero] at this
      exact absurd this (by simp)
    have e : D.ga α * g α - 1 = -(D.ga α * (D.ga α ^ (-1 : ℤ) - g α)) := by
      rw [zpow_neg_one]; field_simp; ring
    rw [e]
    have h2 := vge_mul v (vge_unit v (hga α)).1 ((vge_natCast_bound v D.c _).mpr (hgc α))
    rw [zero_add] at h2
    exact vge_neg v h2
  have hpair : vle v (vN v (fact α0) / 2) (fock F (D.gaAct (dg g (Pr (monomial α0 1))))) := by
    rw [hsplit, fock_add_right]
    refine vle_add_of_lt v hY5 (vge_fock v hbF (bge_dg v herr hY4)) ?_
    linarith

  have ha0 : vN v (fact α0) / 2 ≤ D.n0 v := by
    have := fact_upper hD hα0d
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    rw [h4]; linarith
  have hx0 : 0 ≤ D.n0 v + D.Dl p C0 - vN v (fact α0) / 2 := by linarith
  have hG2P : dg g (Pr (monomial α0 1)) ∈ PolK K D.r D.dO := by
    rw [mem_PolK_iff]
    intro β hβ
    exact (mem_PolK_iff _ _).mp hY1 β (support_dg_subset g _ hβ)
  have hG2b : bge v (0 + (vN v (fact α0) / 2 - D.Dl p C0)) (dg g (Pr (monomial α0 1))) :=
    bge_dg v (fun α => (vge_zero_iff v _).mpr (hg0 α)) hY4
  refine ⟨((p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊) • dg g (Pr (monomial α0 1)),
    ⟨Submodule.smul_mem _ _ hG2P, ?_⟩, ?_, ?_⟩
  · rw [← cge_zero_iff_Integral]
    have h5 := cge_smul v (vge_p_pow hD ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊)
      (cge_of_bge hD hG2P hG2b)
    refine cge_mono v ?_ h5
    have h6 := Nat.le_ceil (D.n0 v + D.Dl p C0 - vN v (fact α0) / 2)
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    linarith
  · intro j m hm
    have h7 := hgC (D.Tset j m) (Set.mem_univ _) _ _ (hY2 j m hm)
    have e : D.thl j m - ((6 * D.c : ℕ) : ℝ) = D.thl j m - 6 * D.c := by push_cast; ring
    rw [e] at h7
    exact vala_smul _ h7
  · have e1 : fock F (D.gaAct (((p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊) •
        dg g (Pr (monomial α0 1)))) =
        (p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊ *
          fock F (D.gaAct (dg g (Pr (monomial α0 1)))) := by
      simp only [gaAct_eq_dg, map_smul, fock_smul_right]
    rw [e1]
    refine vle_mono v ?_ (vle_pow_p hD _ hpair)
    have h8 := Nat.ceil_lt_add_one hx0
    linarith

end StepB

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.IntegralMonomial
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section General

variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}

theorem integral_zero' : Integral v (0 : MvPolynomial σ K) := by
  unfold Integral
  intro α
  simp

theorem integral_add' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F + G) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_add]
  exact le_trans (le_min (hF α) (hG α)) (v.map_add _ _)

theorem integral_sum' {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ K)
    (h : ∀ k ∈ s, Integral v (f k)) : Integral v (∑ k ∈ s, f k) := by
  exact Finset.sum_induction f (fun F => Integral v F) (fun _ _ hF hG => integral_add' hF hG)
    integral_zero' h

theorem integral_smul' {a : K} {F : MvPolynomial σ K} (ha : 0 ≤ v a) (hF : Integral v F) :
    Integral v (a • F) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul, AddValuation.map_mul]
  exact add_nonneg ha (hF α)

theorem integral_mul' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F * G) := by
  classical
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_nonneg (hF _) (hG _)

theorem integral_monomial' (α : σ →₀ ℕ) {c : K} (hc : 0 ≤ v c) : Integral v (monomial α c) := by
  classical
  unfold Integral
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hc
  · simp

end General

section Deg

variable {K : Type} [Field K] {L L' : Type} {r : ℕ}

theorem ldeg_mapDomain [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L') (β : L × Fin r →₀ ℕ)
    (i' : L') :
    ldeg (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) i' =
      ∑ l, if f l = i' then ldeg β l else 0 := by
  classical
  have key : ∀ a : Fin r, (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) (i', a) =
      ∑ l, if f l = i' then β (l, a) else 0 := by
    intro a
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : f l = i'
    · simp [Finsupp.single_apply, hl]
    · simp [Finsupp.single_apply, hl]
  simp only [ldeg, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs <;> simp

theorem HomD_prod {κ : Type} (s : Finset κ) (d : κ → L → ℕ) (f : κ → MvPolynomial (L × Fin r) K)
    (h : ∀ k ∈ s, HomD (d k) (f k)) : HomD (fun i => ∑ k ∈ s, d k i) (∏ k ∈ s, f k) := by
  classical
  have hadd : ∀ (β γ : L × Fin r →₀ ℕ) (i : L), ldeg (β + γ) i = ldeg β i + ldeg γ i := by
    intro β γ i
    simp [ldeg, Finset.sum_add_distrib]
  have hmul : ∀ (d₁ d₂ : L → ℕ) (F G : MvPolynomial (L × Fin r) K), HomD d₁ F → HomD d₂ G →
      HomD (fun i => d₁ i + d₂ i) (F * G) := by
    intro d₁ d₂ F G hF hG β hβ i
    obtain ⟨β₁, h₁, β₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul F G hβ)
    rw [hadd, hF β₁ h₁ i, hG β₂ h₂ i]
  induction s using Finset.induction_on with
  | empty =>
    intro β hβ i
    simp only [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hβ
    subst hβ
    simp [ldeg]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have e : (fun i => ∑ k ∈ insert a s, d k i) = fun i => d a i + ∑ k ∈ s, d k i := by
      funext i
      rw [Finset.sum_insert ha]
    rw [e]
    exact hmul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem HomD_rename [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L')
    (hf : Function.Injective f) (d : L → ℕ) (G : MvPolynomial (L × Fin r) K) (hG : HomD d G) :
    HomD (fun i' => ∑ l, if f l = i' then d l else 0) (rename (Prod.map f (id : Fin r → Fin r)) G) := by
  classical
  intro β hβ i'
  have hinj : Function.Injective (Prod.map f (id : Fin r → Fin r)) := by
    rintro ⟨a, b⟩ ⟨c, e⟩ hac
    simp only [Prod.map, id, Prod.mk.injEq] at hac
    exact Prod.ext (hf hac.1) hac.2
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hβ
  obtain ⟨β₀, h₀, rfl⟩ := hβ
  rw [ldeg_mapDomain]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hG β₀ h₀ l]

theorem valS_prod_le [DecidableEq L] (sg : L → Bool) (S : Finset L) {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (L × Fin r) K) :
    ∑ k ∈ s, valS sg S (f k) ≤ valS sg S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    simp [valS, lord, MvPolynomial.support_one]
    intro b hb a ha
    rw [MvPolynomial.coeff_one] at hb ha
    split_ifs at hb ha with hb0
    · rw [AddMonoidAlgebra.one_def] at ha
      unfold AddMonoidAlgebra.single at ha
      simp at ha
      rw [Finsupp.single_apply] at ha
      split_ifs at ha with ha0
      · subst ha0
        simp
      · exact absurd rfl ha
    · exact absurd rfl hb
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (add_le_add le_rfl ih).trans (by apply valS_mul_le)

end Deg

end Formalism.MainNotions.PlaneGram
end
end

