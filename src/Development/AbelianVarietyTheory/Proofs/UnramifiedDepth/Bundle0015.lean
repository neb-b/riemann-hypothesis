module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import ReciprocityTheory.DualLattices.FormalChartAtZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm.Axis

variable {C : Type} [Field C] {ι ι' : Type}

def VanishesOnFirstAxis (F : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ F = 0

theorem VanishesOnFirstAxis.mul_left {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (G : MvPowerSeries (ι ⊕ ι') C) : VanishesOnFirstAxis (G * F) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [h p.2, mul_zero]
  intro b
  have h1 := hμ b
  rw [← hp', Finsupp.add_apply] at h1
  omega

theorem VanishesOnFirstAxis.smul {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (c : C) : VanishesOnFirstAxis (c • F) := by
  intro μ hμ
  rw [map_smul, h μ hμ, smul_zero]

theorem VanishesOnFirstAxis.sum {α : Type} (s : Finset α) {F : α → MvPowerSeries (ι ⊕ ι') C}
    (h : ∀ x, VanishesOnFirstAxis (F x)) : VanishesOnFirstAxis (∑ x ∈ s, F x) := by
  intro μ hμ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun x _ => h x μ hμ

theorem vanishes_X_inr (b : ι') :
    VanishesOnFirstAxis (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_X, if_neg]
  intro h
  have h1 := hμ b
  rw [h] at h1
  simp at h1

theorem VanishesOnFirstAxis.of_dvd {F G : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (hd : F ∣ G) : VanishesOnFirstAxis G := by
  obtain ⟨K, rfl⟩ := hd
  rw [mul_comm]
  exact h.mul_left K

theorem vanishes_mainM [Fintype ι] [Fintype ι'] (V : VF C) (i : ℕ) (Φ : ι' → ι → C) :
    VanishesOnFirstAxis (mainM V i Φ) :=
  (VanishesOnFirstAxis.sum _ fun b => VanishesOnFirstAxis.sum _ fun _ =>
    ((vanishes_X_inr b).mul_left _).smul _).smul _

theorem vanishes_hM {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ)
    [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) :
    VanishesOnFirstAxis (X.hM g a i e v') := by
  intro μ hμ
  unfold RowData.hM hPullW
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    intro w
    simp [map_sum]))]
  refine finsum_eq_zero_of_forall_eq_zero fun ν => ?_
  by_cases hν : ∀ w ∈ ν.support, w.1 = g
  · rw [X.hL_axes g _ _ ν (Or.inl hν), zero_smul]
  · push Not at hν
    obtain ⟨w, hw, hg⟩ := hν
    have h1 : VanishesOnFirstAxis
        ((∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
          ∑ b : ι', toW (1 - g) (v' b) w •
            (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) := by
      have h0 : ∀ c, toW g (e c) w = 0 := fun c => by simp [toW, hg]
      simp only [h0, zero_smul, Finset.sum_const_zero, zero_add]
      exact VanishesOnFirstAxis.sum _ fun b => (vanishes_X_inr b).smul _
    rw [h1.of_dvd _ μ hμ, smul_zero]
    unfold Finsupp.prod
    exact (dvd_pow_self _ (Finsupp.mem_support_iff.1 hw)).trans (Finset.dvd_prod_of_mem _ hw)

theorem coeff_hM_sub_mainM_eq_zero : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d]
    (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J)
    (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  intro C _ V d _ I J _ _ X g a i ι ι' _ _ e v' Φ μ hμ
  rw [map_sub, vanishes_hM X g a i e v' μ hμ, vanishes_mainM V i Φ μ hμ, sub_zero]

end GlobalTheory.MainTerm.Axis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBasicNEvalSubCoeffMem
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Type} [CommRing S] [Algebra R₀ S]

lemma evBasic_tEval_eq_sum (N : ℕ) (f : MvPowerSeries ι R₀) (a : ι → S) :
    tEval N f a = ∑ e ∈ Fintype.piFinset (fun _ : ι => Finset.range N),
      algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) f) *
        ∏ i, a i ^ e i := by
  unfold tEval
  refine Finset.sum_bij' (fun e _ => fun i => (e i : ℕ))
    (fun e he => fun i => ⟨e i, Finset.mem_range.mp (Fintype.mem_piFinset.mp he i)⟩) ?_ ?_ ?_ ?_ ?_
  · intro e _
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (e i).isLt
  · intro e _
    exact Finset.mem_univ _
  · intro e _
    rfl
  · intro e _
    rfl
  · intro e _
    rfl

lemma evBasic_tEval_of_le {N N' : ℕ} (hN : N ≤ N') (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, a i ^ N = 0) : tEval N f a = tEval N' f a := by
  rw [evBasic_tEval_eq_sum, evBasic_tEval_eq_sum]
  apply Finset.sum_subset
  · intro e he
    rw [Fintype.mem_piFinset] at he ⊢
    exact fun i => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp (he i)) hN)
  · intro e _ hne
    rw [Fintype.mem_piFinset] at hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_range, not_lt] at hi
    have hz : ∏ j, a j ^ e j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← Nat.sub_add_cancel hi, pow_add, ha i, mul_zero])
    rw [hz, mul_zero]

lemma evBasic_tEval_indep {N N' : ℕ} (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, a i ^ N = 0) (ha' : ∀ i, a i ^ N' = 0) : tEval N f a = tEval N' f a := by
  rcases le_total N N' with h | h
  · exact evBasic_tEval_of_le h f a ha
  · exact (evBasic_tEval_of_le h f a ha').symm

lemma evBasic_nEval_eq_tEval (f : MvPowerSeries ι R₀) (a : ι → S) (N : ℕ)
    (ha : ∀ i, a i ^ N = 0) : nEval f a = tEval N f a := by
  classical
  unfold nEval
  split_ifs with h
  · exact evBasic_tEval_indep f a (Nat.find_spec h) ha
  · exact absurd ⟨N, ha⟩ h


omit [DecidableEq ι] in
lemma evBasic_exists_pow (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, a i ^ N = 0 := by
  have ha' : ∀ i, ∃ m : ℕ, a i ^ m = 0 := ha
  choose n hn using ha'
  refine ⟨(∑ i, n i) + 1, Nat.succ_pos _, fun i => pow_eq_zero_of_le ?_ (hn i)⟩
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)).trans (Nat.le_succ _)

lemma evBasic_map_tEval {S' : Type} [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (N : ℕ)
    (f : MvPowerSeries ι R₀) (a : ι → S) :
    φ (tEval N f a) = tEval N f (fun i => φ (a i)) := by
  unfold tEval
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, AlgHom.commutes]

lemma evBasic_map_nEval {S' : Type} [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S')
    (f : MvPowerSeries ι R₀) (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    φ (nEval f a) = nEval f (fun i => φ (a i)) := by
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow a ha
  have hN' : ∀ i, φ (a i) ^ N = 0 := fun i => by rw [← map_pow, hN i, map_zero]
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_nEval_eq_tEval f _ N hN', evBasic_map_tEval]

lemma evBasic_nEval_sub_coeff_mem (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, IsNilpotent (a i)) :
    nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a) := by
  obtain ⟨N, hNpos, hN⟩ := evBasic_exists_pow a ha
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_tEval_eq_sum]
  have h0 : (0 : ι → ℕ) ∈ Fintype.piFinset (fun _ : ι => Finset.range N) :=
    Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr hNpos
  rw [← Finset.add_sum_erase _ _ h0]
  have hc : algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (0 : ι → ℕ)) f) *
      ∏ i, a i ^ (0 : ι → ℕ) i = algebraMap R₀ S (MvPowerSeries.coeff 0 f) := by
    have hz : Finsupp.equivFunOnFinite.symm (0 : ι → ℕ) = 0 := by
      ext i
      rfl
    simp [hz]
  rw [hc, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun e he => ?_
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Finset.ne_of_mem_erase he (funext hcon)
  refine Ideal.mul_mem_left _ _ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _
    (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) _ (Nat.pos_of_ne_zero hi))

end

theorem nEval_basic :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) := by
  intro R₀ _ ι _ _ f S _ _ a
  exact ⟨fun N hN => evBasic_nEval_eq_tEval f a N hN,
    fun ha => ⟨fun S' _ _ φ => evBasic_map_nEval φ f a ha, evBasic_nEval_sub_coeff_mem f a ha⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralGermNabValCongr
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.IntegralColumnGerm

theorem prod_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) {ι : Type} [Fintype ι] (α : ι → R)
    (hα : ∀ l, α l - 1 ∈ I) (n : ι → ℕ) : ∏ l, α l ^ n l - 1 ∈ I := by
  rw [← Ideal.Quotient.eq, map_prod, map_one]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [map_pow, Ideal.Quotient.eq.2 (hα l), map_one, one_pow]

theorem exists_eq_of_unit_mul {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) (I : Ideal R) {P x y : R}
    {v : k} (hP : IsUnit P) (hP1 : P - 1 ∈ I) (hxy : x - y ∈ I) (h : φ P * v = φ x) :
    ∃ r ∈ I, v = φ (y + r) := by
  obtain ⟨Q, hQ⟩ := hP.exists_left_inv
  refine ⟨Q * ((x - y) - (P - 1) * y), I.mul_mem_left _ (I.sub_mem hxy (I.mul_mem_right _ hP1)), ?_⟩
  have e : y + Q * ((x - y) - (P - 1) * y) = Q * x := by linear_combination (-y) * hQ
  rw [e, map_mul, ← h, ← mul_assoc, ← map_mul, hQ, map_one, one_mul]

end GlobalTheory.IntegralColumnGerm

namespace GlobalTheory

open IntegralColumnGerm

theorem exists_integral_germ_nabVal_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (B.hL k h ((N : O) * w))) = algebraMap R k (N * r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) := by
  intro hS hL R _ d O _ _ k _ _ _ B h hh hinj w0 a c N m I hac hN ι _ u α hα1 hαu hα hβ χ
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : ∀ w : O, constantCoeff (B.hL k h w) = 0 := fun w =>
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w) (gp_pt 0))) h hh0
  have e0 : star a * (w0 * a) = (N : O) * (c * w0) := by linear_combination w0 * hac
  have h1 := FramePull.expIntegral_ad hh a 1 (w0 * a)
  rw [e0, mul_one, ← FramePull.ev_actK_hL, ← FramePull.hL_eq] at h1
  obtain ⟨cD, υ, υ1, hυ⟩ := h1
  have hinv : υ * invOfUnit υ 1 = 1 := mul_invOfUnit υ 1 (by simpa using υ1)
  obtain ⟨g, hg⟩ : ∃ g : PS R 1 d, g * υ ^ m = χ :=
    ⟨χ * invOfUnit υ 1 ^ m, by rw [mul_assoc, ← mul_pow, mul_comm _ υ, hinv, one_pow, mul_one]⟩
  refine ⟨g, fun mo => ?_⟩
  have hga : FB.toK k (ev (n := 1) ![B.A.act a] g) = ev (n := 1) ![B.actK k a] (FB.toK k g) := by
    rw [FB.toK, QuadDeriv.map_ev _ _ (single_point_zero_constant (B.A.const a))]
    congr 1
    funext j; fin_cases j; rfl
  have hG : ev (n := 1) ![B.actK k a] (FB.toK k g * FB.expS k ((m : k) • B.hL k h w0)) =
      FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) *
        FB.expS k ((m : k) • B.hL k h ((N : O) * (c * w0))) := by
    have e : FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) =
        FB.toK k (ev (n := 1) ![B.A.act a] g) * FB.toK k υ ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hga, hυ, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, sub_add_cancel]
  have hend := (invariantDeriv_along_endo R d O k B a).2 ι (fun l i => algebraMap R k (u l i))
    (fun l => algebraMap R k (α l)) hα
  have hmap : ∀ (mo : ι →₀ ℕ) (f : PS R 1 d),
      constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (FB.toK k f)) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo f)) := fun mo f => by
    rw [← constantCoeff_map, map_dmonOf]
    rfl
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • B.hL k h ((N : O) * (c * w0)))) = algebraMap R k r := by
    intro mo
    obtain ⟨t, ht⟩ := hS R d O k B h hh (c * w0) N ι u hβ mo
    refine ⟨(m : R) * (N * t), I.mul_mem_left _ (I.mul_mem_right _ hN), ?_⟩
    rw [smul_eq_C_mul, GE.dmonOf_Cmul, map_mul, constantCoeff_C, ht, map_mul (algebraMap R k) (m : R),
      map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cL, mul_zero]) hφ (ev (n := 1) ![B.A.act a] g * υ ^ m) mo
  have hcong : ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) -
      constantCoeff (DmonOf B.G.F u mo g) ∈ I := by
    intro mo
    have e1 : constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) =
        (∏ l, α l ^ mo l) * constantCoeff (DmonOf B.G.F u mo g) := by
      apply hinj
      rw [← hmap, hga, hend, hmap]
      simp only [map_mul, map_prod, map_pow]
    rw [e1, ← sub_one_mul]
    exact I.mul_mem_right _ (prod_pow_sub_one_mem I α hα1 mo)
  have hleib := hL R d B.G.F I ι u _ _ (υ ^ m) hcong mo
  rw [hg] at hleib
  refine exists_eq_of_unit_mul (algebraMap R k) I (P := ∏ l, α l ^ mo l)
    (x := constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g * υ ^ m)) + r)
    (IsUnit.prod_univ_iff.2 fun l => (hαu l).pow _) (prod_pow_sub_one_mem I α hα1 mo) ?_ ?_
  · rw [add_sub_right_comm]
    exact I.add_mem hleib hr
  · unfold FB.nabVal
    rw [PullbackColumn.dpolyOf_monomial_one, ← e]
    simp only [map_prod, map_pow]
    rw [← hend, hG]
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximal
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory

theorem exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue {R : Type} [CommRing R]
    [IsLocalRing R] (n n0 : ℕ) (Φ : Fin n → Fin n0 → R)
    (h : LinearIndependent (IsLocalRing.ResidueField R)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue R (Φ b c))) :
    n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) R, IsUnit Y.det ∧
      ∀ (b : Fin n) (c : Fin n0), ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  have hle : n0 ≤ n := by simpa using h.fintype_card_le_finrank
  refine ⟨hle, ?_⟩
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨w, hw⟩ := exists_linearIndependent_sumElim_of_finrank_eq (n' := n') (by simp) _ h
  choose s hs using IsLocalRing.residue_surjective (R := R)
  let M : Matrix (Fin (n0 + n')) (Fin (n0 + n')) R := Matrix.of fun i j =>
    Sum.elim (Φ i) (fun j' => s (w j' i)) (finSumFinEquiv.symm j)
  have hcol : (M.map (IsLocalRing.residue R)).col =
      Sum.elim (fun (c : Fin n0) (b : Fin (n0 + n')) => IsLocalRing.residue R (Φ b c)) w ∘
        finSumFinEquiv.symm := by
    funext j i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases j with j | j
    · simp [M, Matrix.col]
    · simp [M, Matrix.col, hs]
  have hu : IsUnit (M.map (IsLocalRing.residue R)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hw.comp _ finSumFinEquiv.symm.injective
  have hdet : IsUnit M.det := by
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    have : (M.map (IsLocalRing.residue R)).det = IsLocalRing.residue R M.det :=
      (RingHom.map_det (IsLocalRing.residue R) M).symm
    rw [this] at hu
    exact (isUnit_map_iff (IsLocalRing.residue R) _).mp hu
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨-M⁻¹, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det M hdet)).neg
  · intro b c
    have hij : ∑ b', M⁻¹ b b' * Φ b' c = (M⁻¹ * M) b (Fin.castAdd n' c) := by
      simp [M, Matrix.mul_apply]
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hij, hinv, Matrix.one_apply]
    by_cases hbc : b.val = c.val
    · rw [if_pos hbc, if_pos (Fin.ext hbc)]
    · rw [if_neg hbc, if_neg (fun e => hbc (by rw [e]; rfl)), neg_zero]

theorem exists_unimodular_mul_eq_neg_of_indepMod : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  intro C _ V n n0 Φ hΦ hind
  let O : ValuationSubring C := (AddValuation.toValuation V.v).valuationSubring
  have hmem : ∀ x : C, x ∈ O ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hge : ∀ x : C, V.Ge 0 x ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hunit : ∀ x : O, IsUnit x ↔ V.v (x : C) = 0 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have h1 : V.v (x : C) + V.v (y : C) = 0 := by
        rw [← V.v.map_mul, ← V.v.map_one]
        exact congrArg (fun z : O => V.v (z : C)) hy
      have h2 := (hmem _).1 x.2
      have h3 := (hmem _).1 y.2
      exact le_antisymm (by
        calc V.v (x : C) = V.v (x : C) + 0 := (add_zero _).symm
          _ ≤ V.v (x : C) + V.v (y : C) := by gcongr
          _ = 0 := h1) h2
    · intro hx
      have hx0 : (x : C) ≠ 0 := by
        intro h0
        rw [h0, V.v.map_zero] at hx
        exact WithTop.top_ne_zero hx
      have h1 : V.v (x : C)⁻¹ = 0 := by
        have := V.v.map_mul (x : C) (x : C)⁻¹
        rw [mul_inv_cancel₀ hx0, V.v.map_one, hx, zero_add] at this
        exact this.symm
      exact IsUnit.of_mul_eq_one (⟨(x : C)⁻¹, (hmem _).2 h1.ge⟩ : O)
        (Subtype.ext (mul_inv_cancel₀ hx0))
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ V.MM (x : C) := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨fun h => lt_of_le_of_ne ((hmem _).1 x.2) (Ne.symm h), fun h => ne_of_gt h⟩
  let Ψ : Fin n → Fin n0 → O := fun b c => ⟨Φ b c, (hmem _).2 ((hge _).1 (hΦ b c))⟩
  have hli : LinearIndependent (IsLocalRing.ResidueField O)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue O (Ψ b c)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg ν
    choose s hs using IsLocalRing.residue_surjective (R := O)
    rw [← hs (g ν), hres]
    refine hind (fun ν => (s (g ν) : C)) (fun ν => (hge _).2 ((hmem _).1 (s (g ν)).2)) (fun x => ?_) ν
    have h1 : IsLocalRing.residue O (∑ ν, s (g ν) * Ψ x ν) = 0 := by
      have := congrFun hg x
      simpa [hs, Finset.sum_apply] using this
    rw [hres] at h1
    simpa [Ψ] using h1
  obtain ⟨hle, Y, hY, hYΦ⟩ := exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue n n0 Ψ hli
  refine ⟨hle, Y.map O.subtype, fun b b' => (hge _).2 ((hmem _).1 (Y b b').2), ?_, fun b c _ => ?_⟩
  · have : (Y.map O.subtype).det = O.subtype Y.det := (RingHom.map_det O.subtype Y).symm
    rw [this]
    exact (hunit _).1 hY
  · have := congrArg O.subtype (hYΦ b c)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_mul, apply_ite O.subtype, map_neg, map_one, map_zero] at this
    exact this

end GlobalTheory
end

