module

public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.EndomorphismLimitIntegral
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePE0

open PartialDerivEval

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem actK_self (B : FB C dd O) (a : O) : B.actK C a = B.A.act a := by
  funext i; unfold FB.actK; rw [show algebraMap C C = RingHom.id C from rfl, map_id]; rfl

theorem TendsS.ev {m n : ℕ} {a : ℕ → Fin m → Pt C n dd} {A : Fin m → Pt C n dd} {f : ℕ → PS C m dd}
    {F : PS C m dd} (ha0 : ∀ k, Z0 (a k)) (hA0 : Z0 A) (ha : ∀ j i, TendsS V (fun k => a k j i) (A j i))
    (hf : TendsS V f F) : TendsS V (fun k => ev (a k) (f k)) (ev A F) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  exact TendsS.subst (fun k p => ha0 k p.1 p.2) (fun p => hA0 p.1 p.2) (fun p => ha p.1 p.2) hf

theorem constant_zero_two_points {n : ℕ} (P Q : Pt C n dd) (hP : ∀ i, constantCoeff (P i) = 0) (hQ : ∀ i, constantCoeff (Q i) = 0) :
    Z0 (![P, Q] : Fin 2 → Pt C n dd) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem tends_two {n : ℕ} {P Q : ℕ → Pt C n dd} {P' Q' : Pt C n dd} (hP : ∀ i, TendsS V (fun k => P k i) (P' i))
    (hQ : ∀ i, TendsS V (fun k => Q k i) (Q' i)) :
    ∀ j i, TendsS V (fun k => (![P k, Q k] : Fin 2 → Pt C n dd) j i) ((![P', Q'] : Fin 2 → Pt C n dd) j i) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem const_comp1 {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) {b : Pt C n dd}
    (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin dd) : constantCoeff (comp1 φ b i) = 0 :=
  const_ev (z0_1 b hb) (hφ i)

theorem TendsS.comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {Φ : Pt C 1 dd} {b : ℕ → Pt C n dd} {B : Pt C n dd}
    (hb0 : ∀ k i, constantCoeff (b k i) = 0) (hB0 : ∀ i, constantCoeff (B i) = 0)
    (hφ : ∀ i, TendsS V (fun k => φ k i) (Φ i)) (hb : ∀ i, TendsS V (fun k => b k i) (B i)) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) (b k) i) (comp1 Φ B i) :=
  TendsS.ev (fun k => z0_1 _ (hb0 k)) (z0_1 _ hB0)
    (fun j i' => by rw [Fin.fin_one_eq_zero j]; exact hb i') (hφ i)

theorem TendsS.expS {n : ℕ} {g : ℕ → PS C n dd} {G : PS C n dd} (hg0 : ∀ k, constantCoeff (g k) = 0)
    (hG0 : constantCoeff G = 0) (hg : TendsS V g G) : TendsS V (fun k => FB.expS C (g k)) (FB.expS C G) := by
  unfold FB.expS PowerSeries.subst
  exact TendsS.subst (fun k _ => hg0 k) (fun _ => hG0) (fun _ => hg) (TendsS.const _)

theorem exists_lim (Y : FBChart C V O dd) {φ : ℕ → Pt C 1 dd}
    (hφ : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (coeff μ (φ (n + 1) i) - coeff μ (φ n i))) :
    ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => φ n i) (e i) := by
  have h : ∀ i μ, ∃ x, Tends V (fun n => coeff μ (φ n i)) x := fun i μ => exists_tends Y.cpl fun N => hφ N i μ
  choose L hL using h
  exact ⟨fun i => (fun μ => L i μ : MvPowerSeries (Fin 1 × Fin dd) C), fun i μ => hL i μ⟩

theorem const_of_lim (Y : FBChart C V O dd) {a : ℕ → O} {e : Pt C 1 dd}
    (he : ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i)) (i : Fin dd) : constantCoeff (e i) = 0 := by
  have h := he i 0
  simp only [coeff_zero_eq_constantCoeff_apply, Y.B.A.const] at h
  exact h.unique (tends_const 0)

theorem endomorphism_limit_integral (Y : FBChart C V O dd) : EndomorphismLimitIntegral Y := by
  intro a ha hb
  obtain ⟨e, he⟩ := exists_lim Y (φ := fun n => Y.B.A.act (a n)) ha
  obtain ⟨eb, heb⟩ := exists_lim Y (φ := fun n => Y.B.A.act (star (a n))) hb
  have e0 := const_of_lim Y he
  have eb0 := const_of_lim Y (a := fun n => star (a n)) heb
  have act0 : ∀ x i, constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨e, eb, fun i => (he i).intS fun n => Y.intAct _ i, fun i => (heb i).intS fun n => Y.intAct _ i,
    fun N i μ => he i μ N, fun N i μ => heb i μ N, ?_, ?_⟩
  ·
    funext i
    have hP : ∀ i, constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) i) = 0 :=
      fun j => const_addOf Y 0 1 j
    have L := TendsS.comp1 (φ := fun k => Y.B.A.act (a k)) (b := fun _ => addOf Y.B.G.F (pt C (n := 2) dd 0)
      (pt C (n := 2) dd 1)) (fun _ => hP) hP he (fun j => TendsS.const _) i
    have hc : ∀ (j : Fin 2) k i', constantCoeff (comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd j) i') = 0 :=
      fun j k i' => const_comp1 (act0 _) (fun _ => z0_pt j _) i'
    have hcl : ∀ (j : Fin 2) i', constantCoeff (comp1 e (pt C (n := 2) dd j) i') = 0 :=
      fun j i' => const_comp1 e0 (fun _ => z0_pt j _) i'
    have R := TendsS.ev (V := V) (f := fun _ => Y.B.G.F i) (F := Y.B.G.F i)
      (a := fun k => ![comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 0), comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 1)])
      (A := ![comp1 e (pt C (n := 2) dd 0), comp1 e (pt C (n := 2) dd 1)])
      (fun k => constant_zero_two_points _ _ (hc 0 k) (hc 1 k)) (constant_zero_two_points _ _ (hcl 0) (hcl 1))
      (tends_two (TendsS.comp1 (fun _ => z0_pt 0) (z0_pt 0) he (fun _ => TendsS.const _))
        (TendsS.comp1 (fun _ => z0_pt 1) (z0_pt 1) he (fun _ => TendsS.const _))) (TendsS.const _)
    have eq : (fun k => comp1 (Y.B.A.act (a k)) (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) i) =
        fun k => ev ![comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 0), comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 1)]
          (Y.B.G.F i) := funext fun k => by rw [Y.B.A.hom (a k)]; rfl
    rw [eq] at L
    exact L.unique R
  ·
    let g : ℕ → PS C 2 dd := fun k => ev (n := 2) ![comp1 (Y.B.A.act (a k)) (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 (Y.B.A.act (star (a k))) (pt C dd 1)] Y.h
    have hc0 : ∀ k, Z0 (![comp1 (Y.B.A.act (a k)) (pt C dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) :=
      fun k => constant_zero_two_points _ _ (const_comp1 (act0 _) (fun _ => z0_pt 0 _)) (fun _ => z0_pt 1 _)
    have hc1 : ∀ k, Z0 (![pt C dd 0, comp1 (Y.B.A.act (star (a k))) (pt C dd 1)] : Fin 2 → Pt C 2 dd) :=
      fun k => constant_zero_two_points _ _ (fun _ => z0_pt 0 _) (const_comp1 (act0 _) (fun _ => z0_pt 1 _))
    have hC0 : Z0 (![comp1 e (pt C dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) :=
      constant_zero_two_points _ _ (const_comp1 e0 (fun _ => z0_pt 0 _)) (fun _ => z0_pt 1 _)
    have hC1 : Z0 (![pt C dd 0, comp1 eb (pt C dd 1)] : Fin 2 → Pt C 2 dd) :=
      constant_zero_two_points _ _ (fun _ => z0_pt 0 _) (const_comp1 eb0 (fun _ => z0_pt 1 _))
    have hg : TendsS V g (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h) :=
      (TendsS.ev hc0 hC0 (tends_two (TendsS.comp1 (fun _ => z0_pt 0) (z0_pt 0) he (fun _ => TendsS.const _))
        (fun _ => TendsS.const _)) (TendsS.const _)).sub
      (TendsS.ev hc1 hC1 (tends_two (fun _ => TendsS.const _)
        (TendsS.comp1 (fun _ => z0_pt 1) (z0_pt 1) heb (fun _ => TendsS.const _))) (TendsS.const _))
    have hh := h_const Y
    have hg0 : ∀ k, constantCoeff (g k) = 0 := fun k => by
      simp only [g, map_sub, constantCoeff_ev (hc0 k), constantCoeff_ev (hc1 k), hh, sub_zero]
    have hG0 : constantCoeff (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h) = 0 := by
      simp only [map_sub, constantCoeff_ev hC0, constantCoeff_ev hC1, hh, sub_zero]
    have hE := TendsS.expS hg0 hG0 hg
    have hadk : ∀ k, FB.expS C (g k) = Y.B.ad (a k) := fun k => by
      have h1 := Y.gauge.ad (a k)
      rw [toK_self, actK_self, actK_self] at h1
      exact h1.symm
    simp only [hadk] at hE
    exact hE.intS fun k => Y.intAd _

end RowTiePE0

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValNonnegLeadingCoeffOfMemTySet
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem finsupp_deg_one {σ : Type} (e : σ →₀ ℕ) (h : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  have hdeg : ∑ j ∈ e.support, e j = 1 := h
  have hne : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hdeg
    exact absurd hdeg (by norm_num)
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ j ∈ e.support, e j ≤ 1 := fun j hj =>
    hdeg ▸ Finset.single_le_sum (f := fun k => e k) (fun _ _ => Nat.zero_le _) hj
  have hei : e i = 1 := by
    have h1 := hle i hi
    have h2 := Finsupp.mem_support_iff.mp hi
    omega
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj
    simp [hei]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hj)]
    by_contra hc
    have hjs : j ∈ e.support := Finsupp.mem_support_iff.mpr hc
    have h2 : e i + e j ≤ ∑ k ∈ e.support, e k := by
      rw [← Finset.sum_pair (f := fun k => e k) (Ne.symm hj)]
      apply Finset.sum_le_sum_of_subset
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hjs
    omega

theorem coeff_alongCv_low {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := fun i => by
    have := hγ i 0 (by omega)
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0),
    finsum_eq_sum_of_support_subset (s := Finset.univ.image fun i : σ => Finsupp.single i 1)]
  · rw [Finset.sum_image (fun a _ b _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : (Finsupp.single i 1 : σ →₀ ℕ).prod (fun s e => γ s ^ e) = γ i := by
      rw [Finsupp.prod_single_index (h := fun s e => γ s ^ e) (pow_zero _), pow_one]
    show MvPowerSeries.coeff (Finsupp.single i 1) f •
      MvPowerSeries.coeff (Finsupp.single () n) ((Finsupp.single i 1 : σ →₀ ℕ).prod fun s e => γ s ^ e) = _
    rw [hp, smul_eq_mul]
    rfl
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.coe_image, Set.mem_image]
    by_contra hc
    apply he
    have hdeg : e.degree ≠ 1 := fun h => by
      obtain ⟨i, hi⟩ := finsupp_deg_one e h
      exact hc ⟨i, by simp, hi.symm⟩
    by_cases h0 : e.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have h2 : 2 ≤ e.degree := by omega
      have hdvd : (PowerSeries.X : PowerSeries C) ^ (n * e.degree) ∣ e.prod fun s m => γ s ^ m := by
        unfold Finsupp.prod
        rw [Finsupp.degree_apply, pow_mul, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_dvd_prod_of_dvd
        intro i _
        exact pow_dvd_pow_of_dvd (PowerSeries.X_pow_dvd_iff.2 (hγ i)) _
      have hz : PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 hdvd n (by nlinarith)
      show MvPowerSeries.coeff e f • PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0
      rw [hz, smul_zero]

theorem coeff_tyS_lt {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (s : ℕ) (ha : ∀ i < s, a i = 0) (m : ℕ) (hm : m < l ^ s) :
    PowerSeries.coeff m (tyS l a) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with ht
  · apply ha
    by_contra hc
    push_neg at hc
    have : l ^ s ≤ l ^ t := Nat.pow_le_pow_right (by omega) hc
    omega
  · rfl

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem val_nonneg_leading_coeff_of_mem_tySet (V : VF C) (g : Fin 2)
    (hlin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C))
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (hsat : ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (hmis : ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)))
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (s : ℕ) (h0 : ∀ i < s, x i = 0) (n : I g ⊕ JJ I g) :
    V.Ge 0 (x s n) := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨w, hw, huw⟩ := hsat
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hlin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have hpos : 1 ≤ V.l ^ s := Nat.one_le_pow _ _ (by omega)
  have hlow : ∀ (m : ℕ) (hm1 : 1 ≤ m), (∀ i, ∀ m' < m, PowerSeries.coeff m' (γ i) = 0) → ∀ i,
      PowerSeries.coeff m (γ i) = ∑ c : I g, X.u g c i * PowerSeries.coeff m (tyS V.l fun s => x s (Sum.inl c)) := by
    intro m hm1 hm i
    have e1 := coeff_alongCv_low hm1 hm (hlg0 i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1 i, map_sum] at e1
    simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      PowerSeries.coeff_smul, smul_eq_mul] at e1
    exact e1.symm
  have hord : ∀ m, m < V.l ^ s → ∀ i, PowerSeries.coeff m (γ i) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm i
      by_cases hm0 : m = 0
      · rw [hm0, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact (hγ i).1
      · rw [hlow m (by omega) (fun i m' hm' => ih m' hm' (by omega) i) i]
        apply Finset.sum_eq_zero
        intro c _
        rw [coeff_tyS_lt hl2 _ s (fun i hi => by rw [h0 i hi]; rfl) m hm, mul_zero]
  have hord' : ∀ i, ∀ m < V.l ^ s, PowerSeries.coeff m (γ i) = 0 := fun i m hm => hord m hm i
  have hlead : ∀ i, PowerSeries.coeff (V.l ^ s) (γ i) = ∑ c : I g, X.u g c i * x s (Sum.inl c) := by
    intro i
    rw [hlow _ hpos hord' i]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coeff_tyS_pow hl2]
  have hinl : ∀ c', x s (Sum.inl c') = ∑ i, PowerSeries.coeff (V.l ^ s) (γ i) * w i c' := by
    intro c'
    simp only [hlead, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ c : I g, ∑ i, X.u g c i * x s (Sum.inl c) * w i c' = (if c = c' then 1 else 0) * x s (Sum.inl c) := by
      intro c
      rw [← huw c c', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinlInt : ∀ c', V.Ge 0 (x s (Sum.inl c')) := by
    intro c'
    rw [hinl c']
    exact VF.Ge.sum fun i _ => ((hγ i).2 _).mul_int (hw i c')
  cases n with
  | inl c' => exact hinlInt c'
  | inr q =>
    have e2 := congrArg (PowerSeries.coeff (V.l ^ s)) (h2 q)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_tyS_pow hl2, map_add (f := _), map_sub, coeff_alongCv_low hpos hord' (X.constantCoeff_sg hh _), map_sum] at e2
    have e3 : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (X.sg (X.u (1 - g) q)) * PowerSeries.coeff (V.l ^ s) (γ i) =
        ∑ c : I g, X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) := by
      simp only [hlead, sg1, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    have e4 : ∀ c : I g, PowerSeries.coeff (V.l ^ s) (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) =
        if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) else 0 := by
      intro c
      split_ifs
      · rw [PowerSeries.coeff_smul, coeff_tyS_pow hl2, smul_eq_mul]
      · rw [map_zero]
    simp only [e4] at e2
    rw [e3, sub_add, ← Finset.sum_sub_distrib] at e2
    rw [e2]
    refine ((hlam q).2 _).sub (VF.Ge.sum fun c _ => ?_)
    split_ifs with hc
    · rw [sub_self]
      exact VF.Ge.zero 0
    · rw [sub_zero]
      exact (hmis c q hc).mul_int (hinlInt c)

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

