module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeTriplesDistributive
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistLa

variable {D : D7} {N N' : ℕ}

theorem La_map (T : Tor D) (f : VC D N N' →ₗ[ℂ] VC D N N')
    (g : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E)
    (hfg : ∀ A, f (embV D T A) = embV D T (g A)) {L M : Lat D N} {L' M' : Lat D N'}
    (hg : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L, A.mulVec x ∈ L') → ∀ x ∈ M, (g A).mulVec x ∈ M')
    {z : VC D N N'} (hz : z ∈ La D T L L') : f z ∈ La D T M M' := by
  have h1 : ∀ A ∈ homL D L L', g A ∈ homL D M M' := by
    intro A hA
    have : homL D L L' ≤ (homL D M M').comap (g.restrictScalars (𝓞 D.host.E)) :=
      Submodule.span_le.2 fun B hB => Submodule.subset_span (hg B hB)
    exact this hA
  have h2 : ∀ A ∈ YYl D L L', g A ∈ YYl D M M' := by
    intro A hA
    have : YYl D L L' ≤ (YYl D M M').comap (g.restrictScalars (𝓞 D.host.E)) := by
      refine Submodule.span_le.2 ?_
      rintro B ⟨a, ha, C, hC, rfl⟩
      exact Submodule.subset_span ⟨a, ha, g C, h1 C hC, map_smul g a C⟩
    exact this hA
  have h3 : La D T L L' ≤ (La D T M M').comap f.toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, g A, h2 A hA, ?_⟩
    show f (w • embV D T A) = _
    rw [map_smul, hfg]
  exact h3 hz

def lft (P : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, embT D τ (P i k) * z τ k j
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

def rgt (P : Matrix (Fin N) (Fin N) D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, z τ i k * embT D τ (P k j)
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem lft_add (P : Matrix (Fin N') (Fin N') D.host.E) (z : VC D N N') : lft P z + lft (1 - P) z = z := by
  funext τ i j
  show ∑ k, embT D τ (P i k) * z τ k j + ∑ k, embT D τ ((1 - P) i k) * z τ k j = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← add_mul, ← map_add (f := _), Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem rgt_add (P : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') : rgt P z + rgt (1 - P) z = z := by
  funext τ i j
  show ∑ k, z τ i k * embT D τ (P k j) + ∑ k, z τ i k * embT D τ ((1 - P) k j) = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← mul_add, ← map_add (f := _), Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem lft_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N') (Fin N') D.host.E) {L : Lat D N}
    {L' M' : Lat D N'} (hP : ∀ v ∈ L', P.mulVec v ∈ M') {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    lft P z ∈ La D (tor0 D cc δ) L M' := by
  refine La_map _ (lft P)
    { toFun := fun A => P * A, map_add' := fun A B => Matrix.mul_add P A B,
      map_smul' := fun c A => Matrix.mul_smul P c A } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (P i k) * embT D τ (A k j) = embT D τ ((P * A) i j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (P * A).mulVec x ∈ M'
    rw [← Matrix.mulVec_mulVec]
    exact hP _ (hA x hx)

theorem rgt_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N) (Fin N) D.host.E) {L M : Lat D N}
    {L' : Lat D N'} (hP : ∀ v ∈ M, P.mulVec v ∈ L) {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    rgt P z ∈ La D (tor0 D cc δ) M L' := by
  refine La_map _ (rgt P)
    { toFun := fun A => A * P, map_add' := fun A B => Matrix.add_mul A B P,
      map_smul' := fun c A => Matrix.smul_mul c A P } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (A i k) * embT D τ (P k j) = embT D τ ((A * P) i j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (A * P).mulVec x ∈ L'
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hP x hx)

theorem one_sub_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    (1 - P).mulVec v = v - P.mulVec v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem bet_proj {n : ℕ} {L₁ L₂ L₃ : Lat D n} (hb : Bet D L₁ L₂ L₃) {P : Matrix (Fin n) (Fin n) D.host.E}
    (h1 : ∀ v ∈ L₁ ⊔ L₃, P.mulVec v ∈ L₁) (h2 : ∀ v ∈ L₃, P.mulVec v ∈ L₃)
    (h3 : ∀ v ∈ L₁, v - P.mulVec v ∈ L₃) (v : Fin n → D.host.E) (hv : v ∈ L₂) :
    P.mulVec v ∈ L₁ ∧ P.mulVec v ∈ L₂ ∧ v - P.mulVec v ∈ L₃ := by
  obtain ⟨a, ⟨ha1, ha2⟩, b, ⟨hb2, hb3⟩, rfl⟩ := Submodule.mem_sup.1 (hb.1 hv)
  have pa := h1 a (Submodule.mem_sup_left ha1)
  have pb := h1 b (Submodule.mem_sup_right hb3)
  rw [Matrix.mulVec_add]
  refine ⟨L₁.add_mem pa pb, L₂.add_mem ?_ (hb.2 ⟨pb, h2 b hb3⟩), ?_⟩
  · have := L₂.sub_mem ha2 (hb.2 ⟨L₁.sub_mem ha1 pa, h3 a ha1⟩)
    rwa [sub_sub_cancel] at this
  · rw [add_sub_add_comm]
    exact L₃.add_mem (h3 a ha1) (L₃.sub_mem hb3 (h2 b hb3))

theorem dist_La : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), (∀ (L : Lat D N) (L₁ L₂ L₃ : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L L₁) (La D (tor0 D cc δ) L L₂) (La D (tor0 D cc δ) L L₃)) ∧ (∀ (L₁ L₂ L₃ : Lat D N) (L' : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L₁ L') (La D (tor0 D cc δ) L₂ L') (La D (tor0 D cc δ) L₃ L')) ∧ ∀ (L₀ L : Lat D N) (L₀' L' : Lat D N'), SD D L₀' → SD D L' → Dist (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L₀ L') (La D (tor0 D cc δ) L L') := by
  intro D cc δ N N'
  refine ⟨?_, ?_, ?_⟩
  · intro L L₁ L₂ L₃ s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := _root_.GlobalTheory.LatticeProjection.exists_matrix_projection D N' L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← lft_add P x]
    refine add_mem (AddSubgroup.mem_sup_left ⟨lft_mem cc δ P (fun v hv => (k v hv).1) hx,
      lft_mem cc δ P (fun v hv => (k v hv).2.1) hx⟩) (AddSubgroup.mem_sup_right
        ⟨lft_mem cc δ _ (fun v hv => ?_) hx, lft_mem cc δ _ (fun v hv => ?_) hx⟩)
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
    · rw [one_sub_mulVec]; exact (k v hv).2.2
  · intro L₁ L₂ L₃ L' s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := _root_.GlobalTheory.LatticeProjection.exists_matrix_projection D N L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← rgt_add P x, add_comm]
    refine add_mem (AddSubgroup.mem_sup_left ⟨rgt_mem cc δ _ (fun v hv => ?_) hx,
      rgt_mem cc δ _ (fun v hv => ?_) hx⟩) (AddSubgroup.mem_sup_right
        ⟨rgt_mem cc δ P (fun v hv => (k v hv).2.1) hx,
          rgt_mem cc δ P (fun v hv => hb.2 ⟨h1 v (Submodule.mem_sup_right hv), h2 v hv⟩) hx⟩)
    · rw [one_sub_mulVec]; exact hb.2 ⟨L₁.sub_mem hv (h1 v (Submodule.mem_sup_left hv)), h3 v hv⟩
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
  · intro L₀ L L₀' L' s1 s3 x hx y hy hu
    obtain ⟨P, h1, h2, h3⟩ := _root_.GlobalTheory.LatticeProjection.exists_matrix_projection D N' L₀' L' s1 s3
    have q1 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L₀' := fun v hv => by
      rw [one_sub_mulVec]; exact L₀'.sub_mem hv (h1 v (Submodule.mem_sup_left hv))
    have q2 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact h3 v hv
    have q3 : ∀ v ∈ L', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact L'.sub_mem hv (h2 v hv)
    have e : x = lft P x + lft (1 - P) (x + y) - lft (1 - P) y := by
      rw [map_add (f := _), ← add_assoc, lft_add, add_sub_cancel_right]
    have e2 : lft (1 - P) y = lft (1 - P) (x + y) - lft (1 - P) x := by
      rw [map_add (f := _), add_sub_cancel_left]
    rw [e]
    refine sub_mem (AddSubgroup.mem_sup_left (add_mem
      ⟨lft_mem cc δ P (fun v hv => h1 v (Submodule.mem_sup_right hv)) hx, lft_mem cc δ P h2 hx⟩
      ⟨lft_mem cc δ _ q1 hu, lft_mem cc δ _ q2 hu⟩)) (AddSubgroup.mem_sup_right ⟨?_, lft_mem cc δ _ q3 hy⟩)
    rw [e2]
    exact AddSubgroup.sub_mem _ (lft_mem cc δ _ q2 hu) (lft_mem cc δ _ q3 hx)

end GlobalTheory.DistLa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqCocycleSum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TripleConstant

theorem Wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') (c : ℂ) {ι : Type} (s : Finset ι)
    (G : ι → VC D N N' → ℂ) (v : VC D N N') :
    Wd D T y (fun z => c * ∑ i ∈ s, G i z) v = c * ∑ i ∈ s, Wd D T y (G i) v := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem out_mem_iff {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (q : B ⧸ A.addSubgroupOf B) :
    ((Quotient.out q : B) : V) ∈ A ↔ q = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']

theorem mu_form : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∃ r : ℝ, 0 < r ∧ μ * (r : ℂ) = ∑ᶠ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) := by
  intro D T N N' A₁ A₂ A₃ e μ h
  obtain ⟨h1, h2, h3, n12, n23, n13, he, he0, -, hI⟩ := h
  haveI f12 : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.fintypeOfIndexNeZero n12
  haveI f23 : Fintype (A₃ ⧸ A₂.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n23
  haveI f13 : Fintype (A₃ ⧸ A₁.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n13
  rw [h3.Iop_eq A₂, h2.Iop_eq A₁, h3.Iop_eq A₁] at hI
  simp only [finsum_eq_sum_of_fintype] at hI ⊢
  have p12 : 0 < Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n12))
  have p23 : 0 < Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n23))
  have p13 : 0 < Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n13))
  generalize Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) = s12 at *
  generalize Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) = s23 at *
  generalize Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) = s13 at *
  have key := _root_.GlobalTheory.ThetaTranslateCoef.coef_eq_zero D T N N' A₁ h1 e he he0
    (((A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂)) ⊕ (A₃ ⧸ A₁.addSubgroupOf A₃))
    (Sum.elim (fun p => (s23 : ℂ)⁻¹ * (s12 : ℂ)⁻¹ *
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun _ => -(μ * (s13 : ℂ)⁻¹)))
    (Sum.elim (fun p => ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun q => ((Quotient.out q : A₃) : VC D N N'))) (by
      intro v
      have hv := congrFun hI v
      simp only [Wd_mul_sum, Wd_Wd, Pi.smul_apply, smul_eq_mul] at hv
      simp only [Finset.mul_sum] at hv
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, neg_mul,
        Finset.sum_neg_distrib, mul_assoc]
      rw [hv]; ring)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, out_mem_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at key
  refine ⟨s23 * s12 / s13, by positivity, ?_⟩
  have q12 : (s12 : ℂ) ≠ 0 := by exact_mod_cast p12.ne'
  have q23 : (s23 : ℂ) ≠ 0 := by exact_mod_cast p23.ne'
  have q13 : (s13 : ℂ) ≠ 0 := by exact_mod_cast p13.ne'
  have k2 := congrArg (fun t => (s23 : ℂ) * s12 * t) (add_neg_eq_zero.1 key)
  simp only [Finset.mul_sum] at k2
  have : μ * ((s23 * s12 / s13 : ℝ) : ℂ) = (s23 : ℂ) * s12 * (μ * (s13 : ℂ)⁻¹) := by
    push_cast; ring
  rw [this, ← k2]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁
  · simp only [hp, if_true]
    field_simp
  · simp only [hp, if_false, mul_zero]

end GlobalTheory.TripleConstant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTriple
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleColumns

def IL (D : D7) (cc : Ideal (𝓞 D.host.K)) {n : ℕ} (L : Lat D n) : Lat D n :=
  Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • y}

theorem smul_mem_IL {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {t : D.host.E}
    (ht : t ∈ Iid D cc) {y : Fin n → D.host.E} (hy : y ∈ L) : t • y ∈ IL D cc L :=
  Submodule.subset_span ⟨t, ht, y, hy, rfl⟩

theorem IL_mono {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L L' : Lat D n} (h : L ≤ L') :
    IL D cc L ≤ IL D cc L' :=
  Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩

theorem hE_osmul_left (D : D7) {n : ℕ} (a : 𝓞 D.host.E) (x y : Fin n → D.host.E) :
    hE D (a • x) y = a • hE D x y := by
  rw [← algebraMap_smul D.host.E a x, hE_smul_left, Algebra.smul_def]

theorem pair_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {v w : Fin n → D.host.E}
    (hw : ∀ y ∈ L, IntE D (hE D y w)) (hv : v ∈ IL D cc L) : hE D v w ∈ Iid D cc := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨o, ho⟩ := hw y hy
    rw [hE_smul_left, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ht
  | zero => simp [hE]
  | add u v _ _ hu hv => rw [hE_add_left]; exact add_mem hu hv
  | smul a v _ hv => rw [hE_osmul_left]; exact Submodule.smul_mem _ _ hv

theorem sd_int {D : D7} {n : ℕ} {L : Lat D n} (h : SD D L) {y w : Fin n → D.host.E} (hy : y ∈ L) (hw : w ∈ L) :
    IntE D (hE D y w) := (((sd_iff D L).1 h).2.2 y).1 hy w hw

theorem smul_mem_IL_of_P {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t : D.host.E} (ht : t ∈ P • Iid D cc) :
    t • b ∈ IL D cc M := by
  refine Submodule.smul_induction_on ht (fun p hp s hs => ?_) (fun u v hu hv => ?_)
  · have : (p • s) • b = s • (p • b) := by rw [smul_assoc, smul_comm]
    rw [this]; exact smul_mem_IL hs (hb p hp)
  · rw [add_smul]; exact add_mem hu hv

theorem decomp {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {v : Fin n → D.host.E}
    (hv : v ∈ IL D cc (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : 𝓞 D.host.E, v - (a • t₀) • b ∈ IL D cc M := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨a, ha⟩ := hg (o • t) (Submodule.smul_mem _ _ ht)
    refine ⟨a, ?_⟩
    have : t • (m + o • b) - (a • t₀) • b = t • m + (o • t - a • t₀) • b := by
      rw [smul_add, sub_smul, smul_assoc o t b, smul_comm o t b]; abel
    rw [this]
    exact add_mem (smul_mem_IL ht hm) (smul_mem_IL_of_P hb ha)
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨a', ha'⟩ := hv
    refine ⟨a + a', ?_⟩
    have : u + v - ((a + a') • t₀) • b = (u - (a • t₀) • b) + (v - (a' • t₀) • b) := by
      rw [add_smul, add_smul]; abel
    rw [this]; exact add_mem ha ha'
  | smul c v _ hv =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨c * a, ?_⟩
    have : c • v - ((c * a) • t₀) • b = c • (v - (a • t₀) • b) := by
      rw [smul_sub, mul_smul, smul_assoc c]
    rw [this]; exact Submodule.smul_mem _ _ ha

def mat (D : D7) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E := fun i j => (a j • t₀) * b i

theorem pt_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z : Matrix (Fin N') (Fin N) D.host.E)
    (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) : pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_sub (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z - w) := by
  funext τ i j
  simp only [Pi.sub_apply, pt_apply, Matrix.sub_apply, map_sub, mul_sub]

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z + w) := by
  funext τ i j
  simp only [Pi.add_apply, pt_apply, Matrix.add_apply, map_add (f := _), mul_add]

def ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) :
    (Fin N → 𝓞 D.host.E) →+ VC D N N' :=
  AddMonoidHom.mk' (fun a => pt D (tor0 D cc δ) δ (mat D t₀ b a)) fun a a' => by
    rw [pt_add]; congr 1; funext i j
    simp only [mat, Pi.add_apply, Matrix.add_apply, add_smul, add_mul]

theorem ptH_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a = pt D (tor0 D cc δ) δ (mat D t₀ b a) := rfl

def phiH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N' : ℕ} (t₀ : D.host.E) (b x : Fin N' → D.host.E) :
    𝓞 D.host.E →+ ℂ :=
  AddMonoidHom.mk' (fun s => (∑ τ, ∑ i, embT D τ (s : D.host.E) *
      (δ * embT D τ (t₀ * x i) * (starRingEnd ℂ) (δ * embT D τ (t₀ * b i)))) / (area (tor0 D cc δ).abelian₂ : ℂ))
    fun s s' => by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (c c' : Fin N → 𝓞 D.host.E) :
    Hf D (tor0 D cc δ) (ptH D cc δ N t₀ x c') (ptH D cc δ N t₀ b c) =
      phiH D cc δ t₀ b x (∑ k, c' k * sgO D (c k)) := by
  have h1 : ∀ s : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E (sgO D s) =
      D.host.conj (algebraMap (𝓞 D.host.E) D.host.E s) := fun s => rfl
  rw [phiH, AddMonoidHom.mk'_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, ptH_apply, pt_apply, mat, Algebra.smul_def,
    RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, h1, embT_conj, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pt_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (fun i => z i j) ∈ IL D cc L := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N'
  rw [h2]
  constructor
  · rintro ⟨w, hw, e⟩
    rw [h1 e]; exact (h3 L w).1 hw
  · intro h
    exact ⟨z, (h3 L z).2 h, rfl⟩

theorem ptH_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (a j • t₀) • b ∈ IL D cc L :=
  pt_mem hδ L _

theorem ptH_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a + ptH D cc δ N t₀ x a = ptH D cc δ N t₀ (b + x) a := by
  rw [ptH_apply, ptH_apply, ptH_apply, pt_add]; congr 1; funext i j
  simp only [mat, Pi.add_apply, Matrix.add_apply, mul_add]

theorem exists_sub_ptH {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {M : Lat D N'}
    {P : Ideal (𝓞 D.host.E)} {b : Fin N' → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {z : VC D N N'}
    (hz : z ∈ La D (tor0 D cc δ) (stdL D N) (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : Fin N → 𝓞 D.host.E, ∀ L : Lat D N', M ≤ L →
      z - ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L := by
  obtain ⟨w, -, rfl⟩ := ((GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N').2.1 _ _ z).1 hz
  choose a ha using fun j => decomp hb hg ((pt_mem hδ _ w).1 hz j)
  refine ⟨a, fun L hL => ?_⟩
  rw [ptH_apply, pt_sub, pt_mem hδ]
  exact fun j => IL_mono hL (ha j)

theorem triDat_of_tri : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → ∀ A B C : Lat D N', Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) A) (La D (tor0 D cc δ) (stdL D N) B) (La D (tor0 D cc δ) (stdL D N) C) P N := by
  intro D cc δ hcc hδ N N' P hP A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hbx⟩
  obtain ⟨t₀, ht₀, hg, hθ⟩ := GlobalTheory.IdealGenerator.exists_generator_Iid D cc hcc P hP
  have MA : M ≤ A := eA ▸ le_sup_left
  have MB : M ≤ B := eB ▸ le_sup_left
  have MC : M ≤ C := eC ▸ le_sup_left
  have bxA : b + x ∈ A := eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bB : b ∈ B := eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have xC : x ∈ C := eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hsum : ∀ (y : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E),
      ∑ i, ((ptH D cc δ N t₀ y).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i)) (a i) =
        ptH D cc δ N t₀ y a := by
    intro y a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.univ_sum_single]
  have hin : ∀ (L : Lat D N') (y : Fin N' → D.host.E), y ∈ L → ∀ a : Fin N → 𝓞 D.host.E,
      ptH D cc δ N t₀ y a ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hy a =>
    (ptH_mem hδ L t₀ y a).2 fun j => smul_mem_IL (Submodule.smul_mem _ _ ht₀) hy
  have hinP : ∀ (L : Lat D N') (y : Fin N' → D.host.E), M ≤ L → (∀ p ∈ P, p • y ∈ M) → ∀ i, ∀ p ∈ P,
      ptH D cc δ N t₀ y (Pi.single i p) ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hL hy i p hp =>
    (ptH_mem hδ L t₀ y _).2 fun j => IL_mono hL <| smul_mem_IL_of_P hy <| Submodule.smul_mem_smul (by
      by_cases h : j = i
      · subst h; simpa using hp
      · simp [Pi.single_eq_of_ne h]) ht₀
  refine ⟨fun i => (ptH D cc δ N t₀ b).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun i => (ptH D cc δ N t₀ x).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun _ => phiH D cc δ t₀ b x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a a'
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    rw [Hf_ptH, Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_mul]) (by simp)]
    split_ifs with h
    · subst h; simp only [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, map_zero, mul_zero, map_zero]
  · intro i a
    refine ⟨hin B b bB _, hin C x xC _, ?_⟩
    simp only [AddMonoidHom.comp_apply]
    rw [ptH_add]; exact hin A _ bxA _
  · intro i p hpP
    exact ⟨⟨hinP A b MA (fun p h => (hp p h).1) i p hpP, hinP C b MC (fun p h => (hp p h).1) i p hpP⟩,
      ⟨hinP A x MA (fun p h => (hp p h).2) i p hpP, hinP B x MB (fun p h => (hp p h).2) i p hpP⟩⟩
  · intro z hz
    rw [eB] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).1) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha C MC⟩⟩
  · intro z hz
    rw [eC] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).2) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha B MB⟩⟩
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hA hy bxA) (ha i)
    obtain ⟨o, ho⟩ := sd_int hB bB bB
    refine hθ (hE D b x) hbx (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hC (MC (hp p h).1) xC
    · have : a i • (t₀ * hE D b x) = hE D ((a i • t₀) • b) (b + x) - (a i * o) • t₀ := by
        rw [hE_smul_left, hE_add_right, ← ho]
        simp only [Algebra.smul_def, map_mul]; ring
      rw [this]; exact sub_mem h1 (Submodule.smul_mem _ _ ht₀)
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hB hy bB) (ha i)
    refine hθ (hE D x b) (fun h => hbx (conj_hE D x b ▸ h.conj)) (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hB (MB (hp p h).2) bB
    · rwa [hE_smul_left, smul_mul_assoc] at h1

end GlobalTheory.TriangleColumns
end
end

