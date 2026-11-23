module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS
section
noncomputable section

namespace PI.VolStabSW

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h v hv
    funext j
    refine h v ?_ j
    funext i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro h g hg i
    have hPg : P *ᵥ g = 0 := by
      funext r
      have := congrFun hg r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    exact congrFun (h g hPg) i

theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.toLin'_apply] at hv
    exact (linInd_cols_iff P).1 hP v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' P) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1

theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  rw [linInd_cols_iff]
  intro v hv
  calc v = (W * P) *ᵥ v := by rw [h, Matrix.one_mulVec]
    _ = W *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]

theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun D => D * P
      map_add' := fun D E => Matrix.add_mul D E P
      map_smul' := fun c D => Matrix.smul_mul c D P }
  have hf : ∀ D, f D = D * P := fun D => rfl
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro E
    exact ⟨E * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top] at hrk
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * M - a * a := by omega
  have e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W => ⟨W.1 - L, by rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun D => ⟨D.1 + L, by
        have hD := D.2
        rw [LinearMap.mem_ker, hf] at hD
        rw [Matrix.add_mul, hD, hL, zero_add]⟩
      left_inv := fun W => by ext1; simp
      right_inv := fun D => by ext1; simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker, Nat.mul_sub_left_distrib]

theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  unfold ffH
  simp [Prod.fst_sum, swapR]

theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  unfold ffH
  simp [Prod.snd_sum, swapR]

private theorem ffGram_apply (J : Matrix (Fin M) (Fin M) (k × k))
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    ffGram (swapR k) J X r s = ffH (swapR k) J (X r) (X s) := by
  first
  | rfl
  | simp [ffGram]
  | (unfold ffGram; simp)

private theorem fst_ffGram_eq_V1_mul_map_fst (J : Matrix (Fin M) (Fin M) (k × k)) (X : Fin a → Fin M → k × k)
    (r s : Fin a) :
    (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s = (ffGram (swapR k) J X r s).1 := by
  rw [ffGram_apply, ffH_fst]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, V1, U1, Finset.sum_mul]
  exact Finset.sum_comm

private theorem snd_ffGram_eq_fst_ffGram_swap (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
  rw [ffGram_apply, ffGram_apply, ffH_fst, ffH_snd]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have h := congrArg Prod.fst (hJ x y)
  rw [Prod.fst_swap] at h
  rw [h]
  ring

theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  constructor
  · rintro rfl
    refine Matrix.ext fun r s => ?_
    rw [fst_ffGram_eq_V1_mul_map_fst]
    rfl
  · intro h
    have hf : ∀ r s, (ffGram (swapR k) J X r s).1 = (T r s).1 := fun r s => by
      rw [← fst_ffGram_eq_V1_mul_map_fst]
      exact congrFun (congrFun h r) s
    refine Matrix.ext fun r s => Prod.ext (hf r s) ?_
    rw [snd_ffGram_eq_fst_ffGram_swap J hJ X, hf s r]
    have h2 := congrArg Prod.snd (hT r s)
    rw [Prod.snd_swap] at h2
    exact h2

theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have hJ1 : IsUnit (J.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hJd).1
    rwa [show J.det.1 = (J.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) J] at h1
  have hT1 : IsUnit (T.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hTd).1
    rwa [show T.det.1 = (T.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) T] at h1
  have e : {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} ≃
      {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} :=
    { toFun := fun X => ⟨((T.map Prod.fst)⁻¹ * V1 X.1, J.map Prod.fst * (U1 X.1)ᵀ), by
        have h := (gram_iff J hJ T hT X.1).1 X.2
        show (T.map Prod.fst)⁻¹ * V1 X.1 * (J.map Prod.fst * (U1 X.1)ᵀ) = 1
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V1 X.1), h, Matrix.nonsing_inv_mul _ hT1]⟩
      invFun := fun WP => ⟨fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
          (T.map Prod.fst * WP.1.1) r i), by
        rw [gram_iff J hJ T hT]
        have hU : U1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = ((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ := rfl
        have hV : V1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = T.map Prod.fst * WP.1.1 := rfl
        rw [hU, hV, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (J.map Prod.fst),
          Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul, Matrix.mul_assoc, WP.2, Matrix.mul_one]⟩
      left_inv := fun X => by
        apply Subtype.ext
        funext r i
        apply Prod.ext
        · show (((J.map Prod.fst)⁻¹ * (J.map Prod.fst * (U1 X.1)ᵀ))ᵀ) r i = (X.1 r i).1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ1, Matrix.one_mul,
            Matrix.transpose_transpose]
          rfl
        · show (T.map Prod.fst * ((T.map Prod.fst)⁻¹ * V1 X.1)) r i = (X.1 r i).2
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT1, Matrix.one_mul]
          rfl
      right_inv := fun WP => by
        apply Subtype.ext
        apply Prod.ext
        · show (T.map Prod.fst)⁻¹ * (T.map Prod.fst * WP.1.1) = WP.1.1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT1, Matrix.one_mul]
        · show J.map Prod.fst * (((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ)ᵀ = WP.1.2
          rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1,
            Matrix.one_mul] }
  rw [Nat.card_congr e, card_pairs ha]

end FiniteFieldSplitting

theorem fFSplit_holds : FFSplit := by
  unfold FFSplit
  intro k _ _ M a ha J hJ hJd T hT hTd
  have h := FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd
  simp only [FiniteFieldSplitting.swapR] at h
  rw [h, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : 1 ≤ Nat.card k := Nat.card_pos
  have hi : (i : ℕ) ≤ M := by have := i.isLt; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right h1 hi), Nat.cast_pow, Nat.cast_pow]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x; simp [thick]
  rw [this]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical
  have hC : ∀ y, IsOpen {z : X | z - y ∈ Λ} := fun y =>
    hΛ.preimage (continuous_id.sub continuous_const)
  have hfin : ∀ t : Finset X,
      m1 (⋃ s ∈ t, {z | z - s ∈ Λ}) = m2 (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert s0 t hs0 ih =>
      rw [Finset.set_biUnion_insert]
      by_cases hex : ∃ s ∈ t, s0 - s ∈ Λ
      · obtain ⟨s, hs, hss⟩ := hex
        have hsub : {z : X | z - s0 ∈ Λ} ⊆ ⋃ s ∈ t, {z | z - s ∈ Λ} := by
          intro z hz
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨s, hs, by simpa [sub_add_sub_cancel] using Λ.add_mem hz hss⟩
        rw [Set.union_eq_right.2 hsub, ih]
      · push_neg at hex
        have hdisj : Disjoint {z : X | z - s0 ∈ Λ} (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
          rw [Set.disjoint_left]
          intro z hz hz'
          simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz'
          obtain ⟨s, hs, hzs⟩ := hz'
          apply hex s hs
          simpa [sub_sub_sub_cancel_left] using Λ.sub_mem hzs hz
        have hmeas : MeasurableSet (⋃ s ∈ t, {z : X | z - s ∈ Λ}) :=
          (isOpen_biUnion fun s _ => hC s).measurableSet
        rw [measure_union hdisj hmeas, measure_union hdisj hmeas, h, ih]
  obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun x => {z : X | z - x ∈ Λ})
    (fun x _ => (hC x).mem_nhds (by simp [Λ.zero_mem]))
  have heq : thick S Λ = ⋃ s ∈ t, {z : X | z - s ∈ Λ} := by
    ext x
    simp only [thick, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨u, hu, hsu⟩ := Set.mem_iUnion₂.1 (hcov hs)
      exact ⟨u, hu, by simpa [sub_add_sub_cancel] using Λ.add_mem hxs hsu⟩
    · rintro ⟨u, hu, hxu⟩
      exact ⟨u, htS u hu, hxu⟩
  rw [heq]
  exact hfin t


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [Set.mem_iInter, thick, Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra hxS
    have hc : Continuous fun d : X => x - d := continuous_const.sub continuous_id
    have hN : (fun d : X => x - d) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) :=
      hc.continuousAt.preimage_mem_nhds (hSc.isOpen_compl.mem_nhds (by simpa using hxS))
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have h1 := hn hxs
    simp only [Set.mem_preimage, sub_sub_cancel, Set.mem_compl_iff] at h1
    exact h1 hs
  · intro hx n
    exact ⟨x, hx, by simp [(Λ n).zero_mem]⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro i j hij x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hij hxs⟩
  have hmeas : ∀ n, MeasurableSet (thick S (Λ n)) := fun n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet)
      ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp_rw [heq]

end CosMeas

theorem cosDens_holds : CosDens := by
  intro X _ _ _ _ _ _ ν m _ hν H hHo hHc hanti hb c0 κ hm0 hcos S hS
  have hC : ∀ (n : ℕ) (y : X), IsOpen {z : X | z - y ∈ H n} := fun n y =>
    (hHo n).preimage (continuous_id.sub continuous_const)
  have hC0 : MeasurableSet {z : X | z - c0 ∈ H 0} := (hC 0 c0).measurableSet
  have hback : ∀ n y z, y - c0 ∉ H 0 → z - y ∈ H n → z - c0 ∉ H 0 := by
    intro n y z hy hz hz0
    apply hy
    have hz' : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
    simpa [sub_sub_sub_cancel_left] using (H 0).sub_mem hz0 hz'
  have key := measure_eq_of_cos m (κ • ν.restrict {z : X | z - c0 ∈ H 0}) H hHo hanti hb ?_
    S hS hS.isClosed
  · rw [key, Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
  · intro n y
    rw [Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ⊆ {z : X | z - c0 ∈ H 0} := by
        intro z hz
        have hz0 : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
        simpa [sub_add_sub_cancel] using (H 0).add_mem hz0 hy
      rw [Set.inter_eq_left.2 hsub]
      exact hcos n y hy
    · have hdisj : {z : X | z - y ∈ H n} ∩ {z : X | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact hback n y z hy
      rw [hdisj, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hback n y z hy hz) hm0

end PI.VolStabSW
end
end

