module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetMemSpanAdjugate
section
open Matrix

namespace GlobalTheory.FitSquare

variable {R : Type} [CommRing R]

section blocks
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_updateRow_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α]
    (Φ : Matrix α α R) (k : α) (w : α → R) :
    (Φ.updateRow k w).det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  rw [← det_transpose, ← updateCol_transpose, ← cramer_apply, cramer_eq_adjugate_mulVec,
    ← adjugate_transpose]
  simp only [mulVec, dotProduct, transpose_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(l, k), rfl⟩)

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Φ : Matrix α α R) :
    Φ.det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  obtain ⟨i⟩ := ‹Nonempty α›
  have h := det_updateRow_mem_span_adjugate_entries Φ i (Φ i)
  rwa [updateRow_eq_self] at h

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₂₁_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₂₁ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₂₁ _ _ _

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₁₂_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₁₂ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₁₂ _ _ _


open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.FitSquare.relations_mem {M : Type} [AddCommGroup M] [Module R M]
    (π : (n → R) →ₗ[R] M) (hπ : Function.Surjective π) (Φ : Matrix n n R)
    (hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) (T : Matrix m m R)
    (hT : ∀ y, q (T *ᵥ y) = 0) :
    T.det ∈ Ideal.span {Φ.det} ∧ (Nonempty n → ∀ i j, T.adjugate i j ∈
      Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2)) := by
  choose a ha using fun j : m => hπ (q (Pi.single j 1))
  choose b hb using fun i : n => hq (π (Pi.single i 1))
  let A : Matrix n m R := Matrix.of fun i j => a j i
  let B : Matrix m n R := Matrix.of fun j i => b i j
  have hA : ∀ v, π (A *ᵥ v) = q v := by
    have h : π ∘ₗ A.mulVecLin = q := by
      ext j
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply, LinearMap.single_apply,
        mulVec_single_one]
      rw [← ha j]
      rfl
    intro v
    exact LinearMap.congr_fun h v
  let U : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 (-A) 0 1
  let D : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks Φ 0 0 1
  let N : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 0 (-B) T
  have hker : ∀ u v, π u + q v = 0 → ∃ w, (U * D) *ᵥ w = Sum.elim u v := by
    intro u v h
    obtain ⟨z, hz⟩ := hΦ (u + A *ᵥ v) (by rw [map_add (f := _), hA, h])
    refine ⟨Sum.elim z v, ?_⟩
    rw [← mulVec_mulVec]
    simp [U, D, fromBlocks_mulVec, hz, neg_mulVec]
  have hcol : ∀ c, ∃ w, (U * D) *ᵥ w = fun r => N r c := by
    rintro (i | j)
    · obtain ⟨w, hw⟩ := hker (Pi.single i 1) (-b i) (by rw [map_neg, hb, add_neg_cancel])
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N, B, Pi.single_apply, Matrix.one_apply]
    · obtain ⟨w, hw⟩ := hker 0 (fun r => T r j) (by
        have h := hT (Pi.single j 1)
        rw [mulVec_single_one] at h
        rw [map_zero, zero_add]
        exact h)
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N]
  choose w hw using hcol
  have hN : N = U * D * Matrix.of fun r c => w c r := by
    ext r c
    exact (congrFun (hw c) r).symm
  have hdetN : N.det = T.det := by simp [N, det_fromBlocks_zero₁₂]
  have hdetUD : (U * D).det = Φ.det := by simp [U, D, det_fromBlocks_zero₂₁, det_mul]
  refine ⟨?_, ?_⟩
  · rw [← hdetN, hN, det_mul, hdetUD]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro hn p p'
    have hdetJ := det_mem_span_adjugate_entries Φ
    have hD : ∀ x y, D.adjugate x y ∈
        Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2) := by
      intro x y
      rw [adjugate_apply]
      rcases y with k | k
      · rw [det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h : (D.updateRow (Sum.inl k) (Pi.single x 1)).toBlocks₁₁ =
              Φ.updateRow k (fun l => (Pi.single x 1 : n ⊕ m → R) (Sum.inl l)) := by
            ext s t
            by_cases hs : s = k <;> simp [D, toBlocks₁₁, updateRow_apply, hs]
          rw [h]
          exact Ideal.mul_mem_right _ _ (det_updateRow_mem_span_adjugate_entries _ _ _)
        · ext s t
          simp [D, toBlocks₂₁, updateRow_apply]
      · rw [det_eq_mul_of_toBlocks₁₂_eq_zero]
        · have h : (D.updateRow (Sum.inr k) (Pi.single x 1)).toBlocks₁₁ = Φ := by
            ext s t
            simp [D, toBlocks₁₁, updateRow_apply]
          rw [h]
          exact Ideal.mul_mem_right _ _ hdetJ
        · ext s t
          simp [D, toBlocks₁₂, updateRow_apply]
    have hadj : T.adjugate p p' = N.adjugate (Sum.inr p) (Sum.inr p') := by
      rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₁₂_eq_zero]
      · have h₁ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ = 1 := by
          ext s t
          simp [N, toBlocks₁₁, updateRow_apply]
        have h₂ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
            T.updateRow p' (Pi.single p 1) := by
          ext s t
          by_cases hs : s = p' <;> simp [N, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
        rw [h₁, h₂, det_one, one_mul]
      · ext s t
        simp [N, toBlocks₁₂, updateRow_apply]
    rw [hadj, hN, adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_apply]
    refine Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_right _ _ (hD x y)

end blocks


open Matrix in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.FitSquare.fitting_exact : ∀ (R : Type) [CommRing R] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃), Function.Exact f g → Function.Surjective g → ∀ (k : ℕ) (x : R) (v : Fin k → M₁), Submodule.span R (Set.range v) = ⊤ → (∀ m : M₁, x • m = 0) → ∀ (a b : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Ψ : Matrix (Fin b) (Fin b) R), Nonempty (M₂ ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.mulVecLin)) → Nonempty (M₃ ≃ₗ[R] ((Fin b → R) ⧸ LinearMap.range Ψ.mulVecLin)) → x ^ k * Ψ.det ∈ Ideal.span {Φ.det} ∧ (a = 0 ∨ ((∀ p q, x ^ k * Ψ.adjugate p q ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)) ∧ (b = 0 → x ^ k ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)))) := by
  intro R _ M₁ M₂ M₃ _ _ _ _ _ _ f g hfg hg k x v hv hx a b Φ Ψ ⟨e₂⟩ ⟨e₃⟩
  let π : (Fin a → R) →ₗ[R] M₂ := e₂.symm.toLinearMap ∘ₗ (LinearMap.range Φ.mulVecLin).mkQ
  have hπ : Function.Surjective π := e₂.symm.surjective.comp (Submodule.mkQ_surjective _)
  have hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y := by
    intro y hy
    have hy' : (LinearMap.range Φ.mulVecLin).mkQ y = 0 := by
      simpa [π] using hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy'
    obtain ⟨z, hz⟩ := hy'
    exact ⟨z, hz⟩
  let ρ : (Fin b → R) →ₗ[R] M₃ := e₃.symm.toLinearMap ∘ₗ (LinearMap.range Ψ.mulVecLin).mkQ
  have hρ : Function.Surjective ρ := e₃.symm.surjective.comp (Submodule.mkQ_surjective _)
  choose u hu using fun j : Fin b => hg (ρ (Pi.single j 1))
  let H : (Fin b → R) →ₗ[R] M₂ := Fintype.linearCombination R u
  have hgH : ∀ t, g (H t) = ρ t := by
    have h : g ∘ₗ H = ρ := by
      ext j
      simp [H, hu]
    exact fun t => LinearMap.congr_fun h t
  have hkerg : ∀ y, g y = 0 → ∃ c : Fin k → R, ∑ i, c i • f (v i) = y := by
    intro y hy
    obtain ⟨m₁, rfl⟩ := (hfg y).1 hy
    have hm : m₁ ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hm
    exact ⟨c, by simp [map_sum]⟩
  let q : (Fin k ⊕ Fin b → R) →ₗ[R] M₂ :=
    Fintype.linearCombination R (Sum.elim (fun i => f (v i)) u)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨t, ht⟩ := hρ (g y)
    obtain ⟨c, hc⟩ := hkerg (y - H t) (by rw [map_sub, hgH, ht, sub_self])
    refine ⟨Sum.elim c t, ?_⟩
    rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hc]
    simp [H, Fintype.linearCombination_apply]
  have hcolΨ : ∀ j, ∃ c : Fin k → R, ∑ i, c i • f (v i) = H (fun r => Ψ r j) := by
    intro j
    apply hkerg
    rw [hgH]
    simp only [ρ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨Pi.single j 1, by
      rw [mulVecLin_apply, mulVec_single_one]; rfl⟩), map_zero]
  choose C hC using hcolΨ
  let T : Matrix (Fin k ⊕ Fin b) (Fin k ⊕ Fin b) R :=
    fromBlocks (x • 1) (-Matrix.of fun i j => C j i) 0 Ψ
  have hT : ∀ y, q (T *ᵥ y) = 0 := by
    have h0 : q ∘ₗ T.mulVecLin = 0 := by
      ext c
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply,
        LinearMap.single_apply, mulVec_single_one, LinearMap.zero_apply]
      rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
      rcases c with i | j
      · simp [T, col]
        apply Finset.sum_eq_zero
        intro r _
        rw [mul_comm x, mul_smul, ← map_smul, hx, map_zero, smul_zero]
      · have hCj := hC j
        simp only [H, Fintype.linearCombination_apply] at hCj
        simp [T, col, neg_smul, Finset.sum_neg_distrib, hCj]
    exact fun y => LinearMap.congr_fun h0 y
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.FitSquare.relations_mem π hπ Φ hΦ q hq T hT
  have hdetT : T.det = x ^ k * Ψ.det := by simp [T, det_fromBlocks_zero₂₁, det_smul]
  rw [hdetT] at h₁
  refine ⟨h₁, ?_⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact Or.inl ha
  · right
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    refine ⟨fun p p' => ?_, fun hb0 => ?_⟩
    · have hadj : T.adjugate (Sum.inr p) (Sum.inr p') = x ^ k * Ψ.adjugate p p' := by
        rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h₁₁ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ =
              x • 1 := by
            ext s t
            simp [T, toBlocks₁₁, updateRow_apply]
          have h₂₂ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
              Ψ.updateRow p' (Pi.single p 1) := by
            ext s t
            by_cases hs : s = p' <;> simp [T, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
          rw [h₁₁, h₂₂, det_smul, det_one, mul_one, Fintype.card_fin]
        · ext s t
          simp [T, toBlocks₂₁, updateRow_apply]
      rw [← hadj]
      exact h₂ ‹_› _ _
    · subst hb0
      have h₃ : x ^ k ∈ Ideal.span {Φ.det} := by simpa [det_isEmpty] using h₁
      exact (Ideal.span_singleton_le_iff_mem _).2 (det_mem_span_adjugate_entries Φ) h₃

end GlobalTheory.FitSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DisjointFinsetSupOfSupIndepSup
section
namespace GlobalTheory

theorem disjoint_finset_sup_of_supIndep_sup :
    ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V),
      F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) →
        Disjoint (F.sup G) (F.sup B) := by
  intro R V ι _ _ _ F G B hind hdis
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : s.SupIndep (fun i => G i ⊔ B i) := hind.subset (Finset.subset_insert _ _)
    have ih' := ih hs (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
    have hA : Disjoint (G a ⊔ B a) (s.sup fun i => G i ⊔ B i) :=
      hind (Finset.subset_insert a s) (Finset.mem_insert_self a s) ha
    have hGs : s.sup G ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_left)
    have hBs : s.sup B ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_right)
    rw [Finset.sup_insert, Finset.sup_insert, Submodule.disjoint_def]
    intro x hxG hxB
    obtain ⟨g, hg, g', hg', rfl⟩ := Submodule.mem_sup.mp hxG
    obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.mp hxB
    have h1 : g - b ∈ G a ⊔ B a := Submodule.sub_mem _ (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hb)
    have h2 : g - b ∈ s.sup (fun i => G i ⊔ B i) := by
      have : g - b = b' - g' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm b' b, hbb]
      rw [this]
      exact Submodule.sub_mem _ (hBs hb') (hGs hg')
    have h3 : g - b = 0 := (Submodule.disjoint_def.mp hA) _ h1 h2
    have hgb : g = b := sub_eq_zero.mp h3
    have hg0 : g = 0 := (Submodule.disjoint_def.mp (hdis a (Finset.mem_insert_self a s))) g hg (hgb ▸ hb)
    have hg'b' : g' = b' := by
      subst hgb
      exact add_left_cancel hbb.symm
    have hg'0 : g' = 0 := (Submodule.disjoint_def.mp ih') g' hg' (hg'b' ▸ hb')
    rw [hg0, hg'0, add_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubIffMapMkEq
section
universe u_1 u_2 u_3

namespace GlobalTheory.DvdSubMapMk

theorem dvd_sub_iff_map_mk_eq {R : Type u_1} [inst : CommRing R] {p : Type u_2} {q : Type u_3}
    (a : R) (A B : Matrix p q R) :
    (∀ (i : p) (j : q), a ∣ (A - B) i j) ↔
      Matrix.map A (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) =
        Matrix.map B (⇑(Ideal.Quotient.mk (Ideal.span {a})) : R → R ⧸ Ideal.span {a}) := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    Matrix.sub_apply]

end GlobalTheory.DvdSubMapMk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
section
noncomputable section

open PowerSeries

namespace GlobalTheory.NB.LT

def F (R : Type) [CommRing R] (l : ℕ) : Polynomial R :=
  Polynomial.X * (Polynomial.X + Polynomial.C (l : R)) ^ (l - 1)

abbrev EE (R : Type) [CommRing R] (l : ℕ) : Type :=
  AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))

variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma subsingleton_of_isHausdorff_whole_ideal {I : Ideal R} [IsHausdorff I R] (h : I = ⊤) :
    Subsingleton R := by
  subst h
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : R, z = 0 := fun z =>
    IsHausdorff.haus ‹_› z fun n => by simp [Ideal.top_pow, SModEq.top]
  rw [key x, key y]

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma order_map_toNat_eq_natDegree_of_isDistinguishedAt {I : Ideal R} {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (hI : I ≠ ⊤) :
    ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat = p.natDegree := by
  have h1 : constantCoeff (1 : R⟦X⟧) ∉ I := by
    simpa [Ideal.eq_top_iff_one] using hI
  have := H.coe_natDegree_eq_order_map (p : R⟦X⟧) 1 h1 (by simp)
  rw [← this]
  simp


open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.exists_poly_mod [Nontrivial R] {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (a : R⟦X⟧) :
    ∃ r : Polynomial R, r.degree < p.degree ∧ (p : R⟦X⟧) ∣ a - r := by
  have hI : I ≠ ⊤ := by
    intro h
    have := subsingleton_of_isHausdorff_whole_ideal (I := I) h
    exact not_subsingleton R this
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hd := D.isWeierstrassDivisionAt_div_mod a
  refine ⟨D.mod a, ?_, D.div a, sub_eq_iff_eq_add.mpr hd.eq_mul_add⟩
  have hlt := hd.degree_lt
  rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI] at hlt
  rwa [Polynomial.degree_eq_natDegree (Polynomial.Monic.ne_zero H.monic)]


open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.poly_dvd_of_dvd {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) {r : Polynomial R} (h : (p : R⟦X⟧) ∣ (r : R⟦X⟧)) : p ∣ r := by
  by_cases hI : I = ⊤
  · have := subsingleton_of_isHausdorff_whole_ideal (I := I) hI
    rw [Subsingleton.elim r 0]
    exact dvd_zero p
  have hm := H.monic
  obtain ⟨h, hh⟩ := h
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hdeg : (r %ₘ p).degree < ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat := by
    rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI]
    by_cases hs : Nontrivial R
    · exact (Polynomial.degree_modByMonic_lt r hm).trans_le Polynomial.degree_le_natDegree
    · rw [not_nontrivial_iff_subsingleton] at hs
      rw [Subsingleton.elim (r %ₘ p) 0]
      simp
  have hmul : (p : R⟦X⟧) * (h - ((r /ₘ p : Polynomial R) : R⟦X⟧)) = ((r %ₘ p : Polynomial R) : R⟦X⟧) := by
    have e := Polynomial.modByMonic_add_div r p
    have e' : ((r %ₘ p : Polynomial R) : R⟦X⟧) + (p : R⟦X⟧) * ((r /ₘ p : Polynomial R) : R⟦X⟧)
        = (r : R⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_add, e]
    rw [mul_sub, ← hh, ← e']
    ring
  have := (D.eq_zero_of_mul_eq hdeg hmul).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).mp this

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.algHom_coe {B : Type} [CommRing B] [Algebra R B] (σ : R⟦X⟧ →ₐ[R] B) (r : Polynomial R) :
    σ (r : R⟦X⟧) = Polynomial.aeval (σ X) r := by
  have e : σ.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (σ X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun e r

open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma X_pow_dvd_sub_aeval_trunc (ρ : R⟦X⟧ →ₐ[R] R⟦X⟧) (hρ : X ∣ ρ X) (n : ℕ)
    (f : R⟦X⟧) : X ^ n ∣ ρ f - Polynomial.aeval (ρ X) (trunc n f) := by
  obtain ⟨g, hg⟩ : X ^ n ∣ f - (trunc n f : R⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [coeff_trunc, hm]
  have e : ρ f - Polynomial.aeval (ρ X) (trunc n f) = ρ (X ^ n) * ρ g := by
    rw [← _root_.GlobalTheory.NB.LT.algHom_coe ρ, ← map_sub, hg, map_mul]
  rw [e, map_pow]
  exact (pow_dvd_pow_of_dvd hρ n).mul_right _


open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
theorem _root_.GlobalTheory.NB.LT.algHom_ext_X (σ τ : R⟦X⟧ →ₐ[R] R⟦X⟧) (h : σ X = τ X) (hX : X ∣ σ X) : σ = τ := by
  refine AlgHom.ext fun f => PowerSeries.ext fun m => ?_
  have h1 := X_pow_dvd_sub_aeval_trunc σ hX (m + 1) f
  have h2 := X_pow_dvd_sub_aeval_trunc τ (h ▸ hX) (m + 1) f
  rw [h] at h1
  have h3 := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  have := (X_pow_dvd_iff.mp h3) m (Nat.lt_succ_self m)
  rwa [map_sub, sub_eq_zero] at this

end GlobalTheory.NB.LT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimage
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem dvr_matrix_proj_preimage (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n]
    (S : Submodule K (n → K)) :
    ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧
      ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  classical
  let f : (n → O) →ₗ[O] (n → K) := LinearMap.compLeft (Algebra.linearMap O K) n
  let U : Submodule O (n → O) := (S.restrictScalars O).comap f
  have hmem : ∀ v : n → O, v ∈ U ↔ (fun i => algebraMap O K (v i)) ∈ S := fun v => Iff.rfl
  have htf : NoZeroSMulDivisors O ((n → O) ⧸ U) := by
    constructor
    intro c x hcx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U x
    by_cases hc : c = 0
    · left; exact hc
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcx
    rw [Submodule.Quotient.mk_eq_zero]
    rw [hmem] at hcx ⊢
    have e : (fun i => algebraMap O K ((c • v) i)) = algebraMap O K c • (fun i => algebraMap O K (v i)) := by
      funext i; simp [Algebra.smul_def]
    rw [e] at hcx
    have hc' : algebraMap O K c ≠ 0 := by
      intro h; exact hc ((IsFractionRing.injective O K) (by rw [h, map_zero]))
    have := S.smul_mem (algebraMap O K c)⁻¹ hcx
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
  haveI : Module.Free O ((n → O) ⧸ U) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective O ((n → O) ⧸ U) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property U.mkQ LinearMap.id (Submodule.mkQ_surjective U)
  let π : (n → O) →ₗ[O] (n → O) := LinearMap.id - s ∘ₗ U.mkQ
  have hπU : ∀ v, π v ∈ U := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (U.mkQ v)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply U (s _), this, Submodule.mkQ_apply, sub_self]
  have hπfix : ∀ u ∈ U, π u = u := by
    intro u hu
    have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]
  refine ⟨LinearMap.toMatrix' π, ?_, ?_⟩
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    exact hπU v
  · intro u hu
    rw [LinearMap.toMatrix'_mulVec]
    exact hπfix u hu

end GlobalTheory
end

