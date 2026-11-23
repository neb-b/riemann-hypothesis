module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.MonoZero
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem {A : Type} [CommRing A] (E : Subring A)
    (S : Subalgebra E (M4 A)) (d : Fin 4 → A) (hd : Matrix.diagonal d ∈ S) (hE : ∀ i, d i ∈ E)
    (i j1 j2 j3 : Fin 4) (hc : ∀ k, k = i ∨ k = j1 ∨ k = j2 ∨ k = j3)
    (n1 : j1 ≠ i) (n2 : j2 ≠ i) (n3 : j3 ≠ i) (u1 u2 u3 : A) (m1 : u1 ∈ E) (m2 : u2 ∈ E) (m3 : u3 ∈ E)
    (e1 : u1 * (d i - d j1) = 1) (e2 : u2 * (d i - d j2) = 1) (e3 : u3 * (d i - d j3) = 1) :
    Matrix.single i i (1 : A) ∈ S := by
  have hF : ∀ a b : A, a ∈ E → b ∈ E → (Matrix.diagonal (fun k => a * (d k - b)) : M4 A) ∈ S := by
    intro a b ha hb
    have h : (Matrix.diagonal (fun k => a * (d k - b)) : M4 A) =
        (⟨a, ha⟩ : E) • (Matrix.diagonal d - algebraMap E (M4 A) ⟨b, hb⟩) := by
      ext k l
      by_cases hkl : k = l
      · subst hkl
        simp [Matrix.diagonal_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, Subring.smul_def, mul_sub]
      · simp [Matrix.diagonal_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, hkl, Subring.smul_def]
    rw [h]
    exact S.smul_mem (S.sub_mem hd (S.algebraMap_mem _)) _
  have hP := S.mul_mem (S.mul_mem (hF u1 (d j1) m1 (hE j1)) (hF u2 (d j2) m2 (hE j2)))
    (hF u3 (d j3) m3 (hE j3))
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal] at hP
  convert hP using 1
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hki : k = i
    · subst hki
      simp [Matrix.single_apply, e1, e2, e3]
    · rcases hc k with h | h | h | h
      · exact absurd h hki
      · subst h; simp [Matrix.single_apply, Ne.symm n1]
      · subst h; simp [Matrix.single_apply, Ne.symm n2]
      · subst h; simp [Matrix.single_apply, Ne.symm n3]
  · simp [Matrix.single_apply, Matrix.diagonal_apply, hkl]
    rintro rfl rfl
    exact absurd rfl hkl

private theorem UpperTheory.V.Ws.single_mem_of_diag {A : Type} [CommRing A] (E : Subring A) (S : Subalgebra E (M4 A)) (d : Fin 4 → A)
    (hd : Matrix.diagonal d ∈ S) (hE : ∀ i, d i ∈ E) (hu : ∀ i j, i ≠ j → ∃ u ∈ E, u * (d i - d j) = 1) (i : Fin 4) :
    Matrix.single i i (1 : A) ∈ S := by
  fin_cases i
  · obtain ⟨u1, m1, e1⟩ := hu 0 1 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 0 2 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 0 3 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3
  · obtain ⟨u1, m1, e1⟩ := hu 1 0 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 1 2 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 1 3 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 1 0 2 3 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3
  · obtain ⟨u1, m1, e1⟩ := hu 2 0 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 2 1 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 2 3 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 2 0 1 3 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3
  · obtain ⟨u1, m1, e1⟩ := hu 3 0 (by decide)
    obtain ⟨u2, m2, e2⟩ := hu 3 1 (by decide)
    obtain ⟨u3, m3, e3⟩ := hu 3 2 (by decide)
    exact UpperTheory.V.Ws.single_diag_mem_of_inverse_differences_mem E S d hd hE 3 0 1 2 (by decide) (by decide) (by decide) (by decide)
      u1 u2 u3 m1 m2 m3 e1 e2 e3

theorem UpperTheory.V.Ws.sxMonoZero :
    ∀ {A Γ : Type} [CommRing A] [Group Γ] (E : Subring A) (r : Γ →* M4 A) (g0 : Γ), (∀ g, ∃ ν ∈ E, IsGSp ν (r g)) → (∀ g, (r g).trace ∈ E) → (r g0).IsDiag → (∀ i, r g0 i i ∈ E) → (∀ i j, i ≠ j → ∃ u ∈ E, u * (r g0 i i - r g0 j j) = 1) → mono r 0 ⊆ E := by
  intro A Γ _ _ E r g0 hν htr hdiag hE hu
  let S : Subalgebra E (M4 A) := Algebra.adjoin E (Set.range r)
  have hcl : ∀ y ∈ Submonoid.closure (Set.range r), ∃ g, r g = y := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, map_one r⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul r a b⟩
  have hsp : ∀ x ∈ S, x ∈ Submodule.span E (Submonoid.closure (Set.range r) : Set (M4 A)) := by
    intro x hx
    rw [← Algebra.adjoin_eq_span]
    exact hx
  have htrSp : ∀ x ∈ Submodule.span E (Submonoid.closure (Set.range r) : Set (M4 A)),
      Matrix.trace x ∈ E := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hcl y hy
      exact htr g
    | zero =>
      rw [Matrix.trace_zero]
      exact E.zero_mem
    | add y z _ _ hy hz =>
      rw [Matrix.trace_add]
      exact E.add_mem hy hz
    | smul c y _ hy =>
      show Matrix.trace ((c : A) • y) ∈ E
      rw [Matrix.trace_smul, smul_eq_mul]
      exact E.mul_mem c.2 hy
  have htrS : ∀ x ∈ S.toSubring, Matrix.trace x ∈ E := fun x hx => htrSp x (hsp x hx)
  have hadj0 : adj (0 : M4 A) = 0 := by
    have h0 := (grp A).2.2.2.1 0 0
    simpa using h0
  have hadjSp : ∀ x ∈ Submodule.span E (Submonoid.closure (Set.range r) : Set (M4 A)),
      adj x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hcl y hy
      obtain ⟨ν, hνE, hG⟩ := hν g
      have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [(grp A).2.2.2.2.2.2.1 ν (r g) (r g⁻¹) hG hinv]
      exact S.smul_mem (Algebra.subset_adjoin ⟨g⁻¹, rfl⟩) (⟨ν, hνE⟩ : E)
    | zero =>
      rw [hadj0]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [(grp A).2.2.1]
      exact S.add_mem hy hz
    | smul c y _ hy =>
      show adj ((c : A) • y) ∈ S
      rw [(grp A).2.2.2.1]
      exact S.smul_mem hy c
  have hadjS : ∀ x ∈ S.toSubring, adj x ∈ S.toSubring := fun x hx => hadjSp x (hsp x hx)
  have hdg : Matrix.diagonal (fun i => r g0 i i) = r g0 := (Matrix.isDiag_iff_diagonal_diag _).1 hdiag
  have hsing : ∀ i, Matrix.single i i (1 : A) ∈ S.toSubring := by
    intro i
    refine UpperTheory.V.Ws.single_mem_of_diag E S (fun i => r g0 i i) ?_ hE hu i
    rw [hdg]
    exact Algebra.subset_adjoin ⟨g0, rfl⟩
  intro x hx
  obtain ⟨L, hL0, rfl⟩ := hx
  have hres := sxGma E S.toSubring hsing htrS hadjS (L.map fun a => (r a.1, a.2))
    (by
      intro y hy
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hy
      exact Algebra.subset_adjoin ⟨a.1, rfl⟩)
    (by rw [List.map_map]; exact hL0)
  rw [List.map_map] at hres
  exact hres
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearConj
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

private theorem nc_wt_self (i : Fin 4) : wt i i = 0 := by revert i; decide

private theorem nc_apply {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) :
    tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

private theorem nc_diag {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i : Fin 4) : tconj t X i i = X i i := by
  rw [nc_apply, nc_wt_self]; simp [wv]

private theorem nc_smul {R : Type} [CommRing R] (t : Rˣ × Rˣ) (c : R) (X : M4 R) : tconj t (c • X) = c • tconj t X := by
  ext i j
  simp only [nc_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearConj :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} (t : Rˣ × Rˣ), Φ.Near a 0 D → ∃ D' : RD Φ R, Φ.Near a 0 D' ∧ (∀ g, D'.r g = tconj t (D.r g)) ∧ D'.ψ = D.ψ := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ D t h
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -, -⟩ := grp R
  let r' : Γ →* M4 R :=
    { toFun := fun g => tconj t (D.r g)
      map_one' := by rw [map_one, hone]
      map_mul' := fun g k => by rw [map_mul, hmul] }
  have hr : ∀ g, r' g = tconj t (D.r g) := fun _ => rfl
  refine ⟨⟨r', D.ψ⟩, ⟨⟨fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩, fun i j N => ?_, h.contψ, fun g i => ?_,
    fun g i j hij hτ => ?_, h.redψ⟩, hr, rfl⟩
  · have := h.rep.mult g
    unfold IsGSp at *
    show adj (tconj t (D.r g)) * tconj t (D.r g) = _
    rw [hadj, ← hmul, this, nc_smul, hone]
  · show tconj t (D.r g) = 1
    rw [h.rep.kill g hg, hone]
  · show tconj t (D.r Φ.g0) i j = 0
    rw [nc_apply, h.rep.nrm hij, mul_zero]
  · exact (h.cont i j N).comp fun x => Ideal.Quotient.mk _ (wv t (wt i j) : R) * x
  · show res Λ R (tconj t (D.r g) i i) = _
    rw [nc_diag, h.diag]
  · show tconj t (D.r g) i j ∈ _
    rw [nc_apply]
    exact Ideal.mul_mem_left _ _ (h.off g i j hij hτ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SplitRes
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem split_r {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (b : O →+* R) (g : Γ) :
    (Φ.split b).r g = Matrix.diagonal fun i => b (Φ.χ i g) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Fr.split, mapRep, diagRep]
  · simp [Fr.split, mapRep, diagRep, Matrix.diagonal_apply_ne _ h]

private theorem split_conj {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (b : O →+* R) (v : Φ.ι)
    (g : Γ) : adj ((Φ.split b).n v) * (Φ.split b).r g * (Φ.split b).n v = Matrix.diagonal fun i => b (Φ.χ i g) := by
  show adj 1 * _ * 1 = _
  rw [(grp R).2.2.2.2.1, one_mul, mul_one, split_r]

private theorem adj_diag {R : Type} [CommRing R] (d : Fin 4 → R) :
    adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
  ext i j
  rw [adj_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    fin_cases i <;> simp [sgn]
  · rw [Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), smul_zero]

private theorem res_self {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsCO Λ (ResidueField Λ)] (x : ResidueField Λ) :
    res Λ (ResidueField Λ) x = x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  have := (res Λ (ResidueField Λ)).commutes a
  rwa [IsLocalRing.ResidueField.algebraMap_eq] at this

theorem UpperTheory.V.Ws.sxSplitRes :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Φ : Fr O Γ} {l : ℕ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} [IsCO Λ (ResidueField Λ)], Φ.Std l a → Φ.IsRes ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) ∧ Φ.Lifts a (Φ.split ((residue Λ).comp a)) (Φ.split ((residue Λ).comp a)) := by
  intro O Γ _ _ _ _ Φ l Λ _ _ a _ hs
  have ok := hs.ok
  have hψ : ∀ v i s, (Φ.split ((residue Λ).comp a)).ψ v i s = (residue Λ).comp a (Φ.χ i s) := by
    intro v i s
    unfold PD.ψ
    rw [split_conj, Matrix.diagonal_apply_eq]
  have hpair : Φ.IsPair ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) := by
    refine ⟨fun g => ?_, fun g hg => ?_, ?_, fun v => ?_, fun v s _ => ?_, fun v s hs' i => ?_⟩
    · show adj _ * _ = _
      rw [split_r, adj_diag, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        rw [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
          ← map_mul, ← Units.val_mul, mul_comm, ok.mul]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    · rw [split_r, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact ok.kill g hg i
    · rw [split_r]
      exact Matrix.isDiag_diagonal _
    · show IsLow (1 : M4 (ResidueField Λ))
      refine ⟨?_, fun i => Matrix.one_apply_eq i, fun i j hij => Matrix.one_apply_ne hij.ne⟩
      show adj 1 * 1 = (1 : ResidueField Λ) • 1
      rw [(grp _).2.2.2.2.1, mul_one, one_smul]
    · rw [split_conj]
      intro i j hji
      exact Matrix.diagonal_apply_ne _ hji.ne'
    · rw [hψ]
      exact (hs.mu v s hs').2 i
  have hres : Φ.Res ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) :=
    ⟨fun g i => by rw [split_r, Matrix.diagonal_apply_eq], fun v s _ i => hψ v i s,
      Or.inr fun g i j hij _ => by rw [split_r, Matrix.diagonal_apply_ne _ hij]⟩
  have hcont : ∀ I, (Φ.split ((residue Λ).comp a)).Cont I := by
    intro I i j N
    by_cases h : i = j
    · subst h
      simp only [split_r, Matrix.diagonal_apply_eq]
      exact (ok.lc i).comp _
    · simp only [split_r, Matrix.diagonal_apply_ne _ h, map_zero]
      exact IsLocallyConstant.const _
  refine ⟨⟨hpair, hres, hcont ⊥⟩, ⟨?_, hcont _, ?_⟩⟩
  · rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact hpair
  · apply PD.ext
    · exact MonoidHom.ext fun g => Matrix.ext fun i j => res_self _
    · funext v
      exact Matrix.ext fun i j => res_self _
end

